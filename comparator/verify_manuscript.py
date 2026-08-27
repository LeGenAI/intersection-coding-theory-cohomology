#!/usr/bin/env python3
"""Build and audit all manuscript goals; optionally replay Comparator on Linux.

Output must be a new directory. No SSH setup or machine-specific path is needed
in the artifact. Supply the three pinned tool binaries for a Linux replay.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
from datetime import datetime, timezone

from generate_challenge import mask_comments_and_strings

ROOT = Path(__file__).resolve().parent.parent
CONFIGS = ROOT / "Formalization/Verification/Comparator"
AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
TOOL_HASHES = {
    "comparator": "1b7b27b0233fd75672eeb777fec1c35257f1fb111acbb9cbcb2d0674a7b2c154",
    "lean4export": "293e221ed1b515de1aeaf06d2fe8f3f919f0b75f1e4d3b228f43f53d576501ea",
    "landrun": "6ada66a06669e8994e174a7271af2db636308e55a0d6ec896cc7d326b46727f6",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def closure(modules):
    seen = set()
    pending = list(modules)
    while pending:
        module = pending.pop()
        path = ROOT / (module.replace(".", "/") + ".lean")
        if not path.exists() or path in seen:
            continue
        seen.add(path)
        source = mask_comments_and_strings(path.read_text())
        for imports in re.findall(r"^\s*import\s+([^\n]+)", source, re.M):
            pending.extend(imports.split())
    return seen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True)
    for name in TOOL_HASHES:
        parser.add_argument("--" + name)
    args = parser.parse_args()
    configs = [(p, json.loads(p.read_text())) for p in sorted(CONFIGS.glob("*.json"))]
    names = [name for _, c in configs for name in c["theorem_names"]]
    require(len(configs) == 17 and len(names) == len(set(names)) == 123, "suite/goal inventory")
    for path, c in configs:
        require(set(c["permitted_axioms"]) == AXIOMS and c["enable_nanoda"] is False,
                f"trust configuration: {path.name}")
    solutions = [c["solution_module"] for _, c in configs]
    production = closure(solutions)
    for path in production:
        source = mask_comments_and_strings(path.read_text())
        require(not re.search(r"\b(sorry|admit|axiom|sorryAx|native_decide|implemented_by)\b", source),
                f"forbidden production token: {path.relative_to(ROOT)}")
        require(not path.name.endswith("Challenge.lean"), "Solution imports a Challenge")
    inputs = production | closure([c["challenge_module"] for _, c in configs])
    inputs |= closure(["Formalization", "Formalization.Verification.Examples.RankTwoGF5",
                       "Formalization.Verification.Examples.LargeGF13"])
    inputs |= {p for p, _ in configs}
    inputs |= {ROOT / n for n in ["lakefile.lean", "lake-manifest.json", "lean-toolchain",
                                  "comparator/verify_manuscript.py", "comparator/generate_challenge.py"]}
    inputs |= set((ROOT / "Formalization/Verification/Examples").glob("*applications*"))
    inputs |= set((ROOT / "Formalization/Verification/Examples").glob("*golay*"))
    inputs.add(ROOT / "Formalization/Verification/Examples/check_applications.py")
    inputs.add(ROOT / "Formalization/Verification/Examples/build_application_catalog.py")
    inputs.add(ROOT / "Formalization/Verification/Examples/application_catalog.json")
    inputs.add(ROOT / "Formalization/Verification/Examples/application_catalog_data.tex")
    inputs |= set((ROOT / "Formalization/Verification/Examples/certificates").glob("*.json"))
    hashes = {str(p.relative_to(ROOT)): sha(p) for p in sorted(inputs)}
    out = Path(args.output).resolve()
    out.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ)
    replay = any(getattr(args, n) for n in TOOL_HASHES)
    tools = {}
    if replay:
        require(platform.system() == "Linux", "Comparator replay requires Linux")
        tool_dir = out / "tools"
        tool_dir.mkdir()
        for name, expected in TOOL_HASHES.items():
            supplied = getattr(args, name)
            require(supplied is not None, f"missing --{name}")
            path = Path(supplied).resolve()
            require(sha(path) == expected, f"pinned tool hash mismatch: {name}")
            (tool_dir / name).symlink_to(path)
            tools[name] = expected
        env["PATH"] = str(tool_dir) + os.pathsep + env["PATH"]
    report = dict(status="RUNNING", started_utc=datetime.now(timezone.utc).isoformat(),
                  platform=platform.system(), suite_count=17, goal_count=123,
                  production_file_count=len(production), forbidden_token_scan="PASS",
                  comparator_replayed=replay, tool_sha256=tools, inputs=hashes, steps=[])

    def save():
        (out / "summary.json").write_text(json.dumps(report, indent=2) + "\n")

    def run(name, command, input_text=None, markers=()):
        print("START " + name, flush=True)
        log = out / (name + ".log")
        with log.open("x") as stream:
            result = subprocess.run(command, cwd=ROOT, env=env, input=input_text,
                                    text=True, stdout=stream, stderr=subprocess.STDOUT, timeout=3600)
        contents = log.read_text()
        passed = result.returncode == 0 and all(m in contents for m in markers)
        report["steps"].append(dict(name=name, command=command, exit_code=result.returncode,
                                    status="PASS" if passed else "FAIL", log=log.name, sha256=sha(log)))
        save()
        require(passed, f"failed {name}; inspect {log}")
        print("PASS " + name, flush=True)
        return contents

    save()
    try:
        version = run("lean-version", ["lake", "env", "lean", "--version"])
        require("4.29.0-rc6" in version, "Lean version")
        lock = json.loads((ROOT / "lake-manifest.json").read_text())
        dependencies = {}
        for package in lock["packages"]:
            repo = ROOT / ".lake/packages" / package["name"]
            commit = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"], text=True).strip()
            require(commit == package["rev"], "dependency revision: " + package["name"])
            subprocess.run(["git", "-C", str(repo), "diff", "--quiet", "HEAD", "--"], check=True)
            dependencies[package["name"]] = commit
        report["dependencies"] = dependencies
        run("build", ["lake", "build", "Formalization.Sections.All", *solutions])
        if replay:
            for path, _ in configs:
                run("comparator-" + path.stem,
                    ["lake", "env", "comparator", str(path.relative_to(ROOT))],
                    markers=("Lean default kernel accepts the solution", "Your solution is okay!"))
        audit = "\n".join("import " + m for m in solutions) + "\n"
        audit += "\n".join("#print axioms " + n for n in names) + "\n"
        contents = run("axioms", ["lake", "env", "lean", "--stdin"], input_text=audit)
        found = {name: [a.strip() for a in values.split(",") if a.strip()]
                 for name, values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", contents)}
        require(set(found) == set(names), "exact axiom-report coverage")
        require(all(set(values) <= AXIOMS for values in found.values()), "unpermitted transitive axiom")
        report["axioms"] = found
        run("rank-two-gf5", ["lake", "env", "lean", "Formalization/Verification/Examples/RankTwoGF5.lean"])
        run("large-gf13", ["lake", "env", "lean", "Formalization/Verification/Examples/LargeGF13.lean"])
        run("applications", ["python3", "Formalization/Verification/Examples/check_applications.py", "--check"])
        run("large-applications",
            ["python3", "Formalization/Verification/Examples/check_large_applications.py", "--check"])
        run("golay-lineage",
            ["python3", "Formalization/Verification/Examples/check_golay_lineage.py", "--check"])
        run("application-catalogue",
            ["python3", "Formalization/Verification/Examples/build_application_catalog.py", "--check"])
        require(all(sha(ROOT / p) == h for p, h in hashes.items()), "input changed during verification")
        report.update(status="PASS", inputs_unchanged=True)
    except Exception as error:
        report.update(status="FAIL", error=str(error))
        raise
    finally:
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save()
    print("PASS: 17 suites / 123 axiom reports" + (" / 123 Linux Comparator goals" if replay else " (local audit)"))


if __name__ == "__main__":
    main()
