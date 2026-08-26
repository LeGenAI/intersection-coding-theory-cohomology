#!/usr/bin/env python3
"""Generate the Comparator pair for every theorem in BuildingUpFormalization."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path


EXPECTED_THEOREM_COUNT = 260
THEOREM_START = re.compile(r"(?:@\[[^\n]*\]\s+)*theorem\s+([A-Za-z_][A-Za-z0-9_']*)\b")


@dataclass(frozen=True)
class TheoremCommand:
    name: str
    start: int
    proof_delimiter: int
    end: int


def mask_comments_and_strings(source: str) -> str:
    """Replace non-code characters with spaces while preserving newlines/offsets."""
    masked = list(source)
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False
    i = 0

    while i < len(source):
        ch = source[i]
        nxt = source[i + 1] if i + 1 < len(source) else ""

        if ch == "\n":
            in_line_comment = False
            escaped = False
            i += 1
            continue

        if in_line_comment:
            masked[i] = " "
            i += 1
            continue

        if block_depth:
            masked[i] = " "
            if ch == "/" and nxt == "-":
                masked[i + 1] = " "
                block_depth += 1
                i += 2
            elif ch == "-" and nxt == "/":
                masked[i + 1] = " "
                block_depth -= 1
                i += 2
            else:
                i += 1
            continue

        if in_string:
            masked[i] = " "
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue

        if ch == "-" and nxt == "-":
            masked[i] = masked[i + 1] = " "
            in_line_comment = True
            i += 2
        elif ch == "/" and nxt == "-":
            masked[i] = masked[i + 1] = " "
            block_depth = 1
            i += 2
        elif ch == '"':
            masked[i] = " "
            in_string = True
            i += 1
        else:
            i += 1

    if block_depth or in_string:
        raise ValueError("unterminated block comment or string literal")
    return "".join(masked)


def line_starts(text: str) -> list[int]:
    starts = [0]
    starts.extend(i + 1 for i, ch in enumerate(text) if ch == "\n" and i + 1 < len(text))
    return starts


def top_level_boundaries(source: str, masked: str) -> list[int]:
    """Find starts of top-level commands and top-level comments."""
    boundaries: list[int] = []
    command = re.compile(
        r"(?:@\[[^\n]*\]\s+)*(?:"
        r"import|open|section|namespace|end|variable|include|omit|"
        r"def|noncomputable\s+def|abbrev|structure|class|inductive|"
        r"theorem|lemma|instance|attribute|set_option|local|protected|private"
        r")\b"
    )
    for start in line_starts(source):
        raw_line = source[start : source.find("\n", start) if "\n" in source[start:] else len(source)]
        code_line = masked[start : start + len(raw_line)]
        if command.match(code_line):
            boundaries.append(start)
        elif code_line.strip() == "" and (raw_line.startswith("/-") or raw_line.startswith("--")):
            boundaries.append(start)
    return boundaries


def theorem_commands(source: str) -> list[TheoremCommand]:
    masked = mask_comments_and_strings(source)
    boundaries = top_level_boundaries(source, masked)
    commands: list[TheoremCommand] = []

    for index, start in enumerate(boundaries):
        line_end = source.find("\n", start)
        if line_end == -1:
            line_end = len(source)
        match = THEOREM_START.match(masked[start:line_end])
        if not match:
            continue
        end = next((offset for offset in boundaries[index + 1 :] if offset > start), len(source))
        proof_delimiter = find_proof_delimiter(masked, start, end)
        if proof_delimiter == -1:
            raise ValueError(f"theorem {match.group(1)!r} has no ':=' proof delimiter")
        commands.append(TheoremCommand(match.group(1), start, proof_delimiter, end))

    names = [command.name for command in commands]
    duplicates = sorted({name for name in names if names.count(name) > 1})
    if duplicates:
        raise ValueError(f"duplicate theorem names: {', '.join(duplicates)}")
    if len(commands) != EXPECTED_THEOREM_COUNT:
        raise ValueError(
            f"expected {EXPECTED_THEOREM_COUNT} theorem declarations, found {len(commands)}"
        )
    return commands


def find_proof_delimiter(masked: str, start: int, end: int) -> int:
    """Find the proof `:=`, ignoring named arguments and `let` binders in the type."""
    opening = {"(": ")", "[": "]", "{": "}"}
    closing = set(opening.values())
    stack: list[str] = []
    candidates: list[int] = []
    i = start
    while i < end - 1:
        ch = masked[i]
        if ch in opening:
            stack.append(opening[ch])
        elif ch in closing:
            if not stack or stack.pop() != ch:
                raise ValueError(f"unbalanced delimiter near source offset {i}")
        elif ch == ":" and masked[i + 1] == "=" and not stack:
            candidates.append(i)
        i += 1
    for candidate in candidates:
        following = masked[candidate + 2 : end].lstrip()
        if re.match(r"by\b", following):
            return candidate
    return candidates[0] if len(candidates) == 1 else -1


def active_sections(source: str, masked: str, before: int) -> list[str]:
    """Return named sections open immediately before a source offset."""
    stack: list[str] = []
    for start in line_starts(source):
        if start >= before:
            break
        line_end = source.find("\n", start)
        if line_end == -1:
            line_end = len(source)
        code_line = masked[start:line_end]
        opened = re.match(r"section\s+([A-Za-z_][A-Za-z0-9_']*)\b", code_line)
        if opened:
            stack.append(opened.group(1))
            continue
        closed = re.match(r"end(?:\s+([A-Za-z_][A-Za-z0-9_']*))?\s*$", code_line)
        if closed:
            if not stack:
                raise ValueError(f"unmatched section end at source offset {start}")
            expected = stack.pop()
            if closed.group(1) not in (None, expected):
                raise ValueError(
                    f"section end {closed.group(1)!r} does not close {expected!r}"
                )
    return stack


def module_stem(index: int, theorem_name: str) -> str:
    words = [word for word in theorem_name.split("_") if word]
    camel = "".join(word[0].upper() + word[1:] for word in words)
    return f"T{index:03d}{camel}"


def single_theorem_challenge(
    source: str, masked: str, command: TheoremCommand
) -> str:
    sections = active_sections(source, masked, command.start)
    closers = "".join(f"end {name}\n" for name in reversed(sections))
    return source[: command.proof_delimiter + 2] + " by\n  sorry\n\n" + closers


def generated_files(project: Path) -> dict[Path, str]:
    source_path = project / "Formalization" / "Archive" / "SubmittedBaseline.lean"
    output_dir = project / "ComparatorChallenges/BuildingUp"
    source = source_path.read_text(encoding="utf-8")
    commands = theorem_commands(source)
    masked = mask_comments_and_strings(source)
    names = [command.name for command in commands]
    digest = hashlib.sha256(source.encode("utf-8")).hexdigest()
    challenge_dir = output_dir / "AllTheorems"
    generated: dict[Path, str] = {
        output_dir / "BuildingUpAllSolution.lean": source,
        output_dir / "BuildingUpAllAxiomAudit.lean": (
            "import ComparatorChallenges.BuildingUp.BuildingUpAllSolution\n\n"
            + "\n".join(f"#print axioms {name}" for name in names)
            + "\n"
        ),
    }
    inventory = ["index\ttheorem\tchallenge_module\tconfig"]

    for index, command in enumerate(commands, start=1):
        stem = module_stem(index, command.name)
        challenge_module = f"ComparatorChallenges.BuildingUp.AllTheorems.{stem}Challenge"
        config = {
            "challenge_module": challenge_module,
            "solution_module": "ComparatorChallenges.BuildingUp.BuildingUpAllSolution",
            "theorem_names": [command.name],
            "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
            "enable_nanoda": False,
        }
        generated[challenge_dir / f"{stem}Challenge.lean"] = single_theorem_challenge(
            source, masked, command
        )
        generated[challenge_dir / f"{stem}.json"] = json.dumps(config, indent=2) + "\n"
        inventory.append(f"{index}\t{command.name}\t{challenge_module}\t{stem}.json")

    manifest = {
        "source": "Formalization/Archive/SubmittedBaseline.lean",
        "source_sha256": digest,
        "theorem_count": len(names),
        "strategy": (
            "One cumulative challenge per theorem: preserve the exact source prefix and prior proofs, "
            "replace only the target proof by `by sorry`, omit later declarations, and close open sections."
        ),
    }
    generated[output_dir / "manifest.json"] = json.dumps(manifest, indent=2) + "\n"
    generated[output_dir / "theorems.tsv"] = "\n".join(inventory) + "\n"
    return generated


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="fail if generated files are stale")
    args = parser.parse_args()

    project = Path(__file__).resolve().parent.parent
    expected = generated_files(project)
    stale: list[str] = []
    for path, content in expected.items():
        if args.check:
            if not path.exists() or path.read_text(encoding="utf-8") != content:
                stale.append(str(path.relative_to(project)))
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8")

    if stale:
        raise SystemExit("stale generated files:\n  " + "\n  ".join(stale))
    action = "verified" if args.check else "generated"
    print(f"{action} {len(expected)} files for {EXPECTED_THEOREM_COUNT} theorems")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
