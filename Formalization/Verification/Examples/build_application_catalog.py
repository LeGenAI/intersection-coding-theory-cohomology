#!/usr/bin/env python3
"""Build the public application catalogue and per-code certificates.

The numerical verifiers remain the source of truth.  This script only
packages their deterministic JSON outputs into reviewer-facing records and
generates the compact table used by the manuscript.
"""

import argparse
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
REPOSITORY = (
    "https://github.com/LeGenAI/intersection-coding-theory-cohomology/"
    "blob/afm-revision-2026-08-27/"
    "Formalization/Verification/Examples/certificates"
)


CATALOGUE_METADATA = {
    "gf5_6": {
        "artifact_id": "GF5-06",
        "display_name": r"C_{6}^{(5)}",
        "construction": "split box, $r=1$",
        "distance_status": "optimal (Singleton)",
        "prior_benchmark": {"distance": 4, "a_d": [60], "reference": r"Leon--Pless--Sloane DB~\cite{LeonPlessSloane}"},
        "public_a_d_min_achieved": True,
        "parent": "GF5-04",
        "manuscript_role": "table",
    },
    "gf5_8": {
        "artifact_id": "GF5-08",
        "display_name": r"C_{8}^{(5)}",
        "construction": "split box, $r=1$",
        "distance_status": "optimal (Ball)",
        "prior_benchmark": {"distance": 4, "a_d": [48], "reference": r"Leon--Pless--Sloane DB~\cite{LeonPlessSloane}"},
        "public_a_d_min_achieved": True,
        "parent": "GF5-06",
        "manuscript_role": "table",
    },
    "gf13_8": {
        "artifact_id": "GF13-08",
        "display_name": r"C_{8}^{(13)}",
        "construction": "split box, $r=1$",
        "distance_status": "MDS",
        "prior_benchmark": {"distance": 5, "a_d": [672], "reference": r"Betsumiya et al.~\cite{BetsumiyaEtAl}"},
        "public_a_d_min_achieved": True,
        "parent": None,
        "manuscript_role": "table",
    },
    "gf13_10": {
        "artifact_id": "GF13-10",
        "display_name": r"C_{10}^{(13)}",
        "construction": "split box, $r=1$",
        "distance_status": "MDS",
        "prior_benchmark": {"distance": 6, "a_d": [2520], "reference": r"Betsumiya et al.~\cite{BetsumiyaEtAl}"},
        "public_a_d_min_achieved": True,
        "parent": None,
        "manuscript_role": "table",
    },
    "gf13_12": {
        "artifact_id": "GF13-12A",
        "display_name": r"C_{12,A}^{(13)}",
        "construction": "split box, $r=1$",
        "distance_status": "exact $d=6$",
        "prior_benchmark": {"distance": 6, "a_d": [528, 576, 696, 792], "reference": r"Betsumiya et al.~\cite{BetsumiyaEtAl}"},
        "public_a_d_min_achieved": False,
        "parent": None,
        "manuscript_role": "table",
    },
    "gf13_14_parent": {
        "artifact_id": "GF13-12P",
        "display_name": r"C_{12,P}^{(13)}",
        "construction": "two-coordinate parent",
        "distance_status": "exact $d=6$",
        "prior_benchmark": {"distance": 6, "a_d": [528, 576, 696, 792], "reference": r"Betsumiya et al.~\cite{BetsumiyaEtAl}"},
        "public_a_d_min_achieved": False,
        "parent": None,
        "manuscript_role": "table",
    },
    "gf13_14_mds": {
        "artifact_id": "GF13-14",
        "display_name": r"C_{14}^{(13)}",
        "construction": "universal box, $r=1$",
        "distance_status": "MDS",
        "prior_benchmark": {"distance": 8, "a_d": [36036], "reference": r"Betsumiya et al.~\cite{BetsumiyaEtAl}"},
        "public_a_d_min_achieved": True,
        "parent": "GF13-12P",
        "manuscript_role": "proposition",
    },
}


def certificate_filename(artifact_id):
    return artifact_id.lower() + ".json"


def tex_escape_status(status):
    return status


def build_outputs():
    small = json.loads((HERE / "applications_results.json").read_text())
    large = json.loads((HERE / "large_applications_results.json").read_text())
    small_by_id = {entry["id"]: entry for entry in small["examples"]}

    entries = []
    certificates = {}
    for source_id in ("gf5_6", "gf5_8", "gf13_8", "gf13_10", "gf13_12"):
        result = small_by_id[source_id]
        metadata = CATALOGUE_METADATA[source_id]
        entry = {
            "artifact_id": metadata["artifact_id"],
            "field_order": result["p"],
            "parameters": [result["n"], result["k"], result["distance"]],
            "construction": metadata["construction"].replace("$", ""),
            "distance_status": metadata["distance_status"].replace("$", ""),
            "a_d": result["weight_distribution"][result["distance"]],
            "prior_benchmark": metadata["prior_benchmark"],
            "public_a_d_min_achieved": metadata["public_a_d_min_achieved"],
            "parent": metadata["parent"],
            "manuscript_role": metadata["manuscript_role"],
            "certificate": "certificates/" + certificate_filename(metadata["artifact_id"]),
            "verifier": "check_applications.py --check",
        }
        entries.append(entry)
        certificates[entry["certificate"]] = {
            "catalogue_entry": entry,
            "source": "applications_results.json",
            "source_method": small["method"],
            "result": result,
        }

    metadata = CATALOGUE_METADATA["gf13_14_parent"]
    result = large["deletion_parent"]
    parent_distance = result["parameters"][2]
    entry = {
        "artifact_id": metadata["artifact_id"],
        "field_order": 13,
        "parameters": result["parameters"],
        "construction": metadata["construction"],
        "distance_status": metadata["distance_status"].replace("$", ""),
        "a_d": result["weight_distribution"][parent_distance],
        "prior_benchmark": metadata["prior_benchmark"],
        "public_a_d_min_achieved": metadata["public_a_d_min_achieved"],
        "parent": metadata["parent"],
        "manuscript_role": metadata["manuscript_role"],
        "certificate": "certificates/" + certificate_filename(metadata["artifact_id"]),
        "verifier": "check_large_applications.py --check",
    }
    entries.append(entry)
    certificates[entry["certificate"]] = {
        "catalogue_entry": entry,
        "source": "large_applications_results.json#deletion_parent",
        "result": result,
    }

    metadata = CATALOGUE_METADATA["gf13_14_mds"]
    result = large["code"]
    entry = {
        "artifact_id": metadata["artifact_id"],
        "field_order": 13,
        "parameters": result["parameters"],
        "construction": metadata["construction"].replace("$", ""),
        "distance_status": metadata["distance_status"],
        "a_d": 36036,
        "prior_benchmark": metadata["prior_benchmark"],
        "public_a_d_min_achieved": metadata["public_a_d_min_achieved"],
        "parent": metadata["parent"],
        "manuscript_role": metadata["manuscript_role"],
        "certificate": "certificates/" + certificate_filename(metadata["artifact_id"]),
        "verifier": "check_large_applications.py --check",
    }
    entries.append(entry)
    certificates[entry["certificate"]] = {
        "catalogue_entry": entry,
        "source": "large_applications_results.json",
        "result": large,
    }

    catalogue = {
        "schema_version": 1,
        "policy": {
            "proposition": "A bound improvement, a proved optimal result, or a structurally new exact realization used in the main argument.",
            "table": "A reproducible construction that illustrates the method without carrying a separate theorem-level claim.",
            "bold_a_d": "The achieved A_d is minimal in a complete public online classification at the displayed best distance, or is fixed by the MDS weight enumerator.",
        },
        "entries": entries,
    }

    display_names = {metadata["artifact_id"]: metadata["display_name"]
                     for metadata in CATALOGUE_METADATA.values()}
    rows = []
    rows_by_field = {5: [], 13: []}
    for entry in entries:
        artifact_id = entry["artifact_id"]
        filename = certificate_filename(artifact_id)
        n, k, d = entry["parameters"]
        evidence = (f"\\href{{{REPOSITORY}/{filename}}}"
                    f"{{${display_names[artifact_id]}$}}")
        benchmark = entry["prior_benchmark"]
        prior_a = ",".join(f"{x:,}" for x in benchmark["a_d"])
        if len(benchmark["a_d"]) > 1:
            prior_a = "\\{" + prior_a + "\\}"
        prior = f"$({benchmark['distance']};\\,{prior_a})$"
        a_d = f"{entry['a_d']:,}"
        if entry["public_a_d_min_achieved"]:
            a_d = f"\\mathbf{{{a_d}}}"
        ours = f"$[{n},{k},{d}];\\,{a_d}$"
        row = (
            f"{evidence} & {entry['field_order']} & {ours} & {prior} & "
            f"{benchmark['reference']} \\\\"
        )
        rows.append(row)
        rows_by_field[entry["field_order"]].append(row)
    tex = (
        "% Generated by build_application_catalog.py; do not edit.\n"
        "\\newcommand{\\ApplicationCatalogueRows}{%\n"
        + "\n".join(rows)
        + "\n}\n"
        "\\newcommand{\\ApplicationCatalogueRowsFive}{%\n"
        + "\n".join(rows_by_field[5])
        + "\n}\n"
        "\\newcommand{\\ApplicationCatalogueRowsThirteen}{%\n"
        + "\n".join(rows_by_field[13])
        + "\n}\n"
    )

    outputs = {
        "application_catalog.json": json.dumps(catalogue, indent=2) + "\n",
        "application_catalog_data.tex": tex,
    }
    outputs.update({name: json.dumps(payload, indent=2) + "\n"
                    for name, payload in certificates.items()})
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    outputs = build_outputs()
    for relative_name, contents in outputs.items():
        path = HERE / relative_name
        if args.write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(contents)
        elif not path.exists() or path.read_text() != contents:
            raise SystemExit(f"stale application catalogue: {relative_name}")
    print(f"PASS application catalogue: {len(outputs) - 2} certificates")


if __name__ == "__main__":
    main()
