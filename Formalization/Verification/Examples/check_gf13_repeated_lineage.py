#!/usr/bin/env python3
"""Verify the exact GF(13) repeated lineage centered at length 20."""

import argparse
import hashlib
import json
from pathlib import Path

from check_applications import dot, macwilliams, rank, require
from universal_display import (
    kim_build, matrix_small_tex, matrix_tex, permute_vector,
    universal_normalize,
)


HERE = Path(__file__).resolve().parent
REPOSITORY = (
    "https://github.com/LeGenAI/intersection-coding-theory-cohomology/"
    "blob/afm-revision-2026-08-27/"
    "Formalization/Verification/Examples/certificates/gf13-repeated-lineage.json"
)


def matmul(left, right, p):
    return [[sum(a * b for a, b in zip(row, column)) % p
             for column in zip(*right)] for row in left]


def row_space_equal(left, right, p):
    return rank(left, p) == rank(right, p) == rank(left + right, p)


def circulant_source(first_row, p):
    k = len(first_row)
    identity = [[int(i == j) for j in range(k)] for i in range(k)]
    circulant = [[first_row[(j - i) % k] % p for j in range(k)]
                 for i in range(k)]
    return [identity[i] + circulant[i] for i in range(k)]


def hyperplane_basis(functional, p):
    pivot = next((i for i, value in enumerate(functional) if value % p), None)
    require(pivot is not None, "nonzero coordinate functional")
    inverse = pow(functional[pivot], -1, p)
    basis = []
    for free in range(len(functional)):
        if free == pivot:
            continue
        vector = [0] * len(functional)
        vector[free] = 1
        vector[pivot] = -functional[free] * inverse % p
        basis.append(vector)
    return basis


def normalized_top(child, first, second, p):
    for i in range(len(child)):
        for j in range(i + 1, len(child)):
            determinant = (child[i][first] * child[j][second]
                           - child[j][first] * child[i][second]) % p
            if not determinant:
                continue
            inverse = pow(determinant, -1, p)
            coefficients = [0] * len(child)
            coefficients[i] = child[j][second] * inverse % p
            coefficients[j] = -child[i][second] * inverse % p
            top = matmul([coefficients], child, p)[0]
            require([top[first], top[second]] == [1, 0], "normalized top")
            return top
    raise ValueError("selected pair has no Kim normalization")


def kim_reduction(child, pair, c, p):
    first, second = pair
    functional = [(row[second] - c * row[first]) % p for row in child]
    kernel_rows = matmul(hyperplane_basis(functional, p), child, p)
    top = normalized_top(child, first, second, p)
    order = [first, second] + [j for j in range(len(child[0]))
                              if j not in (first, second)]
    reordered_kernel = [[row[j] for j in order] for row in kernel_rows]
    reordered_child = [[row[j] for j in order] for row in child]
    parent = [row[2:] for row in reordered_kernel]
    x = [top[j] for j in order[2:]]
    y = [(-row[0]) % p for row in reordered_kernel]
    require(all(row[:2] == [(-value) % p, (-c * value) % p]
                for row, value in zip(reordered_kernel, y)), "repeated heads")
    require(dot(x, x, p) == p - 1, "Kim correction norm minus one")
    require(all(value == dot(x, row, p)
                for value, row in zip(y, parent)), "Kim coefficients")
    built = [[1, 0] + x] + [[(-value) % p, (-c * value) % p] + row
                            for value, row in zip(y, parent)]
    require(built == [[top[j] for j in order]] + reordered_kernel,
            "literal repeated Kim matrix")
    require(row_space_equal(built, reordered_child, p), "child row space")
    return {"ordered_pair_zero_based": pair, "coordinate_order_zero_based": order,
            "x": x, "y": y, "parent_matrix": parent,
            "child_kim_matrix": built, "literal_reconstruction": True,
            "row_space_reconstruction": True}


def certify_matrix(matrix, p, parameters, counts=None):
    n, k, distance = parameters
    require(len(matrix) == k and len(matrix[0]) == n, "matrix shape")
    require(rank(matrix, p) == k, "half-dimension")
    require(all(dot(a, b, p) == 0 for a in matrix for b in matrix), "zero Gram")
    result = {"parameters": parameters, "rank": k, "gram_zero": True,
              "matrix": matrix}
    if counts is not None:
        require(len(counts) == n + 1 and sum(counts) == p ** k,
                "complete weight distribution")
        require(next(i for i, value in enumerate(counts) if i and value) == distance,
                "minimum distance from distribution")
        macwilliams(counts, p, k)
        result.update(weight_distribution=counts, a_d=counts[distance],
                      macwilliams_verified=True)
    return result


def tuple_tex(values):
    return "(" + ",".join(map(str, values)) + ")"


def build_outputs():
    source_bytes = (HERE / "gf13_repeated_lineage.json").read_bytes()
    source = json.loads(source_bytes)
    p, c = source["field_order"], source["square_root_minus_one"]
    g20 = circulant_source(source["source"]["first_circulant_row"], p)
    c20 = certify_matrix(g20, p, source["source"]["parameters"],
                         source["source"]["weight_distribution"])
    c20["minimum_weight_verified_by_magma"] = True

    steps, levels = [], [c20]
    current = g20
    for reduction in source["reductions"]:
        require(len(current[0]) == reduction["child_length"], "reduction child")
        pair = [value - 1 for value in reduction["ordered_pair_one_based"]]
        step = kim_reduction(current, pair, c, p)
        stored = reduction["parent_generator"]
        require(row_space_equal(step["parent_matrix"], stored, p),
                "stored parent row space")
        level = certify_matrix(stored, p, reduction["parent_parameters"],
                               reduction["parent_weight_distribution"])
        steps.append(step)
        levels.append(level)
        current = stored

    require(len(levels) == 2, "one best-known-distance reduction")
    c20, c18 = levels
    top_step = steps[0]
    parent_pairs_one_based = [
        (16, 4), (3, 10), (6, 13), (2, 18), (12, 14),
        (15, 11), (9, 1), (7, 8), (5, 17),
    ]
    parent_pairs = [(a - 1, b - 1) for a, b in parent_pairs_one_based]
    display_parent = universal_normalize(
        top_step["parent_matrix"], parent_pairs, c, p,
        rank_one_split_normalize=True)
    display_x = permute_vector(
        top_step["x"], display_parent["coordinate_order_zero_based"])
    display_child = kim_build(display_parent["matrix"], display_x, c, p)
    child_order = [1, 0] + [2 + j for j in
                            display_parent["coordinate_order_zero_based"]]
    require(row_space_equal(
        display_child,
        [[row[j] for j in child_order]
         for row in top_step["child_kim_matrix"]], p),
        "largest child with universal parent")
    display = {
        "parent": display_parent, "correction": display_x,
        "child_matrix": display_child,
        "new_pair_oriented_as_01": True,
        "child_row_space_verified": True,
    }

    certificate = {
        "schema_version": 1,
        "artifact_id": "GF13-BEST-KNOWN-REPEATED-18-20",
        "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
        "interpretation": (
            "An exact two-coordinate reduction of the published GF(13) "
            "[20,10,10] code to a [18,9,8] parent and its literal inverse "
            "Kim--Lee presentation."
        ),
        "levels_ascending": [c18, c20],
        "steps_ascending": steps,
        "largest_universal_display": display,
        "published_benchmarks": source["published_benchmarks"],
        "magma_audit": {
            "replay": "Formalization/Verification/Examples/gf13_repeated_lineage.m",
            "receipt": "Formalization/Verification/Examples/gf13_repeated_lineage.receipt.txt",
            "ordered_pairs": 380,
            "minimum_weight_ten_loss": 1896,
            "minimum_loss_pair_count": 10,
            "zero_loss_pairs": 0,
            "kim_choi_public_a8": 1752
        }
    }
    results = {
        "input_sha256": certificate["source_sha256"],
        "method": "exact rank/Gram/row-space/Kim reconstruction; supplied complete Magma distributions checked by MacWilliams",
        "certificate": certificate
    }

    rows = []
    for level, name, code, relation in [
            (0, r"$C_{18}^{(13)}$", c18, "base parent"),
            (1, r"$C_{20}^{(13)}$", c20,
             r"$\mathcal B_5(G_{18}^{(13)},x_{18}^{(13)})$")]:
        n, k, d = code["parameters"]
        rows.append(f"{level} & {name} & $[{n},{k},{d}]$ & {code['a_d']:,} & {relation} \\\\")

    benchmark_by_length = {item["length"]: item for item in source["published_benchmarks"]}
    catalogue_rows = []
    for symbol, code in [(r"C_{18}^{(13)}", c18), (r"C_{20}^{(13)}", c20)]:
        n, k, d = code["parameters"]
        benchmark = benchmark_by_length[n]
        link = f"\\href{{{REPOSITORY}}}{{${symbol}$}}"
        catalogue_rows.append(
            f"{link} & 13 & $[{n},{k},{d}];\\,{code['a_d']:,}$ & "
            f"$({benchmark['distance']};\\,{benchmark['a_d']:,})$ & "
            f"{benchmark['reference']} \\\\"
        )

    x18 = display_x
    tex = "% Generated by check_gf13_repeated_lineage.py; do not edit.\n"
    tex += "\\newcommand{\\GFThirteenRepeatedLineageRows}{%\n" + "\n".join(rows) + "\n}\n"
    tex += "\\newcommand{\\GFThirteenRepeatedCatalogueRows}{%\n" + "\n".join(catalogue_rows) + "\n}\n"
    tex += ("\\newcommand{\\GFThirteenLargestRepeatedMatrix}{"
            + matrix_tex(display_child, display_parent["k"],
                         display_parent["r"], split_corollary=True) + "}\n")
    tex += ("\\newcommand{\\GFThirteenLargestParentParameters}"
            f"{{c={c},\\; k={display_parent['k']},\\; "
            f"r={display_parent['r']},\\; "
            f"D={matrix_small_tex(display_parent['D'])}}}\n")
    tex += f"\\newcommand{{\\GFThirteenEighteenCorrection}}{{{tuple_tex(x18)}}}\n"
    tex += ("\\newcommand{\\GFThirteenRepeatedCertificate}{\\href{" + REPOSITORY +
            "}{$C_{20}^{(13)}$}}\n")
    return {
        "gf13_repeated_lineage_results.json": json.dumps(results, indent=2) + "\n",
        "gf13_repeated_lineage_data.tex": tex,
        "certificates/gf13-repeated-lineage.json": json.dumps(certificate, indent=2) + "\n"
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for relative_name, contents in build_outputs().items():
        path = HERE / relative_name
        if args.write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(contents)
        else:
            require(path.exists() and path.read_text() == contents,
                    f"stale generated file: {relative_name}")
    print("PASS GF(13) best-known repeated lineage: [18,9,8] -> [20,10,10]")


if __name__ == "__main__":
    main()
