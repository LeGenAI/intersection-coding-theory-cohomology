#!/usr/bin/env python3
"""Verify a four-step Kim lineage centered at length 20 and ending at Golay."""

import argparse
import hashlib
import json
from pathlib import Path

from check_applications import distribution, dot, macwilliams, rank, require
from universal_display import (
    binary_rank_one_child_normalize, kim_build, matrix_small_tex, matrix_tex, permute_vector,
    universal_normalize,
)


HERE = Path(__file__).resolve().parent
REPOSITORY = (
    "https://github.com/LeGenAI/intersection-coding-theory-cohomology/"
    "blob/afm-revision-2026-08-27/"
    "Formalization/Verification/Examples/certificates/binary-golay-lineage.json"
)


def matmul(left, right):
    return [[sum(a * b for a, b in zip(row, column)) % 2
             for column in zip(*right)] for row in left]


def hyperplane_basis(functional):
    pivot = next((i for i, value in enumerate(functional) if value), None)
    require(pivot is not None, "selected coordinate pair must define a nonzero functional")
    basis = []
    for free in range(len(functional)):
        if free == pivot:
            continue
        vector = [0] * len(functional)
        vector[free] = 1
        vector[pivot] = functional[free]
        basis.append(vector)
    return pivot, basis


def row_space_equal(left, right):
    return (rank(left, 2) == rank(right, 2) ==
            rank(left + right, 2))


def kim_reduction(child, requested_pair):
    first, second = requested_pair
    require(first != second and 0 <= first < len(child[0]) and
            0 <= second < len(child[0]), "coordinate pair")
    functional = [(row[first] + row[second]) % 2 for row in child]
    pivot, kernel = hyperplane_basis(functional)
    kernel_rows = matmul(kernel, child)
    top = child[pivot][:]
    if [top[first], top[second]] == [0, 1]:
        first, second = second, first
    require([top[first], top[second]] == [1, 0], "binary Kim top row")
    order = [first, second] + [j for j in range(len(child[0]))
                               if j not in (first, second)]
    reordered_child = [[row[j] for j in order] for row in child]
    reordered_kernel = [[row[j] for j in order] for row in kernel_rows]
    parent = [row[2:] for row in reordered_kernel]
    y = [row[0] for row in reordered_kernel]
    require(all(row[:2] == [value, value]
                for row, value in zip(reordered_kernel, y)), "equal binary heads")
    x = [top[j] for j in order[2:]]
    require(dot(x, x, 2) == 1, "binary Kim correction norm")
    require(all(value == dot(x, row, 2)
                for value, row in zip(y, parent)), "binary Kim coefficients")
    built = [[1, 0] + x] + [[value, value] + row
                            for value, row in zip(y, parent)]
    require(built == [[top[j] for j in order]] + reordered_kernel,
            "literal Kim matrix")
    require(row_space_equal(built, reordered_child), "Kim child row space")
    require(rank(parent, 2) == len(parent), "parent rank")
    require(all(dot(a, b, 2) == 0 for a in parent for b in parent),
            "parent Gram")
    return {
        "requested_pair_zero_based": requested_pair,
        "ordered_pair_zero_based": [first, second],
        "coordinate_order_zero_based": order,
        "x": x,
        "y": y,
        "parent_matrix": parent,
        "child_kim_matrix": built,
        "correction_norm_one": True,
        "coefficient_relation_verified": True,
        "literal_reconstruction": True,
        "row_space_reconstruction": True,
    }


def certified_code(matrix):
    k, n = len(matrix), len(matrix[0])
    require(n == 2 * k and rank(matrix, 2) == k, "binary half-dimension")
    require(all(dot(a, b, 2) == 0 for a in matrix for b in matrix), "binary Gram")
    counts = distribution(matrix, 2)
    distance = next(i for i, count in enumerate(counts) if i and count)
    macwilliams(counts, 2, k)
    return {
        "parameters": [n, k, distance],
        "a_d": counts[distance],
        "matrix": matrix,
        "rank": k,
        "gram_zero": True,
        "weight_distribution": counts,
        "macwilliams_verified": True,
    }


def bit_string(vector):
    return "".join(map(str, vector))


def build_outputs():
    source_bytes = (HERE / "golay_lineage.json").read_bytes()
    source = json.loads(source_bytes)
    current_matrix = source["generator_g24"]
    levels_descending = [certified_code(current_matrix)]
    steps_descending = []
    for pair in source["descent_pairs_zero_based"]:
        step = kim_reduction(current_matrix, pair)
        steps_descending.append(step)
        current_matrix = step["parent_matrix"]
        levels_descending.append(certified_code(current_matrix))
    require([level["parameters"] for level in levels_descending] ==
            source["expected_parameters"], "Golay lineage parameters")
    c24, c22, c20, c18, c16 = levels_descending
    require(c24["weight_distribution"] ==
            [1,0,0,0,0,0,0,0,759,0,0,0,2576,0,0,0,759,0,0,0,0,0,0,0,1],
            "extended Golay weight enumerator")
    require([code["parameters"][2] for code in (c22, c20, c18, c16)] ==
            [6, 4, 4, 4], "four Golay reductions")

    top_step = steps_descending[0]
    parent_pairs = [(2 * i, 2 * i + 1)
                    for i in range(len(top_step["parent_matrix"]))]
    display_parent = universal_normalize(
        top_step["parent_matrix"], parent_pairs, 1, 2,
        zero_binary_pivot_diagonal=True)
    display_x = permute_vector(
        top_step["x"], display_parent["coordinate_order_zero_based"])
    display_child = kim_build(display_parent["matrix"], display_x, 1, 2)
    display_child, swapped_new_pair = binary_rank_one_child_normalize(
        display_child, display_parent["k"])
    initial_pair = [0, 1] if swapped_new_pair else [1, 0]
    child_order = initial_pair + [2 + j for j in
                                  display_parent["coordinate_order_zero_based"]]
    require(row_space_equal(
        display_child,
        [[row[j] for j in child_order]
         for row in top_step["child_kim_matrix"]]),
        "Golay child with universal parent")
    display = {
        "parent": display_parent, "correction": display_x,
        "child_matrix": display_child,
        "new_pair_oriented_as_01": True,
        "literal_binary_rank_one_child": True,
        "child_row_space_verified": True,
    }

    certificate = {
        "schema_version": 1,
        "artifact_id": "BINARY-GOLAY-16-24",
        "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
        "source": source["source"],
        "interpretation": (
            "Exact four-step descent from the extended binary Golay code, "
            "centered at length 20, and literal inverse reconstruction by "
            "four binary Kim steps."
        ),
        "levels_ascending": list(reversed(levels_descending)),
        "steps_ascending": list(reversed(steps_descending)),
        "largest_universal_display": display,
    }
    results = {
        "input_sha256": certificate["source_sha256"],
        "method": "complete binary enumeration; rank, Gram, MacWilliams, and four literal Kim reconstructions",
        "certificate": certificate,
    }

    rows = []
    for level, name, code, relation in [
            (0, r"$C_{16}$", c16, "base parent"),
            (1, r"$C_{18}$", c18, r"$\mathcal B_1(G_{16},x_{16})$"),
            (2, r"$C_{20}$", c20, r"$\mathcal B_1(G_{18},x_{18})$"),
            (3, r"$C_{22}$", c22, r"$\mathcal B_1(G_{20},x_{20})$"),
            (4, r"$\mathcal G_{24}$", c24, r"$\mathcal B_1(G_{22},x_{22})$")]:
        n, k, d = code["parameters"]
        rows.append(
            f"{level} & {name} & $[{n},{k},{d}]$ & "
            f"$\\mathbf{{{code['a_d']:,}}}$ & {relation} \\\\")
    tex = "% Generated by check_golay_lineage.py; do not edit.\n"
    tex += "\\newcommand{\\GolayLineageRows}{%\n" + "\n".join(rows) + "\n}\n"
    catalogue_rows = []
    for symbol, code in [(r"C_{16}^{(2)}", c16), (r"C_{18}^{(2)}", c18),
                         (r"C_{20}^{(2)}", c20), (r"C_{22}^{(2)}", c22),
                         (r"\mathcal G_{24}", c24)]:
        n, k, d = code["parameters"]
        evidence = f"\\href{{{REPOSITORY}}}{{${symbol}$}}"
        catalogue_rows.append(
            f"{evidence} & 2 & $[{n},{k},{d}];\\,"
            f"\\mathbf{{{code['a_d']:,}}}$ & "
            f"$({d};\\,{code['a_d']:,})$ & Harada--Munemasa database \\\\"
        )
    tex += "\\newcommand{\\GolayCatalogueRows}{%\n" + "\n".join(catalogue_rows) + "\n}\n"
    tex += ("\\newcommand{\\BinaryLargestRepeatedMatrix}{"
            + matrix_tex(display_child, display_parent["k"],
                         display_parent["r"], binary_rank_one=True) + "}\n")
    tex += ("\\newcommand{\\BinaryLargestParentParameters}"
            f"{{c=1,\\; k={display_parent['k']},\\; "
            f"r={display_parent['r']},\\; "
            f"D={matrix_small_tex(display_parent['D'])}}}\n")
    corrections = {len(step["x"]): step["x"] for step in steps_descending}
    corrections[22] = display_x
    for length, word in ((16, "Sixteen"), (18, "Eighteen"),
                         (20, "Twenty"), (22, "TwentyTwo")):
        tex += (f"\\newcommand{{\\Golay{word}Correction}}{{\\texttt{{" +
                bit_string(corrections[length]) + "}}\n")
    tex += ("\\newcommand{\\GolayLineageCertificate}{\\href{" + REPOSITORY +
            "}{$\\mathcal G_{24}$}}\n")
    return {
        "golay_lineage_results.json": json.dumps(results, indent=2) + "\n",
        "golay_lineage_data.tex": tex,
        "certificates/binary-golay-lineage.json": json.dumps(certificate, indent=2) + "\n",
    }


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
        else:
            require(path.exists() and path.read_text() == contents,
                    f"stale generated file: {relative_name}")
    print("PASS binary Golay lineage: [16,8,4] -> [18,9,4] -> [20,10,4] -> [22,11,6] -> [24,12,8]")


if __name__ == "__main__":
    main()
