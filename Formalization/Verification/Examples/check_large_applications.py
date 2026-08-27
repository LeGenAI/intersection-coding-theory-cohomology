#!/usr/bin/env python3
"""Normalize a known [14,7,8] code over GF(13) into the universal box.

The script certifies its one-block deletion parent and unique projective
distance-eight correction.  It uses exact prime-field arithmetic only.
"""

import argparse
import hashlib
import itertools
import json
from pathlib import Path

from check_applications import distribution, dot, rank, require

HERE = Path(__file__).resolve().parent


def matmul(a, b, p):
    return [[sum(a[i][t] * b[t][j] for t in range(len(b))) % p
             for j in range(len(b[0]))] for i in range(len(a))]


def transpose(a):
    return [list(row) for row in zip(*a)]


def rref(a, p):
    a = [[x % p for x in row] for row in a]
    pivots = []
    row = 0
    for column in range(len(a[0])):
        pivot = next((i for i in range(row, len(a)) if a[i][column]), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        inverse = pow(a[row][column], -1, p)
        a[row] = [inverse * x % p for x in a[row]]
        for i in range(len(a)):
            if i != row and a[i][column]:
                coefficient = a[i][column]
                a[i] = [(x - coefficient * y) % p
                        for x, y in zip(a[i], a[row])]
        pivots.append(column)
        row += 1
        if row == len(a):
            break
    return a, pivots


def solve_full_row_rank(a, b, p):
    augmented = [row[:] + [value] for row, value in zip(a, b)]
    reduced, pivots = rref(augmented, p)
    require(len(pivots) == len(a) and all(j < len(a[0]) for j in pivots),
            "linear system is not full-row-rank")
    result = [0] * len(a[0])
    for i, pivot in enumerate(pivots):
        result[pivot] = reduced[i][-1]
    return result


def nullspace(a, p):
    reduced, pivots = rref(a, p)
    free = [j for j in range(len(a[0])) if j not in pivots]
    basis = []
    for column in free:
        vector = [0] * len(a[0])
        vector[column] = 1
        for i, pivot in enumerate(pivots):
            vector[pivot] = -reduced[i][column] % p
        basis.append(vector)
    return basis


def inverse(a, p):
    n = len(a)
    augmented = [row[:] + [int(i == j) for j in range(n)]
                 for i, row in enumerate(a)]
    reduced, pivots = rref(augmented, p)
    require(pivots[:n] == list(range(n)), "singular matrix")
    return [row[n:] for row in reduced]


def circulant(first):
    n = len(first)
    return [[first[(j - i) % n] for j in range(n)] for i in range(n)]


def block_permute(g, order):
    return [[x for j in order for x in row[2 * j:2 * j + 2]] for row in g]


def normalize_universal(g, c, p):
    n = len(g)
    defect = [[(row[2 * j + 1] - c * row[2 * j]) % p for j in range(n)]
              for row in g]
    _, pivot_blocks = rref(defect, p)
    k = len(pivot_blocks)
    order = pivot_blocks + [j for j in range(n) if j not in pivot_blocks]
    defect_ordered = [[row[j] for j in order] for row in defect]
    leading = [row[:k] for row in defect_ordered]
    pivot_coefficients = [solve_full_row_rank(transpose(leading),
                                               [int(i == j) for j in range(k)], p)
                          for i in range(k)]
    kernel_coefficients = nullspace(transpose(defect), p)
    transform = pivot_coefficients + kernel_coefficients
    require(rank(transform, p) == n, "normalizing row transformation")
    rows = matmul(transform, block_permute(g, order), p)
    r = n - k

    def alpha(row, j):
        return row[2 * j]

    def beta(row, j):
        return (row[2 * j + 1] - c * row[2 * j]) % p

    require([[beta(rows[i], j) for j in range(k)] for i in range(k)] ==
            [[int(i == j) for j in range(k)] for i in range(k)], "pivot readout")
    require(all(beta(rows[i], j) == 0 for i in range(k, n) for j in range(n)),
            "kernel rows")
    P = [[alpha(rows[i], j) for j in range(k)] for i in range(k)]
    H = [[alpha(rows[i], k + t) for t in range(r)] for i in range(k)]
    Q = [[beta(rows[i], k + t) for t in range(r)] for i in range(k)]
    A = [[alpha(rows[k + s], j) for j in range(k)] for s in range(r)]
    D = [[alpha(rows[k + s], k + t) for t in range(r)] for s in range(r)]
    D_inverse = inverse(D, p)
    normalized_transform = ([row[:] for row in transform[:k]] +
                            matmul(D_inverse, transform[k:], p))
    normalized_rows = matmul(normalized_transform, block_permute(g, order), p)
    normalized_A = matmul(D_inverse, A, p)
    return dict(k=k, r=r, block_order=order, row_transform=normalized_transform,
                rows=normalized_rows, P=P, H=H, Q=Q, A=normalized_A,
                D=[[int(i == j) for j in range(r)] for i in range(r)])


def rank_boxed_rows(data, c, p):
    k, r = data["k"], data["r"]
    P, H, Q, A, D = (data[name] for name in ("P", "H", "Q", "A", "D"))
    rows = []
    for i in range(k):
        row = []
        for j in range(k):
            row.extend([P[i][j], (c * P[i][j] + int(i == j)) % p])
        for t in range(r):
            row.extend([H[i][t], (c * H[i][t] + Q[i][t]) % p])
        rows.append(row)
    for s in range(r):
        row = []
        for j in range(k):
            row.extend([A[s][j], c * A[s][j] % p])
        for t in range(r):
            row.extend([D[s][t], c * D[s][t] % p])
        rows.append(row)
    return rows


def projective_vectors(q, dimension):
    for first in range(dimension):
        for tail in itertools.product(range(q), repeat=dimension - first - 1):
            yield (0,) * first + (1,) + tail


def projective_normalize(vector, p):
    first = next(x for x in vector if x)
    inverse = pow(first, -1, p)
    return tuple(inverse * x % p for x in vector)


def low_weight_lines(g, p, upper):
    result = []
    for coefficients in projective_vectors(p, len(g)):
        word = [sum(coefficients[i] * g[i][j] for i in range(len(g))) % p
                for j in range(len(g[0]))]
        if sum(x != 0 for x in word) <= upper:
            result.append(coefficients)
    return result


def lifting_survivors(g, p, upper):
    low = low_weight_lines(g, p, upper)
    survivors = []
    for gamma in projective_vectors(p, len(g)):
        if all(sum(x * y for x, y in zip(coefficients, gamma)) % p
               for coefficients in low):
            survivors.append(gamma)
    return low, survivors


def tex_macro(name, body):
    return f"\\newcommand{{\\{name}}}{{%\n{body}\n}}\n"


def block_matrix_tex(rows):
    lines = []
    for i, row in enumerate(rows):
        if i + 1 == len(rows):
            lines.append("\\hline")
        blocks = [f"({row[2 * j]},{row[2 * j + 1]})"
                  for j in range(len(row) // 2)]
        lines.append(" & ".join(blocks) + r"\\")
    return ("\\left[\\begin{array}{cccccc|c}\n" + "\n".join(lines) +
            "\n\\end{array}\\right]")


def large_application_tex(specification, universal, parent, parent_distribution,
                          parent_low, parent_survivors):
    q = [row[0] for row in universal["Q"]]
    readout = []
    for i in range(6):
        readout.append([int(i == j) for j in range(6)] + [q[i]])
    readout.append([0] * 7)
    readout_lines = []
    for i, row in enumerate(readout):
        if i == 6:
            readout_lines.append("\\hline")
        readout_lines.append(" & ".join(str(x) for x in row) + r"\\")
    readout_tex = ("\\left[\\begin{array}{cccccc|c}\n" +
                   "\n".join(readout_lines) + "\n\\end{array}\\right]")
    gamma = [row[0] for row in universal["rows"][1:]]
    survivor = parent_survivors[0]
    order = [x + 1 for x in specification["coordinate_order"]]
    a8 = 12 * 3003
    result = "% Generated by check_large_applications.py; do not edit.\n"
    result += tex_macro("AppThirteenFourteenUniversal", block_matrix_tex(universal["rows"]))
    result += tex_macro("AppThirteenFourteenReadout", readout_tex)
    result += tex_macro("AppThirteenFourteenGamma",
                        "(" + ",".join(str(x) for x in gamma) + ")")
    result += tex_macro("AppThirteenFourteenSurvivor",
                        "[" + ":".join(str(x) for x in survivor) + "]")
    result += tex_macro("AppThirteenFourteenCoordinateOrder",
                        "(" + ",".join(str(x) for x in order) + ")")
    result += tex_macro(
        "AppThirteenFourteenDistanceRow",
        f"\\ref{{{specification['label']}}} & 13 & $[14,7]$ & {13**7-1:,} & 8 & {a8:,} \\\\")
    result += tex_macro("AppThirteenFourteenParentDistribution",
                        "(" + ",".join(str(x) for x in parent_distribution) + ")")
    result += tex_macro("AppThirteenFourteenLowLines", str(len(parent_low)))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    source = (HERE / "large_applications.json").read_bytes()
    specification = json.loads(source)
    p, c = specification["p"], specification["c"]
    require(p == 13 and c * c % p == p - 1, "GF(13) split input")
    circulant_matrix = circulant(specification["circulant_first_row"])
    identity = [[int(i == j) for j in range(7)] for i in range(7)]
    g14 = [identity[i] + circulant_matrix[i] for i in range(7)]
    require(rank(g14, p) == 7, "[14,7] rank")
    require(all(dot(x, y, p) == 0 for x in g14 for y in g14), "[14,7] Gram")
    minor_count = 0
    for columns in itertools.combinations(range(14), 7):
        require(rank([[row[j] for j in columns] for row in g14], p) == 7,
                "non-MDS information set")
        minor_count += 1
    require(minor_count == 3432, "MDS minor coverage")

    coordinate_order = specification["coordinate_order"]
    require(sorted(coordinate_order) == list(range(14)), "coordinate permutation")
    paired = [[row[j] for j in coordinate_order] for row in g14]
    universal = normalize_universal(paired, c, p)
    require(universal["block_order"] == list(range(7)), "preordered universal blocks")
    universal["coordinate_order"] = coordinate_order
    require(rank(universal["D"], p) == universal["r"], "normalized terminal matrix")
    require(rank_boxed_rows(universal, c, p) == universal["rows"], "literal reconstruction")
    k, r = universal["k"], universal["r"]
    require(universal["A"] == [[-universal["Q"][j][s] % p for j in range(k)]
                                for s in range(r)], "A + Q^T")
    lhs = [[(int(i == j) + c * (universal["P"][i][j] + universal["P"][j][i])
             + c * sum(universal["H"][i][t] * universal["Q"][j][t]
                       + universal["Q"][i][t] * universal["H"][j][t]
                       for t in range(r))
             + sum(universal["Q"][i][t] * universal["Q"][j][t]
                   for t in range(r))) % p for j in range(k)] for i in range(k)]
    require(all(x == 0 for row in lhs for x in row), "pivot Gram relation")

    parent = [row[2:] for row in universal["rows"][1:]]
    parent_distribution = distribution(parent, p)
    parent_distance = next(i for i, count in enumerate(parent_distribution) if i and count)
    gamma = [row[0] for row in universal["rows"][1:]]
    require(all(row[1] == c * value % p for row, value in zip(universal["rows"][1:], gamma)),
            "deleted-column correction vector")
    parent_low, parent_survivors = lifting_survivors(parent, p, 7)
    require(projective_normalize(gamma, p) in parent_survivors,
            "actual MDS correction survives low-weight filter")

    result = dict(input_sha256=hashlib.sha256(source).hexdigest(),
                  code=dict(parameters=[14, 7, 8], matrix=g14, rank=7,
                            gram_zero=True, full_rank_seven_column_minors=minor_count),
                  universal=universal,
                  deletion_parent=dict(parameters=[12, 6, parent_distance], matrix=parent,
                                       weight_distribution=parent_distribution,
                                       gamma=gamma, low_weight_projective_lines=len(parent_low),
                                       lifting_survivor_count=len(parent_survivors),
                                       lifting_survivors=[list(x) for x in parent_survivors]),
                  interpretation="The MDS code has a rank-one universal box and a unique projective distance-eight correction over its displayed deletion parent.")
    rendered = json.dumps(result, indent=2) + "\n"
    outputs = {
        "large_applications_results.json": rendered,
        "large_applications_data.tex": large_application_tex(
            specification, universal, parent, parent_distribution,
            parent_low, parent_survivors),
    }
    for name, contents in outputs.items():
        output = HERE / name
        if args.write:
            output.write_text(contents)
        else:
            require(output.exists() and output.read_text() == contents,
                    f"stale large-application result: {name}")
    print(f"PASS GF(13) [14,7,8]: {minor_count} information sets")
    print(f"PASS universal normalization: k={k}, r={r}, D=I_{r}")
    print(f"PASS deletion parent: [12,6,{parent_distance}], {len(parent_survivors)} lifting survivors")
    print(f"PASS unique projective distance-eight correction: {parent_survivors[0]}")


if __name__ == "__main__":
    main()
