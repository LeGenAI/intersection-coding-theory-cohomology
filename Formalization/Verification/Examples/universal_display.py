"""Exact universal normalization used by the application figures."""

from check_applications import dot, rank, require


def row_space_equal(left, right, p):
    return rank(left, p) == rank(right, p) == rank(left + right, p)


def rref_with_rows(defect, matrix, p):
    """Put ``defect`` in RREF while applying the same operations to ``matrix``."""
    reduced = [row[:] for row in defect]
    transformed = [row[:] for row in matrix]
    pivot_columns = []
    pivot_row = 0
    for column in range(len(reduced[0])):
        pivot = next((i for i in range(pivot_row, len(reduced))
                      if reduced[i][column] % p), None)
        if pivot is None:
            continue
        reduced[pivot_row], reduced[pivot] = reduced[pivot], reduced[pivot_row]
        transformed[pivot_row], transformed[pivot] = (
            transformed[pivot], transformed[pivot_row])
        inverse = pow(reduced[pivot_row][column], -1, p)
        reduced[pivot_row] = [(inverse * value) % p
                              for value in reduced[pivot_row]]
        transformed[pivot_row] = [(inverse * value) % p
                                  for value in transformed[pivot_row]]
        for i in range(len(reduced)):
            if i == pivot_row or reduced[i][column] % p == 0:
                continue
            scale = reduced[i][column]
            reduced[i] = [(a - scale * b) % p
                          for a, b in zip(reduced[i], reduced[pivot_row])]
            transformed[i] = [(a - scale * b) % p
                              for a, b in zip(transformed[i],
                                              transformed[pivot_row])]
        pivot_columns.append(column)
        pivot_row += 1
        if pivot_row == len(reduced):
            break
    return reduced, transformed, pivot_columns


def determinant(matrix, p):
    work = [row[:] for row in matrix]
    value = 1
    for column in range(len(work)):
        pivot = next((i for i in range(column, len(work))
                      if work[i][column] % p), None)
        if pivot is None:
            return 0
        if pivot != column:
            work[column], work[pivot] = work[pivot], work[column]
            value = -value
        pivot_value = work[column][column] % p
        value = value * pivot_value % p
        inverse = pow(pivot_value, -1, p)
        for i in range(column + 1, len(work)):
            scale = work[i][column] * inverse % p
            work[i] = [(a - scale * b) % p
                       for a, b in zip(work[i], work[column])]
    return value % p


def universal_normalize(matrix, pairs, c, p, zero_binary_pivot_diagonal=False,
                        rank_one_split_normalize=False):
    """Return a literal ``G(c;P,H,Q,D)`` generator for the same code."""
    dimension = len(matrix)
    require(len(pairs) == dimension, "one coordinate pair per row")
    flat = [coordinate for pair in pairs for coordinate in pair]
    require(sorted(flat) == list(range(2 * dimension)),
            "coordinate pairs must partition the parent coordinates")
    defect = [[(row[b] - c * row[a]) % p for a, b in pairs]
              for row in matrix]
    reduced, transformed, pivots = rref_with_rows(defect, matrix, p)
    k = len(pivots)
    free = [j for j in range(dimension) if j not in pivots]
    r = len(free)
    block_order = pivots + free
    ordered_pairs = [pairs[j] for j in block_order]
    if zero_binary_pivot_diagonal:
        require((p, c) == (2, 1),
                "zero diagonal orientation is the binary specialization")
        for i in range(k):
            a, b = ordered_pairs[i]
            if transformed[i][a] % p:
                ordered_pairs[i] = (b, a)
    coordinate_order = [coordinate for pair in ordered_pairs for coordinate in pair]
    normalized = [[row[j] for j in coordinate_order] for row in transformed]
    reduced_ordered = [[row[j] for j in block_order] for row in reduced]
    require(reduced_ordered[:k] == [
        [int(i == j) for j in range(k)] + [*row[k:]]
        for i, row in enumerate(reduced_ordered[:k])
    ], "identity defect block")
    require(all(all(value == 0 for value in row)
                for row in reduced_ordered[k:]), "zero master defects")

    if rank_one_split_normalize:
        require(r == 1, "Corollary 3.10 normalization requires rank one")
        core = normalized[k][2 * k] % p
        require(core != 0, "nonzero rank-one terminal core")
        inverse = pow(core, -1, p)
        normalized[k] = [(inverse * value) % p for value in normalized[k]]
        for i in range(k):
            diagonal = normalized[i][2 * i] % p
            lower = normalized[k][2 * i] % p
            require(diagonal == 0 or lower != 0,
                    "diagonal can be normalized by the master row")
            if diagonal:
                scale = -diagonal * pow(lower, -1, p) % p
                normalized[i] = [(a + scale * b) % p
                                 for a, b in zip(normalized[i], normalized[k])]

    def first(row, block):
        return normalized[row][2 * block]

    p_matrix = [[first(i, j) for j in range(k)] for i in range(k)]
    h_matrix = [[first(i, k + t) for t in range(r)] for i in range(k)]
    q_matrix = [[reduced_ordered[i][k + t] for t in range(r)]
                for i in range(k)]
    d_matrix = [[first(k + s, k + t) for t in range(r)]
                for s in range(r)]
    require(determinant(d_matrix, p) != 0, "invertible terminal core D")
    if zero_binary_pivot_diagonal:
        require(all(p_matrix[i][i] == 0 for i in range(k)),
                "Theorem 3.8 zero pivot diagonal")
    if rank_one_split_normalize:
        require(d_matrix == [[1]], "Corollary 3.10 unit terminal core")
        require(all(p_matrix[i][i] == 0 for i in range(k)),
                "Corollary 3.10 zero pivot diagonal")

    expected = []
    for i in range(k):
        row = []
        for j in range(k):
            value = p_matrix[i][j]
            row += [value, (c * value + int(i == j)) % p]
        for t in range(r):
            value = h_matrix[i][t]
            row += [value, (c * value + q_matrix[i][t]) % p]
        expected.append(row)
    for s in range(r):
        row = []
        for i in range(k):
            value = -sum(d_matrix[s][t] * q_matrix[i][t]
                         for t in range(r)) % p
            row += [value, c * value % p]
        for t in range(r):
            value = d_matrix[s][t]
            row += [value, c * value % p]
        expected.append(row)
    require(normalized == expected, "literal universal G(c;P,H,Q,D) form")
    require(row_space_equal(normalized,
                            [[row[j] for j in coordinate_order]
                             for row in matrix], p), "universal parent row space")
    require(all(dot(a, b, p) == 0 for a in normalized for b in normalized),
            "universal parent Gram")
    return {
        "c": c, "k": k, "r": r, "pairs_zero_based": pairs,
        "ordered_pairs_zero_based": ordered_pairs,
        "block_order_zero_based": block_order,
        "coordinate_order_zero_based": coordinate_order,
        "P": p_matrix, "H": h_matrix, "Q": q_matrix, "D": d_matrix,
        "matrix": normalized, "literal_universal_form": True,
        "zero_pivot_diagonal": zero_binary_pivot_diagonal,
        "rank_one_split_normalized": rank_one_split_normalize,
        "det_D": determinant(d_matrix, p), "gram_zero": True,
    }


def kim_build(parent, correction, c, p):
    coefficients = [dot(correction, row, p) for row in parent]
    return ([[1, 0] + correction] +
            [[(-value) % p, (-c * value) % p] + row
             for value, row in zip(coefficients, parent)])


def permute_vector(vector, coordinate_order):
    return [vector[j] for j in coordinate_order]


def matrix_tex(matrix, k, r, split_corollary=False):
    """Complete child matrix with visible new, P, and D regions."""
    require(len(matrix) == 1 + k + r, "row partition")
    require(len(matrix[0]) == 2 * (1 + k + r), "paired child shape")
    group_sizes = [1, k, r]
    column_spec = "r|cc!{\\vrule width 1.2pt}"
    column_spec += "|".join(["cc"] * k)
    if r:
        column_spec += "!{\\vrule width 1.2pt}" + "|".join(["cc"] * r)
    require(not split_corollary or r == 1,
            "Corollary 3.10 display has a rank-one terminal block")
    pivot_header = (r"P_{ii}=0:\ 01;\quad P_{ij}=b_{ij}:\ b_{ij}(1,c)"
                    if split_corollary else
                    r"P_{ij}(1,c)+\delta_{ij}(0,1)")
    terminal_header = (r"D=(1):\ \ell_i;\ (1,c)"
                       if split_corollary else
                       r"D_{st}(1,c)\text{ terminal pairs}")
    headers = [r"\scriptstyle\text{rows}",
               r"\multicolumn{2}{c!{\vrule width 1.2pt}}{\scriptstyle\text{new pair}}",
               (f"\\multicolumn{{{2 * k}}}{{c!{{\\vrule width 1.2pt}}}}"
                f"{{\\scriptstyle {pivot_header}}}")]
    if r:
        headers.append(f"\\multicolumn{{{2 * r}}}{{c}}"
                       f"{{\\scriptstyle {terminal_header}}}")
    lines = [" & ".join(headers) + r" \\ \noalign{\hrule height 0.7pt}"]
    for index, row in enumerate(matrix):
        if index == 0:
            label, row_color = r"\scriptstyle\text{new}", "blue!65!black"
        elif index <= k:
            label = (r"\scriptstyle b_{ij},\ell_i" if split_corollary
                     else r"\scriptstyle P,H,Q")
            row_color = "teal!60!black"
        else:
            label = (r"\scriptstyle a_i,(1,c)" if split_corollary
                     else r"\scriptstyle -DQ^{T},D")
            row_color = "violet!75!black"
        entries = []
        for column, value in enumerate(row):
            if column < 2 and index > 0:
                color = "orange!80!black"
            elif column >= 2 * (1 + k) and index > k:
                color = "violet!75!black"
            else:
                color = row_color
            entries.append(f"\\textcolor{{{color}}}{{{value}}}")
        suffix = r" \\"
        if index == 0 or index == k:
            suffix += r" \noalign{\hrule height 1.2pt}"
        lines.append(label + " & " + " & ".join(entries) + suffix)
    return ("\\left(\\begin{array}{" + column_spec + "}\n" +
            "\n".join(lines) + "\n\\end{array}\\right)")


def matrix_small_tex(matrix):
    return (r"\begin{pmatrix}" + r"\\".join(
        "&".join(map(str, row)) for row in matrix) + r"\end{pmatrix}")
