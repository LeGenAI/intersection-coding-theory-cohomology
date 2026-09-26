#!/usr/bin/env python3
"""Reproduce the revision's recursive quinary pair (Python standard library).

The single input is applications.json. --write regenerates the JSON
certificates; --check (the default) recomputes them and rejects any drift.
These exhaustive computations are not Lean theorem-prover certificates.
"""

import argparse
import hashlib
import itertools
import json
from math import comb
from pathlib import Path

HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def dot(x, y, p):
    return sum(a * b for a, b in zip(x, y)) % p


def build(example):
    p, c, ell, b = (example[k] for k in ("p", "c", "ell", "b"))
    m = len(ell)
    require(p in (5, 13) and c * c % p == p - 1, "prime-field/split hypothesis")
    require(len(b) == m and all(len(row) == m for row in b), "matrix shape")
    require(all(len(row) == 2 for row in ell), "terminal block shape")
    require(all(0 <= x < p for row in ell + b for x in row), "canonical residues")
    require(all(b[i][i] == 0 for i in range(m)), "zero pivot diagonal")
    require(all(dot(row, row, p) == p - 1 for row in ell), "terminal norm")
    require(all((c * (b[i][j] + b[j][i]) + dot(ell[i], ell[j], p)) % p == 0
                for i in range(m) for j in range(i + 1, m)), "mixed Gram relation")
    a = [-(u + c * v) * pow(c, -1, p) % p for u, v in ell]
    g = []
    for i in range(m):
        row = []
        for j in range(m):
            row.extend([0, 1] if i == j else [b[i][j], c * b[i][j] % p])
        g.append(row + ell[i])
    g.append([x for value in a for x in (value, c * value % p)] + [1, c])
    return a, g


def rank(g, p):
    a = [row[:] for row in g]
    r = 0
    for j in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        inv = pow(a[r][j], -1, p)
        a[r] = [x * inv % p for x in a[r]]
        for i in range(len(a)):
            if i != r:
                coefficient = a[i][j]
                a[i] = [(x - coefficient * y) % p for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def distribution(g, p):
    """Enumerate every base-p coefficient vector, including zero, exactly once.

    Incrementing a digit, even on wraparound, adds its row modulo p.
    This avoids recomputing the full matrix product for each word.
    """
    k, n = len(g), len(g[0])
    digits, word, counts = [0] * k, [0] * n, [0] * (n + 1)
    for _ in range(p ** k):
        counts[sum(x != 0 for x in word)] += 1
        for j in range(k):
            digits[j] = (digits[j] + 1) % p
            word = [(x + y) % p for x, y in zip(word, g[j])]
            if digits[j]:
                break
    return counts


def macwilliams(counts, p, k):
    n = len(counts) - 1
    for j in range(n + 1):
        transformed = sum(
            counts[i] * sum((-1) ** t * (p - 1) ** (j - t)
                            * comb(i, t) * comb(n - i, j - t)
                            for t in range(max(0, j - n + i), min(i, j) + 1))
            for i in range(n + 1))
        require(transformed == p ** k * counts[j], "MacWilliams identity")


def self_test(examples):
    # Independent matrix multiplication checks the incremental enumerator.
    for p, g in [(3, [[1, 1, 0], [0, 1, 2]]), (5, [[1, 2]])]:
        expected = [0] * (len(g[0]) + 1)
        for x in itertools.product(range(p), repeat=len(g)):
            word = [sum(x[i] * g[i][j] for i in range(len(g))) % p
                    for j in range(len(g[0]))]
            expected[sum(y != 0 for y in word)] += 1
        require(distribution(g, p) == expected, "enumerator regression")
    require(len(examples) == 2 and all(e["p"] == 5 for e in examples),
            "revision application inventory")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    data = (HERE / "applications.json").read_bytes()
    examples = json.loads(data)
    self_test(examples)
    g6, g8 = (build(e)[1] for e in examples)
    require([row[2:] for row in g8[1:]] == g6, "literal GF(5) reduction")
    g4 = [row[2:] for row in g6[1:]]
    require(rank(g4, 5) == 2 and all(dot(x, y, 5) == 0 for x in g4 for y in g4),
            "GF(5) length-four self-duality")
    require(distribution(g4, 5)[1] == 0 and distribution(g4, 5)[2] > 0,
            "GF(5) length-four distance")
    certificates = []
    for e in examples:
        p = e["p"]
        a, g = build(e)
        k, n = len(g), len(g[0])
        require(n == 2 * k and rank(g, p) == k, "half-dimension/full row rank")
        require(all(dot(x, y, p) == 0 for x in g for y in g), "matrix Gram condition")
        require(len(e["witness"]) == k and len(e["word"]) == n, "witness shape")
        word = [sum(e["witness"][i] * g[i][j] for i in range(k)) % p for j in range(n)]
        require(word == e["word"], "printed witness word")
        counts = distribution(g, p)
        require(counts[0] == 1 and sum(counts) == p ** k, "complete enumeration")
        distance = next(j for j in range(1, n + 1) if counts[j])
        require(distance == e["distance"] == sum(x != 0 for x in word), "minimum distance")
        macwilliams(counts, p, k)
        certificates.append(dict(id=e["id"], p=p, n=n, k=k, distance=distance, a=a,
                                 matrix=g, rank=k, gram_zero=True, nonzero_vectors=p**k-1,
                                 weight_distribution=counts, witness=e["witness"], word=word,
                                 macwilliams_verified=True))
        print(f"PASS {e['id']}: [{n},{k},{distance}], {p**k-1:,} nonzero vectors", flush=True)
    result = dict(input_sha256=hashlib.sha256(data).hexdigest(),
                  method="complete base-p enumeration; independent rank, Gram and MacWilliams checks",
                  lean_certificate=False, examples=certificates)
    outputs = {"applications_results.json": json.dumps(result, indent=2) + "\n"}
    for name, contents in outputs.items():
        path = HERE / name
        if args.write:
            path.write_text(contents)
        else:
            require(path.exists() and path.read_text() == contents, f"stale generated file: {name}")
    print("PASS all generated files" + (" regenerated" if args.write else " match"))


if __name__ == "__main__":
    main()
