#!/usr/bin/env python3
"""Find an r=1 oriented coordinate pairing with the project-local CaDiCaL."""

import itertools
import json
import subprocess
import tempfile
from pathlib import Path


P = 5
C = 2
G = [
    [1, 3, 3, 2, 1, 1, 1, 3],
    [3, 4, 2, 1, 4, 4, 3, 2],
    [0, 3, 3, 1, 1, 0, 3, 3],
    [2, 0, 1, 4, 1, 0, 0, 0],
]
ROOT = Path(__file__).resolve().parents[5]
CADICAL = (
    ROOT / "references/oqp35_mols10/MOLS_EP/solvers/cadical/build/cadical"
)


class Cnf:
    def __init__(self):
        self.variables = 0
        self.clauses = []

    def new(self):
        self.variables += 1
        return self.variables

    def one_hot(self, size):
        values = [self.new() for _ in range(size)]
        self.clauses.append(values)
        for i, j in itertools.combinations(values, 2):
            self.clauses.append([-i, -j])
        return values

    def write(self, path):
        with path.open("w") as stream:
            stream.write(f"p cnf {self.variables} {len(self.clauses)}\n")
            for clause in self.clauses:
                stream.write(" ".join(map(str, clause)) + " 0\n")


def rank(matrix):
    work = [row[:] for row in matrix]
    result = 0
    for column in range(len(work[0])):
        pivot = next(
            (i for i in range(result, len(work)) if work[i][column] % P),
            None,
        )
        if pivot is None:
            continue
        work[result], work[pivot] = work[pivot], work[result]
        scale = pow(work[result][column], -1, P)
        work[result] = [(scale * value) % P for value in work[result]]
        for i in range(result + 1, len(work)):
            multiple = work[i][column]
            if multiple:
                work[i] = [
                    (x - multiple * y) % P
                    for x, y in zip(work[i], work[result])
                ]
        result += 1
    return result


def defect_rank(pairing):
    matrix = [
        [(G[i][second] - C * G[i][first]) % P for first, second in pairing]
        for i in range(len(G))
    ]
    return rank(matrix)


def build_cnf(blocked):
    cnf = Cnf()
    dimension, length = len(G), len(G[0])
    coefficients = [cnf.one_hot(P) for _ in range(dimension)]
    coordinates = [cnf.one_hot(P) for _ in range(length)]

    for column in range(length):
        state = cnf.one_hot(P)
        cnf.clauses.append([state[0]])
        for row in range(dimension):
            following = cnf.one_hot(P)
            coefficient = G[row][column] % P
            for left in range(P):
                for value in range(P):
                    total = (left + coefficient * value) % P
                    cnf.clauses.append(
                        [-state[left], -coefficients[row][value], following[total]]
                    )
            state = following
        for value in range(P):
            cnf.clauses.append([-state[value], coordinates[column][value]])

    cnf.clauses.append(
        [coefficients[row][value]
         for row in range(dimension) for value in range(1, P)]
    )

    arcs = {}
    for first in range(length):
        for second in range(length):
            if first == second:
                continue
            variable = cnf.new()
            arcs[first, second] = variable
            for value in range(P):
                cnf.clauses.append(
                    [-variable, -coordinates[first][value],
                     coordinates[second][C * value % P]]
                )

    for coordinate in range(length):
        incident = [
            variable for (first, second), variable in arcs.items()
            if coordinate in (first, second)
        ]
        cnf.clauses.append(incident)
        for left, right in itertools.combinations(incident, 2):
            cnf.clauses.append([-left, -right])

    for pairing in blocked:
        cnf.clauses.append([-arcs[edge] for edge in pairing])
    return cnf, arcs


def solve():
    if not CADICAL.exists():
        raise SystemExit(f"project-local CaDiCaL not found: {CADICAL}")
    blocked = []
    with tempfile.TemporaryDirectory(prefix="rank-one-sat-") as directory:
        directory = Path(directory)
        while True:
            cnf, arcs = build_cnf(blocked)
            cnf_path = directory / "pairing.cnf"
            solution_path = directory / "pairing.sol"
            cnf.write(cnf_path)
            result = subprocess.run(
                [str(CADICAL), "-q", "-w", str(solution_path), str(cnf_path)],
                check=False,
            )
            if result.returncode == 20:
                raise SystemExit("UNSAT: no nonzero boxed intersection")
            if result.returncode != 10:
                raise SystemExit(f"CaDiCaL exit code {result.returncode}")
            positive = {
                int(token)
                for token in solution_path.read_text().split()
                if token.lstrip("-").isdigit() and int(token) > 0
            }
            selected = [
                edge for edge, variable in arcs.items() if variable in positive
            ]
            pairing = sorted(selected, key=lambda edge: min(edge))
            defect = defect_rank(pairing)
            r = len(G) - defect
            if r == 1:
                return {
                    "solver": str(CADICAL),
                    "solver_version": subprocess.check_output(
                        [str(CADICAL), "--version"], text=True
                    ).strip(),
                    "field_order": P,
                    "square_root_minus_one": C,
                    "ordered_pairing_zero_based": pairing,
                    "defect_rank": defect,
                    "r": r,
                    "blocked_higher_rank_pairings": len(blocked),
                    "cnf_variables": cnf.variables,
                    "cnf_clauses": len(cnf.clauses),
                }
            blocked.append(pairing)


if __name__ == "__main__":
    print(json.dumps(solve(), indent=2))
