"""Independent finite cross-check of Li's Eq. (5); not a Lean proof oracle.

Pure Python standard library. Data below uses the paper's labels 1 through 9.
The Lean representation subtracts one from every label. The algorithm enumerates
all binary colorings, rather than trusting the witness masks in the Lean file.
"""

from itertools import product


EDGES = (
    (1, 2, 3), (1, 2, 9), (1, 3, 8), (1, 4, 6), (1, 4, 8), (1, 4, 9),
    (1, 5, 7), (1, 5, 8), (1, 5, 9), (1, 6, 7),
    (2, 3, 6), (2, 3, 7), (2, 4, 9), (2, 5, 9), (2, 6, 7),
    (3, 4, 8), (3, 5, 8), (3, 6, 7), (4, 6, 8), (4, 6, 9),
    (5, 7, 8), (5, 7, 9),
)
VERTICES = tuple(range(1, 10))


def proper(edges, coloring):
    return all(len({coloring[v] for v in edge}) >= 2 for edge in edges)


def binary_colorings(vertices):
    for bits in product((0, 1), repeat=len(vertices)):
        yield dict(zip(vertices, bits))


def main():
    assert len(EDGES) == len(set(EDGES)) == 22
    assert all(len(set(e)) == 3 and tuple(sorted(e)) == e for e in EDGES)
    assert {v for e in EDGES for v in e} == set(VERTICES)
    degrees = {v: sum(v in e for e in EDGES) for v in VERTICES}
    assert tuple(degrees.values()) == (10, 7, 7, 7, 7, 7, 7, 7, 7)
    print("Vertices: 9; distinct three-element edges: 22")
    print("Degrees:", degrees)

    colorings = tuple(binary_colorings(VERTICES))
    assert len(colorings) == 512
    assert not any(proper(EDGES, c) for c in colorings)
    print("All 512 binary colorings fail.")
    three = {v: 0 if v in (1, 2, 4, 5) else 2 if v == 7 else 1 for v in VERTICES}
    assert proper(EDGES, three)
    print("Explicit three-coloring passes.")

    for edge in EDGES:
        remaining = tuple(e for e in EDGES if e != edge)
        assert len(remaining) == 21
        assert any(proper(remaining, c) for c in colorings)
    print("All 22 edge deletions admit binary colorings.")

    for vertex in VERTICES:
        surviving = tuple(v for v in VERTICES if v != vertex)
        remaining = tuple(e for e in EDGES if vertex not in e)
        assert remaining
        assert any(proper(remaining, c) for c in binary_colorings(surviving))
    print("All 9 genuine vertex deletions admit binary colorings on 8 vertices.")
    assert not proper(EDGES, {v: 0 for v in VERTICES})
    assert proper((), {v: 0 for v in VERTICES})
    print("Sanity checks: constant coloring fails on H and passes on the empty graph.")
    print("CROSS-CHECK PASS (auxiliary only; Lean is authoritative).")


if __name__ == "__main__":
    main()
