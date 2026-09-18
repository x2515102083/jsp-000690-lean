"""Exhaustive small-order regression check; not an oracle for the Lean proof."""
from __future__ import annotations
import itertools
import json
import time
from collections import Counter


def exhaustive(n: int) -> dict[str, object]:
    if not 3 <= n <= 6:
        raise ValueError('This exhaustive check is restricted to 3..6 vertices.')
    edges = [sum(1 << v for v in e) for e in itertools.combinations(range(n), 3)]
    pairs = [sum(1 << v for v in t) for t in itertools.combinations(range(n), 2)]
    pair_avoiders = [sum(1 << i for i, e in enumerate(edges) if not e & t) for t in pairs]
    triple_avoiders = [sum(1 << i for i, e in enumerate(edges) if not e & t) for t in edges]
    hist: Counter[int] = Counter()
    degree_hist: Counter[int] = Counter()
    for H in range(1 << len(edges)):
        essential = 0
        for missing in pair_avoiders:
            x = H & missing
            if not x:
                break  # A two-element transversal exists: tau <= 2.
            if x & (x - 1) == 0:
                essential |= x  # Deleting this sole unhit edge allows the pair.
        else:
            if essential != H or not any(H & missing == 0 for missing in triple_avoiders):
                continue
            deg = [sum(bool(H & (1 << i)) and bool(e & (1 << v))
                       for i, e in enumerate(edges)) for v in range(n)]
            assert max(deg) <= 6, (n, H, deg)
            hist[H.bit_count()] += 1
            degree_hist[max(deg)] += 1
    return {'vertices': n, 'hypergraphs_checked': 1 << len(edges),
            'critical_hypergraphs': sum(hist.values()),
            'critical_edge_count_histogram': dict(sorted(hist.items())),
            'maximum_degree_histogram': dict(sorted(degree_hist.items()))}


def main() -> None:
    start = time.monotonic()
    results = [exhaustive(n) for n in range(3, 7)]
    assert results[0]['critical_hypergraphs'] == 0
    assert results[1]['critical_hypergraphs'] == 0
    assert results[2]['critical_hypergraphs'] == 1
    assert results[2]['critical_edge_count_histogram'] == {10: 1}
    print(json.dumps({'status': 'PASS', 'method': 'all labelled simple 3-uniform hypergraphs',
                      'results': results, 'elapsed_seconds': round(time.monotonic()-start, 3)},
                     indent=2))

if __name__ == '__main__':
    main()
