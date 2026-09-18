"""Auxiliary exhaustive checks. Not imported by Lean or used as a proof oracle.
Enumerates every rank-two family on at most six labelled vertices and every
three-uniform hypergraph on at most six labelled vertices.
SPDX-License-Identifier: MIT
"""
from itertools import combinations
import json

def require(condition, message):
    if not condition: raise RuntimeError(message)

def check(n, r):
    verts = range(n)
    edges = [sum(1<<v for v in e) for e in combinations(verts,r)]
    pairs = [sum(1<<v for v in e) for k in range(3) for e in combinations(verts,k)]
    misses = []
    for t in pairs:
        misses.append(sum(1<<i for i,e in enumerate(edges) if not (e&t)))
    vmasks = [sum(1<<i for i,e in enumerate(edges) if e&(1<<v)) for v in verts]
    count, largest_degree, largest_family = 0, 0, 0
    for h in range(1<<len(edges)):
        private = 0
        small_cover = False
        for m in misses:
            residual = h&m
            if residual == 0: small_cover = True
            elif residual & (residual-1) == 0: private |= residual
        if private != h: continue
        if r == 3 and small_cover: continue
        # For r=3, a deletion cover plus one vertex of the missing edge gives
        # a size-three cover; no cover of size <=2 was found above.
        count += 1
        d = max(((h&m).bit_count() for m in vmasks), default=0)
        largest_degree = max(largest_degree,d)
        largest_family = max(largest_family,h.bit_count())
        require(d <= (3 if r==2 else 6), 'degree bound violated')
        if r==2: require(h.bit_count() <= 6, 'rank-two family bound violated')
    return {'vertices':n,'rank':r,'families_checked':1<<len(edges),
            'qualifying_families':count,'maximum_degree':largest_degree,
            'maximum_edges':largest_family}

def main():
    results = [check(n,r) for r in (2,3) for n in range(7)]
    sharp = next(x for x in results if x['rank']==3 and x['vertices']==5)
    require(sharp['maximum_degree']==6, 'sharpness cross-check failed')
    print(json.dumps({'status':'pass','results':results},indent=2))

if __name__ == '__main__': main()
