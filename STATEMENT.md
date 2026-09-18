# Statement correspondence and mathematical proof

## Original question and separate notions

Erdos problem 834 asks whether a 3-critical 3-uniform hypergraph can have minimum
degree at least seven. The term critical has two interpretations. The catalog
JSP-000690 explicitly uses the chromatic interpretation. This package retains
that scope and additionally resolves the transversal interpretation; it does
not narrow the question to a finite search.

Sources: https://www.erdosproblems.com/834 and Ruiliang Li,
https://arxiv.org/html/2512.24850v1 , Definitions 2.1/2.3 and Theorems 1.1/1.2.

## Chromatic statement

`JSP690.Hypergraph n` is a list of triples in `Fin n`. `SimpleThreeUniform`
requires a duplicate-free list and increasing, distinct vertices in each
triple, so it represents a simple three-uniform hypergraph.
`Proper` forbids monochromatic edges under weak vertex-colouring.
`ChromaticNumberExactly` quantifies over arbitrary colouring functions and
excludes every smaller natural number of colours. The proof covers all binary
functions via a proved complete enumeration, not by assuming mask completeness.
`AllProperSubgraphsTwoColorable` allows simultaneous removal of vertices and
edges. Total colours restrict to the surviving domain; removed colours play no
role. Every single edge/vertex deletion also has chromatic number exactly two.
The attained degree-seven witness rules out a vacuous empty-domain result.

## Transversal statement

`H : Finset (Finset V)` is a finite simple set system. Uniformity says every
edge has cardinality three. `Covers H T` means T meets each edge.
`TauExactly H k` states both a cover of size k and the absence of covers of
smaller cardinality. `TauCriticalThree H` states exact transversal number three
and exact transversal number two after every edge deletion. These are standard
cover conditions, not assumed conclusions about degree.

`degree_le_six` proves the pointwise bound for every V with decidable equality,
every H, and every vertex. It does not assume a finite ambient universe or a
bound on H's order. `no_minimum_degree_seven` negates the existential question
for all natural vertex counts. The empty ambient type cannot meet its
criticality premise: the required three-element transversal supplies a vertex.
`completeFive_critical` proves exact criticality for K5^(3), and
`completeFive_degrees` proves every degree equals six. Enumeration of its 32
vertex subsets is backed by `fiveSubsets_complete` for every possible Finset.

## Elementary proof of the degree bound

Fix a vertex v. Replace every incident hyperedge e by the pair e minus {v}.
The resulting pair family L has size equal to d(v): deletion of the common
vertex is injective on the incident edges.

For each original edge e, choose a cover B_e of H-e with at most two vertices.
It must be disjoint from e, since otherwise it covers all of H, contradicting
tau(H)=3. For incident e, B_e therefore avoids v and meets every other pair of
L. Thus each pair f of L has a disjoint set of size at most two meeting all
other pairs.

We prove that any pair family with this property has at most six members.
First its maximum vertex degree is at most three: deleting one edge through x
provides a cover avoiding x, and each of its at most two vertices can meet at
most one other edge through x. If all degrees are at most two, any deletion
cover meets at most four remaining edges, giving at most five in total.
Otherwise choose three edges xa, xb, xc. The deletion cover for xa must be
exactly {b,c}; similarly the other two covers are {a,c} and {a,b}. Every edge
not through x must meet all three pairs, hence is one of ab, ac, bc. All edges
are among xa, xb, xc, ab, ac, bc, giving six. This proof is implemented directly
in `pair_card_le_six`; the general Bollobas inequality is not assumed.

Applying the pair bound to L gives d(v)<=6 for every v. In particular a
minimum-degree-seven example under transversal criticality cannot exist.
The complete three-graph on five vertices has transversal number three; after
deleting a triple its complementary pair is a cover and no single vertex is
a cover. Its degree is choose(4,2)=6, proving sharpness.

## Combined endpoint and limits

`JSP690Complete.erdos834_both` conjoins the chromatic existence theorem, the
universally quantified transversal nonexistence theorem and the sharpness
witness. No extra mathematical hypotheses are appended to that endpoint.
The two encodings have their own documented definitions, rather than pretending
chromatic and transversal criticality are equivalent.

This does not prove that Li's nine-vertex example is minimum-order or
minimum-edge among all chromatic examples. It does not assert the ten-edge
transversal theorem from the paper, an original discovery, or an award.
