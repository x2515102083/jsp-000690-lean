# Proof and exact statement correspondence

The source problem asks whether a simple 3-uniform hypergraph can be 3-critical with every vertex of degree at least seven. Two standard criticality notions give opposite answers. We state them separately; no implication identifying them is used.

## 1. Chromatic reading

The unchanged module `JSP690.lean` proves Li's example on nine vertices and twenty-two edges. Edges are strictly increasing triples with no duplicate triples; weak proper colorings forbid a monochromatic triple. It proves chromatic number exactly three, that every edge or vertex deletion is two-colorable (in fact of chromatic number exactly two), and that every arbitrary proper subhypergraph is two-colorable. Its degree sequence is (10,7,7,7,7,7,7,7,7).

The binary-coloring enumeration has a general completeness proof for every function `Fin n -> Bool`, not merely a checked sample of masks. Kernel reduction checks failure of every binary coloring for the concrete graph. The chosen deletion masks are verified witnesses only. The theorem `JSP690.jsp000690` gives the full existential conclusion without an extra hypothesis.

Mathematical source: Ruiliang Li, arXiv:2512.24850v1, Theorems 1.2/4.1 and equation (5). This construction is not new.

## 2. An elementary (2,2) set-pairs lemma

Let I be any finite index set. Suppose each A_i is a two-element set, each B_i has at most two elements, A_i and B_i are disjoint, and A_i intersects B_j whenever i != j. Then |I| <= 6.

First, both maps i -> A_i and i -> B_i are injective: equality of two sets on either side would contradict a cross-intersection and an own-pair disjointness.

**Star bound.** Fix a point a and consider the A_i containing a. Choose one indexed pair A_i in this star. B_i avoids a. Every other A_j in the star meets B_i, and hence is {a,b} for a point b in B_i. Distinct A_j are different, so there are at most two others. Every star has at most three members. Empty stars cause no exception.

**Disjoint-pairs case.** If A_i and A_j are disjoint, every B_k for k outside {i,j} must contain a point of each. Since its size is at most two, B_k is exactly one of the at most four pairs in A_i x A_j. Injectivity of B gives at most four such indices. Including i and j gives at most six.

**Intersecting case.** Otherwise fix A_i={a,b}. Every A_k meets A_i, so all indices belong to the star at a or the star at b. The two star bounds again give at most six. The empty family is immediate.

`pair_system_card_le_six` proves this for arbitrary ambient and index types, with no fixed size bound. This elementary proof is a special case of the classical Bollobás set-pairs inequality; no novelty is claimed.

## 3. Transversal-critical degree bound

A transversal is a vertex set meeting every edge. Suppose H is a finite simple 3-uniform hypergraph with transversal number exactly three, and deleting any edge leaves a transversal of size at most two.

For each edge e choose such a deletion transversal T_e. It must be disjoint from e: otherwise it would already meet every edge of H, contradicting transversal number three.

Now fix any vertex v and restrict to the edges containing v. For each such edge e put A_e=e minus {v}, and B_e=T_e. The A_e have exactly two elements, and the B_e at most two. Their own pairs are disjoint. For distinct e and f, T_f meets e, and T_f avoids v because it avoids f. Thus T_f meets e minus {v}. These pairs satisfy the preceding lemma.

It follows that **d_H(v) <= 6 for every vertex v**. This is the theorem `degree_le_six`. There is no restriction on the finite number of edges or the size of the ambient vertex type. The `DecidableEq` type-class argument supplies decidable equality, not a missing mathematical theorem; ordinary classical finite hypergraphs are included.

The criticality premises cannot hold vacuously for an empty edge set: the empty set would be a transversal. Three-uniformity therefore supplies an active vertex, proved in `exists_positive_degree_le_six`. Hence the statement that every vertex has degree at least seven is impossible, even for an empty ambient type.

The development also proves that each edge-deletion transversal number is **exactly two**. A transversal of size less than two after deleting e, together with any vertex of e, would be a transversal of H of size at most two. Thus our at-most-two definition has exactly the standard edge-critical meaning.

## 4. Sharpness

For the complete 3-graph on five vertices, every three-element set is a transversal and no set of at most two vertices is one. After deleting e, the other two vertices meet every remaining edge. Each vertex belongs to exactly six triples. `complete_five_properties` checks all these facts with ordinary `decide` and proves the bound is attained.

## 5. Combined endpoint and limitations

`JSP690Complete.complete_resolution` is the conjunction of the complete chromatic existence statement, the complete transversal nonexistence statement, and the sharpness witness. Its proof only invokes the above proved declarations.

The chromatic and transversal modules use different explicit standard representations: a duplicate-free list of ordered triples on `Fin n`, and a finite set of three-element finite sets. Their meanings are documented independently. No hidden conversion, weakening of criticality, or equality between the two notions is assumed.

This answers the original degree-seven question under both meanings. It does not claim the separate edge-count bound |E(H)| <= 10, a new mathematical solution, a first formalization, a resolution of Erdős 287, or an official prize decision. Earlier complete formalizations are disclosed in ATTRIBUTION.md.
