# Equal flag vectors and different codimension-three face counts

The order polytopes of the complete face lattices of a hexagonal pyramid and a truncated triangular bipyramid have 35,946 and 35,944 faces of dimension 25. The two input three-polytopes have identical full flag vectors (1, 7, 12, 7, 24, 24, 24, 48). Both output polytopes have dimension 28.

The explicit integer coordinates, proof, and intersection count appear in [the paper](paper/main.pdf). This example limits the information an enumerator for Question 6.6 can use. [Lundström and Saud Maia Leite](https://doi.org/10.1016/j.ejc.2025.104304)

## Reproduce

Run from the top of this checkout.

```sh
sha256sum -c SHA256SUMS
python3 -BI verification/check.py
python3 -Bu formal/verify_lean.py formal TruncatedAudit --jobs 2
```

The coordinate checker reconstructs supporting facets, all face inclusions, and every contraction of three covering arrows. It uses Python’s standard library. The Lean verifier builds from the locked project sources, checks twelve declarations and independently replays the kernel on 93 local modules. For the geometric statement using actual face posets see [the final theorem](formal/TruncatedPhysicalComparison.lean). See [the dated replay](verification/spark-replay.txt) and [coordinate counts](verification/counts.json).

Bowen Zuo, East China University of Science and Technology. Version 1.0.0, 26 November 2026. ChatGPT assisted with mathematical derivation, independent checks, formalization and drafting. The software uses Apache-2.0 and the manuscript carries a separate copyright notice.
