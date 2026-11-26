# maxsat-model3-lean
In the Full Information model of online MAXSAT (Model 3 of [Peña and Borodin][PB19]), each arriving variable must be assigned irrevocably after all clauses containing it are revealed in full. This repository contains a Lean 4 formalization of the proof that no randomized algorithm can achieve a competitive ratio above 3/4 in this model.

The Preprint is in preparation at the moment.

## Main theorem

[`Model3MaxSAT/Main.lean`](Model3MaxSAT/Main.lean) proves
`Model3MaxSAT.randomized_model3_competitiveRatio_le`:

```lean
theorem randomized_model3_competitiveRatio_le
    {Ξ : Type u} [MeasurableSpace Ξ] (A : RandomizedAlgorithm Ξ) :
    competitiveRatio A ≤ (3 : ℝ) / 4
```

The online model is defined in
[`Model3MaxSAT/Model.lean`](Model3MaxSAT/Model.lean), and the competitive ratio
is defined in [`Model3MaxSAT/CompetitiveRatio.lean`](Model3MaxSAT/CompetitiveRatio.lean).

## Build and verify

Install [Lean](https://lean-lang.org/install/) and run these commands from the
repository root:

```bash
lake exe cache get
lake build
lake env lean Audit.lean
```

The repository pins Lean 4.24.0 and the Mathlib revision. The axiom audit
reports `propext`, `Classical.choice`, and `Quot.sound` for the main theorem.

## License

[MIT](LICENSE)

[PB19]: https://www.cs.toronto.edu/~bor/Papers/TCS-online-version.pdf
[slides]: https://www.cs.toronto.edu/~ali/MAXSAT_Model3_Nov11.pdf
