/-
# `NRow14` — RETIRED (the row is false under the frozen `StarPkgo`; the live form is `NRow14T2`)

The statement formerly in this file,

```
theorem NRow14 … : ∃ K, 0 < K ∧ ∀ …, Ctx … →
    HkMem α 4 (N2sg α Φs g) ∧ |IP α (N2sg α Φs g) g| ≤ K * (√α * Xn α g ^ 2)
```

is **not derivable from `Work.FTS.NonlinRows.Ctx`**: the honesty conjunct needs the star
coefficient `U(Φ̃_*)/sin 2θ` to vanish at `θ = 0` like `sin 2θ`, which the flat `WDMem` pricing of
the frozen `VocabO.StarPkgo` does not provide.  The prover's counterexample family (shear-type
perturbations `g = ψ(z)(sin^{1/2}(2θ) − c sin 2θ)` admitted by `GalClass`, for which the `i = 0`
slot of `HkIntegrand α 4 (N2sg α Φs g)` is not integrable) is written up in
`Submission/Work/FTS/NonlinRows/NOTES_NRow14_gap.md`.

The **true** form of the row, in the upgraded context `Work.FTS.VocabO2.Ctx2` (whose package
`StarPkgo2` carries the `𝒲^{4,∞}` fields `UsW`/`UszW` that this row needs), is proved in
`Submission/Work/FTS/NonlinRows/NRow14T2.lean` as `Work.FTS.NonlinRows.NRow14T2`.

Nothing imports this module; it is kept as a pointer.
-/
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.NonlinRows.NRow14T2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

end Work.FTS.NonlinRows
