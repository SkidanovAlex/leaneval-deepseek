import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.Work.ZeroEst.one_var
import Submission.Work.ZeroEst.reduction

/-! Guidance from the project lead (the requester):

# Area Z — zero estimate (`Submission.CDTPlan.ZeroEstimate`)

Paper: REFS/L2chi.tex §"Functional bad approximability": Theorem `Shidlovsky`, Lemma
`lem_Shidlovsky` (ε = 0 in the D-closed case), and Corollary `jumps Cartesian`.

The contract asks for the EXISTENCE of one nonzero minimal-total-degree monomial of the
multivariate auxiliary series `auxSeries f Q` with all exponents `≤ m·D + C` (all the holonomy
bound uses).

This file assembles it from the two Area-Z lemmas:

* `Work.ZeroEst.one_var`  — the one-variable Shidlovsky bound (paper Theorem `Shidlovsky`,
  ε = 0): for `ℚ(x)`-independent, `d/dx`-closed `f`, every nonzero `Σ Pᵢ fᵢ` with `deg Pᵢ < D`
  has order of vanishing at `0` at most `m·D + C`.
* `Work.ZeroEst.reduction` — the Cartesian lift (paper Corollary `jumps Cartesian`): if the
  one-variable bound holds for `f` with constant `C`, then for every `d`, `D` and every
  `Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ` with `degreeOf j (Q i) < D` and
  `auxSeries f Q ≠ 0`, some monomial `n` of minimal total degree has every coordinate
  `n j ≤ m·D + C`.
-/

namespace Work.ZeroEst

open Submission.CDTPlan

/-- **Area Z — the zero estimate** (`Submission.CDTPlan.ZeroEstimate`, paper Lemma
`lem_Shidlovsky` for a `d/dx`-closed span, ε = 0). -/
theorem zero_estimate : ZeroEstimate := by
  intro m f hpi hdc
  obtain ⟨C, hC⟩ := one_var m f hpi hdc
  exact ⟨C, reduction m f C hC⟩

end Work.ZeroEst
