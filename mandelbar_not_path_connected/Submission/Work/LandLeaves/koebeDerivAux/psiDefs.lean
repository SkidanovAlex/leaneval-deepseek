import Mathlib
import Submission.Work.LandLeaves.gronwallDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Auxiliary vocabulary for the exterior area theorem in the `ψ`-language

This file fixes the notation in which the leaves `psiAnnulusArea`, `psiLevel`,
`psiCurveNull` and `psiCoeffSummable` are stated.  Everything is phrased for a function
`ψ : ℂ → ℂ` which is holomorphic and injective on the exterior `{w | 1 < ‖w‖}` of the unit disc
and satisfies `ψ w = w + O(1)` there; the Laurent coefficients `bco ψ n` are those of
`Work.LandLeaves.gronwallDefs`, so that `ψ w = w + ∑ n, bco ψ n * w⁻ⁿ` on `1 < ‖w‖`
(`Work.LandLeaves.psi_expansion`).

* `psiK ψ R` is the *bounded* side of the simple closed curve `ψ '' {w | ‖w‖ = R}`, i.e. the
  complement of the image of the exterior of radius `R`;
* `psiW ψ R` is the area functional `π R² - π ∑ₙ n ‖bco ψ n‖² (R²)⁻ⁿ`, which is the area of that
  region;
* `psiAnn ψ r R` is the image of the closed annulus `{r ≤ ‖w‖ ≤ R}`.

The identities `volume (psiK ψ R) = ofReal (psiW ψ R)` (large `R`) and
`volume (psiAnn ψ r R) = ofReal (…)` (all `1 < r < R`) together give the classical area theorem
`∑ₙ n ‖bco ψ n‖² ≤ 1` and hence Bieberbach's second coefficient bound.
-/

open MeasureTheory

namespace Work.LandLeaves.koebeDerivAux

/-- The bounded side of the curve `ψ '' {w | ‖w‖ = R}`: the complement of the image of the
exterior of radius `R`. -/
noncomputable def psiK (ψ : ℂ → ℂ) (R : ℝ) : Set ℂ := {z | ¬ ∃ w : ℂ, R < ‖w‖ ∧ ψ w = z}

/-- The image of the closed annulus `{r ≤ ‖w‖ ≤ R}` under `ψ`. -/
noncomputable def psiAnn (ψ : ℂ → ℂ) (r R : ℝ) : Set ℂ := ψ '' {w : ℂ | r ≤ ‖w‖ ∧ ‖w‖ ≤ R}

/-- The area functional `π R² - π ∑ₙ n ‖bco ψ n‖² (R²)⁻ⁿ`. -/
noncomputable def psiW (ψ : ℂ → ℂ) (R : ℝ) : ℝ :=
  Real.pi * R ^ 2 - Real.pi * ∑' n : ℕ, (n : ℝ) * ‖bco ψ n‖ ^ 2 * ((R ^ 2)⁻¹) ^ n

/-- The `n`-th coefficient weight `n ‖b_n‖²`. -/
noncomputable def psiCoeff (ψ : ℂ → ℂ) (n : ℕ) : ℝ := (n : ℝ) * ‖bco ψ n‖ ^ 2

lemma psiCoeff_nonneg (ψ : ℂ → ℂ) (n : ℕ) : 0 ≤ psiCoeff ψ n := by
  unfold psiCoeff; positivity

/-- The series `∑ₙ psiCoeff ψ n * ((R²)⁻¹)ⁿ` rewritten with the weight `psiCoeff`. -/
lemma psiW_eq (ψ : ℂ → ℂ) (R : ℝ) :
    psiW ψ R = Real.pi * R ^ 2 - Real.pi * ∑' n : ℕ, psiCoeff ψ n * ((R ^ 2)⁻¹) ^ n := by
  simp only [psiW, psiCoeff]

end Work.LandLeaves.koebeDerivAux
