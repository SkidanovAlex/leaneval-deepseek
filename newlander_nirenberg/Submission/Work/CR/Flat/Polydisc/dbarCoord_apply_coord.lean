import Mathlib
import Submission.Work.CR.Flat.Polydisc

namespace Work.CR.Flat.Polydisc

open scoped NNReal ENNReal
open MeasureTheory Set

/-- The real Fréchet derivative of the `k`-th coordinate function on `ℂⁿ` is the
(real restriction of the) `k`-th projection. -/
lemma fderiv_coord {n : ℕ} (k : Fin n) (z : Fin n → ℂ) :
    fderiv ℝ (fun w : Fin n → ℂ => w k) z
      = ((ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ)).restrictScalars ℝ := by
  rw [show (fun w : Fin n → ℂ => w k)
        = fun w => (ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ) w from rfl]
  exact ((ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.fderiv

/-- The coordinate functions on `ℂⁿ` are holomorphic, so
`∂̄_j (z ↦ z_k) = 0`; this is the basic `∂̄`-vanishing identity for the standard
flat coordinates (contrast `dbarCoord_apply_conj_coord`, where `∂̄_j \bar z_j = 1`). -/
theorem dbarCoord_apply_coord {n : ℕ} (j k : Fin n) (z : Fin n → ℂ) :
    dbarCoord j (fun w : Fin n → ℂ => w k) z = 0 := by
  unfold dbarCoord
  rw [fderiv_coord k z]
  show (1/2 : ℂ) * ((Pi.single j 1 : Fin n → ℂ) k
      + Complex.I * (Pi.single j Complex.I : Fin n → ℂ) k) = 0
  by_cases h : k = j
  · subst h; simp
  · rw [Pi.single_eq_of_ne h]; rw [Pi.single_eq_of_ne h]; ring

end Work.CR.Flat.Polydisc
