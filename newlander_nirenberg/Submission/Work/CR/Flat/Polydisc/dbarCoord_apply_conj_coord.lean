import Mathlib
import Submission.Work.CR.Flat.Polydisc

namespace Work.CR.Flat.Polydisc

open scoped NNReal ENNReal
open MeasureTheory Set

/-- The anti-holomorphic coordinate functions on `ℂⁿ` satisfy
`∂̄_j \bar z_k = δ_{jk}`; in particular `∂̄_j \bar z_j = 1`, the identity behind the
Beltrami-coefficient formulation `∂̄w = μ ∂w`. -/
theorem dbarCoord_apply_conj_coord {n : ℕ} (j k : Fin n) (z : Fin n → ℂ) :
    dbarCoord j (fun w : Fin n → ℂ => star (w k)) z = if j = k then 1 else 0 := by
  -- `w ↦ star (w k)` is the real-linear map `conjCLE ∘ proj k`.
  have hfd : fderiv ℝ (fun w : Fin n → ℂ => star (w k)) z
      = (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj (R := ℝ) k) := by
    have h1 : (fun w : Fin n → ℂ => star (w k))
        = ⇑((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj (R := ℝ) k)) := by
      funext w
      simp [ContinuousLinearMap.comp_apply]
    rw [h1, ContinuousLinearMap.fderiv]
  rw [dbarCoord, hfd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  by_cases h : j = k
  · subst h
    norm_num [Pi.single_eq_same, Complex.I_mul_I, Complex.conjCLE_apply]
  · have hkj : k ≠ j := fun hc => h hc.symm
    rw [ite_eq_right h, Pi.single_eq_of_ne hkj, Pi.single_eq_of_ne hkj]
    simp

end Work.CR.Flat.Polydisc
