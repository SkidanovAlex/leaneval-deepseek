import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Commons.Analysis.Calculus

open scoped ContDiff

theorem iteratedDeriv_two_comp_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) (z w : E) :
    iteratedDeriv 2 (fun θ : ℝ => f (z + θ • w)) 0 = (iteratedFDeriv ℝ 2 f z) ![w, w] := by
  -- Write the affine map `θ ↦ z + θ • w` as `(fun y => z + y) ∘ L` with `L θ = θ • w`.
  set L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) w with hL
  have hLapply : ∀ θ : ℝ, L θ = θ • w := by intro θ; simp [hL]
  have hcomp : (fun θ : ℝ => f (z + θ • w)) = (fun y : E => f (z + y)) ∘ L := by
    ext θ; simp [hLapply]
  have hdiff : ContDiff ℝ 2 (fun y : E => f (z + y)) := by
    simpa [Function.comp_def] using hf.comp (contDiff_const.add contDiff_id)
  -- Iterated derivative of a composition with a continuous linear map on the right.
  have hkey := ContinuousLinearMap.iteratedFDeriv_comp_right (𝕜 := ℝ) (n := (2 : ℕ∞))
    L hdiff 0 (i := 2) (by norm_num)
  have hL0 : L 0 = 0 := by simp [hLapply]
  have hL1 : L 1 = w := by simp [hLapply]
  rw [iteratedDeriv, hcomp, hkey]
  rw [iteratedFDeriv_comp_add_left]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [hL0, add_zero, hL1]
  congr 1
  funext i; fin_cases i <;> rfl

end Commons.Analysis.Calculus