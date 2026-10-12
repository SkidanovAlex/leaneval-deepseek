import Mathlib.Analysis.Calculus.ContDiff.Operations
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Calculus

open scoped ContDiff

theorem norm_iteratedFDeriv_update_le {n k : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (Φ : (Fin n → E) → F) (hΦ : ContDiff ℝ k Φ) (x : Fin n → E) (i : Fin n) (z : E) : ‖iteratedFDeriv ℝ k (fun w : E => Φ (Function.update x i w)) z‖ ≤ ‖iteratedFDeriv ℝ k Φ (Function.update x i z)‖ := by
  classical
  let Siso : E →ₗᵢ[ℝ] (Fin n → E) := LinearIsometry.single ℝ (fun _ : Fin n => E) i
  let S : E →L[ℝ] (Fin n → E) := Siso.toContinuousLinearMap
  set c : Fin n → E := Function.update x i 0 with hc
  have hS_apply : ∀ w : E, S w = Pi.single i w := fun w => rfl
  have hupdate : ∀ w : E, Function.update x i w = c + S w := by
    intro w
    ext j
    rw [Pi.add_apply, hS_apply, Pi.single_apply, hc, Function.update_apply]
    by_cases hj : j = i <;> simp [hj]
  have hf : ContDiff ℝ k (fun v : Fin n → E => Φ (c + v)) :=
    hΦ.comp (contDiff_const.add contDiff_id)
  have hcomp : (fun w : E => Φ (Function.update x i w))
      = (fun v : Fin n → E => Φ (c + v)) ∘ S := by
    funext w
    rw [Function.comp_apply, hupdate w]
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right (𝕜 := ℝ) S hf z le_rfl]
  calc ‖(iteratedFDeriv ℝ k (fun v : Fin n → E => Φ (c + v)) (S z)).compContinuousLinearMap
          (fun _ : Fin k => S)‖
      ≤ ‖iteratedFDeriv ℝ k (fun v : Fin n → E => Φ (c + v)) (S z)‖ :=
        ContinuousMultilinearMap.norm_compContinuous_linearIsometry_le _ (fun _ => Siso)
    _ = ‖iteratedFDeriv ℝ k Φ (c + S z)‖ := by
        rw [iteratedFDeriv_comp_add_left]
    _ = ‖iteratedFDeriv ℝ k Φ (Function.update x i z)‖ := by
        rw [← hupdate z]

end Commons.Analysis.Calculus