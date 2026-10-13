import Mathlib
import Submission.Work.WilkiesH.Defs

namespace Work.WilkiesH.Interp

theorem norm_iteratedFDeriv_comp_proj_le {μ n k : ℕ} (e : Fin k ↪ Fin n)
    (φ : (Fin μ → ℝ) → (Fin n → ℝ)) {j r : ℕ} (hj : j ≤ r) (t : Fin μ → ℝ)
    (hφ : ContDiffAt ℝ r φ t) :
    ‖iteratedFDeriv ℝ j (fun u i => φ u (e i)) t‖ ≤ ‖iteratedFDeriv ℝ j φ t‖ := by
  -- `fun u i => φ u (e i)` is `L ∘ φ` for the coordinate-restriction linear map `L`,
  -- and `‖L‖ ≤ 1` because the norm on `Fin k → ℝ` is the sup norm.
  let L : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) :=
    LinearMap.mkContinuous
      { toFun := fun v i => v (e i)
        map_add' := fun v w => by funext i; simp
        map_smul' := fun c v => by funext i; simp }
      1 (fun v => by
        rw [one_mul]
        exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => norm_le_pi_norm v (e i))
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound L zero_le_one (fun v => by
      rw [one_mul]
      exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => norm_le_pi_norm v (e i))
  have hfun : (fun u i => φ u (e i)) = (L : (Fin n → ℝ) → (Fin k → ℝ)) ∘ φ := by
    funext u i; rfl
  have hiter : iteratedFDeriv ℝ j (fun u i => φ u (e i)) t
      = L.compContinuousMultilinearMap (iteratedFDeriv ℝ j φ t) := by
    rw [hfun]
    exact ContinuousLinearMap.iteratedFDeriv_comp_left L hφ (by exact_mod_cast hj)
  calc ‖iteratedFDeriv ℝ j (fun u i => φ u (e i)) t‖
      = ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ j φ t)‖ := by rw [hiter]
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ j φ t‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le L _
    _ ≤ 1 * ‖iteratedFDeriv ℝ j φ t‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ j φ t‖ := one_mul _

end Work.WilkiesH.Interp
