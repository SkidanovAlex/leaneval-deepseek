import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BSKinetic.exists_chiScale_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open scoped ContDiff Topology

/-- **The derivative of the rescaled bump is uniformly `O(1/ℓ)`.**

`chiScale ℓ x = χ(ℓ⁻¹ • x)` (`Submission.BoseGases.chiScale`), so the chain rule
`fderiv_comp_smul` gives
`fderiv ℝ (chiScale ℓ) x = ℓ⁻¹ • fderiv ℝ χ (ℓ⁻¹ • x)`, and the norm of
`fderiv ℝ χ` is bounded by a constant `M` independent of `ℓ` because `χ` is `C^∞`
with compact support (`Work.BSKinetic.Decomp.exists_bound_fderiv`). -/
theorem exists_fderiv_chiScale_bound_inv :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ℓ : ℝ), 0 < ℓ → ∀ (x w : EuclideanSpace ℝ (Fin 3)),
      |fderiv ℝ (Submission.BoseGases.chiScale ℓ) x w| ≤ (M / ℓ) * ‖w‖ := by
  obtain ⟨M, hM0, -, hder⟩ :=
    Work.BSKinetic.Decomp.exists_bound_fderiv
      Submission.BoseGases.chi_contDiff Submission.BoseGases.chi_hasCompactSupport
  refine ⟨M, hM0, ?_⟩
  intro ℓ hℓ x w
  have hkey : fderiv ℝ (Submission.BoseGases.chiScale ℓ) x w
      = (ℓ⁻¹) • (fderiv ℝ Submission.BoseGases.chi ((ℓ⁻¹) • x) w) := by
    rw [show Submission.BoseGases.chiScale ℓ
        = fun y : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chi ((ℓ⁻¹) • y) from by
      funext y; rfl]
    rw [fderiv_comp_smul]
    simp
  rw [hkey, ← Real.norm_eq_abs]
  calc ‖(ℓ⁻¹) • (fderiv ℝ Submission.BoseGases.chi ((ℓ⁻¹) • x) w)‖
      = ‖(ℓ⁻¹ : ℝ)‖ * ‖fderiv ℝ Submission.BoseGases.chi ((ℓ⁻¹) • x) w‖ := norm_smul _ _
    _ = ℓ⁻¹ * ‖fderiv ℝ Submission.BoseGases.chi ((ℓ⁻¹) • x) w‖ := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
    _ ≤ ℓ⁻¹ * (M * ‖w‖) :=
        mul_le_mul_of_nonneg_left (hder _ _) (le_of_lt (inv_pos.mpr hℓ))
    _ = (M / ℓ) * ‖w‖ := by ring

end Work.BoseBoxFock
