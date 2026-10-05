import Mathlib
import Submission.Work.RPV.Defs

namespace Work.RPCore.Flow

theorem norm_fderiv_pair_le (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 4 ψ) {B' : ℝ}
    (hψ' : ∀ t, |deriv ψ t| ≤ B') :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ × Work.RPV.PS,
      ‖fderiv ℝ (fun z : ℝ × Work.RPV.PS => (ψ z.1, z.2)) z‖ ≤ K := by
  refine ⟨max B' 1, le_trans zero_le_one (le_max_right B' 1), fun z => ?_⟩
  obtain ⟨t, x⟩ := z
  have hdiff : DifferentiableAt ℝ ψ t := (hψ.contDiffAt).differentiableAt (by norm_num)
  have h1 : HasFDerivAt (fun z : ℝ × Work.RPV.PS => ψ z.1)
      ((fderiv ℝ ψ t).comp (ContinuousLinearMap.fst ℝ ℝ Work.RPV.PS)) (t, x) :=
    hdiff.hasFDerivAt.comp (t, x) hasFDerivAt_fst
  have h2 : HasFDerivAt (fun z : ℝ × Work.RPV.PS => z.2)
      (ContinuousLinearMap.snd ℝ ℝ Work.RPV.PS) (t, x) :=
    hasFDerivAt_snd
  have hf : fderiv ℝ (fun z : ℝ × Work.RPV.PS => (ψ z.1, z.2)) (t, x)
      = ((fderiv ℝ ψ t).comp (ContinuousLinearMap.fst ℝ ℝ Work.RPV.PS)).prod
        (ContinuousLinearMap.snd ℝ ℝ Work.RPV.PS) :=
    (h1.prodMk h2).fderiv
  rw [hf]
  have hL1 : ‖(fderiv ℝ ψ t).comp (ContinuousLinearMap.fst ℝ ℝ Work.RPV.PS)‖ ≤ max B' 1 := by
    calc ‖(fderiv ℝ ψ t).comp (ContinuousLinearMap.fst ℝ ℝ Work.RPV.PS)‖
        ≤ ‖fderiv ℝ ψ t‖ * ‖ContinuousLinearMap.fst ℝ ℝ Work.RPV.PS‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖fderiv ℝ ψ t‖ * 1 := by rw [ContinuousLinearMap.norm_fst]
      _ = ‖deriv ψ t‖ := by rw [mul_one, norm_deriv_eq_norm_fderiv]
      _ = |deriv ψ t| := by rw [Real.norm_eq_abs]
      _ ≤ B' := hψ' t
      _ ≤ max B' 1 := le_max_left _ _
  calc ‖((fderiv ℝ ψ t).comp (ContinuousLinearMap.fst ℝ ℝ Work.RPV.PS)).prod
          (ContinuousLinearMap.snd ℝ ℝ Work.RPV.PS)‖
      = ‖((fderiv ℝ ψ t).comp (ContinuousLinearMap.fst ℝ ℝ Work.RPV.PS),
          ContinuousLinearMap.snd ℝ ℝ Work.RPV.PS)‖ := ContinuousLinearMap.opNorm_prod _ _
    _ = max ‖(fderiv ℝ ψ t).comp (ContinuousLinearMap.fst ℝ ℝ Work.RPV.PS)‖
            ‖ContinuousLinearMap.snd ℝ ℝ Work.RPV.PS‖ := by rw [Prod.norm_def]
    _ = max ‖(fderiv ℝ ψ t).comp (ContinuousLinearMap.fst ℝ ℝ Work.RPV.PS)‖ 1 := by
          rw [ContinuousLinearMap.norm_snd]
    _ ≤ max (max B' 1) 1 := max_le_max hL1 le_rfl
    _ = max B' 1 := by rw [max_assoc, max_self]

end Work.RPCore.Flow
