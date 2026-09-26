/-
# Auxiliary estimates for the cusp-`0` tile `E = KEpsilon`

This file collects the analytic inputs for `Work.Asymptotics.EPolyWindowE_one`:

* `Epoly_Delta_sharp`, `Epoly_j_sharp` : sharp (two-sided) bounds for `Δ` and `j` on `E`,
  i.e. the `S`-transport of the funnel asymptotics `‖Δ‖ ≍ e^{-2π Im}`, `‖j‖ ≍ e^{2π Im}`;
* `Epoly_E4_ge_half` : `‖E₄ τ‖ ≥ 1/2` for `Im τ ≥ 2`;
* `Epoly_atom_poly` : polynomial (in `scale w`) bounds for all the atoms on `E`.
-/
import Mathlib
import Submission.Work.Asymptotics.EBase
import Submission.Work.Asymptotics.Xi8_bound_E
import Submission.Work.Asymptotics.DeltaFun_funnel_lower_sharp
import Submission.Work.Asymptotics.DeltaFun_upper_sharp

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics

/-- `‖S • w‖ = ‖w‖⁻¹`. -/
lemma Epoly_norm_S_smul (w : UpperHalfPlane) :
    ‖(((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ = (‖(w : ℂ)‖)⁻¹ := by
  rw [Work.Kernels.S_smul_coe, norm_neg, norm_inv]

/-- Sharp two-sided bounds for `Δ` on `E`. -/
theorem Epoly_Delta_sharp :
    ∃ c C N : ℝ, 0 < c ∧ 0 < C ∧ 0 ≤ N ∧
      ∀ w : UpperHalfPlane, w ∈ KEpsilon →
        c * (Work.Kernels.scale w) ^ (-N) * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im))
            ≤ ‖Work.Kernels.DeltaFun w‖ ∧
        ‖Work.Kernels.DeltaFun w‖
            ≤ C * (Work.Kernels.scale w) ^ N * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) := by
  refine ⟨1 / 2, 2, 12, by norm_num, by norm_num, by norm_num, fun w hw => ?_⟩
  have hS := DeltaFun_S_smul' w
  have him : 2 ≤ (ModularGroup.S • w).im := hw.2
  have hnorm : ‖(((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ = (‖(w : ℂ)‖)⁻¹ :=
    Epoly_norm_S_smul w
  have hle : ‖(((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ ≤ Work.Kernels.scale w :=
    Work.Asymptotics.norm_coe_S_smul_le_scale w
  have hlow : (1 : ℝ) ≤ ‖(((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ := by
    rw [hnorm]
    exact (one_le_inv₀ (E_norm_pos w)).mpr (by linarith [E_norm_le_half hw])
  have hdn : ‖Work.Kernels.DeltaFun (ModularGroup.S • w)‖
      ≤ 2 * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) :=
    DeltaFun_upper_sharp _ (le_trans (by norm_num) him)
  have hdl : (1 / 2) * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im))
      ≤ ‖Work.Kernels.DeltaFun (ModularGroup.S • w)‖ :=
    DeltaFun_funnel_lower_sharp him
  have hsp1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hspos : 0 < Work.Kernels.scale w := Work.Kernels.scale_pos w
  have hexp : (0 : ℝ) < Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) := Real.exp_pos _
  have hrpow : (0 : ℝ) < (Work.Kernels.scale w) ^ (-(12 : ℝ)) := Real.rpow_pos_of_pos hspos _
  have hrpow1 : (Work.Kernels.scale w) ^ (-(12 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hsp1 (by norm_num)
  rw [hS, norm_mul, norm_pow]
  constructor
  · -- lower bound
    have hstep : (1 / 2) * (Work.Kernels.scale w) ^ (-(12 : ℝ))
          * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im))
        ≤ (1 / 2) * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) := by
      nlinarith [hrpow, hrpow1, hexp]
    calc (1 / 2) * (Work.Kernels.scale w) ^ (-(12 : ℝ))
            * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im))
        ≤ (1 / 2) * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) := hstep
      _ ≤ (1 : ℝ) * ((1 / 2) * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im))) := by
          rw [one_mul]
      _ ≤ ‖(((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ ^ 12 *
            ((1 / 2) * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im))) :=
          mul_le_mul_of_nonneg_right (one_le_pow₀ hlow) (by positivity)
      _ ≤ ‖(((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ ^ 12 *
            ‖Work.Kernels.DeltaFun (ModularGroup.S • w)‖ :=
          mul_le_mul_of_nonneg_left hdl (by positivity)
  · -- upper bound
    have hexp1 : Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, him])
    have h1 : ‖(((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ ^ 12 *
          ‖Work.Kernels.DeltaFun (ModularGroup.S • w)‖
        ≤ (Work.Kernels.scale w) ^ 12 * (2 * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im))) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hle 12) hdn (norm_nonneg _) (by positivity)
    calc ‖(((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ ^ 12 *
            ‖Work.Kernels.DeltaFun (ModularGroup.S • w)‖
        ≤ (Work.Kernels.scale w) ^ 12 * (2 * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im))) := h1
      _ = 2 * (Work.Kernels.scale w) ^ (12 : ℝ) * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) := by
          have hrw : (Work.Kernels.scale w) ^ (12 : ℝ) = (Work.Kernels.scale w) ^ 12 :=
            Real.rpow_natCast _ 12
          rw [hrw]; ring

end Work.Asymptotics
