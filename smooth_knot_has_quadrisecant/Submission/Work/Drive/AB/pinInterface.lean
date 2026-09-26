import Submission.Work.Drive.AB.pinBounds
import Submission.Work.Drive.needleAngVelAssembly
import Submission.Work.Drive.sweepFam_double_blur_deriv
import Submission.Work.Drive.avgChordIdentity
import Submission.Work.Drive.needleNumerator
import Submission.Work.Drive.sweepChamferClean

/-!
# The double-average interface of the needle's chart

The two chart coordinates of the shifted needle about a point `c'` — and their `t`-derivatives — are
the iterated weighted averages of the corresponding quantities of the individual chamfered loops of
the blur window:

    ⟪shiftedNeedle t - c', u⟫ = ∫ v', ∫ s, b v' * b s * ⟪L (ε - δ₂ v') (t + period/4 - δ₁ s) - c', u⟫
    d/dt (…)                 = ∫ v', ∫ s, b v' * b s * ⟪chamferVel (ε - δ₂ v') (t + period/4 - δ₁ s), u⟫

These are the interface hypotheses of `Work.Drive.needle_num_pos_of_diag_osc` in the assembly of the
needle's angular-velocity pin.  They are `Work.Drive.sweepFam_coord_eq_doubleAverage` and
`Work.Drive.sweepFam_double_blur_deriv` in the shifted parametrisation, with the integrability
hypotheses discharged from the boundedness and measurability of the loop.

The last import is the *side-free* copy of the double-blur module (needed for the continuity of the
loop in the loop parameter, `Work.Drive.sweepLoopChamfer_continuous_tSF`): the merged universe also
contains `sweepFam_slices_knots`, whose copy of `sweepLoopChamfer_continuous_t` cannot coexist with
`sfcSideFree` — the side-free copy avoids the name altogether.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

variable {r : ℝ → Space} {d : BandArcData}

/-- **The two chart coordinates of the shifted needle are double averages.** -/
lemma inner_shiftedNeedle_eq_doubleAverage (hr : IsSmoothKnot r) (D : SweepData d)
    {lam δ₁ δ₂ ε : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) (c' u : Space) (t : ℝ) :
    inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε t - c') u
      = ∫ v' in (-1 : ℝ)..1, ∫ s in (-1 : ℝ)..1,
          sweepBump v' * sweepBump s *
            inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v')
              (t + period / 4 - δ₁ * s) - c') u := by
  obtain ⟨R, hR0, hR⟩ := wideEnd_knot_bounded hr.continuous hr.periodic
  have hRnn : 0 ≤ R := hR0
  have hloop : ∀ s x : ℝ, ‖sweepLoopChamfer r D lam s x‖ ≤ R :=
    fun s x => sweepLoopChamfer_norm_le hR hlam0 hlam1 s x
  have hsm : ∀ σ : ℝ, ‖sweepSmoothT r D lam δ₁ σ (t + period / 4)‖ ≤ R * 2 :=
    fun σ => norm_sweepSmoothT_le (C := R) (fun s x => hloop s x) σ (t + period / 4)
  -- measurability of the smoothed slice in the sweep parameter
  have hZ : Measurable (fun τ : ℝ => sweepSmoothT r D lam δ₁ (ε - δ₂ * τ) (t + period / 4)) :=
    ((stronglyMeasurable_sweepSmoothT_sigma hr.continuous D lam δ₁ (t + period / 4)).comp_measurable
      (by fun_prop : Measurable fun τ : ℝ => ε - δ₂ * τ)).measurable
  -- (1) the outer integrand
  have hout : IntervalIntegrable
      (fun τ : ℝ => sweepBump τ • sweepSmoothT r D lam δ₁ (ε - δ₂ * τ) (t + period / 4))
      volume (-1) 1 := by
    refine intervalIntegrable_of_measurable_of_bound_Icc (C := R * 2)
      (sweepBump_continuous.measurable.smul hZ) (fun x _ => ?_)
    rw [norm_smul]
    calc ‖sweepBump x‖ * ‖sweepSmoothT r D lam δ₁ (ε - δ₂ * x) (t + period / 4)‖
        ≤ 1 * (R * 2) :=
          mul_le_mul (by rw [Real.norm_eq_abs]; exact abs_sweepBump_le_one_local x)
            (hsm (ε - δ₂ * x)) (norm_nonneg _) (by norm_num)
      _ = R * 2 := one_mul _
  -- (2) the outer integrand with the inner product
  have houtc : IntervalIntegrable
      (fun τ : ℝ => sweepBump τ *
        inner ℝ (sweepSmoothT r D lam δ₁ (ε - δ₂ * τ) (t + period / 4)) u)
      volume (-1) 1 := by
    refine intervalIntegrable_of_measurable_of_bound_Icc (C := (R * 2) * ‖u‖)
      (sweepBump_continuous.measurable.mul (hZ.inner measurable_const)) (fun x _ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |sweepBump x| * |inner ℝ (sweepSmoothT r D lam δ₁ (ε - δ₂ * x) (t + period / 4)) u|
        ≤ 1 * (‖sweepSmoothT r D lam δ₁ (ε - δ₂ * x) (t + period / 4)‖ * ‖u‖) := by
          refine mul_le_mul (abs_sweepBump_le_one_local x)
            (abs_real_inner_le_norm _ _) (abs_nonneg _) (by norm_num)
      _ ≤ 1 * ((R * 2) * ‖u‖) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hsm (ε - δ₂ * x)) (norm_nonneg u)) (by norm_num)
      _ = (R * 2) * ‖u‖ := one_mul _
  -- (3) the inner integrand
  have hloopm : ∀ σ : ℝ, Measurable (fun s : ℝ =>
      sweepLoopChamfer r D lam σ (t + period / 4 - δ₁ * s)) :=
    fun σ => ((sweepLoopChamfer_measurable D hr.continuous lam).comp
      (measurable_const.prodMk (by fun_prop : Measurable fun s : ℝ => t + period / 4 - δ₁ * s)))
  have hinn : ∀ σ : ℝ, IntervalIntegrable
      (fun s : ℝ => sweepBump s • sweepLoopChamfer r D lam σ (t + period / 4 - δ₁ * s))
      volume (-1) 1 := by
    intro σ
    refine intervalIntegrable_of_measurable_of_bound_Icc (C := R)
      (sweepBump_continuous.measurable.smul (hloopm σ)) (fun x _ => ?_)
    rw [norm_smul]
    calc ‖sweepBump x‖ * ‖sweepLoopChamfer r D lam σ (t + period / 4 - δ₁ * x)‖
        ≤ 1 * R :=
          mul_le_mul (by rw [Real.norm_eq_abs]; exact abs_sweepBump_le_one_local x)
            (hloop σ _) (norm_nonneg _) (by norm_num)
      _ = R := one_mul _
  have hinnc : ∀ σ : ℝ, IntervalIntegrable
      (fun s : ℝ => sweepBump s *
        inner ℝ (sweepLoopChamfer r D lam σ (t + period / 4 - δ₁ * s)) u)
      volume (-1) 1 := by
    intro σ
    have hmi : Measurable (fun s : ℝ =>
        inner ℝ (sweepLoopChamfer r D lam σ (t + period / 4 - δ₁ * s)) u) :=
      (hloopm σ).inner measurable_const
    refine intervalIntegrable_of_measurable_of_bound_Icc (C := R * ‖u‖)
      (sweepBump_continuous.measurable.mul hmi) (fun x _ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |sweepBump x| * |inner ℝ (sweepLoopChamfer r D lam σ (t + period / 4 - δ₁ * x)) u|
        ≤ 1 * (‖sweepLoopChamfer r D lam σ (t + period / 4 - δ₁ * x)‖ * ‖u‖) := by
          refine mul_le_mul (abs_sweepBump_le_one_local x)
            (abs_real_inner_le_norm _ _) (abs_nonneg _) (by norm_num)
      _ ≤ 1 * (R * ‖u‖) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hloop σ _) (norm_nonneg u)) (by norm_num)
      _ = R * ‖u‖ := one_mul _
  have := sweepFam_coord_eq_doubleAverage (r := r) (d := d) D lam δ₁ δ₂ ε c' u
    (t + period / 4) hout houtc (fun v => hinn (ε - δ₂ * v)) (fun v => hinnc (ε - δ₂ * v))
  simpa only [shiftedNeedle, needleFam_apply] using this

end Work.Drive
