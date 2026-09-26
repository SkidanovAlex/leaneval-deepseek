import Mathlib
import Submission.Work.Drive.AB.pinSetup
import Submission.Work.Drive.AB.pinInterface

namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

set_option maxHeartbeats 1000000

variable {r : ℝ → Space} {d : BandArcData}

/-- **The clamped width of the retained arc is bounded by the period.** -/
lemma abs_sweepW'_le_period {d : BandArcData} (D : SweepData d) (s : ℝ) :
    |sweepW' D s| ≤ period := by
  have he : sweepW' D s = sweepW D (clampI s) := by
    simp only [sweepW', taR, tbR, sweepW]
  rw [he]
  rcases eq_or_lt_of_le (clampI s).2.1 with h0 | h0
  · have hc : clampI s = 0 := Subtype.ext h0.symm
    rw [hc, sweepW_zero, abs_zero]
    exact period_pos.le
  · rcases eq_or_lt_of_le (clampI s).2.2 with h1 | h1
    · have hc : clampI s = 1 := Subtype.ext h1
      rw [hc, sweepW_one, abs_of_nonneg period_pos.le]
    · rw [abs_of_nonneg (sweepW_pos_lt D (clampI s) ⟨h0, h1⟩).1.le]
      exact (sweepW_pos_lt D (clampI s) ⟨h0, h1⟩).2.le

/-- **Measurability, in the sweep parameter, of the blurred velocity of the loop.** -/
lemma measurable_integral_chamferVel {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) (lam δ₁ δ₂ ε τ : ℝ) :
    Measurable (fun v : ℝ => ∫ s in (-1 : ℝ)..1,
      sweepBump s • chamferVel r D lam (ε - δ₂ * v) (τ - δ₁ * s)) := by
  have hunc : StronglyMeasurable (Function.uncurry (fun v s : ℝ =>
      sweepBump s • chamferVel r D lam (ε - δ₂ * v) (τ - δ₁ * s))) := by
    show StronglyMeasurable (fun p : ℝ × ℝ =>
      sweepBump p.2 • chamferVel r D lam (ε - δ₂ * p.1) (τ - δ₁ * p.2))
    have h1 : Measurable (fun p : ℝ × ℝ => sweepBump p.2) :=
      sweepBump_continuous.measurable.comp measurable_snd
    have h2 : Measurable (fun p : ℝ × ℝ =>
        chamferVel r D lam (ε - δ₂ * p.1) (τ - δ₁ * p.2)) :=
      (wideEnd_measurable_chamferVel_joint hr.continuous
        (hr.smooth.continuous_deriv (by simp)) D lam).comp
        ((measurable_const.sub (measurable_const.mul measurable_fst)).prodMk
          (measurable_const.sub (measurable_const.mul measurable_snd)))
    exact (h1.smul h2).stronglyMeasurable
  have hint : StronglyMeasurable (fun v : ℝ => ∫ s,
      sweepBump s • chamferVel r D lam (ε - δ₂ * v) (τ - δ₁ * s)
        ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1))) := hunc.integral_prod_right
  have heq : (fun v : ℝ => ∫ s, sweepBump s •
        chamferVel r D lam (ε - δ₂ * v) (τ - δ₁ * s)
        ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1)))
      = (fun v : ℝ => ∫ s in (-1 : ℝ)..1, sweepBump s •
        chamferVel r D lam (ε - δ₂ * v) (τ - δ₁ * s)) := by
    funext v
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [heq] at hint
  exact hint.measurable

/-- **A global bound on the velocity of the chamfered loop**, uniform in both parameters. -/
lemma exists_chamferVel_bound {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ σ τ : ℝ, ‖chamferVel r D lam σ τ‖ ≤ Λ := by
  obtain ⟨L, hL0, hL⟩ := wideEnd_knot_bounded (hr.smooth.continuous_deriv (by simp))
    (doubleBlur_velocity_periodic hr)
  obtain ⟨R, hR0, hR⟩ := wideEnd_knot_bounded hr.continuous hr.periodic
  exact ⟨doubleBlurLam lam L R period,
    doubleBlurLam_nonneg hlam0 hL0 hR0 period_pos.le,
    fun σ τ => doubleBlur_chamferVel_bound hlam0 hlam1 hL hR period_pos.le σ
      (abs_sweepW'_le_period D σ) τ⟩

/-- **The derivative of the needle's chart coordinate is the double average of the loops'
velocities.**  This is the `t`-derivative companion of `Work.Drive.inner_shiftedNeedle_eq_doubleAverage`
(`Work.Drive.sweepFam_double_blur_deriv` in the shifted parametrisation), consumed by
`Work.Drive.needle_num_pos_of_diag_osc` in the assembly of the needle's angular-velocity pin. -/
theorem shiftedNeedle_deriv_eq_doubleAverage {r : ℝ → Space} (hr : IsSmoothKnot r)
    {d : BandArcData} (D : Work.Drive.SweepData d)
    {lam δ₁ δ₂ ε : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) (hδ₁ : δ₁ ≠ 0) (hδ₂ : 0 < δ₂)
    (hσlo : 0 < ε - δ₂) (hσhi : ε + δ₂ < 1) (c' u : Space) (t : ℝ) :
    deriv (fun t' : ℝ => inner ℝ (Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε t' - c') u) t
      = ∫ v' in (-1 : ℝ)..1, ∫ s in (-1 : ℝ)..1,
          Work.Drive.sweepBump v' * Work.Drive.sweepBump s *
            inner ℝ (Work.Drive.chamferVel r D lam (ε - δ₂ * v')
              (t + period / 4 - δ₁ * s)) u := by
  obtain ⟨Λ, hΛ0, hvel⟩ := exists_chamferVel_bound hr D hlam0 hlam1
  -- integrability of the inner (loop-parameter) integrand, for every sweep parameter
  have hinn : ∀ v : ℝ, IntervalIntegrable (fun s : ℝ => Work.Drive.sweepBump s •
      Work.Drive.chamferVel r D lam (ε - δ₂ * v) (t + period / 4 - δ₁ * s))
      volume (-1 : ℝ) 1 := by
    intro v
    refine intervalIntegrable_of_measurable_of_bound_Icc (C := Λ) ?_ ?_
    · exact Work.Drive.sweepBump_continuous.measurable.smul
        ((Work.Drive.wideEnd_measurable_chamferVel (hr.smooth.continuous_deriv (by simp)) D lam
          (ε - δ₂ * v)).comp (by fun_prop))
    · intro x _
      rw [norm_smul]
      calc ‖Work.Drive.sweepBump x‖ * ‖Work.Drive.chamferVel r D lam (ε - δ₂ * v)
              (t + period / 4 - δ₁ * x)‖
          ≤ 1 * Λ := mul_le_mul
              (by rw [Real.norm_eq_abs]; exact Work.Drive.abs_sweepBump_le_one_local x)
              (hvel _ _) (norm_nonneg _) (by norm_num)
        _ = Λ := one_mul _
  -- integrability of the outer (sweep-parameter) integrand
  have hint : IntervalIntegrable (fun v : ℝ => Work.Drive.sweepBump v •
      (∫ s in (-1 : ℝ)..1, Work.Drive.sweepBump s •
        Work.Drive.chamferVel r D lam (ε - δ₂ * v) (t + period / 4 - δ₁ * s)))
      volume (-1 : ℝ) 1 := by
    refine intervalIntegrable_of_measurable_of_bound_Icc (C := 2 * Λ) ?_ ?_
    · exact Work.Drive.sweepBump_continuous.measurable.smul
        (measurable_integral_chamferVel hr D lam δ₁ δ₂ ε (t + period / 4))
    · intro v _
      rw [norm_smul]
      have hb : ‖(∫ s in (-1 : ℝ)..1, Work.Drive.sweepBump s •
          Work.Drive.chamferVel r D lam (ε - δ₂ * v) (t + period / 4 - δ₁ * s))‖
          ≤ Λ * 2 := by
        calc ‖∫ s in (-1 : ℝ)..1, Work.Drive.sweepBump s •
              Work.Drive.chamferVel r D lam (ε - δ₂ * v) (t + period / 4 - δ₁ * s)‖
            ≤ Λ * |1 - (-1)| := by
              refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => ?_)
              rw [norm_smul]
              calc ‖Work.Drive.sweepBump x‖ * ‖Work.Drive.chamferVel r D lam (ε - δ₂ * v)
                    (t + period / 4 - δ₁ * x)‖
                  ≤ 1 * Λ := mul_le_mul
                      (by rw [Real.norm_eq_abs]; exact Work.Drive.abs_sweepBump_le_one_local x)
                      (hvel _ _) (norm_nonneg _) (by norm_num)
                _ = Λ := one_mul _
          _ ≤ Λ * 2 := by
              rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 - (-1))]
              linarith [hΛ0]
      calc ‖Work.Drive.sweepBump v‖ * ‖(∫ s in (-1 : ℝ)..1, Work.Drive.sweepBump s •
              Work.Drive.chamferVel r D lam (ε - δ₂ * v) (t + period / 4 - δ₁ * s))‖
          ≤ 1 * (Λ * 2) := mul_le_mul
              (by rw [Real.norm_eq_abs]; exact Work.Drive.abs_sweepBump_le_one_local v)
              hb (norm_nonneg _) (by norm_num)
        _ = 2 * Λ := by ring
  -- the vector derivative of the doubly blurred slice, shifted by `period / 4`
  have hbase : HasDerivAt (fun s : ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ ε s)
      (∫ v in (-1 : ℝ)..1, Work.Drive.sweepBump v •
        (∫ s in (-1 : ℝ)..1, Work.Drive.sweepBump s •
          Work.Drive.chamferVel r D lam (ε - δ₂ * v) (t + period / 4 - δ₁ * s)))
      (t + period / 4) :=
    Work.Drive.sweepFam_double_blur_deriv (σ := ε) (t := t + period / 4)
      hr D hlam0 hlam1 hδ₁ hδ₂ hσlo hσhi
  have hshift : HasDerivAt
      (fun t' : ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ ε (t' + period / 4))
      (∫ v in (-1 : ℝ)..1, Work.Drive.sweepBump v •
        (∫ s in (-1 : ℝ)..1, Work.Drive.sweepBump s •
          Work.Drive.chamferVel r D lam (ε - δ₂ * v) (t + period / 4 - δ₁ * s))) t :=
    hbase.comp_add_const t
  have hfun : (fun t' : ℝ => Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε t')
      = (fun t' : ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ ε (t' + period / 4)) := by
    funext t'
    simp only [Work.Drive.shiftedNeedle, Work.Drive.needleFam]
  rw [← hfun] at hshift
  -- the scalar function `⟪shiftedNeedle ·, u⟫`
  have hinner : HasDerivAt
      (fun t' : ℝ => inner ℝ (Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε t') u)
      (inner ℝ (∫ v in (-1 : ℝ)..1, Work.Drive.sweepBump v •
        (∫ s in (-1 : ℝ)..1, Work.Drive.sweepBump s •
          Work.Drive.chamferVel r D lam (ε - δ₂ * v) (t + period / 4 - δ₁ * s))) u) t := by
    have h := HasDerivAt.inner ℝ hshift (hasDerivAt_const t u)
    simpa using h
  -- subtracting the constant `c'`
  have hsub : HasDerivAt
      (fun t' : ℝ => inner ℝ (Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε t' - c') u)
      (inner ℝ (∫ v in (-1 : ℝ)..1, Work.Drive.sweepBump v •
        (∫ s in (-1 : ℝ)..1, Work.Drive.sweepBump s •
          Work.Drive.chamferVel r D lam (ε - δ₂ * v) (t + period / 4 - δ₁ * s))) u) t := by
    have h := hinner.sub_const (inner ℝ c' u)
    have heq : (fun t' : ℝ =>
          inner ℝ (Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε t' - c') u)
        = (fun t' : ℝ =>
          inner ℝ (Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε t') u - inner ℝ c' u) := by
      funext t'
      rw [inner_sub_left]
    rw [heq]
    exact h
  rw [hsub.deriv]
  -- commutation of the inner product with the outer integral
  rw [Work.Drive.inner_intervalIntegral_comm_left hint u]
  refine intervalIntegral.integral_congr (fun v _ => ?_)
  rw [real_inner_smul_left]
  rw [Work.Drive.inner_intervalIntegral_comm_left (hinn v) u]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  rw [real_inner_smul_left]
  ring

end Work.Drive.Generic
