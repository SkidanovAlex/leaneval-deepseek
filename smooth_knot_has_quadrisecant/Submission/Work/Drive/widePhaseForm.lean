import Mathlib
import Submission.Work.Drive.sweepFamWideTolDefs
import Submission.Work.Drive.chamferVelBranch
import Submission.Work.Drive.sweepFam_double_blur_deriv
import Submission.Work.Drive.exists_trigFun_close_zeroMean
import Submission.Work.Drive.trigFun_hasDerivAt_prim
import Submission.Work.Drive.trigFun_periodic
import Submission.Work.Drive.trigFun_contDiff
import Submission.Work.Drive.sweepFamWideEndFineDefs
import Submission.Work.Drive.wideSigma_ftc
import Submission.Work.Drive.sweepFam_contDiff_periodic
import Submission.Work.Drive.sweepLoopProfile_uniformCont_sweep
import Submission.Work.Drive.sweepLoopProfileDefs

/-!
# The wide-end reparametrisation of the doubly smoothed chord sweep

`Work.Drive.widePhaseForm`: the doubly smoothed slice `sweepFam r D lam δ₁ δ₂ σ₀` of the chord
sweep at a sweep parameter `σ₀ ∈ (0,1)`, in the range where the raw loop is `C⁰`-close to the knot
after the matching phase `wideSig` (`hval`, `hvel` of the statement), coincides with a `C^∞`
reparametrisation `ψ` of the knot to within `ε`, and its velocity coincides with `ψ'` times the
unit-matched knot velocity.

The reparametrisation is the doubly blurred matching phase, re-anchored at the knot parameter of
the loop's start point (`Work.Drive.widePhaseApprox`).

## Contents

* `Work.Drive.wfE` — a nonzero vector of `Space`;
* `Work.Drive.widePhaseApprox`, `Work.Drive.wideRhoFun`;
* measurability/boundedness of the matching phase and its rate;
* `Work.Drive.wf_conv_eq_real` — the real-valued form of `sweepKernel_convolution_eq`;
* `Work.Drive.wf_conv_rate` — the matching rate blur is a convolution, hence `C^∞`;
* `Work.Drive.wf_deriv_phase` — the derivative of the phase is the rate blur;
* the value/period/positivity facts for `widePhaseApprox`;
* the estimates and the theorem.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

noncomputable section

/-! ## The vector `wfE` -/

/-- The first standard basis vector of `Space`. -/
def wfE : Space := !₂[(1 : ℝ), 0, 0]

lemma wfE_norm_sq : ‖wfE‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [wfE, Fin.sum_univ_three]

lemma inner_wfE : inner ℝ (wfE : Space) (wfE : Space) = 1 := by
  rw [real_inner_self_eq_norm_sq, wfE_norm_sq]

/-! ## The phase approximation and the matching rate -/

/-- The phase approximation used at the wide end: the doubly blurred matching phase, re-anchored
at the knot parameter of the loop's start point. -/
def widePhaseApprox {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ σ : ℝ) : ℝ → ℝ :=
  fun τ => widePhaseBlur D lam δ₁ δ₂ σ τ - widePhaseBlur D lam δ₁ δ₂ σ 0
    + (taR D σ + lam * sweepW' D σ)

/-- The matching rate as a function of the two parameters `(σ, τ)`. -/
def wideRhoFun {d : BandArcData} (D : SweepData d) (lam : ℝ) : ℝ × ℝ → ℝ :=
  fun p => wideRho (sweepW' D p.1) (period - sweepW' D p.1) lam (sweepParam p.2)

@[simp] lemma widePhaseApprox_apply {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ σ τ : ℝ) :
    widePhaseApprox D lam δ₁ δ₂ σ τ
      = widePhaseBlur D lam δ₁ δ₂ σ τ - widePhaseBlur D lam δ₁ δ₂ σ 0
        + (taR D σ + lam * sweepW' D σ) := rfl

@[simp] lemma widePhaseApprox_zero {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ σ : ℝ) :
    widePhaseApprox D lam δ₁ δ₂ σ 0 = taR D σ + lam * sweepW' D σ := by
  simp [widePhaseApprox]

/-! ## Measurability of the matching phase and its rate -/

/-- The piecewise affine profile `wideSfrac` is measurable in its last argument. -/
lemma measurable_wideSfrac (ta w d lam : ℝ) :
    Measurable (fun u : ℝ => wideSfrac ta w d lam u) := by
  have h : (fun u : ℝ => wideSfrac ta w d lam u)
      = fun u : ℝ => if u ≤ 1 / 2 then (ta + (lam + (1 - 2 * lam) * (2 * u)) * w)
          else if u ≤ 1 / 2 + lam / 2 then (ta + (1 - lam) * w + (2 * u - 1) * period)
          else if u ≤ 1 - lam / 2 then
            (ta + w + lam * d + ((1 - 2 * lam) * d) * ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam)))
          else (ta + w + (1 - lam) * d + (2 * u - 2 + lam) * period) := by
    funext u
    rw [wideSfrac]
  rw [h]
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) (by fun_prop) ?_
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) (by fun_prop) ?_
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) (by fun_prop) (by fun_prop)

/-- Joint measurability of `wideSfrac` in all five arguments. -/
lemma measurable_wideSfrac_joint :
    Measurable (fun p : ℝ × ℝ × ℝ × ℝ × ℝ =>
      wideSfrac p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have h : (fun p : ℝ × ℝ × ℝ × ℝ × ℝ =>
        wideSfrac p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      = fun p : ℝ × ℝ × ℝ × ℝ × ℝ =>
          if p.2.2.2.2 ≤ 1 / 2 then
            (p.1 + (p.2.2.2.1 + (1 - 2 * p.2.2.2.1) * (2 * p.2.2.2.2)) * p.2.1)
          else if p.2.2.2.2 ≤ 1 / 2 + p.2.2.2.1 / 2 then
            (p.1 + (1 - p.2.2.2.1) * p.2.1 + (2 * p.2.2.2.2 - 1) * period)
          else if p.2.2.2.2 ≤ 1 - p.2.2.2.1 / 2 then
            (p.1 + p.2.1 + p.2.2.2.1 * p.2.2.1 +
              ((1 - 2 * p.2.2.2.1) * p.2.2.1) *
                ((p.2.2.2.2 - (1 / 2 + p.2.2.2.1 / 2)) / (1 / 2 - p.2.2.2.1)))
          else (p.1 + p.2.1 + (1 - p.2.2.2.1) * p.2.2.1 +
              (2 * p.2.2.2.2 - 2 + p.2.2.2.1) * period) := by
    funext p
    rw [wideSfrac]
  rw [h]
  refine Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop) ?_
  refine Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop) ?_
  refine Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop) (by fun_prop)

/-- Measurability of the two-variable matching phase. -/
lemma measurable_widePhaseFun {d : BandArcData} (D : SweepData d) (lam : ℝ) :
    Measurable (widePhaseFun D lam) := by
  have hta : Measurable (fun p : ℝ × ℝ => taR D p.1) :=
    (sweepLoopChamfer_taR_continuous D).measurable.comp measurable_fst
  have hw : Measurable (fun p : ℝ × ℝ => sweepW' D p.1) :=
    (sweepLoopChamfer_sweepW'_continuous D).measurable.comp measurable_fst
  have hu : Measurable (fun p : ℝ × ℝ => sweepParam p.2) :=
    sweepLoopChamfer_sweepParam_measurable.comp measurable_snd
  have hPd : Measurable (fun p : ℝ × ℝ => period - sweepW' D p.1) := measurable_const.sub hw
  have hlam : Measurable (fun _ : ℝ × ℝ => lam) := measurable_const
  have hjoint : Measurable (fun p : ℝ × ℝ =>
      wideSfrac (taR D p.1) (sweepW' D p.1) (period - sweepW' D p.1) lam (sweepParam p.2)) :=
    measurable_wideSfrac_joint.comp (f := fun p : ℝ × ℝ =>
        (taR D p.1, sweepW' D p.1, period - sweepW' D p.1, lam, sweepParam p.2))
      (hta.prod (hw.prod (hPd.prod (hlam.prod hu))))
  have key : (fun p : ℝ × ℝ => widePhaseFun D lam p)
      = fun p : ℝ × ℝ => p.2 + wideSfrac (taR D p.1) (sweepW' D p.1)
          (period - sweepW' D p.1) lam (sweepParam p.2) - sweepParam p.2 * period := by
    funext p
    simp only [widePhaseFun, wideSigma]
    ring
  change Measurable (fun p : ℝ × ℝ => widePhaseFun D lam p)
  rw [key]
  have hfin : Measurable (fun p : ℝ × ℝ => p.2 + wideSfrac (taR D p.1) (sweepW' D p.1)
      (period - sweepW' D p.1) lam (sweepParam p.2) - sweepParam p.2 * period) :=
    (measurable_snd.add hjoint).sub (hu.mul_const period)
  exact hfin

/-- Measurability of the matching rate as a function of `(σ, τ)`. -/
lemma measurable_wideRhoFun {d : BandArcData} (D : SweepData d) (lam : ℝ) :
    Measurable (wideRhoFun D lam) := by
  have hw : Measurable (fun p : ℝ × ℝ => sweepW' D p.1) :=
    (sweepLoopChamfer_sweepW'_continuous D).measurable.comp measurable_fst
  have hu : Measurable (fun p : ℝ × ℝ => sweepParam p.2) :=
    sweepLoopChamfer_sweepParam_measurable.comp measurable_snd
  have h : wideRhoFun D lam = fun p : ℝ × ℝ => if sweepParam p.2 ≤ 1 / 2 then
            ((1 - 2 * lam) * (2 * sweepW' D p.1 / period))
          else if sweepParam p.2 ≤ 1 / 2 + lam / 2 then 2
          else if sweepParam p.2 ≤ 1 - lam / 2 then
            ((1 - 2 * lam) * (period - sweepW' D p.1) /
              (period * (1 / 2 - lam)))
          else 2 := by
    funext p
    rw [wideRhoFun, wideRho]
  rw [h]
  refine Measurable.ite (measurableSet_le hu measurable_const) (by fun_prop) ?_
  refine Measurable.ite (measurableSet_le hu measurable_const) measurable_const ?_
  refine Measurable.ite (measurableSet_le hu measurable_const) (by fun_prop) measurable_const

/-! ## Bounds -/

/-- A uniform bound for the two clamped lifts. -/
lemma wf_lift_bound {d : BandArcData} (D : SweepData d) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ sig : ℝ, |taR D sig| ≤ A ∧ |tbR D sig| ≤ A := by
  obtain ⟨A₀, hA₀⟩ :=
    (isCompact_univ (X := ↥unitInterval)).exists_bound_of_continuousOn D.cont_ta.continuousOn
  obtain ⟨A₁, hA₁⟩ :=
    (isCompact_univ (X := ↥unitInterval)).exists_bound_of_continuousOn D.cont_tb.continuousOn
  refine ⟨max 1 (max A₀ A₁), le_trans zero_le_one (le_max_left _ _), fun sig => ⟨?_, ?_⟩⟩
  · have h : |taR D sig| ≤ A₀ := by
      have h' := hA₀ (clampI sig) (Set.mem_univ _)
      simpa [taR, Real.norm_eq_abs] using h'
    exact h.trans (le_trans (le_max_left A₀ A₁) (le_max_right 1 (max A₀ A₁)))
  · have h : |tbR D sig| ≤ A₁ := by
      have h' := hA₁ (clampI sig) (Set.mem_univ _)
      simpa [tbR, Real.norm_eq_abs] using h'
    exact h.trans (le_trans (le_max_right A₀ A₁) (le_max_right 1 (max A₀ A₁)))

/-- An explicit bound for `|wideSfrac|` on the profile interval `[0,1]`. -/
lemma wf_wideSfrac_bound {ta w d lam u : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1 / 4)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    |wideSfrac ta w d lam u| ≤ |ta| + 2 * |w| + 2 * |d| + period := by
  have hP : 0 < period := period_pos
  have htan : 0 ≤ |ta| := abs_nonneg ta
  have hwn : 0 ≤ |w| := abs_nonneg w
  have hdn : 0 ≤ |d| := abs_nonneg d
  have hu0 : 0 ≤ u := hu.1
  have hu1 : u ≤ 1 := hu.2
  have hdl : 0 ≤ 1 - 2 * lam := by linarith
  by_cases hA : u ≤ 1 / 2
  · rw [wideSfrac_arc hA]
    have hc : |lam + (1 - 2 * lam) * (2 * u)| ≤ 1 := by
      rw [abs_le]
      constructor
      · nlinarith [h0, hdl, hu0]
      · nlinarith [h1, hdl, hA]
    have hstep : |ta + (lam + (1 - 2 * lam) * (2 * u)) * w| ≤ |ta| + |w| := by
      have h := abs_add_le ta ((lam + (1 - 2 * lam) * (2 * u)) * w)
      rw [abs_mul] at h
      have h2 := mul_le_mul_of_nonneg_right hc hwn
      linarith
    linarith
  · by_cases hB : u ≤ 1 / 2 + lam / 2
    · rw [wideSfrac_chamfer₁ hA hB]
      have hc : |2 * u - 1| ≤ lam := by
        rw [abs_le]
        constructor
        · nlinarith [hA]
        · nlinarith [hB]
      have h1m : |1 - lam| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have hstep : |ta + (1 - lam) * w + (2 * u - 1) * period| ≤ |ta| + |w| + period := by
        have h12 : |(1 - lam) * w| = |1 - lam| * |w| := abs_mul _ _
        have h13 : |1 - lam| * |w| ≤ |w| := by
          simpa using mul_le_mul_of_nonneg_right h1m hwn
        have h14 : |(2 * u - 1) * period| ≤ lam * period := by
          rw [abs_mul, abs_of_pos hP]
          exact mul_le_mul_of_nonneg_right hc hP.le
        have h15 : lam * period ≤ period := by
          simpa using mul_le_mul_of_nonneg_right (by linarith : lam ≤ 1) hP.le
        have h16 := abs_add_le (ta + (1 - lam) * w) ((2 * u - 1) * period)
        have h17 := abs_add_le ta ((1 - lam) * w)
        linarith
      linarith
    · by_cases hC : u ≤ 1 - lam / 2
      · rw [wideSfrac_chord hA hB hC]
        have hden : (0:ℝ) < 1 / 2 - lam := by linarith
        have hfrac : |(u - (1 / 2 + lam / 2)) / (1 / 2 - lam)| ≤ 1 := by
          rw [abs_div, abs_of_pos hden, div_le_one hden, abs_le]
          constructor
          · nlinarith [hB]
          · nlinarith [hC]
        have hcoef : |1 - 2 * lam| ≤ 1 := by rw [abs_le]; constructor <;> linarith
        have hstep : |ta + w + lam * d
            + ((1 - 2 * lam) * d) * ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam))|
            ≤ |ta| + |w| + 2 * |d| := by
          have h20 : |((1 - 2 * lam) * d) * ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam))|
              = |1 - 2 * lam| * |d| * |(u - (1 / 2 + lam / 2)) / (1 / 2 - lam)| := by
            rw [abs_mul, abs_mul]
          have h21 : |1 - 2 * lam| * |d| * |(u - (1 / 2 + lam / 2)) / (1 / 2 - lam)| ≤ |d| := by
            have h22 : |1 - 2 * lam| * |d| ≤ 1 * |d| := mul_le_mul_of_nonneg_right hcoef hdn
            have h22'' : |1 - 2 * lam| * |d| * |(u - (1 / 2 + lam / 2)) / (1 / 2 - lam)|
                ≤ (1 * |d|) * 1 := mul_le_mul h22 hfrac (abs_nonneg _) (by linarith)
            linarith
          have h23 : |lam * d| ≤ |d| := by
            have h23a : |lam| ≤ 1 := by rw [abs_of_pos h0]; linarith
            rw [abs_mul]
            simpa using mul_le_mul_of_nonneg_right h23a hdn
          have h24 : |(ta + w) + lam * d| ≤ |ta + w| + |lam * d| := abs_add_le _ _
          have h25 : |ta + w| ≤ |ta| + |w| := abs_add_le _ _
          have h26 : |(ta + w + lam * d)
                + ((1 - 2 * lam) * d) * ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam))|
              ≤ |ta + w + lam * d|
                + |((1 - 2 * lam) * d) * ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam))| :=
            abs_add_le _ _
          linarith
        linarith
      · rw [wideSfrac_chamfer₂ hA hB hC]
        have hc : |2 * u - 2 + lam| ≤ lam := by
          rw [abs_le]
          constructor
          · nlinarith [hC]
          · nlinarith [hu1]
        have h1m : |1 - lam| ≤ 1 := by rw [abs_le]; constructor <;> linarith
        have hstep : |ta + w + (1 - lam) * d + (2 * u - 2 + lam) * period|
            ≤ |ta| + |w| + |d| + period := by
          have h13 : |(1 - lam) * d| ≤ |d| := by
            rw [abs_mul]
            simpa using mul_le_mul_of_nonneg_right h1m hdn
          have h14 : |(2 * u - 2 + lam) * period| ≤ lam * period := by
            rw [abs_mul, abs_of_pos hP]
            exact mul_le_mul_of_nonneg_right hc hP.le
          have h15 : lam * period ≤ period := by
            simpa using mul_le_mul_of_nonneg_right (by linarith : lam ≤ 1) hP.le
          have h24 : |(ta + w) + (1 - lam) * d| ≤ |ta + w| + |(1 - lam) * d| := abs_add_le _ _
          have h25 : |ta + w| ≤ |ta| + |w| := abs_add_le _ _
          have h26 : |(ta + w + (1 - lam) * d) + (2 * u - 2 + lam) * period|
              ≤ |ta + w + (1 - lam) * d| + |(2 * u - 2 + lam) * period| := abs_add_le _ _
          linarith
        linarith

/-- A bound for the matching phase in terms of a bound for the profile. -/
lemma wf_wideSigma_bound {ta w d lam τ C : ℝ}
    (hC : ∀ u ∈ Set.Icc (0 : ℝ) 1, |wideSfrac ta w d lam u| ≤ C) :
    |wideSigma ta w d lam τ| ≤ |τ| + C + period := by
  have hu := sweepParam_mem τ
  have h1 : |wideSfrac ta w d lam (sweepParam τ)| ≤ C := hC _ ⟨hu.1, hu.2.le⟩
  have h2 : |sweepParam τ| ≤ 1 := by
    rw [abs_of_nonneg hu.1]; exact hu.2.le
  have h3 : |sweepParam τ * period| ≤ period := by
    rw [abs_mul, abs_of_pos period_pos]
    simpa using mul_le_mul_of_nonneg_right h2 period_pos.le
  have h4 : |wideSfrac ta w d lam (sweepParam τ) - sweepParam τ * period|
      ≤ |wideSfrac ta w d lam (sweepParam τ)| + |sweepParam τ * period| := by
    simpa using abs_sub_le (wideSfrac ta w d lam (sweepParam τ)) 0 (sweepParam τ * period)
  have h5 := abs_add_le τ (wideSfrac ta w d lam (sweepParam τ) - sweepParam τ * period)
  simp only [wideSigma]
  linarith

/-- A bound for the matching phase of the chord sweep. -/
lemma wf_wideSig_bound {d : BandArcData} (D : SweepData d) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (sig τ : ℝ), |wideSig D lam sig τ| ≤ |τ| + C + period := by
  obtain ⟨A, hA0, hA⟩ := wf_lift_bound D
  have hP : 0 < period := period_pos
  refine ⟨A + 2 * (2 * A) + 2 * (period + 2 * A) + period, by positivity, fun sig τ => ?_⟩
  have hsig := hA sig
  have hw : |sweepW' D sig| ≤ 2 * A := by
    have h4 : |tbR D sig - taR D sig| ≤ |tbR D sig| + |taR D sig| := by
      simpa using abs_sub_le (tbR D sig) 0 (taR D sig)
    simp only [sweepW']
    linarith
  have hd : |period - sweepW' D sig| ≤ period + 2 * A := by
    have h4 : |period - sweepW' D sig| ≤ |period| + |sweepW' D sig| := by
      simpa using abs_sub_le period 0 (sweepW' D sig)
    rw [abs_of_pos hP] at h4
    linarith
  have hC : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |wideSfrac (taR D sig) (sweepW' D sig) (period - sweepW' D sig) lam u| ≤
        A + 2 * (2 * A) + 2 * (period + 2 * A) + period := by
    intro u hu
    have := wf_wideSfrac_bound (ta := taR D sig) (w := sweepW' D sig)
      (d := period - sweepW' D sig) (u := u) h0 h1 hu
    linarith [hsig.1, hw, hd]
  have := wf_wideSigma_bound (ta := taR D sig) (w := sweepW' D sig)
    (d := period - sweepW' D sig) (lam := lam) (τ := τ) hC
  simpa only [wideSig] using this

/-- A bound for the matching rate in terms of the profile data. -/
lemma wf_wideRho_bound {w d lam u : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1 / 4) :
    |wideRho w d lam u| ≤ 2 * |w| / period + 2 + 4 * |d| / period := by
  have hP : 0 < period := period_pos
  have hwn : 0 ≤ |w| := abs_nonneg w
  have hdn : 0 ≤ |d| := abs_nonneg d
  have hcoef : |1 - 2 * lam| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hden : (0:ℝ) < 1 / 2 - lam := by linarith
  have hw2 : (0:ℝ) ≤ 2 * |w| / period := div_nonneg (by linarith) hP.le
  have hd4 : (0:ℝ) ≤ 4 * |d| / period := div_nonneg (by linarith) hP.le
  by_cases hA : u ≤ 1 / 2
  · rw [wideRho_arc hA]
    have h2 : |2 * w / period| = 2 * |w| / period := by
      simp only [abs_div, abs_mul, abs_of_pos hP, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    rw [abs_mul, h2]
    have := mul_le_mul_of_nonneg_right hcoef hw2
    linarith
  · by_cases hB : u ≤ 1 / 2 + lam / 2
    · rw [wideRho_chamfer₁ hA hB, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      linarith
    · by_cases hC : u ≤ 1 - lam / 2
      · rw [wideRho_chord hA hB hC]
        have hden2 : (0:ℝ) < period * (1 / 2 - lam) := mul_pos hP hden
        have h6 : |(1 - 2 * lam) * d / (period * (1 / 2 - lam))|
            = |1 - 2 * lam| * |d| / (period * (1 / 2 - lam)) := by
          simp only [abs_div, abs_mul, abs_of_pos hden2]
        rw [h6]
        have h4 : |1 - 2 * lam| * |d| ≤ |d| := by
          have h := mul_le_mul_of_nonneg_right hcoef hdn
          linarith
        have h4' : |1 - 2 * lam| * |d| / (period * (1 / 2 - lam))
            ≤ |d| / (period * (1 / 4)) := by
          have hCB : period * (1 / 4) ≤ period * (1 / 2 - lam) := by
            have : (1:ℝ) / 4 ≤ 1 / 2 - lam := by linarith
            exact mul_le_mul_of_nonneg_left this hP.le
          have hC4 : (0:ℝ) < period * (1 / 4) := by positivity
          have h1 : 1 / (period * (1 / 2 - lam)) ≤ 1 / (period * (1 / 4)) :=
            one_div_le_one_div_of_le hC4 hCB
          calc |1 - 2 * lam| * |d| / (period * (1 / 2 - lam))
              = |1 - 2 * lam| * |d| * (1 / (period * (1 / 2 - lam))) := by ring
            _ ≤ |d| * (1 / (period * (1 / 4))) :=
                mul_le_mul h4 h1 (le_of_lt (one_div_pos.mpr hden2)) hdn
            _ = |d| / (period * (1 / 4)) := by ring
        have h5 : |d| / (period * (1 / 4)) = 4 * |d| / period := by ring
        linarith
      · rw [wideRho_chamfer₂ hA hB hC, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        linarith

/-- A bound for the matching rate of the chord sweep. -/
lemma wf_wideRhoFun_bound {d : BandArcData} (D : SweepData d) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (sig τ : ℝ), |wideRhoFun D lam (sig, τ)| ≤ C := by
  obtain ⟨A, hA0, hA⟩ := wf_lift_bound D
  have hP : 0 < period := period_pos
  refine ⟨2 * (2 * A) / period + 2 + 4 * (period + 2 * A) / period, by positivity,
    fun sig τ => ?_⟩
  have hsig := hA sig
  have hw : |sweepW' D sig| ≤ 2 * A := by
    have h4 : |tbR D sig - taR D sig| ≤ |tbR D sig| + |taR D sig| := by
      simpa using abs_sub_le (tbR D sig) 0 (taR D sig)
    simp only [sweepW']
    linarith
  have hd : |period - sweepW' D sig| ≤ period + 2 * A := by
    have h4 : |period - sweepW' D sig| ≤ |period| + |sweepW' D sig| := by
      simpa using abs_sub_le period 0 (sweepW' D sig)
    rw [abs_of_pos hP] at h4
    linarith
  have hthis := wf_wideRho_bound (w := sweepW' D sig) (d := period - sweepW' D sig)
    (lam := lam) (u := sweepParam τ) h0 h1
  have h1' : 2 * |sweepW' D sig| / period ≤ 2 * (2 * A) / period := by
    apply div_le_div_of_nonneg_right _ hP.le
    linarith [hw]
  have h2' : 4 * |period - sweepW' D sig| / period ≤ 4 * (period + 2 * A) / period := by
    apply div_le_div_of_nonneg_right _ hP.le
    linarith [hd]
  simp only [wideRhoFun]
  linarith


/-! ## Integrability helpers and bounds for the phase blur -/

/-- Interval integrability of a function that is a.e. strongly measurable and bounded on
`[-1,1]`. -/
lemma wf_intervalIntegrable_of_bound_on {g : ℝ → ℝ} {C : ℝ} (hg : AEStronglyMeasurable g volume)
    (hb : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ‖g u‖ ≤ C) : IntervalIntegrable g volume (-1) 1 := by
  constructor
  · refine IntegrableOn.of_bound ?_ hg.restrict C ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with x hx
      exact hb x ⟨le_of_lt hx.1, hx.2⟩
  · refine IntegrableOn.of_bound ?_ hg.restrict C ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with x hx
      exact hb x ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- A bound for the two-variable matching phase. -/
lemma wf_phaseFun_bound {d : BandArcData} (D : SweepData d) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ s : ℝ), |widePhaseFun D lam (σ, s)| ≤ |s| + C + period := by
  obtain ⟨C, hC0, hCb⟩ := wf_wideSig_bound D h0 h1
  exact ⟨C, hC0, fun σ s => hCb σ s⟩

/-- Strong measurability of the singly blurred phase in the sweep parameter. -/
lemma wf_phaseBlur1_sigma_stronglyMeasurable {d : BandArcData} (D : SweepData d)
    (lam δ₁ τ : ℝ) :
    StronglyMeasurable (fun σ : ℝ => widePhaseBlur1 D lam δ₁ σ τ) := by
  have hpair : Measurable (fun p : ℝ × ℝ => ((p.1, τ - δ₁ * p.2) : ℝ × ℝ)) := by
    refine Measurable.prod ?_ ?_
    · exact measurable_fst
    · exact measurable_const.sub (measurable_const.mul measurable_snd)
  have hL : Measurable
      (fun p : ℝ × ℝ => sweepBump p.2 * widePhaseFun D lam (p.1, τ - δ₁ * p.2)) :=
    (continuous_sweepBump.measurable.comp measurable_snd).mul
      ((measurable_widePhaseFun D lam).comp hpair)
  have h2 : StronglyMeasurable (fun σ : ℝ =>
      ∫ u : ℝ, sweepBump u * widePhaseFun D lam (σ, τ - δ₁ * u)
        ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1))) :=
    MeasureTheory.StronglyMeasurable.integral_prod_right
      (f := fun (σ : ℝ) (u : ℝ) => sweepBump u * widePhaseFun D lam (σ, τ - δ₁ * u))
      hL.stronglyMeasurable
  have hfun : (fun σ : ℝ => ∫ u : ℝ, sweepBump u * widePhaseFun D lam (σ, τ - δ₁ * u)
        ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1)))
      = (fun σ : ℝ => widePhaseBlur1 D lam δ₁ σ τ) := by
    funext σ
    rw [widePhaseBlur1, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      Set.uIoc_of_le (by norm_num)]
  rw [hfun] at h2
  exact h2

/-- A pointwise bound for the integrand of the singly blurred phase. -/
lemma wf_phaseBlur1_integrand_bound {d : BandArcData} (D : SweepData d) {lam C : ℝ}
    (hC : ∀ (σ s : ℝ), |widePhaseFun D lam (σ, s)| ≤ |s| + C + period) (hC0 : 0 ≤ C)
    (δ₁ σ s u : ℝ) (hu : |u| ≤ 1) :
    |sweepBump u * widePhaseFun D lam (σ, s - δ₁ * u)| ≤ |s| + C + period + |δ₁| := by
  have hb : sweepBump u ≤ 1 := by
    rw [sweepBump]
    exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.le_one _)
  have hb0 : 0 ≤ sweepBump u := sweepBump_nonneg u
  have h := hC σ (s - δ₁ * u)
  have h2 : |s - δ₁ * u| ≤ |s| + |δ₁| := by
    have h3 := abs_sub_le s 0 (δ₁ * u)
    simp only [sub_zero, zero_sub, abs_neg, abs_mul] at h3
    have h4 : |δ₁| * |u| ≤ |δ₁| := by
      simpa using mul_le_mul_of_nonneg_left hu (abs_nonneg δ₁)
    linarith [h3, h4]
  rw [abs_mul, abs_of_nonneg hb0]
  have h0' : 0 ≤ |s| + C + period + |δ₁| := by
    have := period_pos; linarith [abs_nonneg s, abs_nonneg δ₁, hC0]
  calc sweepBump u * |widePhaseFun D lam (σ, s - δ₁ * u)|
      ≤ 1 * (|s - δ₁ * u| + C + period) :=
        mul_le_mul hb h (abs_nonneg _) zero_le_one
    _ ≤ 1 * (|s| + C + period + |δ₁|) := by
        have h5 : |s - δ₁ * u| + C + period ≤ |s| + C + period + |δ₁| := by linarith
        linarith
    _ = |s| + C + period + |δ₁| := one_mul _

/-- Measurability of the phase composed with an affine map of its second variable. -/
lemma wf_phaseFun_comp_meas {d : BandArcData} (D : SweepData d) (lam a b δ₁ : ℝ) :
    Measurable (fun u : ℝ => widePhaseFun D lam (a, b - δ₁ * u)) := by
  have h1 : Measurable (fun _ : ℝ => a) := measurable_const
  have h2 : Measurable (fun u : ℝ => b - δ₁ * u) :=
    measurable_const.sub (measurable_const.mul measurable_id)
  exact (measurable_widePhaseFun D lam).comp (h1.prod h2)

/-- A bound for the singly blurred phase. -/
lemma wf_phaseBlur1_bound {d : BandArcData} (D : SweepData d) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam ≤ 1 / 4) (δ₁ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ s : ℝ),
      |widePhaseBlur1 D lam δ₁ σ s| ≤ |s| + C + period + |δ₁| := by
  obtain ⟨C, hC0, hCb⟩ := wf_phaseFun_bound D h0 h1
  refine ⟨C, hC0, fun σ s => ?_⟩
  have hδ1 : 0 ≤ |δ₁| := abs_nonneg δ₁
  have hpt : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |widePhaseFun D lam (σ, s - δ₁ * u)| ≤ |s| + C + period + |δ₁| := by
    intro u hu
    have := hCb σ (s - δ₁ * u)
    have h2 : |s - δ₁ * u| ≤ |s| + |δ₁| := by
      have h3 := abs_sub_le s 0 (δ₁ * u)
      simp only [sub_zero, zero_sub, abs_neg, abs_mul] at h3
      have h4 : |u| ≤ 1 := by
        rw [abs_le]; exact ⟨by linarith [hu.1], hu.2⟩
      have h5 : |δ₁| * |u| ≤ |δ₁| * 1 := mul_le_mul_of_nonneg_left h4 hδ1
      simp only [mul_one] at h5
      linarith [h3, h5]
    linarith
  have hbnd : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |sweepBump u * widePhaseFun D lam (σ, s - δ₁ * u)| ≤ |s| + C + period + |δ₁| := by
    intro u hu
    have hb : sweepBump u ≤ 1 := by
      rw [sweepBump]
      exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
        (Real.smoothTransition.le_one _)
    have hb0 : 0 ≤ sweepBump u := sweepBump_nonneg u
    have h0' : 0 ≤ |s| + C + period + |δ₁| := by
      have := period_pos; linarith [abs_nonneg s, abs_nonneg δ₁, hC0]
    rw [abs_mul, abs_of_nonneg hb0]
    calc sweepBump u * |widePhaseFun D lam (σ, s - δ₁ * u)|
        ≤ 1 * (|s| + C + period + |δ₁|) :=
          mul_le_mul hb (hpt u hu) (abs_nonneg _) zero_le_one
      _ = |s| + C + period + |δ₁| := one_mul _
  have hmeas : Measurable (fun u : ℝ => sweepBump u * widePhaseFun D lam (σ, s - δ₁ * u)) :=
    continuous_sweepBump.measurable.mul (wf_phaseFun_comp_meas D lam σ s δ₁)
  have hint := wf_intervalIntegrable_of_bound_on (C := |s| + C + period + |δ₁|)
    hmeas.aestronglyMeasurable (fun u hu => by rw [Real.norm_eq_abs]; exact hbnd u hu)
  have habs : IntervalIntegrable
      (fun u : ℝ => sweepBump u * |widePhaseFun D lam (σ, s - δ₁ * u)|) volume (-1) 1 := by
    refine wf_intervalIntegrable_of_bound_on (C := |s| + C + period + |δ₁|) ?_ ?_
    · exact (continuous_sweepBump.measurable.mul
        (wf_phaseFun_comp_meas D lam σ s δ₁).abs).aestronglyMeasurable
    · intro u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sweepBump_nonneg u) (abs_nonneg _))]
      rw [show sweepBump u * |widePhaseFun D lam (σ, s - δ₁ * u)|
          = |sweepBump u * widePhaseFun D lam (σ, s - δ₁ * u)| from by
            rw [abs_mul, abs_of_nonneg (sweepBump_nonneg u)]]
      exact hbnd u hu
  have hconst : IntervalIntegrable
      (fun u : ℝ => sweepBump u * (|s| + C + period + |δ₁|)) volume (-1) 1 :=
    (continuous_sweepBump.mul_const _).intervalIntegrable _ _
  rw [widePhaseBlur1]
  rw [show |∫ u in (-1 : ℝ)..1, sweepBump u * widePhaseFun D lam (σ, s - δ₁ * u)|
      = ‖∫ u in (-1 : ℝ)..1, sweepBump u * widePhaseFun D lam (σ, s - δ₁ * u)‖ from
      Real.norm_eq_abs _]
  calc ‖∫ u in (-1 : ℝ)..1, sweepBump u * widePhaseFun D lam (σ, s - δ₁ * u)‖
      ≤ ∫ u in (-1 : ℝ)..1, ‖sweepBump u * widePhaseFun D lam (σ, s - δ₁ * u)‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1 : ℝ) ≤ 1)
    _ = ∫ u in (-1 : ℝ)..1, sweepBump u * |widePhaseFun D lam (σ, s - δ₁ * u)| := by
        refine intervalIntegral.integral_congr (fun u _ => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sweepBump_nonneg u)]
    _ ≤ ∫ u in (-1 : ℝ)..1, sweepBump u * (|s| + C + period + |δ₁|) :=
        intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1) habs hconst
          (fun u hu => mul_le_mul_of_nonneg_left (hpt u hu) (sweepBump_nonneg u))
    _ = |s| + C + period + |δ₁| := by
        rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]

/-! ## The period shift of the phase -/

lemma widePhaseBlur1_add_period {d : BandArcData} (D : SweepData d) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam ≤ 1 / 4) (δ₁ σ τ : ℝ) :
    widePhaseBlur1 D lam δ₁ σ (τ + period) = widePhaseBlur1 D lam δ₁ σ τ + period := by
  obtain ⟨C, hC0, hCb⟩ := wf_phaseFun_bound D h0 h1
  have hpt : ∀ u : ℝ, widePhaseFun D lam (σ, τ + period - δ₁ * u)
      = widePhaseFun D lam (σ, τ - δ₁ * u) + period := by
    intro u
    simp only [widePhaseFun_apply]
    rw [show τ + period - δ₁ * u = (τ - δ₁ * u) + period by ring, wideSigma_add_period]
  have hmeas : Measurable (fun u : ℝ => sweepBump u * widePhaseFun D lam (σ, τ - δ₁ * u)) :=
    continuous_sweepBump.measurable.mul (wf_phaseFun_comp_meas D lam σ τ δ₁)
  have hbnd : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |sweepBump u * widePhaseFun D lam (σ, τ - δ₁ * u)| ≤ |τ| + C + period + |δ₁| :=
    fun u hu => wf_phaseBlur1_integrand_bound D hCb hC0 δ₁ σ τ u
      (by rw [abs_le]; exact ⟨by linarith [hu.1], hu.2⟩)
  have hI1 : IntervalIntegrable (fun u : ℝ => sweepBump u * widePhaseFun D lam (σ, τ - δ₁ * u))
      volume (-1) 1 :=
    wf_intervalIntegrable_of_bound_on (C := |τ| + C + period + |δ₁|) hmeas.aestronglyMeasurable
      (fun u hu => by rw [Real.norm_eq_abs]; exact hbnd u hu)
  have hI2 : IntervalIntegrable (fun u : ℝ => sweepBump u * period) volume (-1) 1 :=
    (continuous_sweepBump.mul_const period).intervalIntegrable _ _
  rw [widePhaseBlur1]
  have h1' : (∫ u in (-1 : ℝ)..1, sweepBump u * widePhaseFun D lam (σ, τ + period - δ₁ * u))
      = ∫ u in (-1 : ℝ)..1,
          (sweepBump u * widePhaseFun D lam (σ, τ - δ₁ * u) + sweepBump u * period) := by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    rw [hpt u]; ring
  rw [h1', intervalIntegral.integral_add hI1 hI2]
  rw [widePhaseBlur1, intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]

lemma widePhaseBlur_add_period {d : BandArcData} (D : SweepData d) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam ≤ 1 / 4) (δ₁ δ₂ σ τ : ℝ) :
    widePhaseBlur D lam δ₁ δ₂ σ (τ + period) = widePhaseBlur D lam δ₁ δ₂ σ τ + period := by
  obtain ⟨C, hC0, hCb⟩ := wf_phaseBlur1_bound D h0 h1 δ₁
  have hpt : ∀ v : ℝ, widePhaseBlur1 D lam δ₁ (σ - δ₂ * v) (τ + period)
      = widePhaseBlur1 D lam δ₁ (σ - δ₂ * v) τ + period :=
    fun v => widePhaseBlur1_add_period D h0 h1 δ₁ (σ - δ₂ * v) τ
  have hmap : Measurable (fun v : ℝ => σ - δ₂ * v) :=
    measurable_const.sub (measurable_const.mul measurable_id)
  have hmeas : AEStronglyMeasurable
      (fun v : ℝ => sweepBump v * widePhaseBlur1 D lam δ₁ (σ - δ₂ * v) τ) volume :=
    continuous_sweepBump.measurable.aestronglyMeasurable.mul
      ((wf_phaseBlur1_sigma_stronglyMeasurable D lam δ₁ τ).comp_measurable hmap).aestronglyMeasurable
  have hbnd : ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      |sweepBump v * widePhaseBlur1 D lam δ₁ (σ - δ₂ * v) τ| ≤ |τ| + C + period + |δ₁| := by
    intro v hv
    have hb : sweepBump v ≤ 1 := by
      rw [sweepBump]
      exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
        (Real.smoothTransition.le_one _)
    have hb0 : 0 ≤ sweepBump v := sweepBump_nonneg v
    have h := hCb (σ - δ₂ * v) τ
    have h0' : 0 ≤ |τ| + C + period + |δ₁| := by
      have := period_pos; linarith [abs_nonneg τ, abs_nonneg δ₁, hC0]
    rw [abs_mul, abs_of_nonneg hb0]
    calc sweepBump v * |widePhaseBlur1 D lam δ₁ (σ - δ₂ * v) τ|
        ≤ 1 * (|τ| + C + period + |δ₁|) :=
          mul_le_mul hb h (abs_nonneg _) zero_le_one
      _ = |τ| + C + period + |δ₁| := one_mul _
  have hI1 : IntervalIntegrable
      (fun v : ℝ => sweepBump v * widePhaseBlur1 D lam δ₁ (σ - δ₂ * v) τ) volume (-1) 1 :=
    wf_intervalIntegrable_of_bound_on (C := |τ| + C + period + |δ₁|) hmeas (fun v hv => by
      rw [Real.norm_eq_abs]; exact hbnd v hv)
  have hI2 : IntervalIntegrable (fun v : ℝ => sweepBump v * period) volume (-1) 1 :=
    (continuous_sweepBump.mul_const period).intervalIntegrable _ _
  rw [widePhaseBlur]
  have h1' : (∫ v in (-1 : ℝ)..1, sweepBump v * widePhaseBlur1 D lam δ₁ (σ - δ₂ * v) (τ + period))
      = ∫ v in (-1 : ℝ)..1,
          (sweepBump v * widePhaseBlur1 D lam δ₁ (σ - δ₂ * v) τ + sweepBump v * period) := by
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    rw [hpt v]; ring
  rw [h1', intervalIntegral.integral_add hI1 hI2]
  rw [widePhaseBlur, intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]

/-- The phase approximation is period-shifting. -/
lemma widePhaseApprox_add_period {d : BandArcData} (D : SweepData d) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam ≤ 1 / 4) (δ₁ δ₂ σ τ : ℝ) :
    widePhaseApprox D lam δ₁ δ₂ σ (τ + period)
      = widePhaseApprox D lam δ₁ δ₂ σ τ + period := by
  rw [widePhaseApprox_apply, widePhaseApprox_apply, widePhaseBlur_add_period D h0 h1 δ₁ δ₂ σ τ]
  ring

/-! ## The real-valued convolution bridge -/

/-- **The real-valued form of `sweepKernel_convolution_eq`.** -/
theorem wf_conv_eq_real (f : ℝ × ℝ → ℝ) (hf : LocallyIntegrable f volume)
    {δ₁ δ₂ : ℝ} (hδ₁ : δ₁ ≠ 0) (hδ₂ : δ₂ ≠ 0) (s t : ℝ) :
    (∫ y : ℝ × ℝ, sweepKernel δ₁ δ₂ ((s, t) - y) * f y)
      = ∫ v in (-1 : ℝ)..1, sweepBump v *
          (∫ u in (-1 : ℝ)..1, sweepBump u * f (s - δ₂ * v, t - δ₁ * u)) := by
  have hF : LocallyIntegrable (fun y : ℝ × ℝ => f y • (wfE : Space)) volume := by
    rw [locallyIntegrable_iff]
    intro k hk
    exact (hf.integrableOn_isCompact hk).smul_const (wfE : Space)
  have h := sweepKernel_convolution_eq (fun y : ℝ × ℝ => f y • (wfE : Space)) hF hδ₁ hδ₂ s t
  have hL : (∫ y : ℝ × ℝ, sweepKernel δ₁ δ₂ ((s, t) - y) • (f y • (wfE : Space)))
      = (∫ y : ℝ × ℝ, sweepKernel δ₁ δ₂ ((s, t) - y) * f y) • (wfE : Space) := by
    rw [show (fun y : ℝ × ℝ => sweepKernel δ₁ δ₂ ((s, t) - y) • (f y • (wfE : Space)))
        = (fun y : ℝ × ℝ => (sweepKernel δ₁ δ₂ ((s, t) - y) * f y) • (wfE : Space)) from by
          funext y; rw [smul_smul]]
    exact integral_smul_const _ _
  have hR : (∫ v in (-1 : ℝ)..1, sweepBump v •
        (∫ u in (-1 : ℝ)..1, sweepBump u • (f (s - δ₂ * v, t - δ₁ * u) • (wfE : Space))))
      = (∫ v in (-1 : ℝ)..1, sweepBump v *
          (∫ u in (-1 : ℝ)..1, sweepBump u * f (s - δ₂ * v, t - δ₁ * u))) • (wfE : Space) := by
    have hinner : ∀ v : ℝ,
        (∫ u in (-1 : ℝ)..1, sweepBump u • (f (s - δ₂ * v, t - δ₁ * u) • (wfE : Space)))
          = (∫ u in (-1 : ℝ)..1,
              sweepBump u * f (s - δ₂ * v, t - δ₁ * u)) • (wfE : Space) := by
      intro v
      rw [show (fun u : ℝ => sweepBump u • (f (s - δ₂ * v, t - δ₁ * u) • (wfE : Space)))
          = (fun u : ℝ => (sweepBump u * f (s - δ₂ * v, t - δ₁ * u)) • (wfE : Space)) from by
            funext u; rw [smul_smul]]
      exact intervalIntegral.integral_smul_const _ _
    simp only [hinner]
    rw [show (fun v : ℝ => sweepBump v •
          ((∫ u in (-1 : ℝ)..1, sweepBump u * f (s - δ₂ * v, t - δ₁ * u)) • (wfE : Space)))
        = (fun v : ℝ => (sweepBump v *
            (∫ u in (-1 : ℝ)..1, sweepBump u * f (s - δ₂ * v, t - δ₁ * u))) •
              (wfE : Space)) from by
          funext v; rw [smul_smul]]
    exact intervalIntegral.integral_smul_const _ _
  rw [hL, hR] at h
  have h2 := congrArg (fun z : Space => inner ℝ (wfE : Space) z) h
  rw [inner_smul_right, inner_smul_right, inner_wfE, mul_one, mul_one] at h2
  exact h2


/-! ## Smoothness of the blurred phase -/

lemma wf_phaseFun_locallyIntegrable {d : BandArcData} (D : SweepData d) {lam : ℝ}
    (h0 : 0 < lam) (h1 : lam ≤ 1 / 4) :
    LocallyIntegrable (widePhaseFun D lam) volume := by
  obtain ⟨C, hC0, hCb⟩ := wf_phaseFun_bound D h0 h1
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨R, hR⟩ := hk.exists_bound_of_continuousOn
    (f := fun p : ℝ × ℝ => p.2) continuous_snd.continuousOn
  refine IntegrableOn.of_bound hk.measure_lt_top
    (measurable_widePhaseFun D lam).aestronglyMeasurable.restrict (R + C + period) ?_
  rw [ae_restrict_iff' hk.measurableSet]
  filter_upwards with x hx
  have h := hCb x.1 x.2
  have h2 := hR x hx
  rw [Real.norm_eq_abs] at h2
  rw [Real.norm_eq_abs]
  have hp : 0 < period := period_pos
  linarith [abs_nonneg x.2]

lemma wf_phaseBlur_conv {d : BandArcData} (D : SweepData d) {lam δ₁ δ₂ : ℝ}
    (h0 : 0 < lam) (h1 : lam ≤ 1 / 4) (hδ₁ : δ₁ ≠ 0) (hδ₂ : δ₂ ≠ 0) (σ τ : ℝ) :
    widePhaseBlur D lam δ₁ δ₂ σ τ
      = ∫ y : ℝ × ℝ, sweepKernel δ₁ δ₂ ((σ, τ) - y) * widePhaseFun D lam y := by
  simp only [widePhaseBlur, widePhaseBlur1]
  exact (wf_conv_eq_real (widePhaseFun D lam) (wf_phaseFun_locallyIntegrable D h0 h1)
    hδ₁ hδ₂ σ τ).symm

lemma contDiff_widePhaseBlur {d : BandArcData} (D : SweepData d) {lam δ₁ δ₂ σ : ℝ}
    (h0 : 0 < lam) (h1 : lam ≤ 1 / 4) (hδ₁ : δ₁ ≠ 0) (hδ₂ : δ₂ ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun τ : ℝ => widePhaseBlur D lam δ₁ δ₂ σ τ) := by
  have hG := wf_phaseFun_locallyIntegrable D h0 h1
  have hcs : HasCompactSupport (sweepKernel δ₁ δ₂) := hasCompactSupport_sweepKernel hδ₁ hδ₂
  have hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sweepKernel δ₁ δ₂) :=
    contDiff_sweepKernel δ₁ δ₂
  have hconv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (MeasureTheory.convolution (widePhaseFun D lam) (sweepKernel δ₁ δ₂)
        (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume) :=
    hcs.contDiff_convolution_right (μ := MeasureTheory.volume)
      (ContinuousLinearMap.mul ℝ ℝ) hG hK
  have hfun : (fun τ : ℝ => widePhaseBlur D lam δ₁ δ₂ σ τ)
      = (fun τ : ℝ => MeasureTheory.convolution (widePhaseFun D lam) (sweepKernel δ₁ δ₂)
          (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume (σ, τ)) := by
    funext τ
    rw [MeasureTheory.convolution_def]
    have hcomm : (fun t : ℝ × ℝ => (ContinuousLinearMap.mul ℝ ℝ (widePhaseFun D lam t))
        (sweepKernel δ₁ δ₂ ((σ, τ) - t)))
        = (fun t : ℝ × ℝ => sweepKernel δ₁ δ₂ ((σ, τ) - t) * widePhaseFun D lam t) := by
      funext t
      rw [show (ContinuousLinearMap.mul ℝ ℝ (widePhaseFun D lam t))
          (sweepKernel δ₁ δ₂ ((σ, τ) - t))
          = widePhaseFun D lam t * sweepKernel δ₁ δ₂ ((σ, τ) - t) from rfl]
      ring
    rw [hcomm]
    exact wf_phaseBlur_conv D h0 h1 hδ₁ hδ₂ σ τ
  rw [hfun]
  exact hconv.comp (contDiff_prodMk_right σ)

lemma contDiff_widePhaseApprox {d : BandArcData} (D : SweepData d) {lam δ₁ δ₂ σ : ℝ}
    (h0 : 0 < lam) (h1 : lam ≤ 1 / 4) (hδ₁ : δ₁ ≠ 0) (hδ₂ : δ₂ ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (widePhaseApprox D lam δ₁ δ₂ σ) := by
  have hfun : widePhaseApprox D lam δ₁ δ₂ σ
      = fun τ : ℝ => widePhaseBlur D lam δ₁ δ₂ σ τ
          + ((-widePhaseBlur D lam δ₁ δ₂ σ 0) + (taR D σ + lam * sweepW' D σ)) := by
    funext τ
    simp only [widePhaseApprox_apply]
    ring
  rw [hfun]
  exact (contDiff_widePhaseBlur D h0 h1 hδ₁ hδ₂).add contDiff_const

/-! ## The derivative of the blurred phase -/

lemma wf_clampI_self {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    clampI x = (⟨x, h0, h1⟩ : unitInterval) := by
  refine Subtype.ext ?_
  change min 1 (max 0 x) = x
  rw [max_eq_right h0, min_eq_right h1]

lemma wf_sweepW'_eq {d : BandArcData} (D : SweepData d) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    sweepW' D s = sweepW D (⟨s, h0, h1⟩ : unitInterval) := by
  simp only [sweepW', taR, tbR, sweepW]
  rw [wf_clampI_self h0 h1]

/-- The singly blurred phase is `2`-Lipschitz in its argument. -/
lemma wf_phaseBlur1_lipschitz {d : BandArcData} (D : SweepData d) {lam δ₁ σ : ℝ}
    (h0 : 0 < lam) (h1 : lam ≤ 1 / 4) (hw0 : 0 ≤ sweepW' D σ) (hwP : sweepW' D σ ≤ period)
    (x y : ℝ) :
    ‖widePhaseBlur1 D lam δ₁ σ x - widePhaseBlur1 D lam δ₁ σ y‖ ≤ 2 * |x - y| := by
  have hd0 : 0 ≤ period - sweepW' D σ := by linarith
  have hφlip : ∀ a b : ℝ, |wideSig D lam σ b - wideSig D lam σ a| ≤ 2 * |b - a| := by
    intro a b
    simpa only [wtPar, wideSig_apply] using
      wtPar_lipschitz (taR D σ) (sweepW' D σ) (period - sweepW' D σ) lam
        (by ring) hw0 hd0 h0 (by linarith) a b
  obtain ⟨C, hC0, hCb⟩ := wf_phaseFun_bound D h0 h1
  have hI : ∀ z : ℝ, IntervalIntegrable
      (fun u : ℝ => sweepBump u * widePhaseFun D lam (σ, z - δ₁ * u)) volume (-1) 1 := by
    intro z
    refine wf_intervalIntegrable_of_bound_on (C := |z| + C + period + |δ₁|) ?_ ?_
    · exact (continuous_sweepBump.measurable.mul
        (wf_phaseFun_comp_meas D lam σ z δ₁)).aestronglyMeasurable
    · intro u hu
      have := wf_phaseBlur1_integrand_bound D hCb hC0 δ₁ σ z u
        (by rw [abs_le]; exact ⟨by linarith [hu.1], hu.2⟩)
      simpa only [Real.norm_eq_abs] using this
  have hdiff : widePhaseBlur1 D lam δ₁ σ x - widePhaseBlur1 D lam δ₁ σ y
      = ∫ u in (-1 : ℝ)..1, (sweepBump u * widePhaseFun D lam (σ, x - δ₁ * u)
          - sweepBump u * widePhaseFun D lam (σ, y - δ₁ * u)) := by
    rw [widePhaseBlur1, widePhaseBlur1, ← intervalIntegral.integral_sub (hI x) (hI y)]
  rw [hdiff]
  refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1 : ℝ) ≤ 1)).trans ?_
  have hpt : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      ‖sweepBump u * widePhaseFun D lam (σ, x - δ₁ * u)
        - sweepBump u * widePhaseFun D lam (σ, y - δ₁ * u)‖
      ≤ sweepBump u * (2 * |x - y|) := by
    intro u _
    rw [show sweepBump u * widePhaseFun D lam (σ, x - δ₁ * u)
          - sweepBump u * widePhaseFun D lam (σ, y - δ₁ * u)
        = sweepBump u * (wideSig D lam σ (x - δ₁ * u) - wideSig D lam σ (y - δ₁ * u)) from by
          simp only [wideSig_apply, widePhaseFun]; ring,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (sweepBump_nonneg u)]
    have h := hφlip (y - δ₁ * u) (x - δ₁ * u)
    have h3 : x - δ₁ * u - (y - δ₁ * u) = x - y := by ring
    rw [h3] at h
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (sweepBump_nonneg u)
  have hmeas1 : IntervalIntegrable
      (fun u : ℝ => ‖sweepBump u * widePhaseFun D lam (σ, x - δ₁ * u)
        - sweepBump u * widePhaseFun D lam (σ, y - δ₁ * u)‖) volume (-1) 1 :=
    ((hI x).sub (hI y)).norm
  have hmeas2 : IntervalIntegrable (fun u : ℝ => sweepBump u * (2 * |x - y|)) volume (-1) 1 :=
    (continuous_sweepBump.mul_const _).intervalIntegrable _ _
  refine (intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1) hmeas1 hmeas2
    hpt).trans ?_
  rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]

/-- The inner differentiation: the singly blurred phase has derivative the blurred rate. -/
lemma wf_hasDerivAt_phaseBlur1 {d : BandArcData} (D : SweepData d)
    {lam δ₁ σ τ : ℝ} (hδ₁ : δ₁ ≠ 0) (h0 : 0 < lam) (h1 : lam ≤ 1 / 4)
    (hw0 : 0 ≤ sweepW' D σ) (hwP : sweepW' D σ ≤ period) :
    HasDerivAt (fun x : ℝ => widePhaseBlur1 D lam δ₁ σ x)
      (∫ u in (-1 : ℝ)..1, sweepBump u *
        wideRho (sweepW' D σ) (period - sweepW' D σ) lam (sweepParam (τ - δ₁ * u))) τ := by
  have hd0 : 0 ≤ period - sweepW' D σ := by linarith
  have hφlip : ∀ a b : ℝ, |wideSig D lam σ b - wideSig D lam σ a| ≤ 2 * |b - a| := by
    intro a b
    simpa only [wtPar, wideSig_apply] using
      wtPar_lipschitz (taR D σ) (sweepW' D σ) (period - sweepW' D σ) lam
        (by ring) hw0 hd0 h0 (by linarith) a b
  have hne : (1 : ℝ) / 2 - lam ≠ 0 := by linarith
  have hderiv0 : ∀ᵐ u : ℝ ∂volume, HasDerivAt (fun x : ℝ => wideSig D lam σ (x - δ₁ * u))
      (wideRho (sweepW' D σ) (period - sweepW' D σ) lam (sweepParam (τ - δ₁ * u))) τ := by
    filter_upwards [wideEnd_ae_not_chamferCorner lam τ δ₁ hδ₁] with u hu
    simp only [chamferCorner, not_or] at hu
    have h2 := wsftc_hasDerivAt_wideSigma (taR D σ) (sweepW' D σ) (period - sweepW' D σ) lam
      hne hu.1 hu.2.1 hu.2.2.1 hu.2.2.2
    have hlin : HasDerivAt (fun x : ℝ => x - δ₁ * u) 1 τ := by
      simpa using (hasDerivAt_id τ).sub_const (δ₁ * u)
    exact (h2.comp τ hlin).congr_deriv (by rw [mul_one])
  have hderiv : ∀ᵐ u : ℝ ∂volume, u ∈ Set.uIoc (-1 : ℝ) 1 →
      HasDerivAt (fun x : ℝ => sweepBump u * wideSig D lam σ (x - δ₁ * u))
        (sweepBump u * wideRho (sweepW' D σ) (period - sweepW' D σ) lam
          (sweepParam (τ - δ₁ * u))) τ :=
    hderiv0.mono (fun u hu _ => (hu.const_mul (sweepBump u)))
  obtain ⟨C, hC0, hCb⟩ := wf_phaseFun_bound D h0 h1
  have hFint : IntervalIntegrable (fun u : ℝ => sweepBump u * wideSig D lam σ (τ - δ₁ * u))
      volume (-1) 1 := by
    refine wf_intervalIntegrable_of_bound_on (C := |τ| + C + period + |δ₁|) ?_ ?_
    · exact (continuous_sweepBump.measurable.mul
        (wf_phaseFun_comp_meas D lam σ τ δ₁)).aestronglyMeasurable
    · intro u hu
      have h := wf_phaseBlur1_integrand_bound D hCb hC0 δ₁ σ τ u
        (by rw [abs_le]; exact ⟨by linarith [hu.1], hu.2⟩)
      simpa only [Real.norm_eq_abs, wideSig, widePhaseFun] using h
  have hF'meas : AEStronglyMeasurable
      (fun u : ℝ => sweepBump u *
        wideRho (sweepW' D σ) (period - sweepW' D σ) lam (sweepParam (τ - δ₁ * u)))
      (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    have hpairR : Measurable (fun u : ℝ => ((σ, τ - δ₁ * u) : ℝ × ℝ)) := by
      refine Measurable.prod ?_ ?_
      · exact measurable_const
      · exact measurable_const.sub (measurable_const.mul measurable_id)
    have hmeas : Measurable (fun u : ℝ => sweepBump u * wideRhoFun D lam (σ, τ - δ₁ * u)) :=
      continuous_sweepBump.measurable.mul ((measurable_wideRhoFun D lam).comp hpairR)
    exact (by simpa only [wideRhoFun] using hmeas.aestronglyMeasurable)
  have hlipF : ∀ᵐ u : ℝ ∂volume, u ∈ Set.uIoc (-1 : ℝ) 1 →
      LipschitzOnWith (Real.nnabs (‖sweepBump u‖ * 2))
        (fun x : ℝ => sweepBump u * wideSig D lam σ (x - δ₁ * u)) Set.univ := by
    refine Filter.Eventually.of_forall (fun u _ => ?_)
    refine LipschitzOnWith.of_dist_le_mul (fun x _ y _ => ?_)
    rw [dist_eq_norm, Real.dist_eq, Real.coe_nnabs, ← mul_sub, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (sweepBump_nonneg u)]
    have h2 : |‖sweepBump u‖ * 2| = sweepBump u * 2 := by
      rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)),
        Real.norm_eq_abs, abs_of_nonneg (sweepBump_nonneg u)]
    rw [h2]
    have h := hφlip (y - δ₁ * u) (x - δ₁ * u)
    have h3 : x - δ₁ * u - (y - δ₁ * u) = x - y := by ring
    rw [h3] at h
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (sweepBump_nonneg u)
  have hboundint : IntervalIntegrable (fun u : ℝ => ‖sweepBump u‖ * 2) volume (-1) 1 :=
    ((continuous_sweepBump.norm).mul_const 2).intervalIntegrable _ _
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (a := (-1 : ℝ)) (b := 1) (μ := (volume : Measure ℝ))
    (F := fun x u => sweepBump u * wideSig D lam σ (x - δ₁ * u))
    (F' := fun u => sweepBump u *
      wideRho (sweepW' D σ) (period - sweepW' D σ) lam (sweepParam (τ - δ₁ * u)))
    (bound := fun u => ‖sweepBump u‖ * 2) (x₀ := τ) (s := Set.univ)
    Filter.univ_mem (Filter.Eventually.of_forall (fun x => (continuous_sweepBump.measurable.mul
      (wf_phaseFun_comp_meas D lam σ x δ₁)).aestronglyMeasurable)) hFint hF'meas hlipF hboundint
    hderiv
  simpa only [widePhaseBlur1, wideSig, widePhaseFun] using hmain.2

/-- The outer differentiation: the doubly blurred phase has derivative the doubly blurred rate. -/
lemma wf_hasDerivAt_phaseBlur {d : BandArcData} (D : SweepData d)
    {lam δ₁ δ₂ σ τ : ℝ} (hδ₁ : δ₁ ≠ 0) (hδ₂ : 0 < δ₂) (h0 : 0 < lam) (h1 : lam ≤ 1 / 4)
    (hσlo : 0 < σ - δ₂) (hσhi : σ + δ₂ < 1) :
    HasDerivAt (fun x : ℝ => widePhaseBlur D lam δ₁ δ₂ σ x)
      (wideRateBlur D lam δ₁ δ₂ σ τ) τ := by
  have hwin : ∀ v : ℝ, v ∈ Set.uIoc (-1 : ℝ) 1 → 0 ≤ sweepW' D (σ - δ₂ * v) ∧
      sweepW' D (σ - δ₂ * v) ≤ period := by
    intro v hv
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hv
    have hmem1 : σ - δ₂ ≤ σ - δ₂ * v := by nlinarith [hv.2]
    have hmem2 : σ - δ₂ * v ≤ σ + δ₂ := by nlinarith [hv.1]
    have h0' : 0 < σ - δ₂ * v := by linarith
    have h1'' : σ - δ₂ * v < 1 := by linarith
    have hposlt := sweepW_pos_lt D ⟨σ - δ₂ * v, h0'.le, h1''.le⟩ ⟨h0', h1''⟩
    rw [wf_sweepW'_eq D h0'.le h1''.le]
    exact ⟨hposlt.1.le, hposlt.2.le⟩
  obtain ⟨C, hC0, hCb⟩ := wf_phaseBlur1_bound D h0 h1 δ₁
  have hderiv : ∀ᵐ v : ℝ ∂volume, v ∈ Set.uIoc (-1 : ℝ) 1 → HasDerivAt
      (fun x : ℝ => sweepBump v * widePhaseBlur1 D lam δ₁ (σ - δ₂ * v) x)
      (sweepBump v * (∫ u in (-1 : ℝ)..1, sweepBump u *
        wideRho (sweepW' D (σ - δ₂ * v)) (period - sweepW' D (σ - δ₂ * v)) lam
          (sweepParam (τ - δ₁ * u)))) τ :=
    Filter.Eventually.of_forall (fun v hv =>
      (wf_hasDerivAt_phaseBlur1 D hδ₁ h0 h1 (hwin v hv).1 (hwin v hv).2).const_mul (sweepBump v))
  have hlip : ∀ᵐ v : ℝ ∂volume, v ∈ Set.uIoc (-1 : ℝ) 1 → LipschitzOnWith
      (Real.nnabs (‖sweepBump v‖ * 2))
      (fun x : ℝ => sweepBump v * widePhaseBlur1 D lam δ₁ (σ - δ₂ * v) x) Set.univ := by
    refine Filter.Eventually.of_forall (fun v hv => ?_)
    have hwinv := hwin v hv
    refine LipschitzOnWith.of_dist_le_mul (fun x _ y _ => ?_)
    rw [dist_eq_norm, Real.dist_eq, Real.coe_nnabs, ← mul_sub, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (sweepBump_nonneg v)]
    have h2 : |‖sweepBump v‖ * 2| = sweepBump v * 2 := by
      rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)),
        Real.norm_eq_abs, abs_of_nonneg (sweepBump_nonneg v)]
    rw [h2]
    have h := wf_phaseBlur1_lipschitz (δ₁ := δ₁) D h0 h1 hwinv.1 hwinv.2 x y
    rw [Real.norm_eq_abs] at h
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (sweepBump_nonneg v)
  have hI : IntervalIntegrable
      (fun v : ℝ => sweepBump v * widePhaseBlur1 D lam δ₁ (σ - δ₂ * v) τ) volume (-1) 1 := by
    have hmap : Measurable (fun v : ℝ => σ - δ₂ * v) :=
      measurable_const.sub (measurable_const.mul measurable_id)
    have hmeas : AEStronglyMeasurable
        (fun v : ℝ => sweepBump v * widePhaseBlur1 D lam δ₁ (σ - δ₂ * v) τ) volume :=
      continuous_sweepBump.measurable.aestronglyMeasurable.mul
        ((wf_phaseBlur1_sigma_stronglyMeasurable D lam δ₁ τ).comp_measurable
          hmap).aestronglyMeasurable
    refine wf_intervalIntegrable_of_bound_on (C := |τ| + C + period + |δ₁|) hmeas ?_
    intro v _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sweepBump_nonneg v)]
    have hb : sweepBump v ≤ 1 := by
      rw [sweepBump]
      exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
        (Real.smoothTransition.le_one _)
    have h0' : 0 ≤ |τ| + C + period + |δ₁| := by
      have := period_pos; linarith [abs_nonneg τ, abs_nonneg δ₁]
    calc sweepBump v * |widePhaseBlur1 D lam δ₁ (σ - δ₂ * v) τ|
        ≤ 1 * (|τ| + C + period + |δ₁|) :=
          mul_le_mul hb (hCb _ _) (abs_nonneg _) zero_le_one
      _ = |τ| + C + period + |δ₁| := one_mul _
  have hboundint : IntervalIntegrable
      (fun v : ℝ => ‖sweepBump v‖ * 2) volume (-1) 1 :=
    ((continuous_sweepBump.norm).mul_const 2).intervalIntegrable _ _
  have hρss : StronglyMeasurable (fun σ' : ℝ =>
      ∫ u in (-1 : ℝ)..1, sweepBump u * wideRhoFun D lam (σ', τ - δ₁ * u)) := by
    have hL : StronglyMeasurable (Function.uncurry
        (fun (σ' : ℝ) (u : ℝ) => sweepBump u * wideRhoFun D lam (σ', τ - δ₁ * u))) := by
      have hpairR : Measurable (fun p : ℝ × ℝ => ((p.1, τ - δ₁ * p.2) : ℝ × ℝ)) := by
        refine Measurable.prod ?_ ?_
        · exact measurable_fst
        · exact measurable_const.sub (measurable_const.mul measurable_snd)
      have h : Measurable (fun p : ℝ × ℝ => sweepBump p.2 * wideRhoFun D lam (p.1, τ - δ₁ * p.2)) :=
        (continuous_sweepBump.measurable.comp measurable_snd).mul
          ((measurable_wideRhoFun D lam).comp hpairR)
      rw [show Function.uncurry (fun (σ' : ℝ) (u : ℝ) => sweepBump u * wideRhoFun D lam (σ', τ - δ₁ * u))
          = fun p : ℝ × ℝ => sweepBump p.2 * wideRhoFun D lam (p.1, τ - δ₁ * p.2) from rfl]
      exact h.stronglyMeasurable
    have h2 := MeasureTheory.StronglyMeasurable.integral_prod_right
      (f := fun (σ' : ℝ) (u : ℝ) => sweepBump u * wideRhoFun D lam (σ', τ - δ₁ * u))
      hL (ν := volume.restrict (Set.uIoc (-1 : ℝ) 1))
    have hfun : (fun σ' : ℝ => ∫ u : ℝ, sweepBump u * wideRhoFun D lam (σ', τ - δ₁ * u)
          ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1)))
        = (fun σ' : ℝ => ∫ u in (-1 : ℝ)..1, sweepBump u * wideRhoFun D lam (σ', τ - δ₁ * u)) := by
      funext σ'
      rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
        Set.uIoc_of_le (by norm_num)]
    rw [hfun] at h2
    exact h2
  have hF'meas : AEStronglyMeasurable
      (fun v : ℝ => sweepBump v *
        (∫ u in (-1 : ℝ)..1, sweepBump u *
          wideRho (sweepW' D (σ - δ₂ * v)) (period - sweepW' D (σ - δ₂ * v)) lam
            (sweepParam (τ - δ₁ * u))))
      (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    have hmap : Measurable (fun v : ℝ => σ - δ₂ * v) :=
      measurable_const.sub (measurable_const.mul measurable_id)
    have h3 : StronglyMeasurable (fun v : ℝ => ∫ u in (-1 : ℝ)..1, sweepBump u *
        wideRhoFun D lam (σ - δ₂ * v, τ - δ₁ * u)) :=
      hρss.comp_measurable hmap
    have h4 : StronglyMeasurable (fun v : ℝ =>
        sweepBump v * (∫ u in (-1 : ℝ)..1, sweepBump u *
          wideRhoFun D lam (σ - δ₂ * v, τ - δ₁ * u))) :=
      continuous_sweepBump.stronglyMeasurable.mul h3
    have hfun : (fun v : ℝ => sweepBump v * (∫ u in (-1 : ℝ)..1, sweepBump u *
          wideRhoFun D lam (σ - δ₂ * v, τ - δ₁ * u)))
        = (fun v : ℝ => sweepBump v * (∫ u in (-1 : ℝ)..1, sweepBump u *
            wideRho (sweepW' D (σ - δ₂ * v)) (period - sweepW' D (σ - δ₂ * v)) lam
              (sweepParam (τ - δ₁ * u)))) := by
      funext v
      simp only [wideRhoFun]
    rw [hfun] at h4
    exact h4.aestronglyMeasurable.restrict
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (a := (-1 : ℝ)) (b := 1) (μ := (volume : Measure ℝ))
    (F := fun x v => sweepBump v * widePhaseBlur1 D lam δ₁ (σ - δ₂ * v) x)
    (F' := fun v => sweepBump v *
      (∫ u in (-1 : ℝ)..1, sweepBump u *
        wideRho (sweepW' D (σ - δ₂ * v)) (period - sweepW' D (σ - δ₂ * v)) lam
          (sweepParam (τ - δ₁ * u))))
    (bound := fun v => ‖sweepBump v‖ * 2) (x₀ := τ) (s := Set.univ)
    Filter.univ_mem (Filter.Eventually.of_forall (fun x => by
      have hmap : Measurable (fun v : ℝ => σ - δ₂ * v) :=
        measurable_const.sub (measurable_const.mul measurable_id)
      exact (continuous_sweepBump.measurable.aestronglyMeasurable.mul
        ((wf_phaseBlur1_sigma_stronglyMeasurable D lam δ₁ x).comp_measurable
          hmap).aestronglyMeasurable).restrict)) hI hF'meas hlip hboundint hderiv
  have hval : (∫ v in (-1 : ℝ)..1, sweepBump v *
      (∫ u in (-1 : ℝ)..1, sweepBump u *
        wideRho (sweepW' D (σ - δ₂ * v)) (period - sweepW' D (σ - δ₂ * v)) lam
          (sweepParam (τ - δ₁ * u))))
      = wideRateBlur D lam δ₁ δ₂ σ τ := by
    simp only [wideRateBlur, wideRhoFun]
  have h2 := hmain.2
  rw [hval] at h2
  simpa only [widePhaseBlur] using h2

/-- The derivative of the phase approximation is the doubly blurred rate. -/
lemma deriv_widePhaseApprox {d : BandArcData} (D : SweepData d)
    {lam δ₁ δ₂ σ : ℝ} (hδ₁ : δ₁ ≠ 0) (hδ₂ : 0 < δ₂) (h0 : 0 < lam) (h1 : lam ≤ 1 / 4)
    (hσlo : 0 < σ - δ₂) (hσhi : σ + δ₂ < 1) (τ : ℝ) :
    deriv (widePhaseApprox D lam δ₁ δ₂ σ) τ = wideRateBlur D lam δ₁ δ₂ σ τ := by
  have hfun : (fun t : ℝ => widePhaseBlur D lam δ₁ δ₂ σ t
      + ((-widePhaseBlur D lam δ₁ δ₂ σ 0) + (taR D σ + lam * sweepW' D σ)))
      = widePhaseApprox D lam δ₁ δ₂ σ := by
    funext t
    simp only [widePhaseApprox_apply]
    ring
  rw [← hfun]
  exact ((wf_hasDerivAt_phaseBlur D hδ₁ hδ₂ h0 h1 hσlo hσhi).add_const _).deriv

/-! ## Positivity of the blurred rate -/

lemma wf_rateBlur_pos {d : BandArcData} (D : SweepData d) {lam δ₁ δ₂ σ τ : ℝ}
    (h0 : 0 < lam) (h1 : lam ≤ 1 / 4) (hδ₂ : 0 ≤ δ₂) (hσlo : 0 < σ - δ₂)
    (hσhi : σ + δ₂ < 1) :
    0 < wideRateBlur D lam δ₁ δ₂ σ τ := by
  have hwin : ∀ σ' ∈ Set.Icc (σ - δ₂) (σ + δ₂), 0 < sweepW' D σ' ∧ sweepW' D σ' < period := by
    intro σ' hσ'
    have h0' : 0 < σ' := by linarith [hσ'.1]
    have h1' : σ' < 1 := by linarith [hσ'.2]
    have hposlt := sweepW_pos_lt D ⟨σ', h0'.le, h1'.le⟩ ⟨h0', h1'⟩
    rw [wf_sweepW'_eq D h0'.le h1'.le]
    exact hposlt
  have hρpos : ∀ σ' ∈ Set.Icc (σ - δ₂) (σ + δ₂), ∀ u : ℝ,
      0 < wideRho (sweepW' D σ') (period - sweepW' D σ') lam u := by
    intro σ' hσ' u
    obtain ⟨hw0, hwP⟩ := hwin σ' hσ'
    have hdl : (0:ℝ) < 1 - 2 * lam := by linarith
    have hd2 : (0:ℝ) < 1 / 2 - lam := by linarith
    simp only [wideRho]
    split_ifs
    · exact mul_pos hdl (div_pos (mul_pos (by norm_num) hw0) period_pos)
    · norm_num
    · exact div_pos (mul_pos hdl (by linarith)) (mul_pos period_pos hd2)
    · norm_num
  obtain ⟨Cρ, hCρ0, hCρb⟩ := wf_wideRhoFun_bound D h0 h1
  have hb1 : ∀ u : ℝ, sweepBump u ≤ 1 := by
    intro u
    rw [sweepBump]
    exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.le_one _)
  have hin : ∀ v ∈ Set.Ioo (-1 : ℝ) 1, 0 < ∫ u in (-1 : ℝ)..1, sweepBump u *
      wideRhoFun D lam (σ - δ₂ * v, τ - δ₁ * u) := by
    intro v hv
    have hvmem : σ - δ₂ * v ∈ Set.Icc (σ - δ₂) (σ + δ₂) := by
      rw [Set.mem_Icc]; constructor <;> nlinarith [hδ₂, hv.1, hv.2]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ ?_ (by norm_num)
    · refine wf_intervalIntegrable_of_bound_on (C := Cρ) ?_ ?_
      · refine (continuous_sweepBump.measurable.mul ((measurable_wideRhoFun D lam).comp
          ?_)).aestronglyMeasurable
        refine Measurable.prod ?_ ?_
        · exact measurable_const
        · exact measurable_const.sub (measurable_const.mul measurable_id)
      · intro u _
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sweepBump_nonneg u)]
        have h := hCρb (σ - δ₂ * v) (τ - δ₁ * u)
        simp only [wideRhoFun] at h
        calc sweepBump u * |wideRhoFun D lam (σ - δ₂ * v, τ - δ₁ * u)|
            ≤ 1 * Cρ := mul_le_mul (hb1 u) h (abs_nonneg _) zero_le_one
          _ = Cρ := one_mul _
    · intro u hu
      exact mul_pos (sweepBump_pos hu.1 hu.2)
        (by simpa only [wideRhoFun] using hρpos _ hvmem _)
  have hρss : StronglyMeasurable (fun σ' : ℝ =>
      ∫ u in (-1 : ℝ)..1, sweepBump u * wideRhoFun D lam (σ', τ - δ₁ * u)) := by
    have hpairR : Measurable (fun p : ℝ × ℝ => ((p.1, τ - δ₁ * p.2) : ℝ × ℝ)) := by
      refine Measurable.prod ?_ ?_
      · exact measurable_fst
      · exact measurable_const.sub (measurable_const.mul measurable_snd)
    have hL : StronglyMeasurable (Function.uncurry
        (fun (σ' : ℝ) (u : ℝ) => sweepBump u * wideRhoFun D lam (σ', τ - δ₁ * u))) := by
      have h : Measurable (fun p : ℝ × ℝ => sweepBump p.2 * wideRhoFun D lam (p.1, τ - δ₁ * p.2)) :=
        (continuous_sweepBump.measurable.comp measurable_snd).mul
          ((measurable_wideRhoFun D lam).comp hpairR)
      rw [show Function.uncurry (fun (σ' : ℝ) (u : ℝ) =>
            sweepBump u * wideRhoFun D lam (σ', τ - δ₁ * u))
          = fun p : ℝ × ℝ => sweepBump p.2 * wideRhoFun D lam (p.1, τ - δ₁ * p.2) from rfl]
      exact h.stronglyMeasurable
    have h2 := MeasureTheory.StronglyMeasurable.integral_prod_right
      (f := fun (σ' : ℝ) (u : ℝ) => sweepBump u * wideRhoFun D lam (σ', τ - δ₁ * u)) hL
      (ν := volume.restrict (Set.uIoc (-1 : ℝ) 1))
    have hfun : (fun σ' : ℝ => ∫ u : ℝ, sweepBump u * wideRhoFun D lam (σ', τ - δ₁ * u)
          ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1)))
        = (fun σ' : ℝ => ∫ u in (-1 : ℝ)..1, sweepBump u * wideRhoFun D lam (σ', τ - δ₁ * u)) := by
      funext σ'
      rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
        Set.uIoc_of_le (by norm_num)]
    rw [hfun] at h2
    exact h2
  have hinner_bd : ∀ v : ℝ, |∫ u in (-1 : ℝ)..1, sweepBump u *
      wideRhoFun D lam (σ - δ₂ * v, τ - δ₁ * u)| ≤ Cρ := by
    intro v
    rw [← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1 : ℝ) ≤ 1)).trans ?_
    have hpt : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
        ‖sweepBump u * wideRhoFun D lam (σ - δ₂ * v, τ - δ₁ * u)‖ ≤ sweepBump u * Cρ := by
      intro u _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sweepBump_nonneg u)]
      have h := hCρb (σ - δ₂ * v) (τ - δ₁ * u)
      simp only [wideRhoFun] at h
      exact mul_le_mul_of_nonneg_left h (sweepBump_nonneg u)
    have hm1 : IntervalIntegrable (fun u : ℝ =>
        ‖sweepBump u * wideRhoFun D lam (σ - δ₂ * v, τ - δ₁ * u)‖) volume (-1) 1 := by
      refine wf_intervalIntegrable_of_bound_on (C := Cρ) ?_ ?_
      · refine (continuous_sweepBump.measurable.mul ((measurable_wideRhoFun D lam).comp
          ?_)).norm.aestronglyMeasurable
        refine Measurable.prod ?_ ?_
        · exact measurable_const
        · exact measurable_const.sub (measurable_const.mul measurable_id)
      · intro u hu
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        have h2 : sweepBump u * Cρ ≤ Cρ := by nlinarith [hb1 u, hCρ0]
        exact (hpt u hu).trans h2
    have hm2 : IntervalIntegrable (fun u : ℝ => sweepBump u * Cρ) volume (-1) 1 :=
      (continuous_sweepBump.mul_const _).intervalIntegrable _ _
    refine (intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1) hm1 hm2 hpt).trans ?_
    rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]
  rw [wideRateBlur]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ ?_ (by norm_num)
  · have hmap : Measurable (fun v : ℝ => σ - δ₂ * v) :=
      measurable_const.sub (measurable_const.mul measurable_id)
    have hmeas : AEStronglyMeasurable (fun v : ℝ => sweepBump v * (∫ u in (-1 : ℝ)..1, sweepBump u *
        wideRhoFun D lam (σ - δ₂ * v, τ - δ₁ * u))) volume :=
      continuous_sweepBump.measurable.aestronglyMeasurable.mul
        (hρss.comp_measurable hmap).aestronglyMeasurable
    refine wf_intervalIntegrable_of_bound_on (C := Cρ) hmeas ?_
    intro v _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sweepBump_nonneg v)]
    have h := hinner_bd v
    calc sweepBump v * |∫ u in (-1 : ℝ)..1, sweepBump u *
          wideRhoFun D lam (σ - δ₂ * v, τ - δ₁ * u)|
        ≤ 1 * Cρ := mul_le_mul (hb1 v) h (abs_nonneg _) zero_le_one
      _ = Cρ := one_mul _
  · intro v hv
    exact mul_pos (sweepBump_pos hv.1 hv.2) (hin v hv)


/-! ## The value error of the blurred phase -/

/-- Blurring against the bump is a small perturbation for functions that are uniformly continuous
with an explicit modulus. -/
lemma wf_blur_close {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Continuous f) {ε δ δ' : ℝ} (hε : 0 ≤ ε)
    (hbd : ∀ t h : ℝ, |h| ≤ δ → ‖f (t + h) - f t‖ ≤ ε) (hδ : |δ'| ≤ δ) (t : ℝ) :
    ‖(∫ u in (-1 : ℝ)..1, sweepBump u • f (t - δ' * u)) - f t‖ ≤ ε := by
  have hcont : Continuous (fun u : ℝ => sweepBump u • f (t - δ' * u)) :=
    sweepBump_continuous.smul (hf.comp (continuous_const.sub (continuous_const.mul continuous_id)))
  have hcont' : Continuous (fun u : ℝ => sweepBump u • (f (t - δ' * u) - f t)) :=
    sweepBump_continuous.smul
      ((hf.comp (continuous_const.sub (continuous_const.mul continuous_id))).sub continuous_const)
  have hconstcont : Continuous (fun u : ℝ => sweepBump u • f t) :=
    sweepBump_continuous.smul continuous_const
  have hconst : (∫ u in (-1 : ℝ)..1, sweepBump u • f t) = f t := by
    rw [intervalIntegral.integral_smul_const, integral_sweepBump, one_smul]
  have hdiff : (∫ u in (-1 : ℝ)..1, sweepBump u • f (t - δ' * u)) - f t
      = ∫ u in (-1 : ℝ)..1, sweepBump u • (f (t - δ' * u) - f t) := by
    nth_rewrite 1 [← hconst]
    rw [← intervalIntegral.integral_sub (hcont.intervalIntegrable (-1) 1)
      (hconstcont.intervalIntegrable (-1) 1)]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    rw [smul_sub]
  rw [hdiff]
  refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1 : ℝ) ≤ 1)).trans ?_
  have hpt : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      ‖sweepBump u • (f (t - δ' * u) - f t)‖ ≤ sweepBump u * ε := by
    intro u hu
    rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u)]
    have habs : |δ' * u| ≤ δ := by
      rw [abs_mul]
      calc |δ'| * |u| ≤ |δ'| * 1 :=
            mul_le_mul_of_nonneg_left (abs_le.mpr hu) (abs_nonneg _)
        _ = |δ'| := by ring
        _ ≤ δ := hδ
    have habs' : |-(δ' * u)| ≤ δ := by simpa using habs
    have h := hbd t (-(δ' * u)) habs'
    have h' : ‖f (t - δ' * u) - f t‖ ≤ ε := by
      simpa [show t + -(δ' * u) = t - δ' * u by ring] using h
    exact mul_le_mul_of_nonneg_left h' (sweepBump_nonneg u)
  have hmono : (∫ u in (-1 : ℝ)..1, ‖sweepBump u • (f (t - δ' * u) - f t)‖)
      ≤ ∫ u in (-1 : ℝ)..1, sweepBump u * ε :=
    intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1)
      (hcont'.norm.intervalIntegrable (-1) 1)
      ((sweepBump_continuous.mul continuous_const).intervalIntegrable (-1) 1) hpt
  refine hmono.trans ?_
  rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]

/-- Pulling a constant `c` out of an integral against the bump, with a bound `D` on the deviation
`|h - c|` on `[-1,1]`. -/
lemma wf_blur_sub_const_le {h : ℝ → ℝ} {c D : ℝ}
    (hIh : IntervalIntegrable (fun u : ℝ => sweepBump u * h u) volume (-1) 1)
    (hIsub : IntervalIntegrable (fun u : ℝ => sweepBump u * h u - sweepBump u * c) volume (-1) 1)
    (hb : ∀ u ∈ Set.Icc (-1 : ℝ) 1, |h u - c| ≤ D) :
    |(∫ u in (-1 : ℝ)..1, sweepBump u * h u) - c| ≤ D := by
  have hc : (∫ u in (-1 : ℝ)..1, sweepBump u * c) = c := by
    rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]
  have hpull : (∫ u in (-1 : ℝ)..1, sweepBump u * h u) - c
      = ∫ u in (-1 : ℝ)..1, (sweepBump u * h u - sweepBump u * c) := by
    have hstep : (∫ u in (-1 : ℝ)..1, sweepBump u * h u) - c
        = (∫ u in (-1 : ℝ)..1, sweepBump u * h u)
          - (∫ u in (-1 : ℝ)..1, sweepBump u * c) := by rw [hc]
    rw [hstep]
    exact (intervalIntegral.integral_sub hIh
      ((continuous_sweepBump.mul_const c).intervalIntegrable _ _)).symm
  rw [hpull, show |∫ u in (-1 : ℝ)..1, (sweepBump u * h u - sweepBump u * c)|
      = ‖∫ u in (-1 : ℝ)..1, (sweepBump u * h u - sweepBump u * c)‖ from Real.norm_eq_abs _]
  refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1 : ℝ) ≤ 1)).trans ?_
  have hpt : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      ‖sweepBump u * h u - sweepBump u * c‖ ≤ sweepBump u * D := by
    intro u hu
    rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sweepBump_nonneg u)]
    exact mul_le_mul_of_nonneg_left (hb u hu) (sweepBump_nonneg u)
  refine (intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1) hIsub.norm
    ((continuous_sweepBump.mul_const D).intervalIntegrable _ _) hpt).trans ?_
  rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]

/-- Interval integrability of the integrand of the phase blur. -/
lemma wf_phase_integrand_intervalIntegrable {d : BandArcData} (D : SweepData d)
    {lam C δ₁ σ s : ℝ} (hC0 : 0 ≤ C)
    (hCb : ∀ (σ s : ℝ), |widePhaseFun D lam (σ, s)| ≤ |s| + C + period) :
    IntervalIntegrable (fun u : ℝ => sweepBump u * widePhaseFun D lam (σ, s - δ₁ * u))
      volume (-1) 1 := by
  refine wf_intervalIntegrable_of_bound_on (C := |s| + C + period + |δ₁|) ?_ ?_
  · exact (continuous_sweepBump.measurable.mul
      (wf_phaseFun_comp_meas D lam σ s δ₁)).aestronglyMeasurable
  · intro u hu
    have h := wf_phaseBlur1_integrand_bound D hCb hC0 δ₁ σ s u
      (by rw [abs_le]; exact ⟨by linarith [hu.1], hu.2⟩)
    simpa only [Real.norm_eq_abs] using h

/-- The doubly blurred phase differs from the phase by at most `η + 2 δ₁`, where `η` bounds the
sweep-parameter variation of the phase. -/
lemma wf_blur_value_error {d : BandArcData} (D : SweepData d) {lam δ₁ δ₂ σ η s : ℝ}
    (hlam0 : 0 < lam) (hlam4 : lam ≤ 1 / 4) (hδ₁ : 0 ≤ δ₁)
    (hη : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ∀ w : ℝ,
      |wideSig D lam (σ - δ₂ * v) w - wideSig D lam σ w| ≤ η)
    (hlip : ∀ a b : ℝ, |wideSig D lam σ a - wideSig D lam σ b| ≤ 2 * |a - b|) :
    |widePhaseBlur D lam δ₁ δ₂ σ s - wideSig D lam σ s| ≤ η + 2 * δ₁ := by
  obtain ⟨C, hC0, hCb⟩ := wf_phaseFun_bound D hlam0 hlam4
  obtain ⟨Cb, hCb0, hCbb⟩ := wf_phaseBlur1_bound D hlam0 hlam4 δ₁
  have hI : ∀ σ' : ℝ, IntervalIntegrable
      (fun u : ℝ => sweepBump u * widePhaseFun D lam (σ', s - δ₁ * u)) volume (-1) 1 :=
    fun σ' => wf_phase_integrand_intervalIntegrable D hC0 hCb
  have hIc : IntervalIntegrable (fun u : ℝ => sweepBump u * widePhaseFun D lam (σ, s))
      volume (-1) 1 := (continuous_sweepBump.mul_const _).intervalIntegrable _ _
  have hptInner : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |widePhaseFun D lam (σ - δ₂ * v, s - δ₁ * u) - widePhaseFun D lam (σ, s)|
        ≤ η + 2 * δ₁ := by
    intro v hv u hu
    have hu1 : |u| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [hu.1], hu.2⟩
    have h2 := hlip (s - δ₁ * u) s
    have h3 : s - δ₁ * u - s = -(δ₁ * u) := by ring
    rw [h3, abs_neg, abs_mul, abs_of_nonneg hδ₁] at h2
    have h5 : (2:ℝ) * (δ₁ * |u|) ≤ 2 * δ₁ := by
      nlinarith [mul_le_mul_of_nonneg_left hu1 hδ₁]
    have h1 := hη v hv (s - δ₁ * u)
    have e1 : |widePhaseFun D lam (σ - δ₂ * v, s - δ₁ * u) - widePhaseFun D lam (σ, s - δ₁ * u)|
        ≤ η := by simpa only [wideSig, widePhaseFun] using h1
    have e2 : |widePhaseFun D lam (σ, s - δ₁ * u) - widePhaseFun D lam (σ, s)|
        ≤ 2 * (δ₁ * |u|) := by simpa only [wideSig, widePhaseFun] using h2
    have hsum := abs_sub_le (widePhaseFun D lam (σ - δ₂ * v, s - δ₁ * u))
      (widePhaseFun D lam (σ, s - δ₁ * u)) (widePhaseFun D lam (σ, s))
    linarith
  have hinner : ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      |(∫ u in (-1 : ℝ)..1, sweepBump u * widePhaseFun D lam (σ - δ₂ * v, s - δ₁ * u))
        - widePhaseFun D lam (σ, s)| ≤ η + 2 * δ₁ := by
    intro v hv
    exact wf_blur_sub_const_le (hI (σ - δ₂ * v)) ((hI (σ - δ₂ * v)).sub hIc)
      (fun u hu => hptInner v hv u hu)
  have hss : StronglyMeasurable (fun σ' : ℝ =>
      ∫ u in (-1 : ℝ)..1, sweepBump u * widePhaseFun D lam (σ', s - δ₁ * u)) := by
    have hpairR : Measurable (fun p : ℝ × ℝ => ((p.1, s - δ₁ * p.2) : ℝ × ℝ)) := by
      refine Measurable.prod ?_ ?_
      · exact measurable_fst
      · exact measurable_const.sub (measurable_const.mul measurable_snd)
    have hL : StronglyMeasurable (Function.uncurry
        (fun (σ' : ℝ) (u : ℝ) => sweepBump u * widePhaseFun D lam (σ', s - δ₁ * u))) := by
      have h : Measurable (fun p : ℝ × ℝ => sweepBump p.2 * widePhaseFun D lam (p.1, s - δ₁ * p.2)) :=
        (continuous_sweepBump.measurable.comp measurable_snd).mul
          ((measurable_widePhaseFun D lam).comp hpairR)
      rw [show Function.uncurry (fun (σ' : ℝ) (u : ℝ) =>
            sweepBump u * widePhaseFun D lam (σ', s - δ₁ * u))
          = fun p : ℝ × ℝ => sweepBump p.2 * widePhaseFun D lam (p.1, s - δ₁ * p.2) from rfl]
      exact h.stronglyMeasurable
    have h2 := MeasureTheory.StronglyMeasurable.integral_prod_right
      (f := fun (σ' : ℝ) (u : ℝ) => sweepBump u * widePhaseFun D lam (σ', s - δ₁ * u)) hL
      (ν := volume.restrict (Set.uIoc (-1 : ℝ) 1))
    have hfun : (fun σ' : ℝ => ∫ u : ℝ, sweepBump u * widePhaseFun D lam (σ', s - δ₁ * u)
          ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1)))
        = (fun σ' : ℝ => ∫ u in (-1 : ℝ)..1, sweepBump u * widePhaseFun D lam (σ', s - δ₁ * u)) := by
      funext σ'
      rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
        Set.uIoc_of_le (by norm_num)]
    rw [hfun] at h2
    exact h2
  have hmap : Measurable (fun v : ℝ => σ - δ₂ * v) :=
    measurable_const.sub (measurable_const.mul measurable_id)
  have hIouter : IntervalIntegrable (fun v : ℝ => sweepBump v *
      (∫ u in (-1 : ℝ)..1, sweepBump u * widePhaseFun D lam (σ - δ₂ * v, s - δ₁ * u)))
      volume (-1) 1 := by
    have hmeas : AEStronglyMeasurable (fun v : ℝ => sweepBump v *
        (∫ u in (-1 : ℝ)..1, sweepBump u * widePhaseFun D lam (σ - δ₂ * v, s - δ₁ * u))) volume :=
      continuous_sweepBump.measurable.aestronglyMeasurable.mul
        ((hss.comp_measurable hmap).aestronglyMeasurable)
    refine wf_intervalIntegrable_of_bound_on (C := |s| + Cb + period + |δ₁|) hmeas ?_
    intro v _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sweepBump_nonneg v)]
    have hb1 : sweepBump v ≤ 1 := by
      rw [sweepBump]
      exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
        (Real.smoothTransition.le_one _)
    have h0' : 0 ≤ |s| + Cb + period + |δ₁| := by
      have := period_pos; linarith [abs_nonneg s, abs_nonneg δ₁]
    calc sweepBump v * |∫ u in (-1 : ℝ)..1,
          sweepBump u * widePhaseFun D lam (σ - δ₂ * v, s - δ₁ * u)|
        ≤ 1 * (|s| + Cb + period + |δ₁|) := mul_le_mul hb1 (by
            have := hCbb (σ - δ₂ * v) s
            simpa only [widePhaseBlur1, widePhaseFun] using this) (abs_nonneg _) zero_le_one
      _ = |s| + Cb + period + |δ₁| := one_mul _
  have hres := wf_blur_sub_const_le (h := fun v : ℝ =>
      ∫ u in (-1 : ℝ)..1, sweepBump u * widePhaseFun D lam (σ - δ₂ * v, s - δ₁ * u))
    (c := widePhaseFun D lam (σ, s)) (D := η + 2 * δ₁) hIouter
    (hIouter.sub ((continuous_sweepBump.mul_const _).intervalIntegrable _ _))
    (fun v hv => hinner v hv)
  simpa only [widePhaseBlur, widePhaseBlur1, wideSig, widePhaseFun] using hres


set_option maxHeartbeats 2000000

/-- Interval integrability on `[-1,1]` from a bound for real-valued functions. -/
lemma wf_intervalIntegrable_of_global_bound {g : ℝ → ℝ} {C : ℝ}
    (hg : AEStronglyMeasurable g volume) (hb : ∀ u : ℝ, ‖g u‖ ≤ C) :
    IntervalIntegrable g volume (-1) 1 :=
  wf_intervalIntegrable_of_bound_on hg (fun u _ => hb u)

/-- `a * (Y / (32 * (a + 1))) ≤ Y / 32` for `a, Y ≥ 0`. -/
lemma wf_mul_div_le {a Y : ℝ} (ha : 0 ≤ a) (hY : 0 ≤ Y) :
    a * (Y / (32 * (a + 1))) ≤ Y / 32 := by
  have h1 : a / (a + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h3 : a * (Y / (32 * (a + 1))) = (Y / 32) * (a / (a + 1)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [h3]
  calc (Y / 32) * (a / (a + 1)) ≤ (Y / 32) * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Y / 32 := by ring

/-- Measurability of `u ↦ g v u` from the joint measurability of `g`. -/
lemma wf_measurable_uncurry_left {E : Type*} [MeasurableSpace E] {g : ℝ → ℝ → E}
    (hgm : Measurable (Function.uncurry g)) (v : ℝ) : Measurable (fun u : ℝ => g v u) := by
  have h1 : Measurable (fun u : ℝ => ((v, u) : ℝ × ℝ)) :=
    Measurable.prod (f := fun u : ℝ => ((v, u) : ℝ × ℝ)) measurable_const measurable_id
  have h2 : Measurable ((Function.uncurry g) ∘ (fun u : ℝ => ((v, u) : ℝ × ℝ))) := hgm.comp h1
  have h3 : (fun u : ℝ => g v u)
      = (Function.uncurry g) ∘ (fun u : ℝ => ((v, u) : ℝ × ℝ)) := rfl
  rw [h3]
  exact h2

/-- The value error of the phase approximation: the reparametrisation is within `2(η + 2 δ₁)` of
the matching phase. -/
lemma wf_phaseApprox_value {d : BandArcData} (D : SweepData d) {lam δ₁ δ₂ σ η : ℝ}
    (hlam0 : 0 < lam) (hlam4 : lam ≤ 1 / 4) (hδ₁ : 0 ≤ δ₁)
    (hη : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ∀ w : ℝ,
      |wideSig D lam (σ - δ₂ * v) w - wideSig D lam σ w| ≤ η)
    (hlip : ∀ a b : ℝ, |wideSig D lam σ a - wideSig D lam σ b| ≤ 2 * |a - b|) (τ : ℝ) :
    |widePhaseApprox D lam δ₁ δ₂ σ τ - wideSig D lam σ τ| ≤ 2 * (η + 2 * δ₁) := by
  have h0 := wf_blur_value_error D hlam0 hlam4 hδ₁ hη hlip (s := τ)
  have h1 := wf_blur_value_error D hlam0 hlam4 hδ₁ hη hlip (s := 0)
  have h3 : wideSig D lam σ 0 = taR D σ + lam * sweepW' D σ := by
    rw [wideSig_apply, wideSigma, sweepParam_zero, wideSfrac_zero]
    ring
  have hψ : widePhaseApprox D lam δ₁ δ₂ σ τ - wideSig D lam σ τ
      = (widePhaseBlur D lam δ₁ δ₂ σ τ - wideSig D lam σ τ)
        - (widePhaseBlur D lam δ₁ δ₂ σ 0 - wideSig D lam σ 0) := by
    rw [widePhaseApprox_apply, h3]
    ring
  rw [hψ]
  have htri := abs_sub_le (widePhaseBlur D lam δ₁ δ₂ σ τ - wideSig D lam σ τ) 0
    (widePhaseBlur D lam δ₁ δ₂ σ 0 - wideSig D lam σ 0)
  simp only [sub_zero, zero_sub, abs_neg] at htri
  linarith

/-- Interval integrability on `[-1,1]` from a bound, in a general normed space. -/
lemma wf_intervalIntegrable_of_bound_on' {E : Type*} [NormedAddCommGroup E] {g : ℝ → E} {C : ℝ}
    (hg : AEStronglyMeasurable g volume)
    (hb : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ‖g u‖ ≤ C) : IntervalIntegrable g volume (-1) 1 := by
  constructor
  · refine IntegrableOn.of_bound ?_ hg.restrict C ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with x hx
      exact hb x ⟨le_of_lt hx.1, hx.2⟩
  · refine IntegrableOn.of_bound ?_ hg.restrict C ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with x hx
      exact hb x ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma wf_intervalIntegrable_of_global_bound' {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    {C : ℝ} (hg : AEStronglyMeasurable g volume) (hb : ∀ u : ℝ, ‖g u‖ ≤ C) :
    IntervalIntegrable g volume (-1) 1 :=
  wf_intervalIntegrable_of_bound_on' hg (fun u _ => hb u)

lemma wf_norm_sub_le_trans {E : Type*} [SeminormedAddCommGroup E] (x y z : E) :
    ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
  have h := dist_triangle x y z
  rwa [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h

lemma wf_sweepBump_le_one (u : ℝ) : sweepBump u ≤ 1 := by
  rw [sweepBump]
  exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

lemma wf_sweepBump_mul_bound {E : Type*} [SeminormedAddCommGroup E] {X : E} {C : ℝ}
    (h : ‖X‖ ≤ C) (u : ℝ) : sweepBump u * ‖X‖ ≤ C := by
  calc sweepBump u * ‖X‖ ≤ 1 * C :=
        mul_le_mul (wf_sweepBump_le_one u) h (norm_nonneg _) zero_le_one
    _ = C := one_mul _

/-- The raw chamfered loop is Lipschitz in the loop parameter, with an explicit constant. -/
lemma wf_loop_lipschitz {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {lam : ℝ} (hlam0 : 0 < lam) (hlam4 : lam ≤ 1 / 4) :
    ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ (σ a b : ℝ),
      ‖sweepLoopChamfer r D lam σ a - sweepLoopChamfer r D lam σ b‖ ≤ Cl * |a - b| := by
  obtain ⟨V, hV0, hV⟩ := wideEnd_speed_bound hr
  obtain ⟨R, hR0, hR⟩ := wideEnd_knot_bounded hr.continuous hr.periodic
  obtain ⟨A, hA0, hA⟩ := wf_lift_bound D
  have hTw0 : 0 ≤ 2 * A := by positivity
  have hW : ∀ s : ℝ, |sweepW' D s| ≤ 2 * A := by
    intro s
    have h1 := hA s
    have h4 : |tbR D s - taR D s| ≤ |tbR D s| + |taR D s| := by
      simpa using abs_sub_le (tbR D s) 0 (taR D s)
    simp only [sweepW']
    linarith [h1.1, h1.2, h4]
  refine ⟨doubleBlurLam lam V R (2 * A), doubleBlurLam_nonneg hlam0 hV0.le hR0 hTw0, ?_⟩
  intro σ a b
  exact doubleBlur_loop_lipschitz (lam := lam) (L := V) (R := R) (Tw := 2 * A)
    (hr.smooth.of_le (by simp)) hlam0 (by linarith) σ
    (fun t => doubleBlur_chamferDeriv_bound hlam0 (by linarith)
      (fun x => by simpa only [velocity] using hV x) hR hTw0 σ (hW σ) t) a b

/-- **The blurred sweep is close to the loop.**  For a fixed chamfer fraction `lam ∈ (0,1/4]`
there is a scale below which the doubly smoothed slice is uniformly close to the raw chamfered
loop. -/
lemma wf_sweepFam_close_loop {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {lam : ℝ} (hlam0 : 0 < lam) (hlam4 : lam ≤ 1 / 4) :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, 0 < L ∧ ∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L →
      ∀ σ t : ℝ, ‖sweepFam r D lam δ₁ δ₂ σ t - sweepLoopChamfer r D lam σ t‖ ≤ ε := by
  intro ε hε
  have hlam1 : lam < 1 / 2 := by linarith
  have hσmod : ∀ ε' : ℝ, 0 < ε' → ∃ θ' : ℝ, 0 < θ' ∧ ∀ (σ σ' : ℝ), |σ - σ'| ≤ θ' →
      ∀ t : ℝ, ‖sweepLoopChamfer r D lam σ' t - sweepLoopChamfer r D lam σ t‖ ≤ ε' := by
    intro ε' hε'
    obtain ⟨θ', hθ'0, hθ'⟩ := sweepLoopProfile_uniformCont_sweep D hr.continuous ε' hε'
    refine ⟨θ', hθ'0, fun σ σ' hσσ' t => ?_⟩
    rw [sweepLoopChamfer_eq_profile r D hlam0 (by linarith) σ' t,
      sweepLoopChamfer_eq_profile r D hlam0 (by linarith) σ t]
    exact hθ' lam hlam0 hlam4 σ σ' (sweepParam t)
      ⟨(sweepParam_mem t).1, (sweepParam_mem t).2.le⟩ hσσ'
  have hloopcont : ∀ σ : ℝ, Continuous (fun x : ℝ => sweepLoopChamfer r D lam σ x) :=
    fun σ => sweepLoopChamfer_continuous_t hr.continuous D hlam0 hlam1
  -- modulation of the single blur in the sweep parameter
  have hsmoothmod : ∀ ε' : ℝ, 0 < ε' → ∃ θ' : ℝ, 0 < θ' ∧
      ∀ (δ₁ : ℝ) (σ σ' : ℝ), |σ - σ'| ≤ θ' → ∀ t : ℝ,
        ‖sweepSmoothT r D lam δ₁ σ' t - sweepSmoothT r D lam δ₁ σ t‖ ≤ ε' := by
    intro ε' hε'
    obtain ⟨θ', hθ'0, hθ'⟩ := hσmod ε' hε'
    refine ⟨θ', hθ'0, fun δ₁ σ σ' hσσ' t => ?_⟩
    simp only [sweepSmoothT]
    have hI1 : IntervalIntegrable
        (fun u : ℝ => sweepBump u • sweepLoopChamfer r D lam σ' (t - δ₁ * u)) volume (-1) 1 :=
      (sweepBump_continuous.smul ((hloopcont σ').comp
        (continuous_const.sub (continuous_const.mul continuous_id)))).intervalIntegrable _ _
    have hI2 : IntervalIntegrable
        (fun u : ℝ => sweepBump u • sweepLoopChamfer r D lam σ (t - δ₁ * u)) volume (-1) 1 :=
      (sweepBump_continuous.smul ((hloopcont σ).comp
        (continuous_const.sub (continuous_const.mul continuous_id)))).intervalIntegrable _ _
    rw [← intervalIntegral.integral_sub hI1 hI2]
    calc ‖∫ u in (-1 : ℝ)..1, (sweepBump u • sweepLoopChamfer r D lam σ' (t - δ₁ * u)
            - sweepBump u • sweepLoopChamfer r D lam σ (t - δ₁ * u))‖
        ≤ ∫ u in (-1 : ℝ)..1, ‖sweepBump u • sweepLoopChamfer r D lam σ' (t - δ₁ * u)
            - sweepBump u • sweepLoopChamfer r D lam σ (t - δ₁ * u)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1 : ℝ) ≤ 1)
      _ ≤ ∫ u in (-1 : ℝ)..1, sweepBump u * ε' :=
          intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1)
            ((hI1.sub hI2).norm) ((sweepBump_continuous.mul_const ε').intervalIntegrable _ _)
            (fun u _ => by
              rw [← smul_sub, norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u)]
              exact mul_le_mul_of_nonneg_left (hθ' σ σ' hσσ' (t - δ₁ * u))
                (sweepBump_nonneg u))
      _ = ε' := by rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]
  obtain ⟨Cl, hCl0, hlip⟩ := wf_loop_lipschitz hr D hlam0 hlam4
  obtain ⟨θσ, hθσ0, hθσ⟩ := hsmoothmod (ε / 3) (by linarith)
  have hCl1 : 0 < Cl + 1 := by linarith
  refine ⟨min θσ (ε / (3 * (Cl + 1))), lt_min hθσ0 (by positivity), ?_⟩
  intro δ₁ δ₂ hδ₁0 hδ₁T hδ₂0 hδ₂S σ t
  have hδ₁σ : δ₁ ≤ θσ := hδ₁T.trans (min_le_left _ _)
  have hδ₁c : δ₁ ≤ ε / (3 * (Cl + 1)) := hδ₁T.trans (min_le_right _ _)
  have hδ₂σ : δ₂ ≤ θσ := hδ₂S.trans (min_le_left _ _)
  have hstep1 : ‖sweepSmoothT r D lam δ₁ σ t - sweepLoopChamfer r D lam σ t‖ ≤ ε / 3 := by
    have hbd : ∀ x h : ℝ, |h| ≤ ε / (3 * (Cl + 1)) →
        ‖sweepLoopChamfer r D lam σ (x + h) - sweepLoopChamfer r D lam σ x‖ ≤ ε / 3 := by
      intro x h hh
      have h1 := hlip σ (x + h) x
      rw [show x + h - x = h by ring] at h1
      have h2 : Cl * |h| ≤ Cl * (ε / (3 * (Cl + 1))) := mul_le_mul_of_nonneg_left hh hCl0
      have h3 : Cl * (ε / (3 * (Cl + 1))) ≤ ε / 3 := by
        have h4 : Cl / (Cl + 1) ≤ 1 := by rw [div_le_one hCl1]; linarith
        have h5 : Cl * (ε / (3 * (Cl + 1))) = (Cl / (Cl + 1)) * (ε / 3) := by
          field_simp
        rw [h5]
        exact mul_le_of_le_one_left (by positivity) h4
      linarith
    have hmain := wf_blur_close (f := fun x : ℝ => sweepLoopChamfer r D lam σ x) (hloopcont σ)
      (ε := ε / 3) (δ := ε / (3 * (Cl + 1))) (δ' := δ₁) (by linarith) hbd
      (by rw [abs_of_pos hδ₁0]; exact hδ₁c) t
    simpa only [sweepSmoothT] using hmain
  have hstep2 : ‖sweepFam r D lam δ₁ δ₂ σ t - sweepSmoothT r D lam δ₁ σ t‖ ≤ ε / 3 := by
    have hcontσ : Continuous (fun sig : ℝ => sweepSmoothT r D lam δ₁ sig t) := by
      rw [Metric.continuous_iff]
      intro b ε' hε'
      obtain ⟨θ', hθ'0, hθ'⟩ := hsmoothmod (ε' / 2) (by linarith)
      refine ⟨θ', hθ'0, fun a ha => ?_⟩
      rw [Real.dist_eq] at ha
      rw [dist_eq_norm]
      have h := hθ' δ₁ b a (by rw [abs_sub_comm] at ha; exact le_of_lt ha) t
      linarith [h, hε']
    have hbd : ∀ x h : ℝ, |h| ≤ θσ →
        ‖sweepSmoothT r D lam δ₁ (x + h) t - sweepSmoothT r D lam δ₁ x t‖ ≤ ε / 3 := by
      intro x h hh
      exact hθσ δ₁ x (x + h) (by rw [show x - (x + h) = -h by ring, abs_neg]; exact hh) t
    have hmain := wf_blur_close (f := fun sig : ℝ => sweepSmoothT r D lam δ₁ sig t) hcontσ
      (ε := ε / 3) (δ := θσ) (δ' := δ₂) (by linarith) hbd
      (by rw [abs_of_pos hδ₂0]; exact hδ₂σ) σ
    simpa only [sweepFam] using hmain
  calc ‖sweepFam r D lam δ₁ δ₂ σ t - sweepLoopChamfer r D lam σ t‖
      ≤ ‖sweepFam r D lam δ₁ δ₂ σ t - sweepSmoothT r D lam δ₁ σ t‖
        + ‖sweepSmoothT r D lam δ₁ σ t - sweepLoopChamfer r D lam σ t‖ :=
        wf_norm_sub_le_trans _ _ _
    _ ≤ ε / 3 + ε / 3 := add_le_add hstep2 hstep1
    _ ≤ ε := by linarith

/-- The double bump average of a constant vector, as the double bump integral of `(v,u) ↦ ρ v u • V`. -/
lemma wf_double_scalar_smul (b : ℝ → ℝ) (ρ : ℝ → ℝ → ℝ) (V : Space) :
    (∫ v in (-1 : ℝ)..1, b v * (∫ u in (-1 : ℝ)..1, b u * ρ v u)) • V
      = ∫ v in (-1 : ℝ)..1, b v • (∫ u in (-1 : ℝ)..1, b u • (ρ v u • V)) := by
  have hinner : ∀ v : ℝ, (∫ u in (-1 : ℝ)..1, b u • (ρ v u • V))
      = (∫ u in (-1 : ℝ)..1, b u * ρ v u) • V := by
    intro v
    rw [show (∫ u in (-1 : ℝ)..1, b u • (ρ v u • V))
        = ∫ u in (-1 : ℝ)..1, (b u * ρ v u) • V from
        intervalIntegral.integral_congr (fun u _ => smul_smul (b u) (ρ v u) V)]
    exact intervalIntegral.integral_smul_const (fun u : ℝ => b u * ρ v u) V
  have houter : (∫ v in (-1 : ℝ)..1, b v • (∫ u in (-1 : ℝ)..1, b u • (ρ v u • V)))
      = ∫ v in (-1 : ℝ)..1, (b v * (∫ u in (-1 : ℝ)..1, b u * ρ v u)) • V := by
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    rw [hinner v, smul_smul]
  rw [houter]
  exact (intervalIntegral.integral_smul_const
    (fun v : ℝ => b v * (∫ u in (-1 : ℝ)..1, b u * ρ v u)) V).symm

/-- **Norm bound for a double bump integral.**  If the vector integrand `g` is dominated by
`c * ρ'` pointwise on the square `[-1,1]²`, then the norm of its double bump integral is at most
`c` times the double bump integral of `ρ'`. -/
lemma wf_double_norm_le {g : ℝ → ℝ → Space} {ρ' : ℝ → ℝ → ℝ} {c Cg Cρ' : ℝ}
    (hgm : Measurable (Function.uncurry g))
    (hgb : ∀ v u : ℝ, ‖g v u‖ ≤ Cg)
    (hρm : Measurable (Function.uncurry ρ'))
    (hρb : ∀ v u : ℝ, |ρ' v u| ≤ Cρ')
    (hCg0 : 0 ≤ Cg) (hc0 : 0 ≤ c)
    (hpoint : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1, ‖g v u‖ ≤ c * ρ' v u) :
    ‖∫ v in (-1 : ℝ)..1, sweepBump v • (∫ u in (-1 : ℝ)..1, sweepBump u • g v u)‖
      ≤ c * ∫ v in (-1 : ℝ)..1, sweepBump v * (∫ u in (-1 : ℝ)..1, sweepBump u * ρ' v u) := by
  have hb0 : ∀ u : ℝ, 0 ≤ sweepBump u := sweepBump_nonneg
  have hCρ0 : 0 ≤ Cρ' := le_trans (abs_nonneg _) (hρb 0 0)
  have hgi : ∀ v : ℝ, IntervalIntegrable (fun u : ℝ => sweepBump u • g v u) volume (-1) 1 := by
    intro v
    refine wf_intervalIntegrable_of_global_bound' (C := Cg) ?_ ?_
    · exact (continuous_sweepBump.measurable.aestronglyMeasurable).smul
        ((wf_measurable_uncurry_left hgm v).aestronglyMeasurable)
    · intro u
      rw [norm_smul, Real.norm_of_nonneg (hb0 u)]
      exact wf_sweepBump_mul_bound (hgb v u) u
  have hρi : ∀ v : ℝ, IntervalIntegrable (fun u : ℝ => sweepBump u * ρ' v u) volume (-1) 1 := by
    intro v
    refine wf_intervalIntegrable_of_global_bound (C := Cρ') ?_ ?_
    · exact (continuous_sweepBump.measurable.mul
        (wf_measurable_uncurry_left (E := ℝ) hρm v)).aestronglyMeasurable
    · intro u
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hb0 u)]
      calc sweepBump u * |ρ' v u| ≤ 1 * Cρ' :=
            mul_le_mul (wf_sweepBump_le_one u) (hρb v u) (abs_nonneg _) zero_le_one
        _ = Cρ' := one_mul _
  have hinner : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ‖∫ u in (-1 : ℝ)..1, sweepBump u • g v u‖
      ≤ c * (∫ u in (-1 : ℝ)..1, sweepBump u * ρ' v u) := by
    intro v hv
    have hpt : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
        ‖sweepBump u • g v u‖ ≤ sweepBump u * (c * ρ' v u) := by
      intro u hu
      rw [norm_smul, Real.norm_of_nonneg (hb0 u)]
      exact mul_le_mul_of_nonneg_left (hpoint v hv u hu) (hb0 u)
    have hI2 : IntervalIntegrable (fun u : ℝ => sweepBump u * (c * ρ' v u)) volume (-1) 1 := by
      refine wf_intervalIntegrable_of_global_bound (C := c * Cρ') ?_ ?_
      · exact (continuous_sweepBump.measurable.mul
          (measurable_const.mul (wf_measurable_uncurry_left (E := ℝ) hρm v))).aestronglyMeasurable
      · intro u
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hb0 u), abs_mul, abs_of_nonneg hc0]
        calc sweepBump u * (c * |ρ' v u|) ≤ 1 * (c * Cρ') :=
              mul_le_mul (wf_sweepBump_le_one u) (mul_le_mul_of_nonneg_left (hρb v u) hc0)
                (by positivity) zero_le_one
          _ = c * Cρ' := one_mul _
    calc ‖∫ u in (-1 : ℝ)..1, sweepBump u • g v u‖
        ≤ ∫ u in (-1 : ℝ)..1, ‖sweepBump u • g v u‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1 : ℝ) ≤ 1)
      _ ≤ ∫ u in (-1 : ℝ)..1, sweepBump u * (c * ρ' v u) :=
          intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1)
            ((hgi v).norm) hI2 hpt
      _ = c * (∫ u in (-1 : ℝ)..1, sweepBump u * ρ' v u) := by
          rw [show (fun u : ℝ => sweepBump u * (c * ρ' v u))
              = (fun u : ℝ => c * (sweepBump u * ρ' v u)) from by funext u; ring]
          rw [intervalIntegral.integral_const_mul]
  have hinner_bound : ∀ v : ℝ, ‖∫ u in (-1 : ℝ)..1, sweepBump u • g v u‖ ≤ 2 * Cg := by
    intro v
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := Cg) (fun u _ => ?_)).trans ?_
    · rw [norm_smul, Real.norm_of_nonneg (hb0 u)]
      exact wf_sweepBump_mul_bound (hgb v u) u
    · rw [show |1 - (-1 : ℝ)| = 2 by norm_num]; linarith
  have hss : StronglyMeasurable (fun v : ℝ => ∫ u in (-1 : ℝ)..1, sweepBump u • g v u) := by
    have hL : StronglyMeasurable
        (Function.uncurry (fun (v : ℝ) (u : ℝ) => sweepBump u • g v u)) := by
      have h : Measurable (fun p : ℝ × ℝ => sweepBump p.2 • g p.1 p.2) :=
        (continuous_sweepBump.measurable.comp measurable_snd).smul
          ((hgm.comp (measurable_fst.prod measurable_snd)))
      rw [show Function.uncurry (fun (v : ℝ) (u : ℝ) => sweepBump u • g v u)
          = fun p : ℝ × ℝ => sweepBump p.2 • g p.1 p.2 from rfl]
      exact h.stronglyMeasurable
    have h2 := MeasureTheory.StronglyMeasurable.integral_prod_right
      (f := fun (v : ℝ) (u : ℝ) => sweepBump u • g v u) hL
      (ν := volume.restrict (Set.uIoc (-1 : ℝ) 1))
    have hfun : (fun v : ℝ => ∫ u : ℝ, sweepBump u • g v u
          ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1)))
        = (fun v : ℝ => ∫ u in (-1 : ℝ)..1, sweepBump u • g v u) := by
      funext v
      rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
        Set.uIoc_of_le (by norm_num)]
    rw [hfun] at h2
    exact h2
  have hssρ : StronglyMeasurable (fun v : ℝ => ∫ u in (-1 : ℝ)..1, sweepBump u * ρ' v u) := by
    have hL : StronglyMeasurable
        (Function.uncurry (fun (v : ℝ) (u : ℝ) => sweepBump u * ρ' v u)) := by
      have h : Measurable (fun p : ℝ × ℝ => sweepBump p.2 * ρ' p.1 p.2) :=
        (continuous_sweepBump.measurable.comp measurable_snd).mul
          ((hρm.comp (measurable_fst.prod measurable_snd)))
      rw [show Function.uncurry (fun (v : ℝ) (u : ℝ) => sweepBump u * ρ' v u)
          = fun p : ℝ × ℝ => sweepBump p.2 * ρ' p.1 p.2 from rfl]
      exact h.stronglyMeasurable
    have h2 := MeasureTheory.StronglyMeasurable.integral_prod_right
      (f := fun (v : ℝ) (u : ℝ) => sweepBump u * ρ' v u) hL
      (ν := volume.restrict (Set.uIoc (-1 : ℝ) 1))
    have hfun : (fun v : ℝ => ∫ u : ℝ, sweepBump u * ρ' v u
          ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1)))
        = (fun v : ℝ => ∫ u in (-1 : ℝ)..1, sweepBump u * ρ' v u) := by
      funext v
      rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
        Set.uIoc_of_le (by norm_num)]
    rw [hfun] at h2
    exact h2
  have hptv : ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      ‖sweepBump v • (∫ u in (-1 : ℝ)..1, sweepBump u • g v u)‖
        ≤ c * (sweepBump v * (∫ u in (-1 : ℝ)..1, sweepBump u * ρ' v u)) := by
    intro v hv
    rw [norm_smul, Real.norm_of_nonneg (hb0 v)]
    calc sweepBump v * ‖∫ u in (-1 : ℝ)..1, sweepBump u • g v u‖
        ≤ sweepBump v * (c * (∫ u in (-1 : ℝ)..1, sweepBump u * ρ' v u)) :=
          mul_le_mul_of_nonneg_left (hinner v hv) (hb0 v)
      _ = c * (sweepBump v * (∫ u in (-1 : ℝ)..1, sweepBump u * ρ' v u)) := by ring
  have hL1 : IntervalIntegrable (fun v : ℝ =>
      sweepBump v • (∫ u in (-1 : ℝ)..1, sweepBump u • g v u)) volume (-1) 1 := by
    refine wf_intervalIntegrable_of_global_bound' (C := 2 * Cg) ?_ ?_
    · exact (continuous_sweepBump.measurable.aestronglyMeasurable).smul
        hss.aestronglyMeasurable
    · intro v
      rw [norm_smul, Real.norm_of_nonneg (hb0 v)]
      calc sweepBump v * ‖∫ u in (-1 : ℝ)..1, sweepBump u • g v u‖ ≤ 1 * (2 * Cg) :=
            mul_le_mul (wf_sweepBump_le_one v) (hinner_bound v) (norm_nonneg _) zero_le_one
        _ = 2 * Cg := one_mul _
  have hL2 : IntervalIntegrable (fun v : ℝ =>
      c * (sweepBump v * (∫ u in (-1 : ℝ)..1, sweepBump u * ρ' v u))) volume (-1) 1 := by
    refine wf_intervalIntegrable_of_global_bound (C := c * (2 * Cρ')) ?_ ?_
    · exact (measurable_const.mul (continuous_sweepBump.measurable.mul hssρ.measurable)).aestronglyMeasurable
    · intro v
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc0, abs_mul, abs_of_nonneg (hb0 v)]
      have h1 : |∫ u in (-1 : ℝ)..1, sweepBump u * ρ' v u| ≤ 2 * Cρ' := by
        rw [← Real.norm_eq_abs]
        refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := Cρ') (fun u _ => ?_)).trans ?_
        · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hb0 u)]
          calc sweepBump u * |ρ' v u| ≤ 1 * Cρ' :=
                mul_le_mul (wf_sweepBump_le_one u) (hρb v u) (abs_nonneg _) zero_le_one
            _ = Cρ' := one_mul _
        · rw [show |1 - (-1 : ℝ)| = 2 by norm_num]; linarith
      calc c * (sweepBump v * |∫ u in (-1 : ℝ)..1, sweepBump u * ρ' v u|)
          ≤ c * (1 * (2 * Cρ')) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (wf_sweepBump_le_one v) h1 (abs_nonneg _) zero_le_one) hc0
        _ = c * (2 * Cρ') := by ring
  refine ((intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1 : ℝ) ≤ 1)).trans
    (intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1) hL1.norm hL2 hptv)).trans ?_
  exact le_of_eq (intervalIntegral.integral_const_mul c
    (fun v : ℝ => sweepBump v * (∫ u in (-1 : ℝ)..1, sweepBump u * ρ' v u)))


theorem widePhaseForm {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {M₁ M₂ Cv : ℝ} (hM₁ : ∀ t : ℝ, ‖LeanEval.KnotTheory.Quadrisecant.velocity r t‖ ≤ M₁)
    (hM₂0 : 0 ≤ M₂)
    (hM₂ : ∀ x y : ℝ, ‖LeanEval.KnotTheory.Quadrisecant.velocity r x
        - LeanEval.KnotTheory.Quadrisecant.velocity r y‖ ≤ M₂ * |x - y|)
    (hCv0 : 0 ≤ Cv)
    {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hσ₀1 : σ₀ < 1)
    (hτlip : ∀ (lam' σ τ₁ τ₂ : ℝ), 0 < lam' → lam' ≤ 1 / 4 →
        |Work.Drive.wideSig D lam' σ τ₁ - Work.Drive.wideSig D lam' σ τ₂| ≤ 2 * |τ₁ - τ₂|)
    (hσmod : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ (lam' σ τ : ℝ), 0 < lam' → lam' ≤ 1 / 4 →
        |σ - σ₀| ≤ δ → ‖Work.Drive.wideSig D lam' σ τ - Work.Drive.wideSig D lam' σ₀ τ‖ ≤ η)
    (hval : ∀ (lam' σ τ : ℝ), 0 < lam' → lam' ≤ 1 / 4 → 0 < σ → σ ≤ 1 →
        ‖Work.Drive.sweepLoopChamfer r D lam' σ τ - r (Work.Drive.wideSig D lam' σ τ)‖
          ≤ Cv * (lam' * LeanEval.KnotTheory.Quadrisecant.period
              + (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ)) ^ 2)
    (hvel : ∀ (lam' σ τ : ℝ), 0 < lam' → lam' ≤ 1 / 4 → 0 < σ → σ < 1 →
        ‖Work.Drive.chamferVel r D lam' σ τ -
          Work.Drive.wideRho (Work.Drive.sweepW' D σ)
            (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ) lam'
            (Work.Drive.sweepParam τ) •
          LeanEval.KnotTheory.Quadrisecant.velocity r (Work.Drive.wideSig D lam' σ τ)‖
          ≤ M₂ * (1 + LeanEval.KnotTheory.Quadrisecant.period) *
              (lam' + (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ)) *
            Work.Drive.wideRho (Work.Drive.sweepW' D σ)
              (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ) lam'
              (Work.Drive.sweepParam τ))
    {ε lam L : ℝ} (hε : 0 < ε) (hL : 0 < L) (hlam0 : 0 < lam) (hlamL : lam ≤ L)
    (hlam4 : lam ≤ 1 / 4)
    (hvalε : 16 * (Cv + 1) * (lam * LeanEval.KnotTheory.Quadrisecant.period
        + (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ₀)) ^ 2 ≤ ε)
    (hvelε : 16 * (M₂ + 1) * (1 + LeanEval.KnotTheory.Quadrisecant.period) *
        (lam + (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ₀)) ≤ ε) :
    ∃ (δ₁ δ₂ : ℝ) (ψ : ℝ → ℝ),
      0 < δ₁ ∧ δ₁ ≤ L ∧ 0 < δ₂ ∧ δ₂ ≤ L ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
      (∀ t : ℝ, ψ (t + LeanEval.KnotTheory.Quadrisecant.period)
        = ψ t + LeanEval.KnotTheory.Quadrisecant.period) ∧
      (∀ t : ℝ, 0 < deriv ψ t) ∧
      (∀ t : ℝ, ‖Work.Drive.sweepFam r D lam δ₁ δ₂ σ₀ t - r (ψ t)‖ ≤ ε / 2) ∧
      (∀ t : ℝ, ‖deriv (fun u : ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ σ₀ u) t
        - deriv ψ t • LeanEval.KnotTheory.Quadrisecant.velocity r (ψ t)‖
          ≤ (ε / 2) * deriv ψ t) := by
  have hP : 0 < period := period_pos
  have hM₁0 : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0)
  have hlipr : ∀ x y : ℝ, ‖r x - r y‖ ≤ M₁ * |x - y| := by
    intro x y
    rcases le_total x y with hxy | hxy
    · have hcont : ContDiffOn ℝ 1 r (Set.Icc x y) := (hr.smooth.of_le (by simp)).contDiffOn
      have hftc := intervalIntegral.integral_deriv_of_contDiffOn_Icc (f := r) hcont hxy
      have h1 : r x - r y = -(∫ z in x..y, velocity r z) := by
        rw [show (∫ z in x..y, velocity r z) = r y - r x from hftc]
        rw [neg_sub]
      rw [h1, norm_neg, abs_sub_comm]
      exact intervalIntegral.norm_integral_le_of_norm_le_const (C := M₁) (fun z _ => hM₁ z)
    · have hcont : ContDiffOn ℝ 1 r (Set.Icc y x) := (hr.smooth.of_le (by simp)).contDiffOn
      have hftc := intervalIntegral.integral_deriv_of_contDiffOn_Icc (f := r) hcont hxy
      have h1 : r x - r y = ∫ z in y..x, velocity r z := by
        rw [show (∫ z in y..x, velocity r z) = r x - r y from hftc]
      rw [h1]
      exact intervalIntegral.norm_integral_le_of_norm_le_const (C := M₁) (fun z _ => hM₁ z)
  set A : ℝ := M₁ + 2 with hAdef
  set B : ℝ := M₂ + 2 with hBdef
  have hA1 : (1:ℝ) ≤ A := by rw [hAdef]; linarith
  have hB1 : (1:ℝ) ≤ B := by rw [hBdef]; linarith
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA1
  have hB0 : 0 < B := lt_of_lt_of_le one_pos hB1
  have hM₁A : M₁ ≤ A := by rw [hAdef]; linarith
  have hM₂B : M₂ ≤ B := by rw [hBdef]; linarith
  set η : ℝ := min 1 (min (ε / (1024 * A)) (ε / (1024 * B))) with hηdef
  have hη0 : 0 < η := by
    rw [hηdef]
    exact lt_min one_pos (lt_min (by positivity) (by positivity))
  have hηA : η ≤ ε / (1024 * A) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hηB : η ≤ ε / (1024 * B) :=
    (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨δσ, hδσ0, hδσ⟩ := hσmod η hη0
  obtain ⟨δw, hδw0, hδw⟩ := Metric.continuousAt_iff.mp
    ((sweepLoopChamfer_sweepW'_continuous D).continuousAt)
    (3 * ε / (32 * (M₂ * (1 + period) + 1))) (by positivity)
  obtain ⟨δc, hδc0, hδc⟩ := wf_sweepFam_close_loop hr D hlam0 hlam4 (ε / 8) (by positivity)
  set θ : ℝ := min L (min δc (min δσ (min (δw / 2) (min (σ₀ / 2) (min ((1 - σ₀) / 2)
    (min (ε / (1024 * A)) (min (ε / (1024 * B)) 1))))))) with hθdef
  have hθ0 : 0 < θ := by
    rw [hθdef]
    refine lt_min hL (lt_min hδc0 (lt_min hδσ0 (lt_min (by linarith) (lt_min (by linarith)
      (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) one_pos)))))))
  have hθL : θ ≤ L := by rw [hθdef]; exact min_le_left _ _
  have hθc : θ ≤ δc := by
    rw [hθdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hθσ : θ ≤ δσ := by
    rw [hθdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθw : θ ≤ δw / 2 := by
    rw [hθdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hθs0 : θ ≤ σ₀ / 2 := by
    rw [hθdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hθs1 : θ ≤ (1 - σ₀) / 2 := by
    rw [hθdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hθA : θ ≤ ε / (1024 * A) := by
    rw [hθdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _))))))
  have hθB : θ ≤ ε / (1024 * B) := by
    rw [hθdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))))))
  have hθ1 : θ ≤ 1 := by
    rw [hθdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))))))
  have hθσlo : 0 < σ₀ - θ := by linarith
  have hθσhi : σ₀ + θ < 1 := by linarith
  obtain ⟨Vb, hVb0, hVb⟩ := wideEnd_speed_bound hr
  obtain ⟨Rb, hRb0, hRb⟩ := wideEnd_knot_bounded hr.continuous hr.periodic
  obtain ⟨AAb, hAAb0, hAAb⟩ := wf_lift_bound D
  have hTwb0 : 0 ≤ 2 * AAb := by positivity
  have hWb : ∀ s : ℝ, |sweepW' D s| ≤ 2 * AAb := by
    intro s
    have h1 := hAAb s
    have h4 : |tbR D s - taR D s| ≤ |tbR D s| + |taR D s| := by
      simpa using abs_sub_le (tbR D s) 0 (taR D s)
    simp only [sweepW']
    linarith [h1.1, h1.2, h4]
  obtain ⟨Cρ, hCρ0, hCρb⟩ := wf_wideRhoFun_bound D hlam0 hlam4
  have hσv : ∀ v : ℝ, v ∈ Set.Icc (-1 : ℝ) 1 → 0 < σ₀ - θ * v ∧ σ₀ - θ * v < 1 := by
    intro v hv
    constructor <;> nlinarith [hv.1, hv.2, hθ0, hθσlo, hθσhi]
  have hηθ : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ∀ w : ℝ,
      |wideSig D lam (σ₀ - θ * v) w - wideSig D lam σ₀ w| ≤ η := by
    intro v hv w
    have hv1 : |v| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [hv.1], hv.2⟩
    have h : |σ₀ - θ * v - σ₀| ≤ δσ := by
      rw [show σ₀ - θ * v - σ₀ = -(θ * v) by ring, abs_neg, abs_mul, abs_of_nonneg hθ0.le]
      calc θ * |v| ≤ θ * 1 := mul_le_mul_of_nonneg_left hv1 hθ0.le
        _ = θ := mul_one _
        _ ≤ δσ := hθσ
    have h' := hδσ lam (σ₀ - θ * v) w hlam0 hlam4 h
    rwa [Real.norm_eq_abs] at h'
  have hψval : ∀ s : ℝ, |widePhaseApprox D lam θ θ σ₀ s - wideSig D lam σ₀ s|
      ≤ 2 * (η + 2 * θ) := fun s =>
    wf_phaseApprox_value D hlam0 hlam4 hθ0.le hηθ (fun a b => hτlip lam σ₀ a b hlam0 hlam4) s
  have hη4 : M₁ * (2 * (η + 2 * θ)) ≤ ε / 16 := by
    have h8 : η + 2 * θ ≤ 3 * (ε / (1024 * A)) := by linarith [hηA, hθA]
    have h10 : M₁ * (2 * (η + 2 * θ)) ≤ A * (2 * (η + 2 * θ)) :=
      mul_le_mul_of_nonneg_right hM₁A (by positivity)
    have h13 : A * (2 * (η + 2 * θ)) ≤ A * (2 * (3 * (ε / (1024 * A)))) :=
      mul_le_mul_of_nonneg_left (by linarith [h8]) (by positivity)
    have h11 : A * (2 * (3 * (ε / (1024 * A)))) ≤ ε / 16 := by
      have h12 : A * (2 * (3 * (ε / (1024 * A)))) = 6 * ε / 1024 := by
        field_simp <;> ring
      rw [h12]; linarith
    exact le_trans h10 (le_trans h13 h11)
  have hvalb : Cv * (lam * period + (period - sweepW' D σ₀)) ^ 2 ≤ ε / 16 := by
    nlinarith [hvalε, hCv0]
  have hσ₀win : 0 < sweepW' D σ₀ ∧ sweepW' D σ₀ < period := by
    have h := sweepW_pos_lt D ⟨σ₀, hσ₀.le, hσ₀1.le⟩ ⟨hσ₀, hσ₀1⟩
    rwa [wf_sweepW'_eq D hσ₀.le hσ₀1.le]
  have hMp : 0 ≤ M₂ * (1 + period) := by positivity
  have hX0 : 0 ≤ lam + (period - sweepW' D σ₀) := by linarith [hlam0, hσ₀win.2]
  have hX1 : M₂ * (1 + period) * (lam + (period - sweepW' D σ₀)) ≤ ε / 16 := by
    have h1 : M₂ ≤ M₂ + 1 := by linarith
    have h2 : 0 ≤ (1 + period) * (lam + (period - sweepW' D σ₀)) :=
      mul_nonneg (by linarith [hP]) hX0
    have h3 : M₂ * ((1 + period) * (lam + (period - sweepW' D σ₀)))
        ≤ (M₂ + 1) * ((1 + period) * (lam + (period - sweepW' D σ₀))) :=
      mul_le_mul_of_nonneg_right h1 h2
    have h4 : (M₂ + 1) * (1 + period) * (lam + (period - sweepW' D σ₀)) ≤ ε / 16 := by
      linarith [hvelε]
    linarith [h3, h4]
  have hC1 : M₂ * (3 * η + 6 * θ) ≤ 9 * ε / 1024 := by
    have h1 : 3 * η + 6 * θ ≤ 9 * (ε / (1024 * B)) := by
      have ha : 3 * η ≤ 3 * (ε / (1024 * B)) := mul_le_mul_of_nonneg_left hηB (by norm_num)
      have hb : 6 * θ ≤ 6 * (ε / (1024 * B)) := mul_le_mul_of_nonneg_left hθB (by norm_num)
      linarith
    have h5 : M₂ * (9 * (ε / (1024 * B))) ≤ 9 * ε / 1024 := by
      have hq : M₂ / B ≤ 1 := by rw [div_le_one hB0]; linarith [hM₂B]
      have hY : 0 ≤ 9 * ε / 1024 := by positivity
      calc M₂ * (9 * (ε / (1024 * B))) = (9 * ε / 1024) * (M₂ / B) := by ring_nf
        _ ≤ (9 * ε / 1024) * 1 := mul_le_mul_of_nonneg_left hq hY
        _ = 9 * ε / 1024 := by ring
    calc M₂ * (3 * η + 6 * θ) ≤ M₂ * (9 * (ε / (1024 * B))) :=
          mul_le_mul_of_nonneg_left h1 hM₂0
      _ ≤ 9 * ε / 1024 := h5
  refine ⟨θ, θ, widePhaseApprox D lam θ θ σ₀, hθ0, hθL, hθ0, hθL, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_widePhaseApprox D hlam0 hlam4 (ne_of_gt hθ0) (ne_of_gt hθ0)
  · intro t
    exact widePhaseApprox_add_period D hlam0 hlam4 θ θ σ₀ t
  · intro t
    rw [deriv_widePhaseApprox D (ne_of_gt hθ0) hθ0 hlam0 hlam4 (by linarith) (by linarith)]
    exact wf_rateBlur_pos D hlam0 hlam4 hθ0.le hθσlo hθσhi
  · intro t
    have h1 : ‖sweepFam r D lam θ θ σ₀ t - sweepLoopChamfer r D lam σ₀ t‖ ≤ ε / 8 :=
      hδc θ θ hθ0 hθc hθ0 hθc σ₀ t
    have h2 : ‖sweepLoopChamfer r D lam σ₀ t - r (wideSig D lam σ₀ t)‖
        ≤ Cv * (lam * period + (period - sweepW' D σ₀)) ^ 2 :=
      hval lam σ₀ t hlam0 hlam4 hσ₀ hσ₀1.le
    have h4 : ‖r (wideSig D lam σ₀ t) - r (widePhaseApprox D lam θ θ σ₀ t)‖ ≤ ε / 16 := by
      have h6 := hlipr (wideSig D lam σ₀ t) (widePhaseApprox D lam θ θ σ₀ t)
      have h7 : |wideSig D lam σ₀ t - widePhaseApprox D lam θ θ σ₀ t| ≤ 2 * (η + 2 * θ) := by
        have h := hψval t
        rwa [abs_sub_comm] at h
      calc ‖r (wideSig D lam σ₀ t) - r (widePhaseApprox D lam θ θ σ₀ t)‖
          ≤ M₁ * |wideSig D lam σ₀ t - widePhaseApprox D lam θ θ σ₀ t| := h6
        _ ≤ M₁ * (2 * (η + 2 * θ)) := mul_le_mul_of_nonneg_left h7 hM₁0
        _ ≤ ε / 16 := hη4
    calc ‖sweepFam r D lam θ θ σ₀ t - r (widePhaseApprox D lam θ θ σ₀ t)‖
        ≤ ‖sweepFam r D lam θ θ σ₀ t - sweepLoopChamfer r D lam σ₀ t‖
          + ‖sweepLoopChamfer r D lam σ₀ t - r (wideSig D lam σ₀ t)‖
          + ‖r (wideSig D lam σ₀ t) - r (widePhaseApprox D lam θ θ σ₀ t)‖ := by
          have h8 := wf_norm_sub_le_trans (sweepFam r D lam θ θ σ₀ t)
            (sweepLoopChamfer r D lam σ₀ t) (r (widePhaseApprox D lam θ θ σ₀ t))
          have h9 := wf_norm_sub_le_trans (sweepLoopChamfer r D lam σ₀ t)
            (r (wideSig D lam σ₀ t)) (r (widePhaseApprox D lam θ θ σ₀ t))
          linarith
      _ ≤ ε / 8 + ε / 16 + ε / 16 := by linarith
      _ ≤ ε / 2 := by linarith
  · intro τ
    have hdF : HasDerivAt (fun u : ℝ => sweepFam r D lam θ θ σ₀ u)
        (∫ v in (-1 : ℝ)..1, sweepBump v •
          (∫ u in (-1 : ℝ)..1, sweepBump u •
            chamferVel r D lam (σ₀ - θ * v) (τ - θ * u))) τ :=
      sweepFam_double_blur_deriv hr D hlam0 (by linarith) (ne_of_gt hθ0) hθ0
        (by linarith) (by linarith)
    have hdψ : deriv (widePhaseApprox D lam θ θ σ₀) τ = wideRateBlur D lam θ θ σ₀ τ :=
      deriv_widePhaseApprox D (ne_of_gt hθ0) hθ0 hlam0 hlam4 (by linarith) (by linarith) τ
    rw [hdF.deriv, hdψ]
    have hΓb : ∀ v u : ℝ, ‖chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)‖ ≤ doubleBlurLam lam Vb Rb (2 * AAb) := by
      intro v u
      exact doubleBlur_chamferVel_bound hlam0 (by linarith)
        (fun x => by simpa only [velocity] using hVb x) hRb hTwb0 (σ₀ - θ * v) (hWb _) (τ - θ * u)
    have hCΓ0 : 0 ≤ doubleBlurLam lam Vb Rb (2 * AAb) :=
      doubleBlurLam_nonneg hlam0 hVb0.le hRb0 hTwb0
    have hVVb : ‖velocity r (widePhaseApprox D lam θ θ σ₀ τ)‖ ≤ Vb := hVb _
    have hwpos : ∀ v : ℝ, v ∈ Set.Icc (-1 : ℝ) 1 →
        0 < sweepW' D (σ₀ - θ * v) ∧ sweepW' D (σ₀ - θ * v) < period := by
      intro v hv
      obtain ⟨h1, h2⟩ := hσv v hv
      have h := sweepW_pos_lt D ⟨σ₀ - θ * v, h1.le, h2.le⟩ ⟨h1, h2⟩
      rwa [wf_sweepW'_eq D h1.le h2.le]
    have hdev : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
        |wideSig D lam (σ₀ - θ * v) (τ - θ * u) - widePhaseApprox D lam θ θ σ₀ τ| ≤ 3 * η + 6 * θ := by
      intro v hv u hu
      have hu1 : |u| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [hu.1], hu.2⟩
      have e1 : |wideSig D lam (σ₀ - θ * v) (τ - θ * u) - wideSig D lam σ₀ (τ - θ * u)| ≤ η := hηθ v hv (τ - θ * u)
      have e2 : |wideSig D lam σ₀ (τ - θ * u) - wideSig D lam σ₀ τ| ≤ 2 * θ := by
        have h := hτlip lam σ₀ (τ - θ * u) τ hlam0 hlam4
        have h2 : |τ - θ * u - τ| = θ * |u| := by
          rw [show τ - θ * u - τ = -(θ * u) by ring, abs_neg, abs_mul, abs_of_nonneg hθ0.le]
        rw [h2] at h
        nlinarith [h, hu1, hθ0]
      have e3 : |wideSig D lam σ₀ τ - widePhaseApprox D lam θ θ σ₀ τ| ≤ 2 * (η + 2 * θ) :=
        (abs_sub_comm _ _).trans_le (hψval τ)
      have htri := abs_sub_le (wideSig D lam (σ₀ - θ * v) (τ - θ * u)) (wideSig D lam σ₀ (τ - θ * u)) (widePhaseApprox D lam θ θ σ₀ τ)
      have htri2 := abs_sub_le (wideSig D lam σ₀ (τ - θ * u)) (wideSig D lam σ₀ τ) (widePhaseApprox D lam θ θ σ₀ τ)
      linarith
    have hρpos : ∀ v : ℝ, v ∈ Set.Icc (-1 : ℝ) 1 → ∀ u : ℝ, 0 < wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) := by
      intro v hv u
      obtain ⟨hw0, hwP⟩ := hwpos v hv
      have hdl : (0:ℝ) < 1 - 2 * lam := by linarith
      have hd2 : (0:ℝ) < 1 / 2 - lam := by linarith
      simp only [wideRho]
      split_ifs
      · exact mul_pos hdl (div_pos (mul_pos (by norm_num) hw0) period_pos)
      · norm_num
      · exact div_pos (mul_pos hdl (by linarith)) (mul_pos period_pos hd2)
      · norm_num
    have hpoint : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
        ‖chamferVel r D lam (σ₀ - θ * v) (τ - θ * u) - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)‖ ≤ (ε / 2) * wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) := by
      intro v hv u hu
      have hρp : 0 < wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) := hρpos v hv u
      obtain ⟨hσv0, hσv1⟩ := hσv v hv
      have hVel := hvel lam (σ₀ - θ * v) (τ - θ * u) hlam0 hlam4 hσv0 hσv1
      have hv2 : ‖velocity r (wideSig D lam (σ₀ - θ * v) (τ - θ * u)) - velocity r (widePhaseApprox D lam θ θ σ₀ τ)‖ ≤ M₂ * (3 * η + 6 * θ) := by
        have h := hM₂ (wideSig D lam (σ₀ - θ * v) (τ - θ * u)) (widePhaseApprox D lam θ θ σ₀ τ)
        have hd := hdev v hv u hu
        nlinarith [h, hd, hM₂0]
      have h2 : ‖wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (wideSig D lam (σ₀ - θ * v) (τ - θ * u)) - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)‖ ≤ wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) * (M₂ * (3 * η + 6 * θ)) := by
        rw [← smul_sub, norm_smul, Real.norm_of_nonneg hρp.le]
        exact mul_le_mul_of_nonneg_left hv2 hρp.le
      have hsplit : lam + (period - sweepW' D (σ₀ - θ * v))
          = (lam + (period - sweepW' D σ₀)) + (sweepW' D σ₀ - sweepW' D (σ₀ - θ * v)) := by ring
      have hΔ : |sweepW' D σ₀ - sweepW' D (σ₀ - θ * v)|
          ≤ 3 * ε / (32 * (M₂ * (1 + period) + 1)) := by
        have hv1 : |v| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [hv.1], hv.2⟩
        have hd : dist (σ₀ - θ * v) σ₀ < δw := by
          rw [Real.dist_eq, show σ₀ - θ * v - σ₀ = -(θ * v) by ring, abs_neg, abs_mul,
            abs_of_nonneg hθ0.le]
          calc θ * |v| ≤ θ * 1 := mul_le_mul_of_nonneg_left hv1 hθ0.le
            _ = θ := mul_one _
            _ < δw := by linarith [hθw, hδw0]
        have h := hδw hd
        rw [Real.dist_eq, abs_sub_comm] at h
        exact le_of_lt h
      have hB1 : M₂ * (1 + period) * (sweepW' D σ₀ - sweepW' D (σ₀ - θ * v)) ≤ 3 * ε / 32 := by
        refine (mul_le_mul_of_nonneg_left (le_abs_self _) hMp).trans ?_
        exact (mul_le_mul_of_nonneg_left hΔ hMp).trans
          (wf_mul_div_le hMp (by positivity))
      have hξ : M₂ * (1 + period) * (lam + (period - sweepW' D (σ₀ - θ * v)))
          + M₂ * (3 * η + 6 * θ) ≤ ε / 2 := by
        rw [hsplit, mul_add]
        linarith [hX1, hB1, hC1, hε]
      have hdecomp : chamferVel r D lam (σ₀ - θ * v) (τ - θ * u) - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)
          = (chamferVel r D lam (σ₀ - θ * v) (τ - θ * u) - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (wideSig D lam (σ₀ - θ * v) (τ - θ * u))) + (wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (wideSig D lam (σ₀ - θ * v) (τ - θ * u)) - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)) := by
        rw [sub_add_sub_cancel]
      calc ‖chamferVel r D lam (σ₀ - θ * v) (τ - θ * u) - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)‖
          = ‖(chamferVel r D lam (σ₀ - θ * v) (τ - θ * u) - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (wideSig D lam (σ₀ - θ * v) (τ - θ * u))) + (wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (wideSig D lam (σ₀ - θ * v) (τ - θ * u)) - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))‖ := by
            rw [hdecomp]
        _ ≤ ‖chamferVel r D lam (σ₀ - θ * v) (τ - θ * u) - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (wideSig D lam (σ₀ - θ * v) (τ - θ * u))‖ + ‖wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (wideSig D lam (σ₀ - θ * v) (τ - θ * u)) - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)‖ := norm_add_le _ _
        _ ≤ M₂ * (1 + period) * (lam + (period - sweepW' D (σ₀ - θ * v))) * wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u))
              + wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) * (M₂ * (3 * η + 6 * θ)) := add_le_add hVel h2
        _ = wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) * (M₂ * (1 + period) * (lam + (period - sweepW' D (σ₀ - θ * v)))
              + M₂ * (3 * η + 6 * θ)) := by ring
        _ ≤ wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) * (ε / 2) := mul_le_mul_of_nonneg_left hξ hρp.le
        _ = (ε / 2) * wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) := by ring
    have hpairstuff : Measurable (fun p : ℝ × ℝ => (σ₀ - θ * p.1, τ - θ * p.2)) :=
      (measurable_const.sub (measurable_const.mul measurable_fst)).prod
        (measurable_const.sub (measurable_const.mul measurable_snd))
    have hΓm0 : Measurable (fun p : ℝ × ℝ => chamferVel r D lam p.1 p.2) :=
      wideEnd_measurable_chamferVel_joint hr.continuous (hr.smooth.continuous_deriv (by simp)) D lam
    have hΓm : Measurable (fun p : ℝ × ℝ => chamferVel r D lam (σ₀ - θ * p.1) (τ - θ * p.2)) :=
      hΓm0.comp hpairstuff
    have hρm0 : Measurable (fun p : ℝ × ℝ => wideRhoFun D lam (σ₀ - θ * p.1, τ - θ * p.2)) :=
      (measurable_wideRhoFun D lam).comp hpairstuff
    have hρm : Measurable (fun p : ℝ × ℝ =>
        wideRho (sweepW' D (σ₀ - θ * p.1)) (period - sweepW' D (σ₀ - θ * p.1)) lam
          (sweepParam (τ - θ * p.2))) := by
      simpa only [wideRhoFun] using hρm0
    have hgm : Measurable (Function.uncurry (fun (v u : ℝ) =>
        chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)
          - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
              (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))) :=
      hΓm.sub (hρm.smul measurable_const)
    have hgb : ∀ v u : ℝ, ‖chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)
        - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
            (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)‖ ≤ doubleBlurLam lam Vb Rb (2 * AAb) + Cρ * Vb := by
      intro v u
      refine (norm_sub_le _ _).trans ?_
      refine add_le_add (hΓb v u) ?_
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hCρb (σ₀ - θ * v) (τ - θ * u)) (hVb _) (norm_nonneg _) hCρ0
    have hρb : ∀ v u : ℝ, |wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
        (sweepParam (τ - θ * u))| ≤ Cρ := fun v u => hCρb (σ₀ - θ * v) (τ - θ * u)
    have hCg0 : 0 ≤ doubleBlurLam lam Vb Rb (2 * AAb) + Cρ * Vb := by
      have h1 := hCΓ0; have h2 := hCρ0; have h3 := hVb0; positivity
    have hΓint : ∀ v : ℝ, IntervalIntegrable
        (fun u : ℝ => sweepBump u • chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)) volume (-1) 1 := by
      intro v
      refine wf_intervalIntegrable_of_global_bound' (C := doubleBlurLam lam Vb Rb (2 * AAb)) ?_ ?_
      · have hmap : Measurable (fun u : ℝ => ((σ₀ - θ * v, τ - θ * u) : ℝ × ℝ)) :=
          Measurable.prod (f := fun u : ℝ => ((σ₀ - θ * v, τ - θ * u) : ℝ × ℝ))
            measurable_const (measurable_const.sub (measurable_const.mul measurable_id))
        have hΓu : AEStronglyMeasurable
            (fun u : ℝ => chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)) volume :=
          (hΓm0.comp hmap).aestronglyMeasurable
        exact (continuous_sweepBump.measurable.aestronglyMeasurable).smul hΓu
      · intro u
        rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u)]
        exact wf_sweepBump_mul_bound (hΓb v u) u
    have hVint : ∀ v : ℝ, IntervalIntegrable
        (fun u : ℝ => sweepBump u • (wideRho (sweepW' D (σ₀ - θ * v))
          (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)))
        volume (-1) 1 := by
      intro v
      refine wf_intervalIntegrable_of_global_bound' (C := Cρ * Vb) ?_ ?_
      · have hmap : Measurable (fun u : ℝ => ((σ₀ - θ * v, τ - θ * u) : ℝ × ℝ)) :=
          Measurable.prod (f := fun u : ℝ => ((σ₀ - θ * v, τ - θ * u) : ℝ × ℝ))
            measurable_const (measurable_const.sub (measurable_const.mul measurable_id))
        have hρu : AEStronglyMeasurable (fun u : ℝ => wideRho (sweepW' D (σ₀ - θ * v))
            (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u))) volume :=
          ((measurable_wideRhoFun D lam).comp hmap).aestronglyMeasurable
        refine (continuous_sweepBump.measurable.aestronglyMeasurable).smul ?_
        exact hρu.smul measurable_const.aestronglyMeasurable
      · intro u
        rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u), norm_smul, Real.norm_eq_abs]
        calc sweepBump u * (|wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v))
              lam (sweepParam (τ - θ * u))| * ‖velocity r (widePhaseApprox D lam θ θ σ₀ τ)‖)
            ≤ 1 * (Cρ * Vb) :=
              mul_le_mul (wf_sweepBump_le_one u)
                (mul_le_mul (hCρb (σ₀ - θ * v) (τ - θ * u)) hVVb (norm_nonneg _) hCρ0)
                (by positivity) zero_le_one
          _ = Cρ * Vb := one_mul _
    have hssΓ : StronglyMeasurable (fun v : ℝ =>
        ∫ u in (-1 : ℝ)..1, sweepBump u • chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)) := by
      have hL : StronglyMeasurable (Function.uncurry
          (fun (v u : ℝ) => sweepBump u • chamferVel r D lam (σ₀ - θ * v) (τ - θ * u))) := by
        have h : Measurable (fun p : ℝ × ℝ => sweepBump p.2 •
            chamferVel r D lam (σ₀ - θ * p.1) (τ - θ * p.2)) :=
          (continuous_sweepBump.measurable.comp measurable_snd).smul hΓm
        rw [show Function.uncurry (fun (v u : ℝ) => sweepBump u •
              chamferVel r D lam (σ₀ - θ * v) (τ - θ * u))
            = fun p : ℝ × ℝ => sweepBump p.2 •
              chamferVel r D lam (σ₀ - θ * p.1) (τ - θ * p.2) from rfl]
        exact h.stronglyMeasurable
      have h2 := MeasureTheory.StronglyMeasurable.integral_prod_right
        (f := fun (v u : ℝ) => sweepBump u • chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)) hL
        (ν := volume.restrict (Set.uIoc (-1 : ℝ) 1))
      have hfun : (fun v : ℝ => ∫ u : ℝ, sweepBump u •
            chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)
          ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1)))
          = (fun v : ℝ => ∫ u in (-1 : ℝ)..1, sweepBump u •
            chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)) := by
        funext v
        rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
          Set.uIoc_of_le (by norm_num)]
      rw [hfun] at h2
      exact h2
    have hssV : StronglyMeasurable (fun v : ℝ =>
        ∫ u in (-1 : ℝ)..1, sweepBump u • (wideRho (sweepW' D (σ₀ - θ * v))
          (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))) := by
      have hL : StronglyMeasurable (Function.uncurry (fun (v u : ℝ) => sweepBump u •
          (wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
            (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)))) := by
        have h : Measurable (fun p : ℝ × ℝ => sweepBump p.2 •
            (wideRho (sweepW' D (σ₀ - θ * p.1)) (period - sweepW' D (σ₀ - θ * p.1)) lam
              (sweepParam (τ - θ * p.2)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))) :=
          (continuous_sweepBump.measurable.comp measurable_snd).smul (hρm.smul measurable_const)
        rw [show Function.uncurry (fun (v u : ℝ) => sweepBump u •
              (wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
                (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)))
            = fun p : ℝ × ℝ => sweepBump p.2 •
              (wideRho (sweepW' D (σ₀ - θ * p.1)) (period - sweepW' D (σ₀ - θ * p.1)) lam
                (sweepParam (τ - θ * p.2)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)) from rfl]
        exact h.stronglyMeasurable
      have h2 := MeasureTheory.StronglyMeasurable.integral_prod_right
        (f := fun (v u : ℝ) => sweepBump u • (wideRho (sweepW' D (σ₀ - θ * v))
          (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))) hL
        (ν := volume.restrict (Set.uIoc (-1 : ℝ) 1))
      have hfun : (fun v : ℝ => ∫ u : ℝ, sweepBump u •
            (wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
              (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))
          ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1)))
          = (fun v : ℝ => ∫ u in (-1 : ℝ)..1, sweepBump u •
            (wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
              (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))) := by
        funext v
        rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
          Set.uIoc_of_le (by norm_num)]
      rw [hfun] at h2
      exact h2
    have hΓbd : ∀ v : ℝ, ‖∫ u in (-1 : ℝ)..1, sweepBump u •
        chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)‖ ≤ 2 * doubleBlurLam lam Vb Rb (2 * AAb) := by
      intro v
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := doubleBlurLam lam Vb Rb (2 * AAb)) (fun u _ => ?_)).trans ?_
      · rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u)]
        exact wf_sweepBump_mul_bound (hΓb v u) u
      · rw [show |1 - (-1 : ℝ)| = 2 by norm_num]; linarith
    have hVbd : ∀ v : ℝ, ‖∫ u in (-1 : ℝ)..1, sweepBump u • (wideRho (sweepW' D (σ₀ - θ * v))
        (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))‖
        ≤ 2 * (Cρ * Vb) := by
      intro v
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := Cρ * Vb)
        (fun u _ => ?_)).trans ?_
      · rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u), norm_smul, Real.norm_eq_abs]
        calc sweepBump u * (|wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v))
              lam (sweepParam (τ - θ * u))| * ‖velocity r (widePhaseApprox D lam θ θ σ₀ τ)‖)
            ≤ 1 * (Cρ * Vb) :=
              mul_le_mul (wf_sweepBump_le_one u)
                (mul_le_mul (hCρb (σ₀ - θ * v) (τ - θ * u)) hVVb (norm_nonneg _) hCρ0)
                (by positivity) zero_le_one
          _ = Cρ * Vb := one_mul _
      · rw [show |1 - (-1 : ℝ)| = 2 by norm_num]; linarith
    have hL1 : IntervalIntegrable (fun v : ℝ => sweepBump v •
        (∫ u in (-1 : ℝ)..1, sweepBump u •
          chamferVel r D lam (σ₀ - θ * v) (τ - θ * u))) volume (-1) 1 := by
      refine wf_intervalIntegrable_of_global_bound' (C := 2 * doubleBlurLam lam Vb Rb (2 * AAb)) ?_ ?_
      · exact (continuous_sweepBump.measurable.aestronglyMeasurable).smul hssΓ.aestronglyMeasurable
      · intro v
        rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg v)]
        exact wf_sweepBump_mul_bound (hΓbd v) v
    have hV1 : IntervalIntegrable (fun v : ℝ => sweepBump v •
        (∫ u in (-1 : ℝ)..1, sweepBump u • (wideRho (sweepW' D (σ₀ - θ * v))
          (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))))
        volume (-1) 1 := by
      refine wf_intervalIntegrable_of_global_bound' (C := 2 * (Cρ * Vb)) ?_ ?_
      · exact (continuous_sweepBump.measurable.aestronglyMeasurable).smul hssV.aestronglyMeasurable
      · intro v
        rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg v)]
        exact wf_sweepBump_mul_bound (hVbd v) v
    have hkey : (∫ v in (-1 : ℝ)..1, sweepBump v •
          (∫ u in (-1 : ℝ)..1, sweepBump u •
            chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)))
        - wideRateBlur D lam θ θ σ₀ τ • velocity r (widePhaseApprox D lam θ θ σ₀ τ)
        = ∫ v in (-1 : ℝ)..1, sweepBump v •
            (∫ u in (-1 : ℝ)..1, sweepBump u •
              (chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)
                - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
                    (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))) := by
      have hΛV : wideRateBlur D lam θ θ σ₀ τ • velocity r (widePhaseApprox D lam θ θ σ₀ τ)
          = ∫ v in (-1 : ℝ)..1, sweepBump v •
              (∫ u in (-1 : ℝ)..1, sweepBump u •
                (wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
                  (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))) := by
        rw [wideRateBlur]
        exact wf_double_scalar_smul sweepBump
          (fun v u => wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
            (sweepParam (τ - θ * u))) (velocity r (widePhaseApprox D lam θ θ σ₀ τ))
      rw [hΛV, ← intervalIntegral.integral_sub hL1 hV1]
      refine intervalIntegral.integral_congr (fun v _ => ?_)
      have hinner : (∫ u in (-1 : ℝ)..1, sweepBump u •
            chamferVel r D lam (σ₀ - θ * v) (τ - θ * u))
          - (∫ u in (-1 : ℝ)..1, sweepBump u •
              (wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
                (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)))
          = ∫ u in (-1 : ℝ)..1, sweepBump u •
              (chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)
                - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
                    (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)) := by
        rw [← intervalIntegral.integral_sub (hΓint v) (hVint v)]
        exact intervalIntegral.integral_congr (fun u _ => (smul_sub (sweepBump u) _ _).symm)
      rw [← smul_sub, hinner]
    rw [hkey, wideRateBlur]
    exact wf_double_norm_le (g := fun (v u : ℝ) => chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)
          - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
              (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))
      (ρ' := fun (v u : ℝ) => wideRho (sweepW' D (σ₀ - θ * v))
        (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)))
      (c := ε / 2) (Cg := doubleBlurLam lam Vb Rb (2 * AAb) + Cρ * Vb) (Cρ' := Cρ)
      hgm hgb hρm hρb hCg0 (by linarith) hpoint

end

end Work.Drive
