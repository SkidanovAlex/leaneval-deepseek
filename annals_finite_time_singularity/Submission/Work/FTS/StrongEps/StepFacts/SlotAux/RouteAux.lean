import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.Pointwise
import Submission.Work.FTS.StrongEps.KernAux.hasCompactSupport_partFst_partSnd
import Submission.Work.FTS.StrongEps.KernAux.integral_mul_partFst_eq_neg
import Submission.Work.Blocks.IMC.cs_integral_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StepFacts

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Auxiliary facts for `slot_route_bounds`

The target is a pure weighted Cauchy–Schwarz estimate: the routed integral identity
(`hcomm`) writes `M = ∫ p, K p · G p` with `K` a derivative of the mollifier kernel `Jker ρ ε`
and `G` a shifted slot of the profile `f`; the hypothesis (`hW`) compares the weight at the base
point `(z,θ)` with the shifted one.  Then

  `(M · W)² ≤ (∫ |K|) · ∫ |K| · e^{2c|p|} · (G · W)²`

is `|∫ K G W| ≤ ∫ |K| |G W|` followed by Cauchy–Schwarz with respect to the (nonnegative,
compactly supported) weight `|K|`, and the pointwise comparison
`W₀² ≤ e^{2c|p|}·W²`.

The lemmas below supply (i) the integrability of `p ↦ |K p| · B p` for `B` continuous on the
ball of radius `ε` (`K` is supported there, being a derivative of the compactly supported
`Jker ρ ε`), and (ii) the nonnegativity of the two weights. -/

section Helpers

/-- `p ↦ e^{2c(|p₁|+|p₂|)}` is continuous. -/
lemma srb_continuous_exp_two (c : ℝ) :
    Continuous (fun p : ℝ × ℝ => Real.exp (2 * c * (|p.1| + |p.2|))) := by
  refine Real.continuous_exp.comp (Continuous.mul continuous_const ?_)
  exact (continuous_abs.comp continuous_fst).add (continuous_abs.comp continuous_snd)

/-- The derivative of the second-coordinate slice of a `C¹` function is the Fréchet derivative
applied to the direction `(0,1)`. -/
private lemma srb_deriv_slice_snd_eq_fderiv {F : ℝ × ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ F (z, θ)) :
    deriv (fun t : ℝ => F (z, t)) θ = fderiv ℝ F (z, θ) (0, 1) := by
  have h2 : HasFDerivAt (fun t : ℝ => (z, t)) (ContinuousLinearMap.inr ℝ ℝ ℝ) θ :=
    hasFDerivAt_prodMk_right z θ
  have h3 : HasDerivAt (fun t : ℝ => F (z, t))
      ((fderiv ℝ F (z, θ)) (ContinuousLinearMap.inr ℝ ℝ ℝ 1)) θ :=
    (h.hasFDerivAt.comp θ h2).hasDerivAt
  rw [h3.deriv]; simp

/-- The derivative of the second-coordinate slice of a `C¹` function is continuous. -/
private lemma srb_continuous_deriv_slice_snd {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F) :
    Continuous (fun p : ℝ × ℝ => deriv (fun t : ℝ => F (p.1, t)) p.2) := by
  have h1 : Continuous (fun p : ℝ × ℝ => fderiv ℝ F p (0, 1)) :=
    (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact h1.congr (fun p =>
    (srb_deriv_slice_snd_eq_fderiv (hF.differentiable_one.differentiableAt)).symm)

/-- Off the closed ball of radius `ε` the derivative of the first-coordinate slice of
`Jker ρ ε` vanishes. -/
private lemma srb_deriv_Jker_fst_eq_zero_of_notMem {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ} (hp : p ∉ Metric.closedBall (0 : ℝ × ℝ) ε) :
    deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1 = 0 := by
  have hmax : ε < max |p.1| |p.2| := by
    by_contra hcon
    exact hp (by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        Real.norm_eq_abs]
      exact not_lt.mp hcon)
  rcases lt_or_ge ε |p.1| with h1 | h1
  · -- `ε < |p₁|`: a whole neighbourhood of `p₁` consists of points with `|s| > ε`
    have hev : (fun s : ℝ => Jker ρ ε (s, p.2)) =ᶠ[𝓝 p.1] (fun _ => (0 : ℝ)) := by
      change ∀ᶠ s in 𝓝 p.1, Jker ρ ε (s, p.2) = 0
      rw [Metric.eventually_nhds_iff]
      refine ⟨(|p.1| - ε) / 2, by linarith, fun s hs => ?_⟩
      have hs' : |s - p.1| < (|p.1| - ε) / 2 := by simpa [Real.dist_eq] using hs
      have hgt : ε < |s| := by
        have h3 : |p.1| ≤ |s| + |s - p.1| := by
          calc |p.1| = |s + (p.1 - s)| := by ring_nf
            _ ≤ |s| + |p.1 - s| := abs_add_le _ _
            _ = |s| + |s - p.1| := by rw [abs_sub_comm]
        linarith
      refine Jker_eq_zero_of_not_mem hρ hε ?_
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        Real.norm_eq_abs]
      intro hmem
      have : |s| ≤ ε := le_trans (le_max_left _ _) hmem
      linarith
    rw [hev.deriv_eq, deriv_const]
  · -- `|p₁| ≤ ε`, hence `|p₂| > ε`: the whole slice vanishes
    have h2ε : ε < |p.2| := by
      rcases lt_or_ge ε |p.2| with h | h
      · exact h
      · exact absurd (max_le h1 h) (not_le.mpr hmax)
    have hev : (fun s : ℝ => Jker ρ ε (s, p.2)) = fun _ => (0 : ℝ) := by
      funext s
      refine Jker_eq_zero_of_not_mem hρ hε ?_
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        Real.norm_eq_abs]
      intro hmem
      have : |p.2| ≤ ε := le_trans (le_max_right _ _) hmem
      linarith
    rw [hev, deriv_const]

/-- Off the closed ball of radius `ε` the derivative of the second-coordinate slice of
`Jker ρ ε` vanishes. -/
private lemma srb_deriv_Jker_snd_eq_zero_of_notMem {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ} (hp : p ∉ Metric.closedBall (0 : ℝ × ℝ) ε) :
    deriv (fun t : ℝ => Jker ρ ε (p.1, t)) p.2 = 0 := by
  have hmax : ε < max |p.1| |p.2| := by
    by_contra hcon
    exact hp (by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        Real.norm_eq_abs]
      exact not_lt.mp hcon)
  rcases lt_or_ge ε |p.2| with h1 | h1
  · have hev : (fun t : ℝ => Jker ρ ε (p.1, t)) =ᶠ[𝓝 p.2] (fun _ => (0 : ℝ)) := by
      change ∀ᶠ t in 𝓝 p.2, Jker ρ ε (p.1, t) = 0
      rw [Metric.eventually_nhds_iff]
      refine ⟨(|p.2| - ε) / 2, by linarith, fun t ht => ?_⟩
      have ht' : |t - p.2| < (|p.2| - ε) / 2 := by simpa [Real.dist_eq] using ht
      have hgt : ε < |t| := by
        have h3 : |p.2| ≤ |t| + |t - p.2| := by
          calc |p.2| = |t + (p.2 - t)| := by ring_nf
            _ ≤ |t| + |p.2 - t| := abs_add_le _ _
            _ = |t| + |t - p.2| := by rw [abs_sub_comm]
        linarith
      refine Jker_eq_zero_of_not_mem hρ hε ?_
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        Real.norm_eq_abs]
      intro hmem
      have : |t| ≤ ε := le_trans (le_max_right _ _) hmem
      linarith
    rw [hev.deriv_eq, deriv_const]
  · have h2ε : ε < |p.1| := by
      rcases lt_or_ge ε |p.1| with h | h
      · exact h
      · exact absurd (max_le h h1) (not_le.mpr hmax)
    have hev : (fun t : ℝ => Jker ρ ε (p.1, t)) = fun _ => (0 : ℝ) := by
      funext t
      refine Jker_eq_zero_of_not_mem hρ hε ?_
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        Real.norm_eq_abs]
      intro hmem
      have : |p.1| ≤ ε := le_trans (le_max_left _ _) hmem
      linarith
    rw [hev, deriv_const]

/-- **Integrability against a function continuous on the ball**: the first slice-derivative of
`Jker ρ ε` times a function continuous on the ball of radius `ε` is integrable on all of `ℝ²`
(the derivative factor is supported in that ball). -/
lemma srb_integrable_abs_deriv_fst_mul (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {B : ℝ × ℝ → ℝ}
    (hB : ContinuousOn B (Metric.closedBall (0 : ℝ × ℝ) ε)) :
    Integrable (fun p : ℝ × ℝ => |deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1| * B p) := by
  have hJ : ContDiff ℝ 1 (Jker ρ ε) := Jker_smooth (n := 1) hρ ε
  have hcont : Continuous
      (fun p : ℝ × ℝ => deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1) :=
    Work.FTS.StrongEps.KernAux.continuous_deriv_slice_fst hJ
  have hon : IntegrableOn (fun p : ℝ × ℝ =>
      |deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1| * B p) (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    ((hcont.abs.continuousOn).mul hB).integrableOn_compact (isCompact_closedBall 0 ε)
  exact hon.integrable_of_forall_notMem_eq_zero (fun p hp => by
    rw [srb_deriv_Jker_fst_eq_zero_of_notMem hρ.moll hε hp, abs_zero, zero_mul])

/-- **Integrability against a function continuous on the ball**: the second slice-derivative of
`Jker ρ ε` times a function continuous on the ball of radius `ε` is integrable on all of `ℝ²`. -/
lemma srb_integrable_abs_deriv_snd_mul (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {B : ℝ × ℝ → ℝ}
    (hB : ContinuousOn B (Metric.closedBall (0 : ℝ × ℝ) ε)) :
    Integrable (fun p : ℝ × ℝ => |deriv (fun t : ℝ => Jker ρ ε (p.1, t)) p.2| * B p) := by
  have hJ : ContDiff ℝ 1 (Jker ρ ε) := Jker_smooth (n := 1) hρ ε
  have hcont : Continuous
      (fun p : ℝ × ℝ => deriv (fun t : ℝ => Jker ρ ε (p.1, t)) p.2) :=
    srb_continuous_deriv_slice_snd hJ
  have hon : IntegrableOn (fun p : ℝ × ℝ =>
      |deriv (fun t : ℝ => Jker ρ ε (p.1, t)) p.2| * B p) (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    ((hcont.abs.continuousOn).mul hB).integrableOn_compact (isCompact_closedBall 0 ε)
  exact hon.integrable_of_forall_notMem_eq_zero (fun p hp => by
    rw [srb_deriv_Jker_snd_eq_zero_of_notMem hρ.moll hε hp, abs_zero, zero_mul])

/-- The weight `Wt α z θ = w z · sin(2θ)^{-γ/2}` is nonnegative on the open quadrant. -/
lemma srb_Wt_nonneg (α : ℝ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 ≤ Work.Spaces.Wt α z θ := by
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    le_of_lt (Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1],
      by linarith [hθ.2, Real.pi_pos]⟩)
  simp only [Work.Spaces.Wt, Work.Spaces.w, Work.Spaces.wTheta]
  exact mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg hsin _)

/-- The `η`-weight `w z / sin(2θ)^{η/2}` is nonnegative on the open quadrant. -/
lemma srb_wdiv_nonneg {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    le_of_lt (Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1],
      by linarith [hθ.2, Real.pi_pos]⟩)
  refine div_nonneg ?_ (Real.rpow_nonneg hsin _)
  simp only [Work.Spaces.w]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **The weighted Cauchy–Schwarz core.**  If `M = ∫ p, K p · G p`, the weight `W₀` is
nonnegative and dominated by `e^{c|p|} · W` at every `p`, and the three relevant functions are
integrable, then

  `(M · W₀)² ≤ (∫ |K|) · ∫ |K| · e^{2c|p|} · (G · W)²`.

Proof: `M · W₀ = ∫ p, K p · (G p · W₀)`; `|∫ f| ≤ ∫ |f|`; the pointwise domination
`W₀² ≤ e^{2c|p|} W²` converts `|K|·(G W₀)²` into the majorant; and Cauchy–Schwarz for the
`L²`-pair `√|K|`, `√(|K| (G W₀)²)` gives the two `∫ |K|`-factors. -/
theorem srb_cs_core {K G W : ℝ × ℝ → ℝ} {W₀ c M : ℝ}
    (hW₀ : 0 ≤ W₀)
    (hW : ∀ p : ℝ × ℝ, W₀ ≤ Real.exp (c * (|p.1| + |p.2|)) * W p)
    (hKint : Integrable fun p : ℝ × ℝ => |K p|)
    (hQ : Integrable fun p : ℝ × ℝ =>
      |K p| * Real.exp (2 * c * (|p.1| + |p.2|)) * (G p * W p) ^ 2)
    (hK2 : Integrable fun p : ℝ × ℝ => |K p| * (G p * W₀) ^ 2)
    (hM : M = ∫ p : ℝ × ℝ, K p * G p) :
    (M * W₀) ^ 2 ≤ (∫ p : ℝ × ℝ, |K p|) *
      ∫ p : ℝ × ℝ, |K p| * Real.exp (2 * c * (|p.1| + |p.2|)) * (G p * W p) ^ 2 := by
  -- the pointwise comparison of the two weighted squares
  have hpt : ∀ p : ℝ × ℝ, |K p| * (G p * W₀) ^ 2
      ≤ |K p| * Real.exp (2 * c * (|p.1| + |p.2|)) * (G p * W p) ^ 2 := by
    intro p
    have hE : (0 : ℝ) < Real.exp (c * (|p.1| + |p.2|)) := Real.exp_pos _
    have hEW : 0 ≤ Real.exp (c * (|p.1| + |p.2|)) * W p := le_trans hW₀ (hW p)
    have hWnn : 0 ≤ W p := by
      have := hEW
      rw [mul_comm] at this
      exact nonneg_of_mul_nonneg_left this hE
    have hsq : W₀ ^ 2 ≤ Real.exp (2 * c * (|p.1| + |p.2|)) * (W p) ^ 2 := by
      have h1 : W₀ ^ 2 ≤ (Real.exp (c * (|p.1| + |p.2|)) * W p) ^ 2 :=
        pow_le_pow_left₀ hW₀ (hW p) 2
      have h2 : (Real.exp (c * (|p.1| + |p.2|)) * W p) ^ 2
          = Real.exp (2 * c * (|p.1| + |p.2|)) * (W p) ^ 2 := by
        rw [mul_pow, sq, ← Real.exp_add]
        congr 1
        ring
      rwa [h2] at h1
    calc |K p| * (G p * W₀) ^ 2
        = |K p| * ((G p) ^ 2 * W₀ ^ 2) := by ring_nf
      _ ≤ |K p| * ((G p) ^ 2 * (Real.exp (2 * c * (|p.1| + |p.2|)) * (W p) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (sq_nonneg _))
            (abs_nonneg _)
      _ = |K p| * Real.exp (2 * c * (|p.1| + |p.2|)) * (G p * W p) ^ 2 := by ring
  -- `M · W₀` is the integral against the weight `W₀`
  have hMW : M * W₀ = ∫ p : ℝ × ℝ, K p * (G p * W₀) := by
    rw [hM, ← integral_mul_const W₀ (fun p : ℝ × ℝ => K p * G p)]
    exact integral_congr_ae (Eventually.of_forall fun p => by ring)
  -- Cauchy–Schwarz
  have hcs : |∫ p : ℝ × ℝ, K p * (G p * W₀)|
      ≤ Real.sqrt (∫ p : ℝ × ℝ, |K p|)
        * Real.sqrt (∫ p : ℝ × ℝ, |K p| * (G p * W₀) ^ 2) := by
    have hfm : AEStronglyMeasurable (fun p : ℝ × ℝ => Real.sqrt |K p|) volume :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hKint.aestronglyMeasurable
    have hgm : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Real.sqrt (|K p| * (G p * W₀) ^ 2)) volume :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hK2.aestronglyMeasurable
    have hf2 : Integrable (fun p : ℝ × ℝ => (Real.sqrt |K p|) ^ 2) volume :=
      hKint.congr (Eventually.of_forall fun p => (Real.sq_sqrt (abs_nonneg _)).symm)
    have hg2 : Integrable (fun p : ℝ × ℝ => (Real.sqrt (|K p| * (G p * W₀) ^ 2)) ^ 2) volume :=
      hK2.congr (Eventually.of_forall fun p =>
        (Real.sq_sqrt (mul_nonneg (abs_nonneg _) (sq_nonneg _))).symm)
    have h := Work.Blocks.IMC.cs_integral_mul_le volume hfm hgm hf2 hg2
    have hkey : ∀ p : ℝ × ℝ, Real.sqrt |K p| * Real.sqrt (|K p| * (G p * W₀) ^ 2)
        = |K p * (G p * W₀)| := by
      intro p
      have hs : Real.sqrt (|K p| * (G p * W₀) ^ 2) = Real.sqrt |K p| * |G p * W₀| := by
        rw [Real.sqrt_mul (abs_nonneg (K p)), Real.sqrt_sq_eq_abs]
      rw [hs, ← mul_assoc, Real.mul_self_sqrt (abs_nonneg (K p))]
      simp only [abs_mul]
    rw [show (fun p : ℝ × ℝ => Real.sqrt |K p| * Real.sqrt (|K p| * (G p * W₀) ^ 2))
        = fun p : ℝ × ℝ => |K p * (G p * W₀)| from funext hkey] at h
    have e1 : (∫ x : ℝ × ℝ, (Real.sqrt |K x|) ^ 2) = ∫ x : ℝ × ℝ, |K x| :=
      integral_congr_ae (Eventually.of_forall fun x => Real.sq_sqrt (abs_nonneg _))
    have e2 : (∫ x : ℝ × ℝ, (Real.sqrt (|K x| * (G x * W₀) ^ 2)) ^ 2)
        = ∫ x : ℝ × ℝ, |K x| * (G x * W₀) ^ 2 :=
      integral_congr_ae (Eventually.of_forall fun x =>
        Real.sq_sqrt (mul_nonneg (abs_nonneg _) (sq_nonneg _)))
    rw [e1, e2] at h
    have h' : |(∫ p : ℝ × ℝ, K p * (G p * W₀))|
        ≤ |(∫ p : ℝ × ℝ, |K p * (G p * W₀)|)| := by
      rw [abs_of_nonneg (integral_nonneg fun p => abs_nonneg _)]
      exact abs_integral_le_integral_abs
    exact le_trans h' h
  -- the monotonicity of the second factor
  have hA0 : 0 ≤ ∫ p : ℝ × ℝ, |K p| := integral_nonneg fun p => abs_nonneg _
  have hB0 : 0 ≤ ∫ p : ℝ × ℝ, |K p| * (G p * W₀) ^ 2 :=
    integral_nonneg fun p => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hmono : (∫ p : ℝ × ℝ, |K p| * (G p * W₀) ^ 2)
      ≤ ∫ p : ℝ × ℝ, |K p| * Real.exp (2 * c * (|p.1| + |p.2|)) * (G p * W p) ^ 2 :=
    integral_mono_of_nonneg
      (Eventually.of_forall fun p => mul_nonneg (abs_nonneg _) (sq_nonneg _)) hQ
      (Eventually.of_forall hpt)
  calc (M * W₀) ^ 2 = |M * W₀| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt (∫ p : ℝ × ℝ, |K p|)
          * Real.sqrt (∫ p : ℝ × ℝ, |K p| * (G p * W₀) ^ 2)) ^ 2 := by
        rw [hMW]
        exact pow_le_pow_left₀ (abs_nonneg _) hcs 2
    _ = (∫ p : ℝ × ℝ, |K p|) * (∫ p : ℝ × ℝ, |K p| * (G p * W₀) ^ 2) := by
        rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
    _ ≤ (∫ p : ℝ × ℝ, |K p|)
          * ∫ p : ℝ × ℝ, |K p| * Real.exp (2 * c * (|p.1| + |p.2|)) * (G p * W p) ^ 2 :=
        mul_le_mul_of_nonneg_left hmono hA0

end Helpers

/-- **The `θ`-slot form of the core bound.**  When the routed identity carries a factor `2`
(`D_θ^i(J_ε f) = 2 ∫ K · G`), the bound of `srb_cs_core` acquires a factor `4`. -/
theorem srb_cs_core_four {K G W : ℝ × ℝ → ℝ} {W₀ c I : ℝ}
    (hW₀ : 0 ≤ W₀)
    (hW : ∀ p : ℝ × ℝ, W₀ ≤ Real.exp (c * (|p.1| + |p.2|)) * W p)
    (hKint : Integrable fun p : ℝ × ℝ => |K p|)
    (hQ : Integrable fun p : ℝ × ℝ =>
      |K p| * Real.exp (2 * c * (|p.1| + |p.2|)) * (G p * W p) ^ 2)
    (hK2 : Integrable fun p : ℝ × ℝ => |K p| * (G p * W₀) ^ 2)
    (hI : I = ∫ p : ℝ × ℝ, K p * G p) :
    ((2 * I) * W₀) ^ 2 ≤ 4 * (∫ p : ℝ × ℝ, |K p|) *
      ∫ p : ℝ × ℝ, |K p| * Real.exp (2 * c * (|p.1| + |p.2|)) * (G p * W p) ^ 2 := by
  have key := srb_cs_core hW₀ hW hKint hQ hK2 hI
  calc ((2 * I) * W₀) ^ 2 = 4 * (I * W₀) ^ 2 := by ring
    _ ≤ 4 * ((∫ p : ℝ × ℝ, |K p|) *
          ∫ p : ℝ × ℝ, |K p| * Real.exp (2 * c * (|p.1| + |p.2|)) * (G p * W p) ^ 2) :=
        mul_le_mul_of_nonneg_left key (by norm_num)
    _ = 4 * (∫ p : ℝ × ℝ, |K p|) *
          ∫ p : ℝ × ℝ, |K p| * Real.exp (2 * c * (|p.1| + |p.2|)) * (G p * W p) ^ 2 := by
        ring

end Work.FTS.StrongEps.StepFacts
