import Mathlib
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.mfun_props

/-!
# C8 (Kotani theory): the energy-derivative of the `m`-function

Vocabulary for the computation of `∂_ε ℓ` (the Kotani derivative formula).  Since
`E ↦ mfun α lam E y` is holomorphic on `{0 < Im E}`, it has a complex derivative there;
we write

* `mderiv α lam E y = ∂_E mfun α lam E y`;
* `Rfun α lam E y = mderiv α lam E y / mfun α lam E y` (the logarithmic derivative);
* `Hfun α lam E y = mderiv α lam E y / defect α lam E y` (the coboundary function).

The main identity (proved in `Kotani_l5_identity.lean`) is

`Rfun E x = 1/defect E (x+α) - mderiv E (x+α)/defect E (x+α) + mderiv E x/defect E x`

together with the vanishing of the integral of the coboundary term.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Kotani

open Work.TMContract

/-- `m'(E,y) = ∂_E m(E,y)`, the derivative of the `m`-function with respect to the energy. -/
def mderiv (α lam : ℝ) (E : ℂ) (y : ℝ) : ℂ := deriv (fun z : ℂ => mfun α lam z y) E

/-- `R(E,y) = m'(E,y)/m(E,y)`, the logarithmic derivative of the `m`-function in the energy. -/
def Rfun (α lam : ℝ) (E : ℂ) (y : ℝ) : ℂ := mderiv α lam E y / mfun α lam E y

/-- `H(E,y) = m'(E,y)/defect E y`, the coboundary function of (L5). -/
def Hfun (α lam : ℝ) (E : ℂ) (y : ℝ) : ℂ := mderiv α lam E y / defect α lam E y

/-! ## Uniform bounds for the `m`-function -/

/-- Uniform norm bound for `mfun` (uniform in the phase). -/
theorem mfun_norm_le (α lam : ℝ) {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) {E : ℂ} (hE : h ≤ E.im)
    (x : ℝ) : ‖mfun α lam E x‖ ≤ max 1 (‖E‖ + 2 * |lam| + 1 / h) := by
  have hconv : Tendsto (fun n : ℕ => approx α lam E n x) atTop (𝓝 (mfun α lam E x)) :=
    MfunProbs.approx_tendsto_mfun α lam (ε := h) (R := ‖E‖ + 1) (x := x) hh hE (by linarith)
  have h2 : Tendsto (fun n : ℕ => ‖approx α lam E n x‖) atTop (𝓝 ‖mfun α lam E x‖) :=
    continuous_norm.tendsto _ |>.comp hconv
  refine le_of_tendsto h2 ?_
  filter_upwards with n
  exact MfunProbs.approx_norm_le hh hE h1 n x

/-- Uniform lower bound for the imaginary part of `mfun` (uniform in the phase). -/
theorem mfun_im_ge (α lam : ℝ) {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) {E : ℂ} (hE : h ≤ E.im)
    (x : ℝ) : h ≤ (mfun α lam E x).im := by
  have hconv : Tendsto (fun n : ℕ => approx α lam E n x) atTop (𝓝 (mfun α lam E x)) :=
    MfunProbs.approx_tendsto_mfun α lam (ε := h) (R := ‖E‖ + 1) (x := x) hh hE (by linarith)
  have h2 : Tendsto (fun n : ℕ => (approx α lam E n x).im) atTop (𝓝 (mfun α lam E x).im) :=
    Complex.continuous_im.tendsto _ |>.comp hconv
  refine ge_of_tendsto h2 ?_
  filter_upwards with n
  exact (MfunProbs.approx_im_ge hh hE h1 n x).2

/-! ## The defect is `ℍ`-valued -/

theorem defect_im_pos (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) (y : ℝ) :
    0 < (defect α lam E y).im := by
  have h1 : 0 < (mfun α lam E y).im := MfunProbs.mfun_im_pos α lam hE y
  have h2 : 0 < (mfun α lam E (α - y)).im := MfunProbs.mfun_im_pos α lam hE (α - y)
  have h2ne : mfun α lam E (α - y) ≠ 0 := ne_of_apply_ne Complex.im (ne_of_gt h2)
  have h3 : 0 < ‖mfun α lam E (α - y)‖ ^ 2 := pow_pos (norm_pos_iff.mpr h2ne) 2
  rw [defect, sSec, Complex.sub_im, one_div, Complex.inv_im, Complex.normSq_eq_norm_sq]
  have : -(mfun α lam E (α - y)).im / ‖mfun α lam E (α - y)‖ ^ 2 < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos h2) h3
  linarith

theorem defect_ne_zero (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) (y : ℝ) :
    defect α lam E y ≠ 0 :=
  ne_of_apply_ne Complex.im (ne_of_gt (defect_im_pos α lam hE y))

/-- `Im (defect E y) ≥ Im (m(E,y))`, since the subtracted section `s` lies in `-ℍ`. -/
theorem mfun_im_le_defect_im (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) (y : ℝ) :
    (mfun α lam E y).im ≤ (defect α lam E y).im := by
  have h2 : 0 < (mfun α lam E (α - y)).im := MfunProbs.mfun_im_pos α lam hE (α - y)
  have h2ne : mfun α lam E (α - y) ≠ 0 := ne_of_apply_ne Complex.im (ne_of_gt h2)
  have h3 : 0 < ‖mfun α lam E (α - y)‖ ^ 2 := pow_pos (norm_pos_iff.mpr h2ne) 2
  rw [defect, sSec, Complex.sub_im, one_div, Complex.inv_im, Complex.normSq_eq_norm_sq]
  have : -(mfun α lam E (α - y)).im / ‖mfun α lam E (α - y)‖ ^ 2 < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos h2) h3
  linarith

/-! ## Periodicity in the phase -/

theorem mderiv_period (α lam : ℝ) (E : ℂ) (y : ℝ) :
    mderiv α lam E (y + 1) = mderiv α lam E y := by
  have h : (fun z : ℂ => mfun α lam z (y + 1)) = (fun z : ℂ => mfun α lam z y) := by
    funext z; exact MfunProbs.mfun_period α lam z y
  simp only [mderiv, h]

theorem sSec_period (α lam : ℝ) (E : ℂ) (y : ℝ) :
    sSec α lam E (y + 1) = sSec α lam E y := by
  simp only [sSec]
  congr 1
  have h := MfunProbs.mfun_period α lam E (α - y - 1)
  rw [show α - (y + 1) = α - y - 1 by ring]
  rw [show α - y - 1 + 1 = α - y by ring] at h
  exact h.symm

theorem defect_period (α lam : ℝ) (E : ℂ) (y : ℝ) :
    defect α lam E (y + 1) = defect α lam E y := by
  simp only [defect, sSec_period]
  rw [MfunProbs.mfun_period α lam E y]

theorem Hfun_period (α lam : ℝ) (E : ℂ) (y : ℝ) :
    Hfun α lam E (y + 1) = Hfun α lam E y := by
  simp only [Hfun, mderiv_period, defect_period]

theorem Rfun_im_period (α lam : ℝ) (E : ℂ) (y : ℝ) :
    (Rfun α lam E (y + 1)).im = (Rfun α lam E y).im := by
  simp only [Rfun, mderiv_period, MfunProbs.mfun_period α lam E y]

/-! ## Measurability in the phase -/

theorem continuous_mfun_phase (α lam : ℝ) {A : ℂ} (hA : 0 < A.im) :
    Continuous (fun y : ℝ => mfun α lam A y) := by
  have h := (MfunProbs.mfun_continuousOn α lam).comp_continuous
    (continuous_const.prodMk continuous_id) (fun y => hA)
  simpa [Function.comp_def] using h

theorem measurable_mderiv (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) :
    Measurable (fun y : ℝ => mderiv α lam E y) := by
  have hreal : ∀ n : ℕ, ((1:ℂ)/((n:ℂ)+1)).im = 0 := by
    intro n
    have h : (1:ℂ)/((n:ℂ)+1) = (((1:ℝ)/((n:ℝ)+1) : ℝ) : ℂ) := by push_cast; ring
    rw [h]; exact Complex.ofReal_im _
  have hc : Tendsto (fun n : ℕ => (1:ℂ)/((n:ℂ)+1)) atTop (𝓝[≠] (0:ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))
    · filter_upwards with n
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact div_ne_zero one_ne_zero (Nat.cast_add_one_ne_zero n)
  have key : ∀ y : ℝ,
      Tendsto (fun n : ℕ => ((1:ℂ)/((n:ℂ)+1))⁻¹ *
        (mfun α lam (E + (1:ℂ)/((n:ℂ)+1)) y - mfun α lam E y))
        atTop (𝓝 (mderiv α lam E y)) := by
    intro y
    have hdiff : DifferentiableAt ℂ (fun z : ℂ => mfun α lam z y) E :=
      (MfunProbs.mfun_differentiableOn α lam y).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hE)
    have h := (hasDerivAt_iff_tendsto_slope_zero.mp hdiff.hasDerivAt).comp hc
    simpa [mderiv, Function.comp_def, smul_eq_mul] using h
  refine measurable_of_tendsto_metrizable (f := fun n y =>
    ((1:ℂ)/((n:ℂ)+1))⁻¹ * (mfun α lam (E + (1:ℂ)/((n:ℂ)+1)) y - mfun α lam E y)) ?_ ?_
  · intro n
    have h1 : Continuous (fun y : ℝ => mfun α lam (E + (1:ℂ)/((n:ℂ)+1)) y) := by
      apply continuous_mfun_phase α lam
      simp only [Complex.add_im]
      rw [hreal n, add_zero]; exact hE
    have h2 : Continuous (fun y : ℝ => mfun α lam E y) := continuous_mfun_phase α lam hE
    exact (continuous_const.mul (h1.sub h2)).measurable
  · exact tendsto_pi_nhds.mpr key

theorem continuous_defect_phase (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) :
    Continuous (fun y : ℝ => defect α lam E y) := by
  have h1 : Continuous (fun y : ℝ => mfun α lam E y) := continuous_mfun_phase α lam hE
  have h2 : Continuous (fun y : ℝ => mfun α lam E (α - y)) :=
    (continuous_mfun_phase α lam hE).comp (continuous_const.sub continuous_id)
  have h2n : ∀ y, mfun α lam E (α - y) ≠ 0 := fun y =>
    ne_of_apply_ne Complex.im (ne_of_gt (MfunProbs.mfun_im_pos α lam hE (α - y)))
  have hgoal : Continuous (fun y : ℝ => mfun α lam E y - (mfun α lam E (α - y))⁻¹) :=
    h1.sub (h2.inv₀ h2n)
  simpa [defect, sSec, one_div] using hgoal

theorem measurable_Rfun_im (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) :
    Measurable (fun y : ℝ => (Rfun α lam E y).im) := by
  have h1 : Measurable (fun y : ℝ => mderiv α lam E y) := measurable_mderiv α lam E hE
  have h2 : Measurable (fun y : ℝ => mfun α lam E y) :=
    (continuous_mfun_phase α lam hE).measurable
  have h3 : Measurable (fun y : ℝ => mderiv α lam E y / mfun α lam E y) := h1.div h2
  simpa only [Rfun, Function.comp_def] using Complex.continuous_im.measurable.comp h3

theorem measurable_Hfun_im (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) :
    Measurable (fun y : ℝ => (Hfun α lam E y).im) := by
  have h1 : Measurable (fun y : ℝ => mderiv α lam E y) := measurable_mderiv α lam E hE
  have h2 : Measurable (fun y : ℝ => defect α lam E y) :=
    (continuous_defect_phase α lam hE).measurable
  have h3 : Measurable (fun y : ℝ => mderiv α lam E y / defect α lam E y) := h1.div h2
  simpa only [Hfun, Function.comp_def] using Complex.continuous_im.measurable.comp h3

/-! ## A real calculus lemma: the derivative of `log ‖g‖` -/

theorem hasDerivAt_log_norm {g : ℝ → ℂ} {g' : ℂ} {u : ℝ} (hg : HasDerivAt g g' u)
    (hz : g u ∈ Complex.slitPlane) :
    HasDerivAt (fun u => Real.log ‖g u‖) ((g u)⁻¹ * g').re u := by
  have hlog : HasDerivAt (Complex.log ∘ g) ((g u)⁻¹ * g') u :=
    (Complex.hasDerivAt_log hz).comp u hg
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hlog
  simpa [Function.comp_def, Complex.log_re] using h

/-- **Chain rule along the vertical direction.** For `u > 0` the derivative of
`t ↦ log ‖m(E₀ + i t, y)‖` at `u` is `-Im R(E₀ + i u, y)`. -/
theorem hasDerivAt_log_norm_mfun (α lam : ℝ) (E₀ : ℝ) {u : ℝ} (hu : 0 < u) (y : ℝ) :
    HasDerivAt (fun t : ℝ => Real.log ‖mfun α lam ((E₀:ℂ) + (t:ℂ)*Complex.I) y‖)
      (-(Rfun α lam ((E₀:ℂ) + (u:ℂ)*Complex.I) y).im) u := by
  have hEim : 0 < ((E₀:ℂ) + (u:ℂ)*Complex.I).im := by simpa using hu
  have hphi : HasDerivAt (fun t : ℝ => (E₀:ℂ) + (t:ℂ)*Complex.I) Complex.I u := by
    have h1 : HasDerivAt (fun t : ℝ => (t:ℂ)) (1:ℂ) u := by
      simpa using (hasDerivAt_id u).ofReal_comp
    simpa using ((h1.mul_const Complex.I).const_add (E₀:ℂ))
  have hg : HasDerivAt (fun z : ℂ => mfun α lam z y)
      (mderiv α lam ((E₀:ℂ) + (u:ℂ)*Complex.I) y) ((E₀:ℂ) + (u:ℂ)*Complex.I) :=
    ((MfunProbs.mfun_differentiableOn α lam y).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hEim)).hasDerivAt
  have hcomp : HasDerivAt
      ((fun z : ℂ => mfun α lam z y) ∘ (fun t : ℝ => (E₀:ℂ) + (t:ℂ)*Complex.I))
      (mderiv α lam ((E₀:ℂ) + (u:ℂ)*Complex.I) y * Complex.I) u := hg.comp u hphi
  have hz : ((fun z : ℂ => mfun α lam z y) ∘ (fun t : ℝ => (E₀:ℂ) + (t:ℂ)*Complex.I)) u
      ∈ Complex.slitPlane := by
    simp only [Function.comp_def]
    exact Complex.mem_slitPlane_iff.mpr
      (Or.inr (ne_of_gt (MfunProbs.mfun_im_pos α lam hEim y)))
  have h := hasDerivAt_log_norm hcomp hz
  have hval : ((((fun z : ℂ => mfun α lam z y) ∘ (fun t : ℝ => (E₀:ℂ) + (t:ℂ)*Complex.I)) u)⁻¹ *
        (mderiv α lam ((E₀:ℂ) + (u:ℂ)*Complex.I) y * Complex.I)).re
      = -(Rfun α lam ((E₀:ℂ) + (u:ℂ)*Complex.I) y).im := by
    simp only [Function.comp_def, Rfun]
    rw [show (mfun α lam ((E₀:ℂ) + (u:ℂ)*Complex.I) y)⁻¹ *
        (mderiv α lam ((E₀:ℂ) + (u:ℂ)*Complex.I) y * Complex.I)
        = Complex.I * (mderiv α lam ((E₀:ℂ) + (u:ℂ)*Complex.I) y
            / mfun α lam ((E₀:ℂ) + (u:ℂ)*Complex.I) y)
        by rw [div_eq_mul_inv]; ring]
    rw [Complex.mul_re, Complex.I_re, Complex.I_im]
    ring
  rw [hval] at h
  exact h

end Work.TMComp.Kotani
