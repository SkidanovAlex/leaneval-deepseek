import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Submission.Work.BoseBoxFock.SqrtKin.heatK_t_rpow_swap
import Submission.Work.BoseBoxFock.SqrtKin.heat_ft_p
import Submission.Work.BoseBoxFock.SqrtKin.kinFT_gauss_integrable
import Submission.Work.BoseBoxFock.SqrtKin.subordination_t_p_swap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sqrtKin_diffForm`

The identity
`(2π)^{-3}∫_p ‖p‖‖kinFT g p‖² = (2π²)^{-1}∬ ‖x−y‖^{−4}‖g x − g y‖²`
for `g : ℝ³ → ℂ` smooth with compact support: the Riesz-kernel (subordination)
representation of the square root of the Laplacian in the corpus's `p`-convention.

Writing `f = kinFT g` and using the vocabulary of `SqrtKinDefs`, the proof has three pieces:

1. **subordination (`t`–`p` Tonelli):** `∫_0^∞ t^{-3/2}(kinMass g − kinHeat g t)dt = 2√π·kinFirst g`
   (from the per-frequency identity `∫_0^∞ t^{-3/2}(1−e^{−t‖p‖²})dt = 2√π‖p‖`);
2. **heat pairing:** for `t > 0`, `kinMass g − kinHeat g t = ⅟₂·diffHeat g t`
   (the position-space representation `kinHeat g t = ∬ heatK t (x−y)(⟪g x, g y⟫).re` of the
   Gaussian multiplier, proved by the weak multiplier Fubini; together with Plancherel for
   `kinMass` and the pointwise identity `‖a−b‖² = ‖a‖² + ‖b‖² − 2Re⟪a,b⟫`);
3. **radial kernel integral + Tonelli:** `∫_0^∞ t^{-3/2}diffHeat g t dt = 2π^{-3/2}diffKernel g`.

The constants combine as `(2√π)^{-1}·⅟₂·2π^{-3/2} = (2π²)^{-1}`.
-/

noncomputable section

open MeasureTheory Filter
open scoped Real Topology BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `(↑(∫ x, h x) : ℂ) = ∫ x, (h x : ℂ)`. -/
lemma ofReal_integral_eq (h : ℝ³ → ℝ) :
    ((∫ x : ℝ³, h x : ℝ) : ℂ) = ∫ x : ℝ³, (h x : ℂ) := by
  simpa using (LinearIsometry.integral_comp_comm (E := ℝ) (F := ℂ) Complex.ofRealLI h).symm

/-! ## 1. Elementary facts about the phases, `kinFT`, and the heat kernel -/

lemma norm_cexp_I_ofReal (r : ℝ) : ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

lemma norm_cexp_neg_I_ofReal (r : ℝ) : ‖Complex.exp (-(Complex.I * (r : ℂ)))‖ = 1 := by
  rw [show -(Complex.I * (r : ℂ)) = Complex.I * ((-r : ℝ) : ℂ) by push_cast; ring]
  exact norm_cexp_I_ofReal (-r)

lemma norm_cexp_I_inner (p x : ℝ³) : ‖Complex.exp (Complex.I * (inner ℝ p x : ℂ))‖ = 1 :=
  norm_cexp_I_ofReal _

lemma norm_cexp_neg_I_inner (p x : ℝ³) :
    ‖Complex.exp (-(Complex.I * (inner ℝ p x : ℂ)))‖ = 1 :=
  norm_cexp_neg_I_ofReal _

/-- The `L^∞` bound for `kinFT`. -/
lemma kinFT_norm_le (u : ℝ³ → ℂ) (p : ℝ³) :
    ‖Submission.BoseGases.kinFT u p‖ ≤ ∫ y, ‖u y‖ := by
  rw [Submission.BoseGases.kinFT]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae
  filter_upwards with y
  rw [norm_mul, norm_cexp_neg_I_inner, one_mul]

/-- **The conjugate Fourier identity**: `conj(kinFT u p) = ∫ x, conj(u x)·e^{i⟪p,x⟫}`. -/
lemma conj_kinFT_eq_integral (u : ℝ³ → ℂ) (p : ℝ³) :
    (starRingEnd ℂ) (Submission.BoseGases.kinFT u p)
      = ∫ x, (starRingEnd ℂ) (u x) * Complex.exp (Complex.I * (inner ℝ p x : ℂ)) := by
  rw [Submission.BoseGases.kinFT, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  rw [map_mul, ← Complex.exp_conj]
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul, neg_neg]
  ring

/-- `(↑(‖z‖²) : ℂ) = conj z * z`. -/
lemma ofReal_norm_sq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = (starRingEnd ℂ) z * z := by
  have h : (Complex.normSq z : ℂ) = (starRingEnd ℂ) z * z := Complex.normSq_eq_conj_mul_self
  rw [← h, Complex.normSq_eq_norm_sq]

/-- `‖(r : ℂ)‖ = r` for `r ≥ 0`. -/
lemma norm_ofReal_complex {r : ℝ} (hr : 0 ≤ r) : ‖(r : ℂ)‖ = r := by
  have h1 : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq (r : ℂ), Complex.normSq_ofReal]
    ring
  nlinarith [norm_nonneg (r : ℂ)]

/-- `‖a − b‖² = ‖a‖² + ‖b‖² − 2·Re⟪a, b⟫` on `ℂ`. -/
lemma norm_sub_sq_eq (a b : ℂ) :
    ‖a - b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * (inner ℂ a b).re := by
  have hneg : a - b = -(b - a) := by abel
  rw [hneg, norm_neg, ← Complex.normSq_eq_norm_sq (b - a), Complex.normSq_sub,
    Complex.normSq_eq_norm_sq b, Complex.normSq_eq_norm_sq a, RCLike.inner_apply',
    mul_comm b (starRingEnd ℂ a)]
  ring

/-- The Gaussian `p ↦ e^{−t‖p‖²}` is integrable for `t > 0`. -/
lemma integrable_exp_neg_mul_norm_sq (t : ℝ) (ht : 0 < t) :
    Integrable (fun p : ℝ³ => Real.exp (-(t * ‖p‖ ^ 2))) := by
  have hpt : (fun p : ℝ³ => Real.exp (-(t * ‖p‖ ^ 2)))
      = fun p : ℝ³ => Real.exp (-t * ‖p‖ ^ 2) := by
    funext p
    congr 1
    ring
  rw [hpt]
  have hval : (∫ v : ℝ³, Real.exp (-t * ‖v‖ ^ 2)) ≠ 0 := by
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℝ³) (b := t) ht]
    positivity
  by_contra hcon
  exact hval (MeasureTheory.integral_undef hcon)

/-- The Gaussian kernel `heatK t` is integrable for `t > 0`. -/
lemma integrable_heatK {t : ℝ} (ht : 0 < t) : Integrable (fun z : ℝ³ => heatK t z) := by
  have hne : (∫ y : ℝ³, heatK t y) ≠ 0 := by
    have h1 : (∫ y : ℝ³, heatK t y) = ∫ y : ℝ³, heatK t (0 - y) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [zero_sub, heatK_even]
    rw [h1, SqrtKin.heatK_mass ht 0]
    norm_num
  by_contra hcon
  exact hne (MeasureTheory.integral_undef hcon)

/-- The translated Gaussian is integrable. -/
lemma integrable_heatK_sub (t : ℝ) (ht : 0 < t) (x : ℝ³) :
    Integrable (fun y : ℝ³ => heatK t (x - y)) := by
  have hne : (∫ y : ℝ³, heatK t (x - y)) ≠ 0 := by
    rw [SqrtKin.heatK_mass ht x]
    norm_num
  by_contra hcon
  exact hne (MeasureTheory.integral_undef hcon)

/-- Mass of the translated Gaussian, in the `x`-orientation. -/
lemma heatK_mass_left {t : ℝ} (ht : 0 < t) (y : ℝ³) : ∫ x : ℝ³, heatK t (x - y) = 1 := by
  rw [show (fun x : ℝ³ => heatK t (x - y)) = fun x : ℝ³ => heatK t (y - x) by
    funext x; rw [show x - y = -(y - x) by abel, heatK_even]]
  exact SqrtKin.heatK_mass ht y

lemma integrable_heatK_sub' (t : ℝ) (ht : 0 < t) (y : ℝ³) :
    Integrable (fun x : ℝ³ => heatK t (x - y)) := by
  have hne : (∫ x : ℝ³, heatK t (x - y)) ≠ 0 := by
    rw [heatK_mass_left ht y]
    norm_num
  by_contra hcon
  exact hne (MeasureTheory.integral_undef hcon)

lemma heatK_bound {t : ℝ} (ht : 0 < t) (z : ℝ³) :
    heatK t z ≤ (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) := by
  unfold heatK
  refine mul_le_of_le_one_right (Real.rpow_nonneg (by positivity) _) ?_
  rw [Real.exp_le_one_iff]
  have : 0 ≤ ‖z‖ ^ 2 / (4 * t) := by positivity
  linarith

/-- `‖kinFT g‖²` is integrable. -/
lemma integrable_kinFT_sq {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    Integrable (fun p : ℝ³ => ‖Submission.BoseGases.kinFT g p‖ ^ 2) :=
  SqrtKin.kinFT_sq_integrable hg hgc

/-- `‖g‖²` is integrable. -/
lemma integrable_norm_sq {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) : Integrable (fun x : ℝ³ => ‖g x‖ ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := bounded_g hg hgc
  have h1 : Integrable g := integrable_g_of hg hgc
  refine Integrable.mono' (h1.norm.const_mul C) ?_ ?_
  · exact (h1.1.norm).pow 2
  · filter_upwards with x
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith [norm_nonneg (g x), hC x]

/-- The Gaussian-weighted square of `‖kinFT‖` is integrable. -/
lemma integrable_heat_kinFT_sq {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) {t : ℝ} (ht : 0 < t) :
    Integrable (fun p : ℝ³ =>
      Real.exp (-(t * ‖p‖ ^ 2)) * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  have hG : Integrable (fun p : ℝ³ => Real.exp (-(t * ‖p‖ ^ 2))) :=
    integrable_exp_neg_mul_norm_sq t ht
  refine Integrable.mono' (hG.const_mul ((∫ y, ‖g y‖) ^ 2)) ?_ ?_
  · exact hG.aestronglyMeasurable.mul (integrable_kinFT_sq hg hgc).1
  · filter_upwards with p
    have h1 := kinFT_norm_le g p
    have h2 : (0 : ℝ) ≤ ∫ y, ‖g y‖ := integral_nonneg fun y => norm_nonneg _
    have h3 : (0 : ℝ) ≤ Real.exp (-(t * ‖p‖ ^ 2)) := Real.exp_nonneg _
    rw [Real.norm_of_nonneg (by positivity)]
    have h4 : ‖Submission.BoseGases.kinFT g p‖ ^ 2 ≤ (∫ y, ‖g y‖) ^ 2 := by
      nlinarith [norm_nonneg (Submission.BoseGases.kinFT g p)]
    calc Real.exp (-(t * ‖p‖ ^ 2)) * ‖Submission.BoseGases.kinFT g p‖ ^ 2
        ≤ Real.exp (-(t * ‖p‖ ^ 2)) * (∫ y, ‖g y‖) ^ 2 :=
          mul_le_mul_of_nonneg_left h4 h3
      _ = (∫ y, ‖g y‖) ^ 2 * Real.exp (-(t * ‖p‖ ^ 2)) := by ring

/-! ## 2. The weak multiplier Fubini -/

lemma integrable_uncurry_conj_mul {u : ℝ³ → ℂ} (hu : Integrable u) {c : ℝ³ → ℂ}
    (hc : Integrable c) :
    Integrable (Function.uncurry (fun x p : ℝ³ => (starRingEnd ℂ) (u x) *
        (Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * c p))) (volume.prod volume) := by
  have hnorm : ∀ x p : ℝ³,
      ‖(starRingEnd ℂ) (u x) * (Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * c p)‖
        = ‖u x‖ * ‖c p‖ := by
    intro x p
    simp only [norm_mul, Complex.norm_conj, norm_cexp_I_inner, one_mul]
  refine Integrable.mono' (hu.norm.mul_prod hc.norm) ?_ ?_
  · have h1 : AEStronglyMeasurable (fun q : ℝ³ × ℝ³ => (starRingEnd ℂ) (u q.1))
        (volume.prod volume) := (hu.1.comp_fst).star
    have h2 : Continuous (fun q : ℝ³ × ℝ³ =>
        Complex.exp (Complex.I * (inner ℝ q.2 q.1 : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_snd.prodMk continuous_fst))))
    exact h1.mul (h2.aestronglyMeasurable.mul (hc.1.comp_snd))
  · filter_upwards with q
    obtain ⟨x, p⟩ := q
    exact le_of_eq (hnorm x p)

/-- Integrability of the `x`-integrand of the weak multiplier Fubini. -/
lemma integrable_conj_mul_integral {u : ℝ³ → ℂ} (hu : Integrable u) {c : ℝ³ → ℂ}
    (hc : Integrable c) :
    Integrable (fun x : ℝ³ => (starRingEnd ℂ) (u x) *
        (∫ p, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * c p)) := by
  have h := (integrable_uncurry_conj_mul hu hc).integral_prod_left
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [Function.uncurry]
  rw [MeasureTheory.integral_const_mul]

lemma integral_conj_mul_fubini {u : ℝ³ → ℂ} (hu : Integrable u) {c : ℝ³ → ℂ}
    (hc : Integrable c) :
    (∫ x, (starRingEnd ℂ) (u x) *
        (∫ p, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * c p))
      = ∫ p, (starRingEnd ℂ) (Submission.BoseGases.kinFT u p) * c p := by
  have hInt := integrable_uncurry_conj_mul hu hc
  calc ∫ x, (starRingEnd ℂ) (u x) *
          (∫ p, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * c p)
      = ∫ x, ∫ p, (starRingEnd ℂ) (u x) *
          (Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * c p) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [integral_const_mul]
    _ = ∫ p, ∫ x, (starRingEnd ℂ) (u x) *
          (Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * c p) :=
        integral_integral_swap hInt
    _ = ∫ p, (∫ x, (starRingEnd ℂ) (u x) *
            Complex.exp (Complex.I * (inner ℝ p x : ℂ))) * c p := by
        apply integral_congr_ae
        filter_upwards with p
        rw [← integral_mul_const]
        apply integral_congr_ae
        filter_upwards with x
        ring
    _ = ∫ p, (starRingEnd ℂ) (Submission.BoseGases.kinFT u p) * c p := by
        apply integral_congr_ae
        filter_upwards with p
        rw [conj_kinFT_eq_integral u p]

/-! ## 3. The position-space evaluation of the Gaussian multiplier -/

lemma heat_inner_eval {g : ℝ³ → ℂ} (hgi : Integrable g) {t : ℝ} (ht : 0 < t) (x : ℝ³) :
    (∫ p : ℝ³, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
        ((Real.exp (-(t * ‖p‖ ^ 2)) : ℂ) * Submission.BoseGases.kinFT g p))
      = (((2 * Real.pi) ^ 3 : ℝ) : ℂ) * ∫ y : ℝ³, (heatK t (x - y) : ℂ) * g y := by
  have hG : Integrable (fun p : ℝ³ => Real.exp (-(t * ‖p‖ ^ 2))) :=
    integrable_exp_neg_mul_norm_sq t ht
  set Φ : ℝ³ → ℝ³ → ℂ := fun p y =>
    Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
      ((Real.exp (-(t * ‖p‖ ^ 2)) : ℂ) *
        (Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * g y)) with hΦ
  have hstep1 : (∫ p : ℝ³, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
        ((Real.exp (-(t * ‖p‖ ^ 2)) : ℂ) * Submission.BoseGases.kinFT g p))
      = ∫ p, ∫ y, Φ p y := by
    apply integral_congr_ae
    filter_upwards with p
    rw [Submission.BoseGases.kinFT]
    have h1 : (∫ y, Φ p y) = Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
        ((Real.exp (-(t * ‖p‖ ^ 2)) : ℂ) *
          ∫ y, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * g y) := by
      simp only [hΦ]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [h1]
  have hnorm : ∀ p y : ℝ³, ‖Φ p y‖ = Real.exp (-(t * ‖p‖ ^ 2)) * ‖g y‖ := by
    intro p y
    have h1 : Φ p y = ((Real.exp (-(t * ‖p‖ ^ 2)) : ℂ)) *
        ((Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
          Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))) * g y) := by
      rw [hΦ]
      ring
    have h2 : ‖(Real.exp (-(t * ‖p‖ ^ 2)) : ℂ)‖ = Real.exp (-(t * ‖p‖ ^ 2)) :=
      norm_ofReal_complex (Real.exp_nonneg _)
    rw [h1, norm_mul, h2, norm_mul, norm_mul, norm_cexp_I_inner, norm_cexp_neg_I_inner,
      one_mul, one_mul]
  have hJoint : Integrable (Function.uncurry Φ) (volume.prod volume) := by
    refine Integrable.mono' (hG.norm.mul_prod hgi.norm) ?_ ?_
    · have h1 : Continuous (fun q : ℝ³ × ℝ³ =>
          Complex.exp (Complex.I * (inner ℝ q.1 x : ℂ))) := by fun_prop
      have h2 : Continuous (fun q : ℝ³ × ℝ³ => (Real.exp (-(t * ‖q.1‖ ^ 2)) : ℂ)) := by
        fun_prop
      have h3 : Continuous (fun q : ℝ³ × ℝ³ =>
          Complex.exp (-(Complex.I * (inner ℝ q.1 q.2 : ℂ)))) := by fun_prop
      have hΦ' : Function.uncurry Φ = fun q : ℝ³ × ℝ³ =>
          Complex.exp (Complex.I * (inner ℝ q.1 x : ℂ)) *
            ((Real.exp (-(t * ‖q.1‖ ^ 2)) : ℂ) *
              (Complex.exp (-(Complex.I * (inner ℝ q.1 q.2 : ℂ))) * g q.2)) := by
        funext q
        obtain ⟨p, y⟩ := q
        simp only [Function.uncurry_apply_pair, hΦ]
      rw [hΦ']
      exact h1.aestronglyMeasurable.mul (h2.aestronglyMeasurable.mul
        (h3.aestronglyMeasurable.mul hgi.1.comp_snd))
    · filter_upwards with q
      obtain ⟨p, y⟩ := q
      rw [Function.uncurry_apply_pair, hnorm p y, Real.norm_of_nonneg (Real.exp_nonneg _)]
  have hstep2 : (∫ p, ∫ y, Φ p y) = ∫ y, ∫ p, Φ p y := integral_integral_swap hJoint
  have hstep3 : (∫ y, ∫ p, Φ p y)
      = ∫ y, ((((2 * Real.pi) ^ 3 : ℝ) : ℂ) * ((heatK t (x - y) : ℂ) * g y)) := by
    apply integral_congr_ae
    filter_upwards with y
    have hpt : ∀ p : ℝ³, Φ p y
        = (Complex.exp (Complex.I * (inner ℝ p (x - y) : ℂ)) *
            (Real.exp (-(t * ‖p‖ ^ 2)) : ℂ)) * g y := by
      intro p
      have hexp : Complex.exp (Complex.I * (inner ℝ p (x - y) : ℂ)) =
          Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
            Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) := by
        rw [← Complex.exp_add]
        congr 1
        rw [inner_sub_right]
        push_cast
        ring
      simp only [hΦ, hexp]
      ring
    rw [show (∫ p, Φ p y) = ∫ p,
        (Complex.exp (Complex.I * (inner ℝ p (x - y) : ℂ)) *
            (Real.exp (-(t * ‖p‖ ^ 2)) : ℂ)) * g y from
      integral_congr_ae (Eventually.of_forall hpt)]
    rw [MeasureTheory.integral_mul_const, SqrtKin.heat_ft_p ht (x - y)]
    push_cast
    ring
  rw [hstep1, hstep2, hstep3, MeasureTheory.integral_const_mul]

/-! ## 4. The pairing identity `kinHeat = ∬ heatK·⟪g x, g y⟫.re` -/

lemma kinHeat_eq_double {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) {t : ℝ} (ht : 0 < t) :
    kinHeat g t = ∫ x : ℝ³, ∫ y : ℝ³, heatK t (x - y) * (inner ℂ (g x) (g y)).re := by
  have hgi : Integrable g := integrable_g_of hg hgc
  set c : ℝ³ → ℂ := fun p => (Real.exp (-(t * ‖p‖ ^ 2)) : ℂ) *
    Submission.BoseGases.kinFT g p with hcdef
  have hc : Integrable c := by
    rw [hcdef]; exact SqrtKin.kinFT_gauss_integrable hg hgc ht
  have key := integral_conj_mul_fubini (u := g) hgi (c := c) hc
  have hintx := integrable_conj_mul_integral (u := g) hgi (c := c) hc
  -- momentum side
  have hRHS : (∫ p, (starRingEnd ℂ) (Submission.BoseGases.kinFT g p) * c p)
      = (((2 * Real.pi) ^ 3 * kinHeat g t : ℝ) : ℂ) := by
    have hInt : Integrable (fun p : ℝ³ =>
        Real.exp (-(t * ‖p‖ ^ 2)) * ‖Submission.BoseGases.kinFT g p‖ ^ 2) :=
      integrable_heat_kinFT_sq hg hgc ht
    have hpt : ∀ p : ℝ³, (starRingEnd ℂ) (Submission.BoseGases.kinFT g p) * c p
        = ((Real.exp (-(t * ‖p‖ ^ 2)) * ‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ) := by
      intro p
      rw [hcdef, Complex.ofReal_mul, ofReal_norm_sq]
      ring
    rw [show (∫ p, (starRingEnd ℂ) (Submission.BoseGases.kinFT g p) * c p)
        = ∫ p, ((Real.exp (-(t * ‖p‖ ^ 2)) *
            ‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ) from
      integral_congr_ae (Eventually.of_forall hpt)]
    rw [← ofReal_integral_eq (fun p : ℝ³ =>
      Real.exp (-(t * ‖p‖ ^ 2)) * ‖Submission.BoseGases.kinFT g p‖ ^ 2)]
    congr 1
    rw [kinHeat]
    have hne : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0 := by positivity
    field_simp
  -- position side
  have hLHS : (∫ x, (starRingEnd ℂ) (g x) *
        (∫ p, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * c p))
      = (((2 * Real.pi) ^ 3 : ℝ) : ℂ) *
          ∫ x, (starRingEnd ℂ) (g x) * (∫ y, (heatK t (x - y) : ℂ) * g y) := by
    have h1 : ∀ x : ℝ³, (starRingEnd ℂ) (g x) *
          (∫ p, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * c p)
        = (((2 * Real.pi) ^ 3 : ℝ) : ℂ) *
            ((starRingEnd ℂ) (g x) * (∫ y, (heatK t (x - y) : ℂ) * g y)) := by
      intro x
      rw [hcdef, heat_inner_eval hgi ht x]
      ring
    rw [show (∫ x, (starRingEnd ℂ) (g x) *
          (∫ p, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * c p))
        = ∫ x, (((2 * Real.pi) ^ 3 : ℝ) : ℂ) *
            ((starRingEnd ℂ) (g x) * (∫ y, (heatK t (x - y) : ℂ) * g y)) from
      integral_congr_ae (Eventually.of_forall h1)]
    rw [MeasureTheory.integral_const_mul]
  have hD : (∫ x, (starRingEnd ℂ) (g x) * (∫ y, (heatK t (x - y) : ℂ) * g y))
      = ((kinHeat g t : ℝ) : ℂ) := by
    have h3 : (((2 * Real.pi) ^ 3 : ℝ) : ℂ) *
          (∫ x, (starRingEnd ℂ) (g x) * (∫ y, (heatK t (x - y) : ℂ) * g y))
        = (((2 * Real.pi) ^ 3 : ℝ) : ℂ) * ((kinHeat g t : ℝ) : ℂ) := by
      refine (hLHS.symm.trans (key.trans hRHS)).trans ?_
      rw [Complex.ofReal_mul]
    refine mul_left_cancel₀ ?_ h3
    simp [Complex.ofReal_eq_zero, Real.pi_ne_zero]
  have hDre : (∫ x, (starRingEnd ℂ) (g x) * (∫ y, (heatK t (x - y) : ℂ) * g y)).re
      = kinHeat g t := by
    rw [hD, Complex.ofReal_re]
  have hne3 : ((((2 * Real.pi) ^ 3 : ℝ) : ℂ)) ≠ 0 := by
    simp [Complex.ofReal_eq_zero, Real.pi_ne_zero]
  have hintD : Integrable (fun x : ℝ³ => (starRingEnd ℂ) (g x) *
      (∫ y : ℝ³, (heatK t (x - y) : ℂ) * g y)) := by
    have h2 : Integrable (fun x : ℝ³ => (starRingEnd ℂ) (g x) *
        ((((2 * Real.pi) ^ 3 : ℝ) : ℂ) * (∫ y : ℝ³, (heatK t (x - y) : ℂ) * g y))) := by
      refine hintx.congr (Eventually.of_forall fun x => ?_)
      simp only []
      rw [hcdef, heat_inner_eval hgi ht x]
    have h3 : Integrable (fun x : ℝ³ => (((2 * Real.pi) ^ 3 : ℝ) : ℂ) *
        ((starRingEnd ℂ) (g x) * (∫ y : ℝ³, (heatK t (x - y) : ℂ) * g y))) :=
      h2.congr (Eventually.of_forall fun x => by simp only []; ring)
    refine (h3.const_mul ((((2 * Real.pi) ^ 3 : ℝ) : ℂ))⁻¹).congr
      (Eventually.of_forall fun x => ?_)
    simp only []
    rw [← mul_assoc, inv_mul_cancel₀ hne3, one_mul]
  rw [← hDre, ← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hintD]
  apply integral_congr_ae
  filter_upwards with x
  have hinty : Integrable (fun y : ℝ³ =>
      (heatK t (x - y) : ℂ) * ((starRingEnd ℂ) (g x) * g y)) := by
    have hcont : Continuous (fun y : ℝ³ => (heatK t (x - y) : ℂ)) :=
      Complex.continuous_ofReal.comp ((heatK_continuous ht).comp
        (continuous_const.sub continuous_id))
    refine Integrable.mono' ((hgi.norm.const_mul ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2))).const_mul
      ‖g x‖) ?_ ?_
    · exact hcont.aestronglyMeasurable.mul (hgi.1.const_mul ((starRingEnd ℂ) (g x)))
    · filter_upwards with y
      rw [norm_mul, norm_ofReal_complex (heatK_nonneg ht.le (x - y)),
        norm_mul, Complex.norm_conj]
      have h1 : heatK t (x - y) ≤ (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) := heatK_bound ht (x - y)
      calc heatK t (x - y) * (‖g x‖ * ‖g y‖)
          ≤ (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * (‖g x‖ * ‖g y‖) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = ‖g x‖ * ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * ‖g y‖) := by ring
  have h1 : (starRingEnd ℂ) (g x) * (∫ y, (heatK t (x - y) : ℂ) * g y)
      = ∫ y, (heatK t (x - y) : ℂ) * ((starRingEnd ℂ) (g x) * g y) := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    ring
  rw [h1, ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hinty]
  apply integral_congr_ae
  filter_upwards with y
  rw [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  congr 1
  rw [RCLike.inner_apply']

/-! ## 5. Plancherel and the algebra -/

lemma kinMass_plancherel {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) : kinMass g = ∫ x : ℝ³, ‖g x‖ ^ 2 := by
  have hco : ⇑(hgc.toSchwartzMap hg) = g := funext (hgc.toSchwartzMap_toFun hg)
  have h := Work.BoseKinLoc.NeuFrac.plancherel_pconv_schwartz (hgc.toSchwartzMap hg)
  rw [hco] at h
  simpa only [kinMass] using h

/-- Mixed integrability of the heat kernel against an `L¹` weight. -/
lemma heatK_prod_integrable {h : ℝ³ → ℝ} (hh : Integrable h) {t : ℝ} (ht : 0 < t) :
    Integrable (fun q : ℝ³ × ℝ³ => heatK t (q.1 - q.2) * h q.2) (volume.prod volume) := by
  have h := Integrable.convolution_integrand (μ := volume) (ν := volume)
    (L := ContinuousLinearMap.mul ℝ ℝ) (f := h) (g := fun z : ℝ³ => heatK t z)
    hh (integrable_heatK ht)
  simpa [ContinuousLinearMap.mul_apply, Function.uncurry, mul_comm] using h

lemma heatMass_left {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) {t : ℝ} (ht : 0 < t) :
    (∫ x : ℝ³, ∫ y : ℝ³, heatK t (x - y) * ‖g x‖ ^ 2) = kinMass g := by
  rw [kinMass_plancherel hg hgc]
  apply integral_congr_ae
  filter_upwards with x
  rw [MeasureTheory.integral_mul_const, SqrtKin.heatK_mass ht x, one_mul]

lemma heatMass_right {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) {t : ℝ} (ht : 0 < t) :
    (∫ x : ℝ³, ∫ y : ℝ³, heatK t (x - y) * ‖g y‖ ^ 2) = kinMass g := by
  rw [kinMass_plancherel hg hgc]
  have hjoint := heatK_prod_integrable (integrable_norm_sq hg hgc) ht
  rw [integral_integral_swap hjoint]
  apply integral_congr_ae
  filter_upwards with y
  rw [MeasureTheory.integral_mul_const, heatK_mass_left ht y, one_mul]

lemma diffHeat_eq {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) {t : ℝ} (ht : 0 < t) :
    diffHeat g t
      = (∫ x : ℝ³, ∫ y : ℝ³, heatK t (x - y) * ‖g x‖ ^ 2)
        + (∫ x : ℝ³, ∫ y : ℝ³, heatK t (x - y) * ‖g y‖ ^ 2)
        - 2 * (∫ x : ℝ³, ∫ y : ℝ³, heatK t (x - y) * (inner ℂ (g x) (g y)).re) := by
  have hgi : Integrable g := integrable_g_of hg hgc
  have hg2 : Integrable (fun x : ℝ³ => ‖g x‖ ^ 2) := integrable_norm_sq hg hgc
  have hF2 : Integrable (fun q : ℝ³ × ℝ³ => heatK t (q.1 - q.2) * ‖g q.2‖ ^ 2)
      (volume.prod volume) := heatK_prod_integrable hg2 ht
  have hF1 : Integrable (fun q : ℝ³ × ℝ³ => heatK t (q.1 - q.2) * ‖g q.1‖ ^ 2)
      (volume.prod volume) := by
    have h := hF2.swap
    refine h.congr (Eventually.of_forall fun q => ?_)
    obtain ⟨x, y⟩ := q
    simp only [Function.comp_apply, Prod.swap_prod_mk]
    rw [show heatK t (y - x) = heatK t (x - y) by
      rw [show y - x = -(x - y) by abel, heatK_even]]
  have hF3 : Integrable (fun q : ℝ³ × ℝ³ =>
      heatK t (q.1 - q.2) * (inner ℂ (g q.1) (g q.2)).re) (volume.prod volume) := by
    have hcont : Continuous (fun q : ℝ³ × ℝ³ => heatK t (q.1 - q.2)) :=
      (heatK_continuous ht).comp (continuous_fst.sub continuous_snd)
    have hinner : AEStronglyMeasurable (fun q : ℝ³ × ℝ³ => (inner ℂ (g q.1) (g q.2)).re)
        (volume.prod volume) :=
      Complex.continuous_re.comp_aestronglyMeasurable
        ((hgi.1.comp_fst).inner (hgi.1.comp_snd))
    refine Integrable.mono' ((hgi.norm.mul_prod hgi.norm).const_mul
      ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2))) ?_ ?_
    · exact hcont.aestronglyMeasurable.mul hinner
    · filter_upwards with q
      obtain ⟨x, y⟩ := q
      rw [norm_mul, Real.norm_of_nonneg (heatK_nonneg ht.le (x - y)), Real.norm_eq_abs]
      have h1 : heatK t (x - y) ≤ (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) := heatK_bound ht (x - y)
      have h2 : |(inner ℂ (g x) (g y)).re| ≤ ‖g x‖ * ‖g y‖ :=
        (RCLike.abs_re_le_norm (inner ℂ (g x) (g y))).trans
          (norm_inner_le_norm (g x) (g y))
      have h3 : (0 : ℝ) ≤ heatK t (x - y) := heatK_nonneg ht.le (x - y)
      have h4 : (0 : ℝ) ≤ (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) :=
        Real.rpow_nonneg (by positivity) _
      calc heatK t (x - y) * |(inner ℂ (g x) (g y)).re|
          ≤ heatK t (x - y) * (‖g x‖ * ‖g y‖) :=
            mul_le_mul_of_nonneg_left h2 h3
        _ ≤ (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * (‖g x‖ * ‖g y‖) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
  have hFsum : Integrable (fun q : ℝ³ × ℝ³ =>
      (heatK t (q.1 - q.2) * ‖g q.1‖ ^ 2 + heatK t (q.1 - q.2) * ‖g q.2‖ ^ 2
        - 2 * (heatK t (q.1 - q.2) * (inner ℂ (g q.1) (g q.2)).re))) (volume.prod volume) :=
    (hF1.add hF2).sub (hF3.const_mul 2)
  have hEq1 : diffHeat g t = ∫ x : ℝ³, ∫ y : ℝ³,
      (heatK t (x - y) * ‖g x‖ ^ 2 + heatK t (x - y) * ‖g y‖ ^ 2
        - 2 * (heatK t (x - y) * (inner ℂ (g x) (g y)).re)) := by
    rw [diffHeat]
    apply integral_congr_ae
    filter_upwards with x
    apply integral_congr_ae
    filter_upwards with y
    rw [norm_sub_sq_eq]
    ring
  have hEq2 : (∫ x : ℝ³, ∫ y : ℝ³,
      (heatK t (x - y) * ‖g x‖ ^ 2 + heatK t (x - y) * ‖g y‖ ^ 2
        - 2 * (heatK t (x - y) * (inner ℂ (g x) (g y)).re)))
      = ∫ q : ℝ³ × ℝ³, (heatK t (q.1 - q.2) * ‖g q.1‖ ^ 2
          + heatK t (q.1 - q.2) * ‖g q.2‖ ^ 2
          - 2 * (heatK t (q.1 - q.2) * (inner ℂ (g q.1) (g q.2)).re)) :=
    (MeasureTheory.integral_prod _ hFsum).symm
  have hEq3 : (∫ q : ℝ³ × ℝ³, (heatK t (q.1 - q.2) * ‖g q.1‖ ^ 2
          + heatK t (q.1 - q.2) * ‖g q.2‖ ^ 2
          - 2 * (heatK t (q.1 - q.2) * (inner ℂ (g q.1) (g q.2)).re)))
      = (∫ q : ℝ³ × ℝ³, heatK t (q.1 - q.2) * ‖g q.1‖ ^ 2)
        + (∫ q : ℝ³ × ℝ³, heatK t (q.1 - q.2) * ‖g q.2‖ ^ 2)
        - 2 * (∫ q : ℝ³ × ℝ³, heatK t (q.1 - q.2) * (inner ℂ (g q.1) (g q.2)).re) := by
    have hstep : (∫ q : ℝ³ × ℝ³, (heatK t (q.1 - q.2) * ‖g q.1‖ ^ 2
        + heatK t (q.1 - q.2) * ‖g q.2‖ ^ 2
        - 2 * (heatK t (q.1 - q.2) * (inner ℂ (g q.1) (g q.2)).re)))
        = (∫ q : ℝ³ × ℝ³, heatK t (q.1 - q.2) * ‖g q.1‖ ^ 2
              + heatK t (q.1 - q.2) * ‖g q.2‖ ^ 2)
          - (∫ q : ℝ³ × ℝ³, 2 * (heatK t (q.1 - q.2) * (inner ℂ (g q.1) (g q.2)).re)) :=
      MeasureTheory.integral_sub
        (f := fun q : ℝ³ × ℝ³ => heatK t (q.1 - q.2) * ‖g q.1‖ ^ 2
          + heatK t (q.1 - q.2) * ‖g q.2‖ ^ 2)
        (g := fun q : ℝ³ × ℝ³ => 2 * (heatK t (q.1 - q.2) * (inner ℂ (g q.1) (g q.2)).re))
        (hF1.add hF2) (hF3.const_mul 2)
    rw [hstep]
    congr 1
    · exact MeasureTheory.integral_add
        (f := fun q : ℝ³ × ℝ³ => heatK t (q.1 - q.2) * ‖g q.1‖ ^ 2)
        (g := fun q : ℝ³ × ℝ³ => heatK t (q.1 - q.2) * ‖g q.2‖ ^ 2) hF1 hF2
    · exact MeasureTheory.integral_const_mul 2
        (fun q : ℝ³ × ℝ³ => heatK t (q.1 - q.2) * (inner ℂ (g q.1) (g q.2)).re)
  have hEq4 : (∫ q : ℝ³ × ℝ³, heatK t (q.1 - q.2) * ‖g q.1‖ ^ 2)
      = ∫ x : ℝ³, ∫ y : ℝ³, heatK t (x - y) * ‖g x‖ ^ 2 :=
    MeasureTheory.integral_prod _ hF1
  have hEq5 : (∫ q : ℝ³ × ℝ³, heatK t (q.1 - q.2) * ‖g q.2‖ ^ 2)
      = ∫ x : ℝ³, ∫ y : ℝ³, heatK t (x - y) * ‖g y‖ ^ 2 :=
    MeasureTheory.integral_prod _ hF2
  have hEq6 : (∫ q : ℝ³ × ℝ³, heatK t (q.1 - q.2) * (inner ℂ (g q.1) (g q.2)).re)
      = ∫ x : ℝ³, ∫ y : ℝ³, heatK t (x - y) * (inner ℂ (g x) (g y)).re :=
    MeasureTheory.integral_prod _ hF3
  rw [hEq1, hEq2, hEq3, hEq4, hEq5, hEq6]

/-- **The heat pairing**: `kinMass g − kinHeat g t = ⅟₂·diffHeat g t` for `t > 0`. -/
lemma pairing_diff {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) {t : ℝ} (ht : 0 < t) :
    kinMass g - kinHeat g t = (1 / 2) * diffHeat g t := by
  rw [diffHeat_eq hg hgc ht, heatMass_left hg hgc ht, heatMass_right hg hgc ht,
    ← kinHeat_eq_double hg hgc ht]
  ring

/-! ## 6. The radial kernel integral, and assembly -/

theorem sqrtKin_diffForm {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
        ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2
      = (2 * Real.pi ^ 2)⁻¹ *
          ∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
            ‖x - y‖ ^ (-(4 : ℝ)) * ‖g x - g y‖ ^ 2 := by
  have hswap := SqrtKin.subordination_t_p_swap hg hgc
  have hker := SqrtKin.heatK_t_rpow_swap hg hgc
  have hstep : (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) * (kinMass g - kinHeat g t))
      = ∫ t in Set.Ioi (0 : ℝ), (1 / 2 : ℝ) * (t ^ (-(3 : ℝ) / 2) * diffHeat g t) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => by
      rw [pairing_diff hg hgc ht]
      ring
  rw [hstep, MeasureTheory.integral_const_mul, hker] at hswap
  have hpi : Real.pi ^ (3 / 2 : ℝ) = Real.pi * Real.sqrt Real.pi := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add Real.pi_pos, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hne : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos_of_pos Real.pi_pos).ne'
  have hconst2 : (2 * Real.sqrt Real.pi)⁻¹ * ((1 / 2 : ℝ) * (2 / Real.pi ^ (3 / 2 : ℝ)))
      = (2 * Real.pi ^ 2)⁻¹ := by
    rw [hpi]
    field_simp [Real.pi_ne_zero, hne]
    try rw [Real.sq_sqrt Real.pi_pos.le]
    try ring
  have h1 : (2 * Real.sqrt Real.pi)⁻¹ * ((2 * Real.sqrt Real.pi) * kinFirst g)
      = (2 * Real.sqrt Real.pi)⁻¹ *
          ((1 / 2 : ℝ) * ((2 / Real.pi ^ (3 / 2 : ℝ)) * diffKernel g)) := by
    rw [hswap.symm]
  have h2 : (2 * Real.sqrt Real.pi)⁻¹ * ((2 * Real.sqrt Real.pi) * kinFirst g)
      = kinFirst g := by
    have hne2 : (2 * Real.sqrt Real.pi) ≠ 0 := by positivity
    rw [← mul_assoc, inv_mul_cancel₀ hne2, one_mul]
  have h3 : (2 * Real.sqrt Real.pi)⁻¹ *
        ((1 / 2 : ℝ) * ((2 / Real.pi ^ (3 / 2 : ℝ)) * diffKernel g))
      = (2 * Real.pi ^ 2)⁻¹ * diffKernel g := by
    rw [show (2 * Real.sqrt Real.pi)⁻¹ *
          ((1 / 2 : ℝ) * ((2 / Real.pi ^ (3 / 2 : ℝ)) * diffKernel g))
        = ((2 * Real.sqrt Real.pi)⁻¹ * ((1 / 2 : ℝ) * (2 / Real.pi ^ (3 / 2 : ℝ))))
          * diffKernel g by ring]
    rw [hconst2]
  have hmain : kinFirst g = (2 * Real.pi ^ 2)⁻¹ * diffKernel g :=
    (h2.symm.trans h1).trans h3
  simpa only [kinFirst, diffKernel] using hmain

end Work.BoseBoxFock
