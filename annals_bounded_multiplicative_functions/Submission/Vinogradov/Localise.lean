import Submission.Vinogradov.Nikolskii
import Submission.Commons.Analysis.Fourier.exists_invFourier_compact_pos
import Submission.Commons.Analysis.Fourier.fourierIntegral_mul_measure_eq_zero
import Submission.Commons.Analysis.Fourier.integral_mul_conj_eq_zero_of_disjoint_fourier_support

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Complex
open scoped Real BigOperators FourierTransform RealInnerProductSpace Interval

set_option autoImplicit false

/-!
# Localisation weights and the spectral support of the extension operator

This module begins the formalisation of BDG §5 (the `ε`-removal / localisation step) and of the
`L²`-decoupling principle of their §8.  The key object is a *localisation weight*: a weight which
is `≳ 1` on a ball of radius `R` and whose square root is **band-limited with compactly supported
Fourier transform**.  Such a weight is obtained from the (shared-commons) lemma
`Commons.Analysis.Fourier.exists_invFourier_compact_pos`, which supplies a nonnegative Schwartz
function `φ` with `φ ≥ 1` on the unit ball and `φ = 𝓕⁻ψ` for a compactly supported Schwartz `ψ`.

The main computation of the module is the **spectral support** of the products `φ_B · E_J g`:
for a Schwartz function `φ` whose Fourier transform is supported in the ball of radius `ρ`, the
function `x ↦ φ((x−c)/R) · E_{[a,b]}g(x)` has Fourier transform vanishing off the `ρ/R`-neighbourhood
of the arc `γ([a,b])`.  Consequently, two pieces of the extension operator whose arcs are separated
by more than `2ρ/R` are orthogonal in the `L²(ℝᵏ)` sense after multiplication by the same
localisation weight — which is the crux of BDG's proof of the `L²` decoupling (their Lemma 8.2,
eq. (ne89)).
-/

namespace Submission.Vinogradov

noncomputable section
open Classical

/-- **The localisation bump.**  A Schwartz function on `E k` which is the inverse Fourier transform
of a compactly supported Schwartz function and whose real part is `≥ 1` on the unit ball. -/
noncomputable def locBump (k : ℕ) : SchwartzMap (E k) ℂ :=
  Classical.choose (Commons.Analysis.Fourier.exists_invFourier_compact_pos k)

/-- The compactly supported Schwartz function whose inverse Fourier transform is `locBump`. -/
noncomputable def locBumpF (k : ℕ) : SchwartzMap (E k) ℂ :=
  Classical.choose (Classical.choose_spec (Commons.Analysis.Fourier.exists_invFourier_compact_pos k))

theorem locBumpF_spec (k : ℕ) :
    HasCompactSupport (⇑(locBumpF k)) ∧
      (∀ x, 0 ≤ (locBump k x).re) ∧
      (∀ x, ‖x‖ ≤ 1 → 1 ≤ (locBump k x).re) ∧
      (∀ x, locBump k x
        = ∫ ξ, locBumpF k ξ * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((inner ℝ x ξ : ℝ) : ℂ))) :=
  Classical.choose_spec (Classical.choose_spec (Commons.Analysis.Fourier.exists_invFourier_compact_pos k))

lemma locBumpF_cs (k : ℕ) : HasCompactSupport (⇑(locBumpF k)) := (locBumpF_spec k).1

lemma locBump_re_nonneg (k : ℕ) (x : E k) : 0 ≤ (locBump k x).re := (locBumpF_spec k).2.1 x

lemma locBump_re_ge_one (k : ℕ) {x : E k} (hx : ‖x‖ ≤ 1) : 1 ≤ (locBump k x).re :=
  (locBumpF_spec k).2.2.1 x hx

lemma locBump_invFourier (k : ℕ) (x : E k) :
    locBump k x = ∫ ξ, locBumpF k ξ *
      Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((inner ℝ x ξ : ℝ) : ℂ)) :=
  (locBumpF_spec k).2.2.2 x

/-- A radius outside which the Fourier transform of the localisation bump vanishes. -/
noncomputable def locBand (k : ℕ) : ℝ :=
  Classical.choose ((locBumpF_cs k).isBounded.subset_ball (0 : E k))

lemma locBand_spec (k : ℕ) :
    tsupport (⇑(locBumpF k)) ⊆ Metric.ball (0 : E k) (locBand k) :=
  Classical.choose_spec ((locBumpF_cs k).isBounded.subset_ball (0 : E k))

/-- The Fourier transform of the localisation bump is supported in the ball of radius `locBand k`. -/
lemma locBumpF_eq_zero_of_lt (k : ℕ) {z : E k} (hz : locBand k < ‖z‖) : locBumpF k z = 0 := by
  by_contra h
  have hz' : z ∈ tsupport (⇑(locBumpF k)) :=
    subset_tsupport _ (by simpa [Function.mem_support] using h)
  have hmem := locBand_spec k hz'
  rw [Metric.mem_ball, dist_zero_right] at hmem
  exact absurd hmem (not_lt.mpr (le_of_lt hz))

/-- The normalised character `e(a) = exp(2πi a)`. -/
def echar (a : ℝ) : ℂ := Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * (a : ℂ))

lemma echar_norm (a : ℝ) : ‖echar a‖ = 1 := by
  rw [echar, show (((2 * Real.pi : ℂ) * Complex.I) * (a : ℂ))
      = Complex.I * (((2 * Real.pi * a : ℝ)) : ℂ) by push_cast; ring]
  simpa using Commons.Analysis.Complex.norm_exp_mul_I_ofReal (2 * Real.pi * a)

lemma echar_add (a b : ℝ) : echar (a + b) = echar a * echar b := by
  simp only [echar, Complex.ofReal_add, mul_add, Complex.exp_add]

lemma echar_neg (a : ℝ) : echar (-a) = (echar a)⁻¹ := by
  simp only [echar, Complex.ofReal_neg, mul_neg, Complex.exp_neg]

lemma momChar_eq_echar (k : ℕ) (x : E k) (t : ℝ) : momChar k x t = echar (momPhase k x t) := rfl

/-- The localisation weight at centre `c` and scale `R`: `φ((x − c)/R)` where `φ = locBump`. -/
def locWeight (k : ℕ) (c : E k) (R : ℝ) (x : E k) : ℂ := locBump k ((R⁻¹ : ℝ) • (x - c))

lemma locWeight_apply (k : ℕ) (c : E k) (R : ℝ) (x : E k) :
    locWeight k c R x = locBump k ((R⁻¹ : ℝ) • (x - c)) := rfl

lemma locWeight_re_nonneg (k : ℕ) (c : E k) (R : ℝ) (x : E k) :
    0 ≤ (locWeight k c R x).re := locBump_re_nonneg k _

/-- The square of the modulus of the localisation weight is at least `1` on `B(c,R)`. -/
lemma one_le_normSq_locWeight (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) {x : E k}
    (hx : ‖x - c‖ ≤ R) : 1 ≤ ‖locWeight k c R x‖ ^ 2 := by
  have hnorm : ‖(R⁻¹ : ℝ) • (x - c)‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hR.le), inv_mul_le_iff₀ hR]
    simpa using hx
  have h1 : 1 ≤ (locWeight k c R x).re := locWeight_apply k c R x ▸ locBump_re_ge_one k hnorm
  have hs : ‖locWeight k c R x‖ ^ 2
      = (locWeight k c R x).re * (locWeight k c R x).re
        + (locWeight k c R x).im * (locWeight k c R x).im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_nonneg ((locWeight k c R x).im), h1]

lemma norm_locWeight_le (k : ℕ) (c : E k) {R : ℝ} (x : E k) :
    ‖locWeight k c R x‖ ≤ ∫ ξ, ‖locBumpF k ξ‖ := by
  rw [locWeight_apply, locBump_invFourier]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae
  filter_upwards with ξ
  rw [norm_mul]
  have hξ : ‖Complex.exp (((2 * Real.pi : ℂ) * Complex.I)
      * ((inner ℝ ((R⁻¹ : ℝ) • (x - c)) ξ : ℝ) : ℂ))‖ = 1 := by
    simpa only [echar] using echar_norm (inner ℝ ((R⁻¹ : ℝ) • (x - c)) ξ)
  rw [hξ, mul_one]

lemma cexp_neg_two_pi_eq_echar (a : ℝ) :
    Complex.exp ((↑(-2 * Real.pi * a) * Complex.I)) = echar (-a) := by
  rw [echar]
  congr 1
  push_cast
  ring

lemma fourier_locBump_eq_integral (k : ℕ) (w : E k) :
    𝓕 (⇑(locBump k) : E k → ℂ) w = ∫ y : E k, locBump k y * echar (-(inner ℝ y w)) := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with y
  rw [smul_eq_mul, cexp_neg_two_pi_eq_echar, mul_comm]

/-- **The Fourier transform of the localisation weight.** -/
lemma integral_locWeight_mul_echar (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) (w : E k) :
    (∫ x : E k, locWeight k c R x * echar (-(inner ℝ x w)))
      = ((R ^ k : ℝ) : ℂ) * echar (-(inner ℝ c w))
          * 𝓕 (⇑(locBump k) : E k → ℂ) (R • w) := by
  have hstep : (∫ x : E k, locWeight k c R x * echar (-(inner ℝ x w)))
      = (∫ z : E k, locBump k ((R⁻¹ : ℝ) • z) * echar (-(inner ℝ z w)))
        * echar (-(inner ℝ c w)) := by
    rw [← MeasureTheory.integral_add_left_eq_self
      (fun z : E k => locWeight k c R z * echar (-(inner ℝ z w))) c]
    rw [show (∫ x : E k, locWeight k c R (c + x) * echar (-(inner ℝ (c + x) w)))
        = ∫ x : E k, (locBump k ((R⁻¹ : ℝ) • x) * echar (-(inner ℝ x w)))
            * echar (-(inner ℝ c w)) from by
      apply integral_congr_ae
      filter_upwards with x
      have h1 : locWeight k c R (c + x) = locBump k ((R⁻¹ : ℝ) • x) := by
        rw [locWeight_apply]
        congr 1
        rw [show c + x - c = x from by abel]
      have h2 : echar (-(inner ℝ (c + x) w))
          = echar (-(inner ℝ x w)) * echar (-(inner ℝ c w)) := by
        rw [inner_add_left,
          show -(inner ℝ c w + inner ℝ x w) = -(inner ℝ x w) + -(inner ℝ c w) from by ring,
          echar_add]
      rw [h1, h2]
      ring]
    rw [integral_mul_const]
  have hscale : (∫ z : E k, locBump k ((R⁻¹ : ℝ) • z) * echar (-(inner ℝ z w)))
      = ((R ^ k : ℝ) : ℂ)
        * ∫ y : E k, locBump k y * echar (-(inner ℝ y (R • w))) := by
    have hcongr : (∫ z : E k, locBump k ((R⁻¹ : ℝ) • z) * echar (-(inner ℝ z w)))
        = ∫ z : E k,
            locBump k ((R⁻¹ : ℝ) • z) * echar (-(inner ℝ ((R⁻¹ : ℝ) • z) (R • w))) := by
      apply integral_congr_ae
      filter_upwards with z
      congr 1
      have hinner : inner ℝ ((R⁻¹ : ℝ) • z) (R • w) = inner ℝ z w := by
        rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
          inv_mul_cancel₀ hR.ne', one_mul]
      rw [hinner]
    rw [hcongr]
    have h := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (μ := (volume : Measure (E k)))
      (fun y : E k => locBump k y * echar (-(inner ℝ y (R • w)))) hR.le
    rw [h, show Module.finrank ℝ (E k) = k from by simp]
    rw [Complex.real_smul]
  rw [hstep, hscale, fourier_locBump_eq_integral]
  ring

lemma cexp_two_pi_eq_echar (b : ℝ) :
    Complex.exp ((↑(2 * Real.pi * b) * Complex.I)) = echar b := by
  rw [echar]
  congr 1
  push_cast
  ring

/-- The localisation bump is the inverse Fourier transform of the compactly supported bump. -/
lemma locBump_eq_invFourier (k : ℕ) :
    (⇑(locBump k) : E k → ℂ) = 𝓕⁻ (⇑(locBumpF k)) := by
  funext x
  rw [Real.fourierInv_eq', locBump_invFourier]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [smul_eq_mul]
  rw [mul_comm (Complex.exp ((↑(2 * Real.pi * ⟪ξ, x⟫) * Complex.I))) (locBumpF k ξ)]
  congr 1
  rw [real_inner_comm ξ x]
  congr 1
  push_cast
  ring

/-- The Fourier transform of the localisation bump is the compactly supported bump `locBumpF`. -/
lemma fourier_locBump (k : ℕ) :
    𝓕 (⇑(locBump k) : E k → ℂ) = ⇑(locBumpF k) := by
  rw [locBump_eq_invFourier]
  exact (locBumpF k).continuous.fourier_fourierInv_eq (locBumpF k).integrable
    ((𝓕 (locBumpF k) : SchwartzMap (E k) ℂ)).integrable

lemma momChar_eq_echar_inner (k : ℕ) (x : E k) (t : ℝ) :
    momChar k x t = echar (inner ℝ x (gammaVec k t)) := by
  rw [momChar_eq_echar, inner_gamma]

lemma memLp_locWeight (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) {p : ℝ} (hp : 0 ≤ p) :
    MemLp (fun x : E k => locWeight k c R x) (ENNReal.ofReal p) volume := by
  have hΨ : MemLp ((locBump k : SchwartzMap (E k) ℂ) : E k → ℂ) (ENNReal.ofReal p) volume :=
    SchwartzMap.memLp _ _ _
  have hmap : Measure.map (fun z : E k => (R⁻¹ : ℝ) • z) volume
      = ENNReal.ofReal (R ^ k) • volume := by
    rw [MeasureTheory.Measure.map_addHaar_smul volume (r := R⁻¹) (inv_ne_zero hR.ne')]
    rw [show Module.finrank ℝ (E k) = k from by simp]
    congr 1
    rw [inv_pow, inv_inv, abs_of_nonneg (pow_nonneg hR.le k)]
  have h1 : MemLp ((locBump k : SchwartzMap (E k) ℂ) : E k → ℂ)
      (ENNReal.ofReal p) (ENNReal.ofReal (R ^ k) • volume) :=
    hΨ.smul_measure ENNReal.ofReal_ne_top
  have h2 : MemLp (fun z : E k => locBump k ((R⁻¹ : ℝ) • z)) (ENNReal.ofReal p) volume :=
    h1.comp_measurePreserving ⟨(continuous_const_smul _).measurable, hmap⟩
  have htr : MeasurePreserving (fun y : E k => y - c) volume volume := by
    have h := measurePreserving_add_left volume (-c)
    have h2 : (fun x : E k => -c + x) = (fun y : E k => y - c) := by
      funext x; simp [sub_eq_add_neg, add_comm]
    rwa [h2] at h
  have h3 : MemLp (fun y : E k => locBump k ((R⁻¹ : ℝ) • (y - c))) (ENNReal.ofReal p) volume :=
    h2.comp_measurePreserving htr
  simpa only [locWeight_apply] using h3

lemma integrable_locWeight (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) :
    Integrable (fun x : E k => locWeight k c R x) volume := by
  have h := memLp_locWeight k c hR (p := 1) (by norm_num)
  rw [ENNReal.ofReal_one] at h
  exact memLp_one_iff_integrable.mp h

/-- The inner computation: `locWeight · momChar(·, v)` is the localisation weight modulated by the
frequency `γ(v)`, so its Fourier transform is `locBumpF k` shifted by `R • (ξ − γ(v))`. -/
lemma integral_locWeight_momChar_mul_echar (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R)
    (t : ℝ) (ξ : E k) :
    (∫ x : E k, locWeight k c R x * momChar k x t * echar (-(inner ℝ x ξ)))
      = ((R ^ k : ℝ) : ℂ) * echar (-(inner ℝ c ξ)) * echar (inner ℝ c (gammaVec k t))
          * locBumpF k (R • (ξ - gammaVec k t)) := by
  have hphase : ∀ x : E k, echar (inner ℝ x (gammaVec k t)) * echar (-(inner ℝ x ξ))
      = echar (-(inner ℝ x (ξ - gammaVec k t))) := by
    intro x
    rw [← echar_add]
    congr 1
    rw [inner_sub_right]
    ring
  have hpt : ∀ x : E k, locWeight k c R x * momChar k x t * echar (-(inner ℝ x ξ))
      = locWeight k c R x * echar (-(inner ℝ x (ξ - gammaVec k t))) := by
    intro x
    rw [momChar_eq_echar_inner]
    calc locWeight k c R x * echar (inner ℝ x (gammaVec k t)) * echar (-(inner ℝ x ξ))
        = locWeight k c R x * (echar (inner ℝ x (gammaVec k t)) * echar (-(inner ℝ x ξ))) := by
          ring
      _ = locWeight k c R x * echar (-(inner ℝ x (ξ - gammaVec k t))) := by rw [hphase x]
  have hc : echar (-(inner ℝ c (ξ - gammaVec k t)))
      = echar (-(inner ℝ c ξ)) * echar (inner ℝ c (gammaVec k t)) := by
    rw [inner_sub_right,
      show -(inner ℝ c ξ - inner ℝ c (gammaVec k t))
        = -(inner ℝ c ξ) + inner ℝ c (gammaVec k t) from by ring, echar_add]
  rw [show (fun x : E k => locWeight k c R x * momChar k x t * echar (-(inner ℝ x ξ)))
      = (fun x : E k => locWeight k c R x * echar (-(inner ℝ x (ξ - gammaVec k t))))
      from funext hpt]
  rw [integral_locWeight_mul_echar k c hR (ξ - gammaVec k t), hc,
    congrFun (fourier_locBump k) (R • (ξ - gammaVec k t))]
  ring

lemma norm_momChar (k : ℕ) (x : E k) (t : ℝ) : ‖momChar k x t‖ = 1 := by
  rw [momChar_eq_echar_inner, echar_norm]

lemma continuous_echar : Continuous echar := by
  unfold echar
  exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

lemma continuous_locWeight (k : ℕ) (c : E k) (R : ℝ) :
    Continuous (fun x : E k => locWeight k c R x) := by
  rw [show (fun x : E k => locWeight k c R x)
      = fun x : E k => locBump k ((R⁻¹ : ℝ) • (x - c)) from funext (locWeight_apply k c R)]
  exact (locBump k).continuous.comp ((continuous_const_smul _).comp (continuous_id.sub continuous_const))

lemma continuous_momChar_uncurry (k : ℕ) :
    Continuous (Function.uncurry (fun (x : E k) (t : ℝ) => momChar k x t)) := by
  have hinner : Continuous (fun p : E k × ℝ => inner ℝ p.1 (gammaVec k p.2)) := by
    rw [show (fun p : E k × ℝ => inner ℝ p.1 (gammaVec k p.2))
        = fun p : E k × ℝ => ∑ j : Fin k, p.1 j * p.2 ^ (j.val + 1) from by
      funext p
      rw [inner_gamma]
      rfl]
    exact continuous_finsetSum _ (fun j _ => by fun_prop)
  have : (Function.uncurry (fun (x : E k) (t : ℝ) => momChar k x t))
      = fun p : E k × ℝ => echar (inner ℝ p.1 (gammaVec k p.2)) := by
    funext p
    exact momChar_eq_echar_inner k p.1 p.2
  rw [this]
  exact continuous_echar.comp hinner

set_option maxHeartbeats 2000000 in
/-- **The Fourier transform of `locWeight · E_J g`.** -/
theorem fourier_locWeight_mul_extOp (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) {a b : ℝ} (hab : a ≤ b)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume a b) (ξ : E k) :
    (∫ x : E k, (locWeight k c R x * extOp k g a b x) * echar (-(inner ℝ x ξ)))
      = ((R ^ k : ℝ) : ℂ) * echar (-(inner ℝ c ξ))
          * ∫ t in a..b, g t * echar (inner ℝ c (gammaVec k t))
              * locBumpF k (R • (ξ - gammaVec k t)) := by
  set ν : Measure ℝ := volume.restrict (Set.Ioc a b) with hν
  have hgw : Integrable g ν := by rw [hν]; exact hg.1
  have hL : ∀ x : E k, extOp k g a b x = ∫ t, g t * momChar k x t ∂ν := by
    intro x
    rw [extOp, hν, intervalIntegral.integral_of_le hab]
  have hRw : (∫ t in a..b, g t * echar (inner ℝ c (gammaVec k t))
        * locBumpF k (R • (ξ - gammaVec k t)))
      = ∫ t, g t * echar (inner ℝ c (gammaVec k t))
          * locBumpF k (R • (ξ - gammaVec k t)) ∂ν := by
    rw [hν, intervalIntegral.integral_of_le hab]
  have hpt : ∀ x : E k, (locWeight k c R x * extOp k g a b x) * echar (-(inner ℝ x ξ))
      = ∫ t, locWeight k c R x * (g t * momChar k x t) * echar (-(inner ℝ x ξ)) ∂ν := by
    intro x
    rw [hL x,
      show (fun t : ℝ => locWeight k c R x * (g t * momChar k x t) * echar (-(inner ℝ x ξ)))
        = (fun t : ℝ => (locWeight k c R x * echar (-(inner ℝ x ξ)))
            * (g t * momChar k x t)) from by funext t; ring,
      integral_const_mul]
    ring
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (x : E k) (t : ℝ) =>
      locWeight k c R x * (g t * momChar k x t) * echar (-(inner ℝ x ξ))) (volume.prod ν) := by
    have h1 : AEStronglyMeasurable (fun z : E k × ℝ => locWeight k c R z.1) (volume.prod ν) :=
      (continuous_locWeight k c R).aestronglyMeasurable.comp_fst
    have h2 : AEStronglyMeasurable (fun z : E k × ℝ => momChar k z.1 z.2) (volume.prod ν) :=
      (continuous_momChar_uncurry k).aestronglyMeasurable
    have h3 : AEStronglyMeasurable (fun z : E k × ℝ => g z.2) (volume.prod ν) :=
      hgw.aestronglyMeasurable.comp_snd
    have h4 : AEStronglyMeasurable (fun z : E k × ℝ => echar (-(inner ℝ z.1 ξ)))
        (volume.prod ν) :=
      (by
        apply Continuous.aestronglyMeasurable
        unfold echar
        refine Complex.continuous_exp.comp ?_
        fun_prop)
    exact (h1.mul (h3.mul h2)).mul h4
  have hint : Integrable (Function.uncurry fun (x : E k) (t : ℝ) =>
      locWeight k c R x * (g t * momChar k x t) * echar (-(inner ℝ x ξ))) (volume.prod ν) := by
    refine ((integrable_locWeight k c hR).norm.mul_prod hgw.norm).mono' hmeas ?_
    filter_upwards with z
    show ‖locWeight k c R z.1 * (g z.2 * momChar k z.1 z.2) * echar (-(inner ℝ z.1 ξ))‖
      ≤ ‖locWeight k c R z.1‖ * ‖g z.2‖
    rw [norm_mul, norm_mul, norm_mul, norm_momChar, echar_norm, mul_one, mul_one]
  have hswap : (∫ x : E k, ∫ t, locWeight k c R x * (g t * momChar k x t)
        * echar (-(inner ℝ x ξ)) ∂ν)
      = ∫ t, ∫ x : E k, locWeight k c R x * (g t * momChar k x t)
          * echar (-(inner ℝ x ξ)) ∂volume ∂ν :=
    MeasureTheory.integral_integral_swap hint
  have hinner : ∀ t : ℝ, (∫ x : E k, locWeight k c R x * (g t * momChar k x t)
        * echar (-(inner ℝ x ξ)))
      = g t * (((R ^ k : ℝ) : ℂ) * echar (-(inner ℝ c ξ)) * echar (inner ℝ c (gammaVec k t))
          * locBumpF k (R • (ξ - gammaVec k t))) := by
    intro t
    rw [show (fun x : E k => locWeight k c R x * (g t * momChar k x t)
        * echar (-(inner ℝ x ξ)))
        = (fun x : E k => locWeight k c R x * momChar k x t * echar (-(inner ℝ x ξ)) * g t)
        from by funext x; ring]
    rw [integral_mul_const, integral_locWeight_momChar_mul_echar k c hR t ξ]
    ring
  rw [show (fun x : E k => (locWeight k c R x * extOp k g a b x) * echar (-(inner ℝ x ξ)))
      = fun x : E k => ∫ t, locWeight k c R x * (g t * momChar k x t)
          * echar (-(inner ℝ x ξ)) ∂ν from funext hpt]
  rw [hswap]
  rw [show (fun t : ℝ => ∫ x : E k, locWeight k c R x * (g t * momChar k x t)
        * echar (-(inner ℝ x ξ)))
      = fun t : ℝ => g t * (((R ^ k : ℝ) : ℂ) * echar (-(inner ℝ c ξ))
          * echar (inner ℝ c (gammaVec k t)) * locBumpF k (R • (ξ - gammaVec k t)))
      from funext hinner]
  rw [hRw]
  rw [show (∫ t, g t * (((R ^ k : ℝ) : ℂ) * echar (-(inner ℝ c ξ))
        * echar (inner ℝ c (gammaVec k t)) * locBumpF k (R • (ξ - gammaVec k t))) ∂ν)
      = (∫ t, g t * echar (inner ℝ c (gammaVec k t))
          * locBumpF k (R • (ξ - gammaVec k t)) ∂ν)
        * (((R ^ k : ℝ) : ℂ) * echar (-(inner ℝ c ξ))) from by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with t
    ring]
  ring

/-- **Spectral support of `locWeight · E_J g`.**  If `ξ` is at distance more than `locBand k / R` from
every point of the arc `γ([a,b])`, then the Fourier transform of `locWeight k c R · E_{[a,b]}g`
vanishes at `ξ`: the spectrum of the localised extension operator is contained in the
`locBand k / R`-neighbourhood of the arc. -/
theorem extOp_locWeight_fourier_zero (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) {a b : ℝ}
    (hab : a ≤ b) (g : ℝ → ℂ) (hg : IntervalIntegrable g volume a b) {ξ : E k}
    (hξ : ∀ t ∈ Set.uIcc a b, locBand k / R < ‖ξ - gammaVec k t‖) :
    (∫ x : E k, (locWeight k c R x * extOp k g a b x) * echar (-(inner ℝ x ξ))) = 0 := by
  have hz : ∀ t ∈ Set.uIcc a b, g t * echar (inner ℝ c (gammaVec k t))
      * locBumpF k (R • (ξ - gammaVec k t)) = 0 := by
    intro t ht
    have hlt : locBand k < ‖R • (ξ - gammaVec k t)‖ := by
      have h := hξ t ht
      rw [div_lt_iff₀ hR] at h
      rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hR, mul_comm]
    rw [locBumpF_eq_zero_of_lt k hlt, mul_zero]
  rw [fourier_locWeight_mul_extOp k c hR hab g hg ξ,
    intervalIntegral.integral_congr hz]
  simp

lemma aestronglyMeasurable_locWeight_mul_extOp (k : ℕ) (c : E k) (R : ℝ)
    (g : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) (hg : IntervalIntegrable g volume a b) :
    AEStronglyMeasurable (fun x : E k => locWeight k c R x * extOp k g a b x) volume := by
  set ν : Measure ℝ := volume.restrict (Set.Ioc a b) with hν
  have hgw : Integrable g ν := by rw [hν]; exact hg.1
  have hF : AEStronglyMeasurable (fun z : E k × ℝ => g z.2 * momChar k z.1 z.2)
      (volume.prod ν) :=
    (hgw.aestronglyMeasurable.comp_snd).mul ((continuous_momChar_uncurry k).aestronglyMeasurable)
  have hint : AEStronglyMeasurable (fun x : E k => ∫ t, g t * momChar k x t ∂ν) volume :=
    hF.integral_prod_right'
  refine (continuous_locWeight k c R).aestronglyMeasurable.mul ?_
  have heq : (extOp k g a b) = fun x : E k => ∫ t, g t * momChar k x t ∂ν := by
    funext x
    rw [extOp, hν, intervalIntegral.integral_of_le hab]
  rw [heq]
  exact hint

lemma integrable_locWeight_mul_extOp (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R)
    (g : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) (hg : IntervalIntegrable g volume a b) :
    Integrable (fun x : E k => locWeight k c R x * extOp k g a b x) volume := by
  have hbound : Integrable (fun x : E k =>
      (∫ t in a..b, ‖g t‖) * ‖locWeight k c R x‖)
      volume :=
    (integrable_locWeight k c hR).norm.const_mul _
  refine hbound.mono' (aestronglyMeasurable_locWeight_mul_extOp k c R g hab hg) ?_
  filter_upwards with x
  rw [norm_mul]
  calc ‖locWeight k c R x‖ * ‖extOp k g a b x‖
      ≤ ‖locWeight k c R x‖ * ∫ t in a..b, ‖g t‖ :=
        mul_le_mul_of_nonneg_left (extOp_norm_le k g hab x) (norm_nonneg _)
    _ = (∫ t in a..b, ‖g t‖) * ‖locWeight k c R x‖ := by
        ring

lemma integrable_normSq_locWeight_mul_extOp (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R)
    (g : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) (hg : IntervalIntegrable g volume a b) :
    Integrable (fun x : E k => ‖locWeight k c R x * extOp k g a b x‖ ^ 2) volume := by
  have hsq : Integrable (fun x : E k => ‖locWeight k c R x‖ ^ 2) volume := by
    have h := memLp_locWeight k c hR (p := 2) (by norm_num)
    have h2 := h.integrable_norm_rpow (p := ENNReal.ofReal 2)
      (by simp [ENNReal.ofReal_eq_zero]) (by simp)
    simpa [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] using h2
  have hbound : Integrable (fun x : E k =>
      (∫ t in a..b, ‖g t‖) ^ 2
        * ‖locWeight k c R x‖ ^ 2) volume :=
    hsq.const_mul _
  refine hbound.mono' ((aestronglyMeasurable_locWeight_mul_extOp k c R g hab hg).norm.pow 2) ?_
  filter_upwards with x
  have h2 : ‖locWeight k c R x * extOp k g a b x‖ ^ 2
      = ‖locWeight k c R x‖ ^ 2 * ‖extOp k g a b x‖ ^ 2 := by
    rw [norm_mul, mul_pow]
  rw [h2, Real.norm_of_nonneg (by positivity)]
  refine (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (extOp_norm_le k g hab x) 2) (sq_nonneg _)).trans_eq ?_
  ring

set_option maxHeartbeats 2000000 in
/-- **Weighted `L²` orthogonality of spectrally separated pieces of the extension operator.**
Two pieces whose arcs are separated by more than `2 · locBand k / R` are orthogonal in
`L²(ℝᵏ)` after multiplication by the same localisation weight.  This is the crux of BDG's
`L²`-decoupling lemma (their Lemma 8.2, (ne89)). -/
theorem extOp_locWeight_orthogonal (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R)
    {a b a' b' : ℝ} (hab : a ≤ b) (hab' : a' ≤ b')
    (g g' : ℝ → ℂ) (hg : IntervalIntegrable g volume a b)
    (hg' : IntervalIntegrable g' volume a' b')
    (hsep : ∀ t ∈ Set.uIcc a b, ∀ s ∈ Set.uIcc a' b',
      2 * (locBand k / R) < ‖gammaVec k t - gammaVec k s‖) :
    (∫ x : E k, (locWeight k c R x * extOp k g a b x)
        * starRingEnd ℂ (locWeight k c R x * extOp k g' a' b' x)) = 0 := by
  refine Commons.Analysis.Fourier.integral_mul_conj_eq_zero_of_disjoint_fourier_support k
    (fun x : E k => locWeight k c R x * extOp k g a b x)
    (fun x : E k => locWeight k c R x * extOp k g' a' b' x)
    {ξ : E k | ∃ t ∈ Set.uIcc a b, ‖ξ - gammaVec k t‖ ≤ locBand k / R}
    {ξ : E k | ∃ t ∈ Set.uIcc a' b', ‖ξ - gammaVec k t‖ ≤ locBand k / R}
    (integrable_locWeight_mul_extOp k c hR g hab hg)
    (integrable_locWeight_mul_extOp k c hR g' hab' hg')
    (integrable_normSq_locWeight_mul_extOp k c hR g hab hg)
    (integrable_normSq_locWeight_mul_extOp k c hR g' hab' hg')
    ?_ ?_ ?_
  · intro ξ hξ
    refine extOp_locWeight_fourier_zero k c hR hab g hg ?_
    intro t ht
    by_contra hcon
    exact hξ ⟨t, ht, not_lt.mp hcon⟩
  · intro ξ hξ
    refine extOp_locWeight_fourier_zero k c hR hab' g' hg' ?_
    intro t ht
    by_contra hcon
    exact hξ ⟨t, ht, not_lt.mp hcon⟩
  · rw [Set.disjoint_left]
    intro ξ hξ hξ'
    obtain ⟨t, ht, ht'⟩ := hξ
    obtain ⟨s, hs, hs'⟩ := hξ'
    have htri : ‖gammaVec k t - gammaVec k s‖ ≤ 2 * (locBand k / R) := by
      have h1 : ‖gammaVec k t - gammaVec k s‖
          ≤ ‖gammaVec k t - ξ‖ + ‖ξ - gammaVec k s‖ := by
        have h := dist_triangle (gammaVec k t) ξ (gammaVec k s)
        rwa [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h
      have h2 : ‖gammaVec k t - ξ‖ ≤ locBand k / R := by
        rw [show gammaVec k t - ξ = -(ξ - gammaVec k t) from by abel, norm_neg]
        exact ht'
      calc ‖gammaVec k t - gammaVec k s‖
          ≤ ‖gammaVec k t - ξ‖ + ‖ξ - gammaVec k s‖ := h1
        _ ≤ locBand k / R + locBand k / R := add_le_add h2 hs'
        _ = 2 * (locBand k / R) := by ring
    exact absurd (hsep t ht s hs) (not_lt.mpr htri)

end
end Submission.Vinogradov
