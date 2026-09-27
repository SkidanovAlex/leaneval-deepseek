import Mathlib
import Submission.Work.Drive.N2.saddleModelPsi
import Submission.Work.Drive.N2Lead.modelArc_im_strictMonoOn

namespace Work.Drive.N2Lead

open Work.Drive.N2
open Filter
open scoped Topology

/-! ## The real part of the principal square root

For `z : ℂ` the real part of the principal square root is `√((‖z‖ + z.re)/2)`; this is the
conjugation-invariant form of the branch, and it is what makes the evenness of `w ↦ Re √(ζ w)`
immediate. -/

lemma complex_sqrt_re (z : ℂ) : z.sqrt.re = Real.sqrt ((‖z‖ + z.re) / 2) := by
  rw [Complex.sqrt_eq_real_add_ite]
  split_ifs <;> simp [Complex.mul_re]

/-! ## The two model functions -/

/-- `H w = ‖ζ w‖ + σ w`: twice the square of the real part of `√(ζ w)`. -/
noncomputable def modelH (η δ s : ℝ) (w : ℝ) : ℝ := ‖modelZeta η δ s w‖ + modelSigma η δ s w

/-- `Q w = σ w ^ 2 + w ^ 2 = ‖ζ w‖ ^ 2`: the argument of the real square root. -/
noncomputable def modelQ (η δ s : ℝ) (w : ℝ) : ℝ := modelSigma η δ s w ^ 2 + w ^ 2

/-- The model arc `w ↦ Re √(ζ w)`. -/
noncomputable def modelArcRe (η δ s : ℝ) (w : ℝ) : ℝ := (modelZeta η δ s w).sqrt.re

lemma modelH_eq (η δ s w : ℝ) :
    modelH η δ s w = Real.sqrt (modelQ η δ s w) + modelSigma η δ s w := by
  rw [modelH, norm_modelZeta, modelQ]

lemma modelArcRe_eq (η δ s w : ℝ) : modelArcRe η δ s w = Real.sqrt (modelH η δ s w / 2) := by
  rw [modelArcRe, complex_sqrt_re, modelH, modelZeta_re]

lemma modelH_nonneg (η δ s w : ℝ) : 0 ≤ modelH η δ s w := by
  rw [modelH]
  have h := abs_le.mp (Complex.abs_re_le_norm (modelZeta η δ s w))
  rw [modelZeta_re] at h
  linarith [h.1]

lemma modelH_even (η δ s w : ℝ) : modelH η δ s (-w) = modelH η δ s w := by
  rw [modelH, modelH, norm_modelZeta_neg, modelSigma_even]

/-! ## The plateau is in `[0,1]` on `[0,2]`, and `σ` is bounded by `η` -/

-- NOTE (renamed 2026-09-27 by the `N2/saddleCertifiedWindowOneComp` lane): this lemma used to be
-- called `saddleM_mem_Icc`, a name that `Submission.Work.Drive.N2Lead.upperArcToolkit` also
-- declares (with a different signature).  Importing both modules is impossible while the two share
-- the name, and the D2 core needs both families (`upperRegionRate` and `mobius_bridgeStar`), so the
-- name here is prefixed.  It is used only in this file.
lemma mrsm_saddleM_mem_Icc {δ x : ℝ} (hx : x ∈ Set.Icc 0 2) : saddleM δ x ∈ Set.Icc 0 1 := by
  rw [saddleM, abs_of_nonneg hx.1, saddleMu,
    Real.smoothTransition.zero_of_nonpos (show x - 2 ≤ 0 by linarith [hx.2]), sub_zero, mul_one]
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma modelSigma_mem_Icc {η δ s : ℝ} (hs : 0 < s) (hsη : s ≤ η) {x : ℝ}
    (hx : x ∈ Set.Icc 0 2) : modelSigma η δ s x ∈ Set.Icc (-η) η := by
  obtain ⟨hM0, hM1⟩ := mrsm_saddleM_mem_Icc (δ := δ) hx
  have hηs : 0 < η + s := by linarith
  have h1 : saddleM δ x * (η + s) ≤ η + s := by
    simpa using mul_le_mul_of_nonneg_right hM1 hηs.le
  have h2 : 0 ≤ saddleM δ x * (η + s) := mul_nonneg hM0 hηs.le
  have h3 : modelSigma η δ s x = s - saddleM δ x * (η + s) := by
    rw [modelSigma_eq]; ring
  rw [h3]
  constructor <;> linarith

/-! ## Derivatives of the plateau and of `σ` -/

lemma contDiff_modelSigma (η δ s : ℝ) (hδ : 0 < δ) (h2 : 0 < 2 - 4*δ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (modelSigma η δ s) := by
  rw [show modelSigma η δ s = fun y => s + saddleM δ y * (-η - s)
      from funext fun y => modelSigma_eq η δ s y]
  exact contDiff_const.add ((contDiff_saddleM hδ h2).mul contDiff_const)

lemma saddleM_eventuallyEq_saddleMu {δ x : ℝ} (hx : 0 < x) :
    saddleM δ =ᶠ[𝓝 x] saddleMu δ := by
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  rw [saddleM, abs_of_pos hy]

lemma saddleMu_eventuallyEq {δ x : ℝ} (hx : x < 2) :
    saddleMu δ =ᶠ[𝓝 x] fun y => Real.smoothTransition ((y - (2 - 4*δ))/(2*δ)) := by
  filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
  have hy' : y < 2 := hy
  rw [saddleMu, Real.smoothTransition.zero_of_nonpos (show y - 2 ≤ 0 by linarith),
    sub_zero, mul_one]

/-- On `(0,2)` the derivative of the plateau is the derivative of `smoothTransition` of the
rescaled argument, divided by `2δ`. -/
lemma deriv_saddleM_eq {δ x : ℝ} (hδ : 0 < δ) (hx0 : 0 < x) (hx2 : x < 2) :
    deriv (saddleM δ) x
      = deriv Real.smoothTransition ((x - (2 - 4*δ))/(2*δ)) / (2*δ) := by
  rw [(saddleM_eventuallyEq_saddleMu (δ := δ) hx0).deriv_eq,
    (saddleMu_eventuallyEq (δ := δ) hx2).deriv_eq]
  have hdiff : DifferentiableAt ℝ Real.smoothTransition ((x - (2 - 4*δ))/(2*δ)) :=
    ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp)).differentiableAt
  have ha : HasDerivAt (fun y : ℝ => (y - (2 - 4*δ))/(2*δ)) (1/(2*δ)) x :=
    ((hasDerivAt_id x).sub_const (2 - 4*δ)).div_const (2*δ)
  have h := hdiff.hasDerivAt.comp x ha
  have hval : deriv (fun y : ℝ => Real.smoothTransition ((y - (2 - 4*δ))/(2*δ))) x
      = deriv Real.smoothTransition ((x - (2 - 4*δ))/(2*δ)) * (1/(2*δ)) := h.deriv
  rw [hval]
  ring

lemma deriv_saddleM_abs_le {δ x C₀ : ℝ} (hδ : 0 < δ) (hx0 : 0 < x) (hx2 : x < 2)
    (hC₀ : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ C₀) :
    |deriv (saddleM δ) x| ≤ C₀ / (2*δ) := by
  rw [deriv_saddleM_eq hδ hx0 hx2, abs_div, abs_of_pos (by linarith : (0:ℝ) < 2*δ)]
  exact div_le_div_of_nonneg_right (hC₀ _) (by linarith)

/-- Off the transition zone the plateau is locally constant, hence so is `σ`. -/
lemma deriv_saddleM_eq_zero_of_lt {δ x : ℝ} (hδ : 0 < δ) (hx0 : 0 < x) (hx : x < 2 - 4*δ) :
    deriv (saddleM δ) x = 0 := by
  have hr : 0 < min x (2 - 4*δ - x) / 2 := by
    apply div_pos (lt_min hx0 (by linarith)) (by norm_num)
  have hev : saddleM δ =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hy
    have h1 : 0 ≤ y := by
      have h2 : min x (2 - 4*δ - x)/2 ≤ x/2 :=
        div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      linarith [hy.2]
    have h3 : y ≤ 2 - 4*δ := by
      have h2 : min x (2 - 4*δ - x)/2 ≤ (2 - 4*δ - x)/2 :=
        div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      linarith [hy.1]
    exact saddleM_eq_zero_of_abs_le hδ (by rw [abs_of_nonneg h1]; exact h3)
  rw [hev.deriv_eq, deriv_const]

lemma deriv_saddleM_eq_zero_of_gt {δ x : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1)
    (hx : 2 - 2*δ < x) (hx2 : x < 2) :
    deriv (saddleM δ) x = 0 := by
  have hr : 0 < min (x - (2 - 2*δ)) (2 - x) / 2 := by
    apply div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  have hev : saddleM δ =ᶠ[𝓝 x] fun _ => (1:ℝ) := by
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hy
    have h2a : min (x - (2 - 2*δ)) (2 - x)/2 ≤ (x - (2 - 2*δ))/2 :=
      div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have h2b : min (x - (2 - 2*δ)) (2 - x)/2 ≤ (2 - x)/2 :=
      div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    have h1 : 2 - 2*δ ≤ y := by linarith [hy.2]
    have h3 : y ≤ 2 := by linarith [hy.1]
    have hy0 : 0 ≤ y := by linarith [hy.2]
    rw [saddleM, abs_of_nonneg hy0]
    exact saddleMu_eq_one hδ h1 h3
  rw [hev.deriv_eq, deriv_const]

lemma deriv_modelSigma {η δ s x : ℝ} (hδ : 0 < δ) (h2 : 0 < 2 - 4*δ) :
    deriv (modelSigma η δ s) x = deriv (saddleM δ) x * (-η - s) := by
  have hdiff : DifferentiableAt ℝ (saddleM δ) x :=
    ((contDiff_saddleM hδ h2).differentiable (by simp)).differentiableAt
  rw [show modelSigma η δ s = fun y => s + saddleM δ y * (-η - s)
      from funext fun y => modelSigma_eq η δ s y, deriv_const_add]
  exact deriv_mul_const hdiff _

/-! ## The derivative of `H = ‖ζ‖ + σ` -/

lemma hasDerivAt_modelQ {η δ s x : ℝ} (hδ : 0 < δ) (h2 : 0 < 2 - 4*δ) :
    HasDerivAt (modelQ η δ s)
      (2 * modelSigma η δ s x * deriv (modelSigma η δ s) x + 2 * x) x := by
  have hdiff : DifferentiableAt ℝ (modelSigma η δ s) x :=
    ((contDiff_modelSigma η δ s hδ h2).differentiable (by simp)).differentiableAt
  have h := ((hdiff.hasDerivAt.pow 2).add ((hasDerivAt_id x).pow 2))
  have hfun : (modelSigma η δ s ^ 2 + (id : ℝ → ℝ) ^ 2) = modelQ η δ s := by
    funext y; rfl
  rw [hfun] at h
  refine h.congr_deriv ?_
  simp only [id_eq, Nat.reduceSub, pow_one, Nat.cast_ofNat, mul_one]

lemma deriv_modelQ {η δ s x : ℝ} (hδ : 0 < δ) (h2 : 0 < 2 - 4*δ) :
    deriv (modelQ η δ s) x
      = 2 * modelSigma η δ s x * deriv (modelSigma η δ s) x + 2 * x :=
  (hasDerivAt_modelQ (η := η) (δ := δ) (s := s) (x := x) hδ h2).deriv

lemma hasDerivAt_modelH {η δ s x : ℝ} (hδ : 0 < δ) (h2 : 0 < 2 - 4*δ) (hx0 : 0 < x) :
    HasDerivAt (modelH η δ s)
      ((modelSigma η δ s x * deriv (modelSigma η δ s) x + x) / Real.sqrt (modelQ η δ s x)
        + deriv (modelSigma η δ s) x) x := by
  have hqpos : 0 < modelQ η δ s x := by
    rw [modelQ]
    nlinarith [sq_nonneg (modelSigma η δ s x), pow_pos hx0 2]
  have hdiff : DifferentiableAt ℝ (modelSigma η δ s) x :=
    ((contDiff_modelSigma η δ s hδ h2).differentiable (by simp)).differentiableAt
  have hqd := hasDerivAt_modelQ (η := η) (δ := δ) (s := s) (x := x) hδ h2
  have hsqt := (Real.hasDerivAt_sqrt (x := modelQ η δ s x) hqpos.ne').comp x hqd
  have hsum := hsqt.add hdiff.hasDerivAt
  have hfun : ((Real.sqrt ∘ modelQ η δ s) + modelSigma η δ s) = modelH η δ s := by
    funext y; rw [modelH_eq]; rfl
  rw [hfun] at hsum
  refine hsum.congr_deriv ?_
  field_simp
  try ring

lemma deriv_modelH {η δ s x : ℝ} (hδ : 0 < δ) (h2 : 0 < 2 - 4*δ) (hx0 : 0 < x) :
    deriv (modelH η δ s) x
      = (modelSigma η δ s x * deriv (modelSigma η δ s) x + x) / Real.sqrt (modelQ η δ s x)
        + deriv (modelSigma η δ s) x :=
  (hasDerivAt_modelH hδ h2 hx0).deriv

lemma deriv_modelSigma_eq_zero_of_lt {η δ s x : ℝ} (hδ : 0 < δ) (h2 : 0 < 2 - 4*δ)
    (hx0 : 0 < x) (hx : x < 2 - 4*δ) : deriv (modelSigma η δ s) x = 0 := by
  rw [deriv_modelSigma (η := η) (δ := δ) (s := s) (x := x) hδ h2,
    deriv_saddleM_eq_zero_of_lt hδ hx0 hx, zero_mul]

lemma deriv_modelSigma_eq_zero_of_gt {η δ s x : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1)
    (h2 : 0 < 2 - 4*δ)
    (hx : 2 - 2*δ < x) (hx2 : x < 2) : deriv (modelSigma η δ s) x = 0 := by
  rw [deriv_modelSigma (η := η) (δ := δ) (s := s) (x := x) hδ h2,
    deriv_saddleM_eq_zero_of_gt hδ hδ₁ hx hx2, zero_mul]

/-! ## The sign of the derivative -/

lemma sqrt_sq_add_sq_le (c x : ℝ) (hx : 0 ≤ x) : Real.sqrt (c^2 + x^2) ≤ |c| + x := by
  have hle : c^2 + x^2 ≤ (|c| + x)^2 := by
    rw [add_sq, sq_abs]
    nlinarith [abs_nonneg c]
  calc Real.sqrt (c^2 + x^2) ≤ Real.sqrt ((|c| + x)^2) := Real.sqrt_le_sqrt hle
    _ = |c| + x := Real.sqrt_sq (by linarith [abs_nonneg c])

lemma abs_deriv_modelSigma_le {η δ s x C₀ : ℝ} (hδ : 0 < δ) (h2 : 0 < 2 - 4*δ)
    (hx0 : 0 < x) (hx2 : x < 2) (hs : 0 < s) (hsη : s ≤ η)
    (hC₀ : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ C₀) (hsmall : 4 * C₀ * η ≤ δ) :
    |deriv (modelSigma η δ s) x| ≤ 1/4 := by
  have hb : |deriv (saddleM δ) x| ≤ C₀ / (2*δ) := deriv_saddleM_abs_le hδ hx0 hx2 hC₀
  have hC0nn : 0 ≤ C₀ := le_trans (abs_nonneg _) (hC₀ 0)
  have hηs : 0 < η + s := by linarith
  rw [deriv_modelSigma (η := η) (δ := δ) (s := s) (x := x) hδ h2, abs_mul,
    show -η - s = -(η + s) by ring, abs_neg, abs_of_nonneg hηs.le]
  have h1 : |deriv (saddleM δ) x| * (η + s) ≤ (C₀ / (2*δ)) * (η + s) :=
    mul_le_mul_of_nonneg_right hb hηs.le
  have h2' : (C₀ / (2*δ)) * (η + s) ≤ 1/4 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0:ℝ) < 2*δ)]
    nlinarith
  linarith

/-- The key inequality: `σ · σ' + x + σ' · ‖ζ‖ > 0` on `(0,2)`.  Where `σ' = 0` the term `x`
decides; in the transition zone `σ' < 0` and the smallness hypothesis `4 C₀ η ≤ δ` bounds `-σ'`
by `1/4`, while `x ≥ 2 - 4δ ≥ 1.6`. -/
lemma modelH_deriv_key {η δ s x C₀ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/10) (hη : 0 < η)
    (hη' : η < 1/10) (hs : 0 < s) (hsη : s ≤ η)
    (hC₀ : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ C₀) (hsmall : 4 * C₀ * η ≤ δ)
    (hx0 : 0 < x) (hx2 : x < 2) :
    0 < modelSigma η δ s x * deriv (modelSigma η δ s) x + x
      + deriv (modelSigma η δ s) x * Real.sqrt (modelQ η δ s x) := by
  have h2 : 0 < 2 - 4 * δ := by linarith
  obtain ⟨hσlo, hσhi⟩ := modelSigma_mem_Icc hs hsη (⟨hx0.le, hx2.le⟩ : x ∈ Set.Icc 0 2)
  have habsσ : |modelSigma η δ s x| ≤ η := abs_le.mpr ⟨hσlo, hσhi⟩
  have hle : Real.sqrt (modelQ η δ s x) ≤ |modelSigma η δ s x| + x := by
    rw [modelQ]
    exact sqrt_sq_add_sq_le _ _ hx0.le
  have hlt : |modelSigma η δ s x| < Real.sqrt (modelQ η δ s x) := by
    rw [modelQ]
    exact abs_lt_sqrt_sq_add_sq hx0
  have hspos : 0 < modelSigma η δ s x + Real.sqrt (modelQ η δ s x) := by
    linarith [neg_abs_le (modelSigma η δ s x)]
  rcases le_or_gt 0 (deriv (modelSigma η δ s) x) with hd | hd
  · have hmul : 0 ≤ deriv (modelSigma η δ s) x * (modelSigma η δ s x + Real.sqrt (modelQ η δ s x)) :=
      mul_nonneg hd hspos.le
    nlinarith
  · have hxge : 2 - 4*δ ≤ x := by
      by_contra hlt'
      push_neg at hlt'
      have hz : deriv (modelSigma η δ s) x = 0 := deriv_modelSigma_eq_zero_of_lt hδ h2 hx0 hlt'
      rw [hz] at hd
      exact absurd hd (lt_irrefl 0)
    have hxle : x ≤ 2 - 2*δ := by
      by_contra hlt'
      push_neg at hlt'
      have hz : deriv (modelSigma η δ s) x = 0 :=
        deriv_modelSigma_eq_zero_of_gt hδ (by linarith) h2 hlt' hx2
      rw [hz] at hd
      exact absurd hd (lt_irrefl 0)
    have hc : -deriv (modelSigma η δ s) x ≤ 1/4 := by
      have h := abs_deriv_modelSigma_le (η := η) (δ := δ) (s := s) (x := x) (C₀ := C₀)
        hδ h2 hx0 hx2 hs hsη hC₀ hsmall
      rwa [abs_of_neg hd] at h
    have hsumn : modelSigma η δ s x + Real.sqrt (modelQ η δ s x) ≤ 2*η + x := by linarith
    have hmul : -deriv (modelSigma η δ s) x * (modelSigma η δ s x + Real.sqrt (modelQ η δ s x))
        ≤ (1/4) * (2*η + x) := mul_le_mul hc hsumn hspos.le (by norm_num)
    nlinarith [hmul]

lemma deriv_modelH_pos {η δ s x C₀ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/10) (hη : 0 < η)
    (hη' : η < 1/10) (hs : 0 < s) (hsη : s ≤ η)
    (hC₀ : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ C₀) (hsmall : 4 * C₀ * η ≤ δ)
    (hx : x ∈ Set.Ioo 0 2) : 0 < deriv (modelH η δ s) x := by
  obtain ⟨hx0, hx2⟩ := hx
  have h2 : 0 < 2 - 4*δ := by linarith
  rw [deriv_modelH hδ h2 hx0]
  have hsqpos : 0 < Real.sqrt (modelQ η δ s x) :=
    Real.sqrt_pos.mpr (by
      rw [modelQ]
      nlinarith [sq_nonneg (modelSigma η δ s x), pow_pos hx0 2])
  have hkey := modelH_deriv_key (η := η) (δ := δ) (s := s) (x := x) (C₀ := C₀)
    hδ hδ' hη hη' hs hsη hC₀ hsmall hx0 hx2
  have hdiv : (modelSigma η δ s x * deriv (modelSigma η δ s) x + x) / Real.sqrt (modelQ η δ s x)
      + deriv (modelSigma η δ s) x
      = (modelSigma η δ s x * deriv (modelSigma η δ s) x + x
          + deriv (modelSigma η δ s) x * Real.sqrt (modelQ η δ s x))
        / Real.sqrt (modelQ η δ s x) := by
    field_simp
    try ring
  rw [hdiv]
  exact div_pos hkey hsqpos

/-! ## Strict monotonicity of `H` on `[0,2]` -/

lemma continuous_modelH {η δ s : ℝ} (hδ : 0 < δ) (h2 : 0 < 2 - 4*δ) :
    Continuous (modelH η δ s) := by
  have hsig : Continuous (modelSigma η δ s) := by
    rw [show modelSigma η δ s = fun y => s + saddleM δ y * (-η - s)
        from funext fun y => modelSigma_eq η δ s y]
    exact continuous_const.add (((contDiff_saddleM hδ h2).continuous).mul continuous_const)
  have hq : Continuous (modelQ η δ s) := by
    rw [show modelQ η δ s = (fun y : ℝ => modelSigma η δ s y ^ 2) + (fun y : ℝ => y ^ 2)
        from rfl]
    exact (hsig.pow 2).add (continuous_id.pow 2)
  rw [show modelH η δ s = fun y => Real.sqrt (modelQ η δ s y) + modelSigma η δ s y
      from funext fun y => modelH_eq η δ s y]
  exact (Real.continuous_sqrt.comp hq).add hsig

lemma strictMonoOn_modelH {η δ s C₀ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/10) (hη : 0 < η)
    (hη' : η < 1/10) (hs : 0 < s) (hsη : s ≤ η)
    (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀) (hsmall : 4 * C₀ * η ≤ δ) :
    StrictMonoOn (modelH η δ s) (Set.Icc 0 2) := by
  have h2 : 0 < 2 - 4*δ := by linarith
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 2)
    (continuous_modelH (η := η) (δ := δ) (s := s) hδ h2).continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  exact deriv_modelH_pos hδ hδ' hη hη' hs hsη hC₀ hsmall hx

open scoped Manifold ContDiff Topology in
/-- **The `Re √` twin of the key saddle estimate** (§4 `D2d.4` of `N2Lead/NOTES_LEAD_mobiusSaddle.md`;
consumed by `mobius_upperArcs`, which needs `Re ρ` strictly monotone in `|w|`, and by the `D2b`/`D2c`
arc rows).  With `σ w := saddleSigma η δ (s, w)` and `ζ w := σ w + i w`, the function
`w ↦ (√(ζ w)).re` is **even** and **strictly increasing on `[0,2]`**.  Unlike the `Im √` estimate
(`Work.Drive.N2Lead.modelArc_im_strictMonoOn`, where the sign is structural because `σ' ≤ 0` and
`-σ' b ≥ 0`), here the derivative `(σ' * a + b) / (2 * |ζ w|)` (with `a + i b = √(ζ w)`) needs
`b > |σ'| * a` in the transition zone, so the smallness hypothesis `4 C₀ η ≤ δ` **is** used: it gives
`|σ'| ≤ C₀ * η / δ + 2 * C₀ * η ≤ 1/4 + δ/2` there, while `b / a = w / (|ζ| + σ) ≥ 1.6/1.8` because
the transition zone is `[2 - 4δ, 2 - 2δ] ⊂ (1.6, 2)` and `|σ| ≤ η < 1/10`.  Off the transition zone
`σ' = 0` and the derivative is `b / (2 |ζ|) ≥ 0`, positive for `w > 0` and `0` at `w = 0` (where
`ζ = s > 0`, because `0 ≤ 2 - 4δ`).  The evenness follows from `ζ (-w) = conj (ζ w)` and
`Complex.sqrt_conj` (equivalently `Re √z = √((|z| + Re z)/2)`, which is conjugation-invariant; no
branch-cut caveat: for `z` a negative real both sides are `0`).  The result goes in namespace
`Work.Drive.N2Lead`. -/
theorem modelArc_re_strictMono {η δ s C₀ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η) (hη' : η < 1 / 10)
    (hs : 0 < s) (hsη : s ≤ η)
    (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀) (hsmall : 4 * C₀ * η ≤ δ) :
    StrictMonoOn (fun w : ℝ =>
      (Complex.sqrt ((Work.Drive.N2.saddleSigma η δ (s, w) : ℂ) + (w : ℂ) * Complex.I)).re)
      (Set.Icc 0 2) ∧
    (∀ w : ℝ,
      (Complex.sqrt ((Work.Drive.N2.saddleSigma η δ (s, -w) : ℂ) + ((-w : ℝ) : ℂ) * Complex.I)).re
        = (Complex.sqrt ((Work.Drive.N2.saddleSigma η δ (s, w) : ℂ) + (w : ℂ) * Complex.I)).re) := by
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    have hlt : modelH η δ s a < modelH η δ s b :=
      strictMonoOn_modelH (η := η) (δ := δ) (s := s) (C₀ := C₀)
        hδ hδ' hη hη' hs hsη hC₀ hsmall ha hb hab
    have hnn : 0 ≤ modelH η δ s a := modelH_nonneg η δ s a
    change modelArcRe η δ s a < modelArcRe η δ s b
    rw [modelArcRe_eq, modelArcRe_eq]
    exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
  · intro w
    change modelArcRe η δ s (-w) = modelArcRe η δ s w
    rw [modelArcRe_eq, modelArcRe_eq, modelH_even]

end Work.Drive.N2Lead
