import Mathlib
import Submission.Commons.Analysis.Complex.contour_shift_residue
import Submission.Commons.Analysis.Complex.integral_curve_cross
import Submission.Commons.Analysis.Complex.rectIntegral_sub_inv_inside

/-!
# Contour shift with several poles (generalisation of `Commons.Analysis.Complex.contour_shift_residue`)

`Commons.Analysis.Complex.contour_shift_residue` shifts the vertical line `Re z = c > 0` to the
curve `Γ₀ = {Re = -β/log(|Im|+2)}` for a function `g` that is differentiable on the closed region
between them except for a SINGLE simple pole at `0` (with residue `r`).

This result generalises it to a FINITE set `S` of simple poles strictly inside the region, each with
its own residue.  The proof is the same as the existing one: `g - ∑_{s ∈ S} res s / (z - s)` is
analytic on the closed region (removable singularities at the poles), so its integral over `∂D_T`
vanishes, while `∫_{∂D_T} dz/(z-s) = 2πi` for each `s` inside the contour.

Concretely, in the Green–Tao application the two poles are `0` and `-z` (for a fixed parameter `z`
lying on `Γ₀`).  The existing single-pole result is the special case `S = {0}`.

USEFUL HINT: the existing file `Submission/Commons/Analysis/Complex/contour_shift_residue.lean`
contains all the geometric work (`phi`, `gam`, `gamDot`, `graph_region_cauchy_mono`, the trapezoid
approximation, `horizTerm`).  Adapting it means replacing the single residue computation
`∫_{∂D_T} dz/z = 2π i` by `∑_{s ∈ S} ∫_{∂D_T} dz/(z-s) = 2π i · #S` and the residue term
accordingly.  It is also acceptable to deduce this from the single-pole version by an induction on
`S` if that is easier.
-/
set_option autoImplicit false

open Complex MeasureTheory intervalIntegral Filter Set
open scoped Topology Interval BigOperators ComplexConjugate

namespace Commons.Analysis.Complex

noncomputable section

variable {β c : ℝ}

/-! ## The contour integral of `(z - s)⁻¹` for a pole `s` strictly inside the contour

We compute `Bfun β c (fun z => (z - s)⁻¹) T = 2πi` for every `s` strictly inside the trapezoid
`D_T`.  The three pieces are computed with the fundamental theorem of calculus: the vertical side
and the two horizontal sides are `rectInt_vertical_integral_mul_I` and `rectInt_horizontal_integral`,
while the curved side is a logarithm difference with a `-2πi` correction coming from the branch cut
crossing of `z ↦ log (z - s)` along the curve. -/

/-- For `y ∈ [-T,T]` and `s` strictly inside `D_T`, the curve `gam` avoids `s`. -/
lemma gam_ne_of_mem_Icc {β : ℝ} {T y : ℝ} {s : ℂ}
    (hsre : phi β s.im < s.re) (hy : y ∈ Set.Icc (-T) T) (heq : gam β y = s) : False := by
  have h1 : s.im = y := by rw [← gam_im β y, heq]
  have h2 : s.re = phi β y := by
    have : (gam β y).re = phi β y := by simp [gam]
    rw [heq] at this; exact this
  rw [h1, h2] at hsre
  exact lt_irrefl _ hsre

/-- The curve `z - s` along `gam` is in the slit plane whenever its imaginary part `y - s.im`
does not vanish. -/
lemma gam_sub_mem_slitPlane {β : ℝ} {s : ℂ} {y : ℝ} (hy : y ≠ s.im) :
    gam β y - s ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  have : (gam β y - s).im = y - s.im := by
    rw [Complex.sub_im, gam_im]
  rw [this]
  exact sub_ne_zero.mpr hy

/-- Derivative of the local primitive `log (gam y - s)` at a point where it is holomorphic. -/
lemma hasDerivAt_log_gam_sub {β : ℝ} {s : ℂ} {y : ℝ} (hy : y ≠ 0) (hslit : y ≠ s.im) :
    HasDerivAt (fun y : ℝ => Complex.log (gam β y - s))
      ((gam β y - s)⁻¹ * gamDot β y) y := by
  have h1 : HasDerivAt (fun y : ℝ => gam β y - s) (gamDot β y) y :=
    (hasDerivAt_gam (β := β) hy).sub_const s
  have h2 : HasDerivAt (fun y : ℝ => Complex.log (gam β y - s))
      (gamDot β y / (gam β y - s)) y :=
    HasDerivAt.clog_real h1 (gam_sub_mem_slitPlane (β := β) hslit)
  refine h2.congr_deriv ?_
  rw [div_eq_inv_mul, mul_comm]

/-- The shifted integrand is interval integrable on `[-T,T]`. -/
lemma intervalIntegrable_curve_sub_inv {β : ℝ} (hβ : 0 < β) {s : ℂ}
    (hsre : phi β s.im < s.re) {T : ℝ} (hT : 0 < T) (hsimlo : -T < s.im) (hsimhi : s.im < T) :
    IntervalIntegrable (fun y : ℝ => (gam β y - s)⁻¹ * gamDot β y) volume (-T) T := by
  have hne : ∀ y ∈ Set.Icc (-T) T, gam β y ≠ s := fun y hy h =>
    gam_ne_of_mem_Icc (β := β) hsre hy h
  have hleft : IntervalIntegrable (fun y : ℝ => (gam β y - s)⁻¹ * gamDot β y)
      volume (-T) 0 := by
    have hcont : ContinuousOn (fun y : ℝ => (gam β y - s)⁻¹ * gamDotNeg β y)
        (Set.Icc (-T) 0) := by
      refine ContinuousOn.mul (ContinuousOn.inv₀ ?_ ?_) (continuousOn_gamDotNeg β T)
      · exact (gam_continuous β).continuousOn.sub continuousOn_const
      · intro y hy
        exact sub_ne_zero.mpr (hne y ⟨hy.1, le_trans hy.2 hT.le⟩)
    rw [← Set.uIcc_of_le (by linarith : (-T:ℝ) ≤ 0)] at hcont
    exact (intervalIntegrable_congr_uIoo
      (f := fun y : ℝ => (gam β y - s)⁻¹ * gamDot β y)
      (g := fun y : ℝ => (gam β y - s)⁻¹ * gamDotNeg β y) (by
        intro y hy
        rw [Set.uIoo_of_le (by linarith : -T ≤ 0)] at hy
        simp only [gamDot, gamDotNeg, Phi', if_neg (not_le.mpr hy.2)])).mpr
      hcont.intervalIntegrable
  have hright : IntervalIntegrable (fun y : ℝ => (gam β y - s)⁻¹ * gamDot β y)
      volume 0 T := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hT.le]
    exact ContinuousOn.mul (ContinuousOn.inv₀
      ((gam_continuous β).continuousOn.sub continuousOn_const)
      (fun y hy => sub_ne_zero.mpr (hne y ⟨le_trans (by linarith) hy.1, hy.2⟩)))
      (continuousOn_gamDot_nonneg β T)
  exact hleft.trans hright

/-! ## One-sided limits of the primitive along the curve -/

/-- Continuity of the primitive at a point where the curve avoids `s`. -/
lemma continuousAt_log_gam_sub {β : ℝ} {s : ℂ} {y : ℝ} (hy : y ≠ s.im) :
    ContinuousAt (fun y : ℝ => Complex.log (gam β y - s)) y :=
  ((gam_continuous β).continuousAt.sub_const s).clog (gam_sub_mem_slitPlane (β := β) hy)

lemma gam_sub_sim_re {β : ℝ} {s : ℂ} : (gam β s.im - s).re = phi β s.im - s.re := by
  simp [gam]
lemma gam_sub_sim_im {β : ℝ} {s : ℂ} : (gam β s.im - s).im = 0 := by
  simp [gam, gam_im]

/-- One-sided limits of the primitive at `s.im`, where the curve crosses the branch cut. -/
lemma tendsto_log_gam_sub_at_sim_left {β : ℝ} {s : ℂ} (hsre : phi β s.im < s.re) :
    Tendsto (fun y : ℝ => Complex.log (gam β y - s)) (𝓝[<] s.im)
      (𝓝 ((Real.log ‖gam β s.im - s‖ : ℂ) - (Real.pi : ℂ) * Complex.I)) := by
  have hzre : (gam β s.im - s).re < 0 := by
    rw [gam_sub_sim_re]; linarith
  have hlog := Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hzre gam_sub_sim_im
  have h1 : Tendsto (fun y : ℝ => gam β y - s) (𝓝[<] s.im) (𝓝 (gam β s.im - s)) :=
    (Tendsto.sub_const ((gam_continuous β).continuousAt (x := s.im)) s).mono_left inf_le_left
  have h2 : Tendsto (fun y : ℝ => gam β y - s) (𝓝[<] s.im) (𝓟 {z : ℂ | z.im < 0}) := by
    rw [tendsto_principal]
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [Complex.sub_im, gam_im]
    exact sub_neg.mpr hy
  exact hlog.comp ((h1.inf h2).mono_left (le_inf le_rfl le_rfl))

/-- The other one-sided limit at `s.im`. -/
lemma tendsto_log_gam_sub_at_sim_right {β : ℝ} {s : ℂ} (hsre : phi β s.im < s.re) :
    Tendsto (fun y : ℝ => Complex.log (gam β y - s)) (𝓝[>] s.im)
      (𝓝 ((Real.log ‖gam β s.im - s‖ : ℂ) + (Real.pi : ℂ) * Complex.I)) := by
  have hzre : (gam β s.im - s).re < 0 := by
    rw [gam_sub_sim_re]; linarith
  have hlog := Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hzre gam_sub_sim_im
  have h1 : Tendsto (fun y : ℝ => gam β y - s) (𝓝[>] s.im) (𝓝 (gam β s.im - s)) :=
    (Tendsto.sub_const ((gam_continuous β).continuousAt (x := s.im)) s).mono_left inf_le_left
  have h2 : Tendsto (fun y : ℝ => gam β y - s) (𝓝[>] s.im) (𝓟 {z : ℂ | 0 ≤ z.im}) := by
    rw [tendsto_principal]
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [Complex.sub_im, gam_im]
    exact sub_nonneg.mpr hy.le
  exact hlog.comp ((h1.inf h2).mono_left (le_inf le_rfl le_rfl))

/-- Same, at the origin, when `s.im ≠ 0` (so the origin is not a branch-cut crossing). -/
lemma tendsto_log_gam_sub_at_zero_left {β : ℝ} {s : ℂ} (hs : s.im ≠ 0) :
    Tendsto (fun y : ℝ => Complex.log (gam β y - s)) (𝓝[<] (0:ℝ))
      (𝓝 (Complex.log (gam β 0 - s))) :=
  (continuousAt_log_gam_sub (β := β) (s := s) (Ne.symm hs)).mono_left inf_le_left

lemma tendsto_log_gam_sub_at_zero_right {β : ℝ} {s : ℂ} (hs : s.im ≠ 0) :
    Tendsto (fun y : ℝ => Complex.log (gam β y - s)) (𝓝[>] (0:ℝ))
      (𝓝 (Complex.log (gam β 0 - s))) :=
  (continuousAt_log_gam_sub (β := β) (s := s) (Ne.symm hs)).mono_left inf_le_left

lemma tendsto_log_gam_sub_at_T {β : ℝ} {s : ℂ} {T : ℝ} (hT : s.im ≠ T) :
    Tendsto (fun y : ℝ => Complex.log (gam β y - s)) (𝓝[<] T)
      (𝓝 (Complex.log (gam β T - s))) :=
  (continuousAt_log_gam_sub (β := β) (s := s) (y := T) (Ne.symm hT)).mono_left inf_le_left

lemma tendsto_log_gam_sub_at_negT {β : ℝ} {s : ℂ} {T : ℝ} (hT : s.im ≠ -T) :
    Tendsto (fun y : ℝ => Complex.log (gam β y - s)) (𝓝[>] (-T))
      (𝓝 (Complex.log (gam β (-T) - s))) :=
  (continuousAt_log_gam_sub (β := β) (s := s) (y := -T) (Ne.symm hT)).mono_left inf_le_left

/-! ## Interval integrability of the shifted integrand on pieces -/

lemma intervalIntegrable_curve_sub_inv_of_pos {β : ℝ} {s : ℂ} {p q : ℝ} (hp : 0 ≤ p)
    (hpq : p ≤ q) (hne : ∀ y ∈ Set.Icc p q, gam β y ≠ s) :
    IntervalIntegrable (fun y : ℝ => (gam β y - s)⁻¹ * gamDot β y) volume p q := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hpq]
  refine ContinuousOn.mul (ContinuousOn.inv₀
    ((gam_continuous β).continuousOn.sub continuousOn_const) ?_) ?_
  · intro y hy; exact sub_ne_zero.mpr (hne y hy)
  · refine ((continuousOn_gamDotPos β q).mono ?_).congr ?_
    · intro y hy; exact ⟨le_trans hp hy.1, hy.2⟩
    · intro y hy
      simp only [gamDot, gamDotPos, Phi', if_pos (le_trans hp hy.1)]

lemma intervalIntegrable_curve_sub_inv_of_neg {β : ℝ} {s : ℂ} {p q : ℝ} (hq : q ≤ 0)
    (hpq : p ≤ q) (hne : ∀ y ∈ Set.Icc p q, gam β y ≠ s) :
    IntervalIntegrable (fun y : ℝ => (gam β y - s)⁻¹ * gamDot β y) volume p q := by
  refine (intervalIntegrable_congr_uIoo
    (f := fun y : ℝ => (gam β y - s)⁻¹ * gamDot β y)
    (g := fun y : ℝ => (gam β y - s)⁻¹ * gamDotNeg β y) ?_).mpr ?_
  · intro y hy
    rw [Set.uIoo_of_le hpq] at hy
    simp only [gamDot, gamDotNeg, Phi', if_neg (not_le.mpr (lt_of_lt_of_le hy.2 hq))]
  · refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hpq]
    refine ContinuousOn.mul (ContinuousOn.inv₀
      ((gam_continuous β).continuousOn.sub continuousOn_const) ?_) ?_
    · intro y hy; exact sub_ne_zero.mpr (hne y hy)
    · refine ((continuousOn_gamDotNeg β (-p)).mono ?_)
      intro y hy
      exact ⟨by linarith [hy.1], le_trans hy.2 hq⟩

/-! ## The curved side of the contour -/

/-- Integral along the curved side of `∂D_T` of `(z - s)⁻¹ dz`, for `s` strictly inside. -/
lemma integral_curve_sub_inv {β : ℝ} {s : ℂ} (hsre : phi β s.im < s.re)
    {T : ℝ} (hT : 0 < T) (hsimlo : -T < s.im) (hsimhi : s.im < T) :
    (∫ y in (-T)..T, (gam β y - s)⁻¹ * gamDot β y)
      = Complex.log (gam β T - s) - Complex.log (gam β (-T) - s)
        - 2 * (Real.pi : ℂ) * Complex.I := by
  have hneC : ∀ {p q : ℝ}, -T ≤ p → q ≤ T → ∀ y ∈ Set.Icc p q, gam β y ≠ s := by
    intro p q hp hq y hy h
    exact gam_ne_of_mem_Icc (β := β) hsre ⟨le_trans hp hy.1, le_trans hy.2 hq⟩ h
  have hderiv : ∀ {p q : ℝ} (hpq : p ≤ q),
      (∀ y ∈ Set.Ioo p q, y ≠ 0) → (∀ y ∈ Set.Ioo p q, y ≠ s.im) →
      (∀ y ∈ Set.Ioo p q, HasDerivAt (fun y : ℝ => Complex.log (gam β y - s))
        ((gam β y - s)⁻¹ * gamDot β y) y) := by
    intro p q hpq h0 hs y hy
    exact hasDerivAt_log_gam_sub (β := β) (h0 y hy) (hs y hy)
  rcases lt_trichotomy s.im 0 with hlt | heq | hgt
  · -- s.im < 0
    have hint1 : IntervalIntegrable (fun y : ℝ => (gam β y - s)⁻¹ * gamDot β y)
        volume (-T) s.im :=
      intervalIntegrable_curve_sub_inv_of_neg (β := β) (s := s) hlt.le (by linarith)
        (hneC (le_rfl) (by linarith))
    have hint2 : IntervalIntegrable (fun y : ℝ => (gam β y - s)⁻¹ * gamDot β y)
        volume s.im 0 :=
      intervalIntegrable_curve_sub_inv_of_neg (β := β) (s := s) le_rfl hlt.le
        (hneC (by linarith) (by linarith))
    have hint3 : IntervalIntegrable (fun y : ℝ => (gam β y - s)⁻¹ * gamDot β y)
        volume (0:ℝ) T :=
      intervalIntegrable_curve_sub_inv_of_pos (β := β) (s := s) le_rfl hT.le
        (hneC (by linarith) (le_rfl))
    have h1 : (∫ y in (-T)..s.im, (gam β y - s)⁻¹ * gamDot β y)
        = ((Real.log ‖gam β s.im - s‖ : ℂ) - (Real.pi : ℂ) * Complex.I)
          - Complex.log (gam β (-T) - s) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by linarith)
        (hderiv (by linarith) (fun y hy => by linarith [hy.1, hy.2, hlt])
          (fun y hy => by linarith [hy.2])) hint1
        (tendsto_log_gam_sub_at_negT (β := β) (s := s) (T := T) (by linarith))
        (tendsto_log_gam_sub_at_sim_left (β := β) (s := s) hsre)
    have h2 : (∫ y in s.im..0, (gam β y - s)⁻¹ * gamDot β y)
        = Complex.log (gam β 0 - s)
          - ((Real.log ‖gam β s.im - s‖ : ℂ) + (Real.pi : ℂ) * Complex.I) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hlt
        (hderiv hlt.le (fun y hy => by linarith [hy.2])
          (fun y hy => by linarith [hy.1])) hint2
        (tendsto_log_gam_sub_at_sim_right (β := β) (s := s) hsre)
        (tendsto_log_gam_sub_at_zero_left (β := β) (s := s) (ne_of_lt hlt))
    have h3 : (∫ y in (0:ℝ)..T, (gam β y - s)⁻¹ * gamDot β y)
        = Complex.log (gam β T - s) - Complex.log (gam β 0 - s) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hT
        (hderiv hT.le (fun y hy => by linarith [hy.1])
          (fun y hy => by linarith [hy.1, hlt])) hint3
        (tendsto_log_gam_sub_at_zero_right (β := β) (s := s) (ne_of_lt hlt))
        (tendsto_log_gam_sub_at_T (β := β) (s := s) (T := T) (by linarith))
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 (hint2.trans hint3),
      ← intervalIntegral.integral_add_adjacent_intervals hint2 hint3, h1, h2, h3]
    ring
  · -- s.im = 0
    have hlimL : Tendsto (fun y : ℝ => Complex.log (gam β y - s)) (𝓝[<] (0:ℝ))
        (𝓝 ((Real.log ‖gam β 0 - s‖ : ℂ) - (Real.pi : ℂ) * Complex.I)) := by
      have h := tendsto_log_gam_sub_at_sim_left (β := β) (s := s) hsre
      rwa [heq] at h
    have hlimR : Tendsto (fun y : ℝ => Complex.log (gam β y - s)) (𝓝[>] (0:ℝ))
        (𝓝 ((Real.log ‖gam β 0 - s‖ : ℂ) + (Real.pi : ℂ) * Complex.I)) := by
      have h := tendsto_log_gam_sub_at_sim_right (β := β) (s := s) hsre
      rwa [heq] at h
    have hint1 : IntervalIntegrable (fun y : ℝ => (gam β y - s)⁻¹ * gamDot β y)
        volume (-T) 0 :=
      intervalIntegrable_curve_sub_inv_of_neg (β := β) (s := s) le_rfl (by linarith)
        (hneC (le_rfl) (by linarith))
    have hint2 : IntervalIntegrable (fun y : ℝ => (gam β y - s)⁻¹ * gamDot β y)
        volume (0:ℝ) T :=
      intervalIntegrable_curve_sub_inv_of_pos (β := β) (s := s) le_rfl hT.le
        (hneC (by linarith) (le_rfl))
    have h1 : (∫ y in (-T)..0, (gam β y - s)⁻¹ * gamDot β y)
        = ((Real.log ‖gam β 0 - s‖ : ℂ) - (Real.pi : ℂ) * Complex.I)
          - Complex.log (gam β (-T) - s) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by linarith)
        (hderiv (by linarith) (fun y hy => by linarith [hy.2])
          (fun y hy => by rw [heq]; linarith [hy.2])) hint1
        (tendsto_log_gam_sub_at_negT (β := β) (s := s) (T := T) (by linarith))
        hlimL
    have h2 : (∫ y in (0:ℝ)..T, (gam β y - s)⁻¹ * gamDot β y)
        = Complex.log (gam β T - s)
          - ((Real.log ‖gam β 0 - s‖ : ℂ) + (Real.pi : ℂ) * Complex.I) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hT
        (hderiv hT.le (fun y hy => by linarith [hy.1])
          (fun y hy => by rw [heq]; linarith [hy.1])) hint2
        hlimR
        (tendsto_log_gam_sub_at_T (β := β) (s := s) (T := T) (by linarith))
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2, h1, h2]
    ring
  · -- s.im > 0
    have hint1 : IntervalIntegrable (fun y : ℝ => (gam β y - s)⁻¹ * gamDot β y)
        volume (-T) 0 :=
      intervalIntegrable_curve_sub_inv_of_neg (β := β) (s := s) le_rfl (by linarith)
        (hneC (le_rfl) (by linarith))
    have hint2 : IntervalIntegrable (fun y : ℝ => (gam β y - s)⁻¹ * gamDot β y)
        volume (0:ℝ) s.im :=
      intervalIntegrable_curve_sub_inv_of_pos (β := β) (s := s) le_rfl hgt.le
        (hneC (by linarith) (by linarith))
    have hint3 : IntervalIntegrable (fun y : ℝ => (gam β y - s)⁻¹ * gamDot β y)
        volume s.im T :=
      intervalIntegrable_curve_sub_inv_of_pos (β := β) (s := s) hgt.le hsimhi.le
        (hneC (by linarith) (le_rfl))
    have h1 : (∫ y in (-T)..0, (gam β y - s)⁻¹ * gamDot β y)
        = Complex.log (gam β 0 - s) - Complex.log (gam β (-T) - s) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by linarith)
        (hderiv (by linarith) (fun y hy => by linarith [hy.2])
          (fun y hy => by linarith [hy.2, hgt])) hint1
        (tendsto_log_gam_sub_at_negT (β := β) (s := s) (T := T) (by linarith))
        (tendsto_log_gam_sub_at_zero_left (β := β) (s := s) (ne_of_gt hgt))
    have h2 : (∫ y in (0:ℝ)..s.im, (gam β y - s)⁻¹ * gamDot β y)
        = ((Real.log ‖gam β s.im - s‖ : ℂ) - (Real.pi : ℂ) * Complex.I)
          - Complex.log (gam β 0 - s) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hgt
        (hderiv hgt.le (fun y hy => by linarith [hy.1])
          (fun y hy => by linarith [hy.2])) hint2
        (tendsto_log_gam_sub_at_zero_right (β := β) (s := s) (ne_of_gt hgt))
        (tendsto_log_gam_sub_at_sim_left (β := β) (s := s) hsre)
    have h3 : (∫ y in s.im..T, (gam β y - s)⁻¹ * gamDot β y)
        = Complex.log (gam β T - s)
          - ((Real.log ‖gam β s.im - s‖ : ℂ) + (Real.pi : ℂ) * Complex.I) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hsimhi
        (hderiv hsimhi.le (fun y hy => by linarith [hy.1, hgt])
          (fun y hy => by linarith [hy.1])) hint3
        (tendsto_log_gam_sub_at_sim_right (β := β) (s := s) hsre)
        (tendsto_log_gam_sub_at_T (β := β) (s := s) (T := T) (by linarith))
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 (hint2.trans hint3),
      ← intervalIntegral.integral_add_adjacent_intervals hint2 hint3, h1, h2, h3]
    ring

/-! ## The contour integral of a single shifted pole -/

/-- **Winding number of a single pole inside the contour**: the boundary integral
`∫_{∂D_T} dz/(z - s)` equals `2πi` for `s` strictly inside `D_T`. -/
lemma Bfun_sub_inv {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {T : ℝ} (hT : 0 < T) {s : ℂ}
    (hsre : phi β s.im < s.re) (hsre2 : s.re < c) (hlo : -T < s.im) (hhi : s.im < T) :
    Bfun β c (fun z => (z - s)⁻¹) T = 2 * (Real.pi : ℂ) * Complex.I := by
  have hvert := rectInt_vertical_integral_mul_I (c := -T) (d := T) (s := c) (u := s) hsre2
  have htop := rectInt_horizontal_integral (a := phi β T) (b := c) (r := T) (u := s)
    (by linarith)
  have hbot := rectInt_horizontal_integral (a := phi β (-T)) (b := c) (r := -T) (u := s)
    (by linarith)
  have hcurve := integral_curve_sub_inv (β := β) (s := s) hsre hT hlo hhi
  rw [Bfun, ← intervalIntegral.integral_const_mul, hvert, hcurve, htop, hbot]
  simp only [gam]
  ring


/-! ## A ball around an interior point inside the region -/

lemma exists_ball_subset_region {β : ℝ} (hβ : 0 < β) {c : ℝ} {s : ℂ}
    (hs1 : phi β s.im < s.re) (hs2 : s.re < c) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, dist z s < ρ → phi β z.im ≤ z.re ∧ z.re ≤ c := by
  have hδ : 0 < s.re - phi β s.im := sub_pos.mpr hs1
  have hhalf : phi β s.im < phi β s.im + (s.re - phi β s.im) / 2 := by linarith
  have hev : ∀ᶠ y in 𝓝 s.im, phi β y < phi β s.im + (s.re - phi β s.im) / 2 :=
    ((continuous_phi β).continuousAt).eventually (eventually_lt_nhds hhalf)
  obtain ⟨ε, hε, hε'⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min (ε / 2) (min ((s.re - phi β s.im) / 4) ((c - s.re) / 4)), ?_, ?_⟩
  · exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  · intro z hz
    have him : dist z.im s.im < ε := by
      have h1 : dist z.im s.im ≤ dist z s := by
        rw [Complex.dist_eq, Real.dist_eq]
        simpa using Complex.abs_im_le_norm (z - s)
      have h2 : dist z s < ε / 2 := lt_of_lt_of_le hz (min_le_left _ _)
      linarith
    have hre1 : |z.re - s.re| ≤ dist z s := by
      rw [Complex.dist_eq]
      simpa using Complex.abs_re_le_norm (z - s)
    have hre2 : dist z s < (s.re - phi β s.im) / 4 :=
      lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _))
    have hre3 : dist z s < (c - s.re) / 4 :=
      lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_right _ _))
    have hlt := hε' him
    constructor
    · have h3 : z.re > s.re - (s.re - phi β s.im) / 4 := by
        have := abs_lt.mp (lt_of_le_of_lt hre1 hre2)
        linarith [this.2]
      linarith
    · have h5 : z.re < s.re + (c - s.re) / 4 := by
        have := abs_lt.mp (lt_of_le_of_lt hre1 hre3)
        linarith [this.1]
      linarith

lemma differentiableAt_const_div_sub {a b : ℂ} {z : ℂ} (h : z ≠ b) :
    DifferentiableAt ℂ (fun w : ℂ => a / (w - b)) z :=
  (differentiableAt_const a).div (differentiableAt_id.sub (differentiableAt_const b))
    (sub_ne_zero.mpr h)

lemma differentiableAt_finset_sum_div {S : Finset ℂ} (res : ℂ → ℂ) {w : ℂ}
    (hw : ∀ s ∈ S, w ≠ s) :
    DifferentiableAt ℂ (fun z : ℂ => ∑ s ∈ S, res s / (z - s)) w := by
  have hfun : (fun z : ℂ => ∑ s ∈ S, res s / (z - s))
      = ∑ s ∈ S, (fun z : ℂ => res s / (z - s)) := by
    funext z
    rw [Finset.sum_apply]
  rw [hfun]
  exact DifferentiableAt.sum (fun s hs => differentiableAt_const_div_sub (hw s hs))

/-! ## Removable singularity at a simple pole -/

/-- The function `w ↦ (g w - r/(w - s)) - W w` satisfies the little-`o` condition at `s` when
`g` has a simple pole of residue `r` at `s` and `W` is holomorphic near `s`. -/
lemma isLittleO_remove_pole {g W : ℂ → ℂ} {s r : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hdiff : ∀ z : ℂ, dist z s < ρ → z ≠ s → DifferentiableAt ℂ g z)
    (hres : Tendsto (fun z : ℂ => (z - s) * g z) (nhdsWithin s ({s}ᶜ : Set ℂ)) (nhds r))
    (hW : ∀ z : ℂ, dist z s < ρ → DifferentiableAt ℂ W z) :
    (fun z : ℂ => ((g z - r / (z - s)) - W z) - ((g s - r / (s - s)) - W s))
      =o[nhdsWithin s ({s}ᶜ : Set ℂ)] (fun z : ℂ => (z - s)⁻¹) := by
  have hWlim : Tendsto W (nhdsWithin s ({s}ᶜ : Set ℂ)) (nhds (W s)) :=
    (((hW s (by simpa using hρ)).continuousAt).tendsto).mono_left inf_le_left
  have hid : Tendsto (fun z : ℂ => z - s) (𝓝[≠] s) (nhds 0) := by
    have h : Tendsto (fun z : ℂ => z) (𝓝[≠] s) (nhds s) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa using h.sub_const s
  have hF : Tendsto (fun z : ℂ => (z - s) *
      (((g z - r / (z - s)) - W z) - ((g s - r / (s - s)) - W s))) (𝓝[≠] s) (nhds 0) := by
    have hclean : Tendsto (fun z : ℂ => ((z - s) * g z - r) - (z - s) * W z
        - (z - s) * ((g s - r / (s - s)) - W s)) (𝓝[≠] s) (nhds 0) := by
      have h1 : Tendsto (fun z : ℂ => (z - s) * g z - r) (𝓝[≠] s) (nhds 0) := by
        simpa using hres.sub_const r
      have h2 : Tendsto (fun z : ℂ => (z - s) * W z) (𝓝[≠] s) (nhds 0) := by
        simpa using hid.mul hWlim
      have h3 : Tendsto (fun z : ℂ => (z - s) * ((g s - r / (s - s)) - W s))
          (𝓝[≠] s) (nhds 0) := by
        simpa using hid.mul_const (((g s - r / (s - s)) - W s))
      simpa using (h1.sub h2).sub h3
    refine hclean.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzs : z ≠ s := by simpa using hz
    have hs' : z - s ≠ 0 := sub_ne_zero.mpr hzs
    field_simp
  refine Asymptotics.IsLittleO.of_bound (fun ε hε => ?_)
  filter_upwards [Metric.tendsto_nhds.mp hF ε hε, self_mem_nhdsWithin] with z hzc hzne
  have hzs : z ≠ s := by simpa using hzne
  have hzn : 0 < ‖z - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzs)
  rw [dist_zero_right, norm_mul] at hzc
  rw [norm_inv, ← div_eq_mul_inv, le_div_iff₀ hzn]
  exact (calc ‖((g z - r / (z - s)) - W z) - ((g s - r / (s - s)) - W s)‖ * ‖z - s‖
      = ‖z - s‖ * ‖((g z - r / (z - s)) - W z) - ((g s - r / (s - s)) - W s)‖ := by ring
    _ < ε := hzc).le

/-- **Removable singularity for a shifted simple pole.** -/
lemma differentiableAt_update_limUnder_pole {g W : ℂ → ℂ} {s r : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hdiff : ∀ z : ℂ, dist z s < ρ → z ≠ s → DifferentiableAt ℂ g z)
    (hres : Tendsto (fun z : ℂ => (z - s) * g z) (nhdsWithin s ({s}ᶜ : Set ℂ)) (nhds r))
    (hW : ∀ z : ℂ, dist z s < ρ → DifferentiableAt ℂ W z) :
    DifferentiableAt ℂ (Function.update (fun z : ℂ => (g z - r / (z - s)) - W z) s
      ((nhdsWithin s ({s}ᶜ : Set ℂ)).limUnder fun z : ℂ => (g z - r / (z - s)) - W z)) s := by
  have hball : Metric.ball s ρ ∈ nhds s := Metric.ball_mem_nhds s hρ
  have hd : DifferentiableOn ℂ (fun z : ℂ => (g z - r / (z - s)) - W z)
      (Metric.ball s ρ \ {s}) := by
    intro z hz
    have hz0 : z ≠ s := by simpa using hz.2
    have hzd : dist z s < ρ := Metric.mem_ball.mp hz.1
    exact (((hdiff z hzd hz0).sub (differentiableAt_const_div_sub (a := r) (b := s)
      hz0)).sub (hW z hzd)).differentiableWithinAt
  exact (Complex.differentiableOn_update_limUnder_of_isLittleO (c := s) hball hd
    (isLittleO_remove_pole hρ hdiff hres hW)).differentiableAt hball

/-! ## The holomorphic extension of the residue-removed function -/

/-- A small ball around a point of a finite set meets the set only at that point. -/
lemma exists_ball_inter_finset {S : Finset ℂ} {z : ℂ} (hz : z ∈ S) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ w : ℂ, dist w z < ρ → w ∈ S → w = z := by
  have hopen : IsOpen ((↑(S.erase z) : Set ℂ)ᶜ) :=
    (Set.Finite.isClosed (S.erase z).finite_toSet).isOpen_compl
  have hmem : z ∈ (↑(S.erase z) : Set ℂ)ᶜ := by
    simp only [Set.mem_compl_iff, Finset.mem_coe]
    intro h
    rw [Finset.mem_erase] at h
    exact h.1 rfl
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
  refine ⟨ρ, hρ, fun w hw hwS => ?_⟩
  by_contra hne
  exact hρ' hw (Finset.mem_erase.mpr ⟨hne, hwS⟩)

/-- The residue-removed function `g - ∑_{s ∈ S} res s / (z - s)`, with the removable
singularities at the points of `S` filled in by the appropriate limits. -/
def gResExt (g : ℂ → ℂ) (S : Finset ℂ) (res : ℂ → ℂ) : ℂ → ℂ := fun z =>
  if h : z ∈ S then (nhdsWithin z ({z}ᶜ : Set ℂ)).limUnder
    (fun w => (g w - res z / (w - z)) - ∑ s ∈ S.erase z, res s / (w - s))
  else g z - ∑ s ∈ S, res s / (z - s)

lemma gResExt_of_notMem {g : ℂ → ℂ} {S : Finset ℂ} {res : ℂ → ℂ} {z : ℂ} (hz : z ∉ S) :
    gResExt g S res z = g z - ∑ s ∈ S, res s / (z - s) := dif_neg hz

/-- **The residue-removed function is holomorphic on the region.** -/
lemma gResExt_differentiableAt {β c : ℝ} (hβ : 0 < β) {g : ℂ → ℂ} {S : Finset ℂ} {res : ℂ → ℂ}
    (hS : ∀ s ∈ S, phi β s.im < s.re ∧ s.re < c)
    (hdiff : ∀ z : ℂ, phi β z.im ≤ z.re → z.re ≤ c → z ∉ S → DifferentiableAt ℂ g z)
    (hres : ∀ s ∈ S, Tendsto (fun z : ℂ => (z - s) * g z) (nhdsWithin s ({s}ᶜ : Set ℂ))
      (nhds (res s)))
    {z : ℂ} (hz1 : phi β z.im ≤ z.re) (hz2 : z.re ≤ c) :
    DifferentiableAt ℂ (gResExt g S res) z := by
  by_cases hzS : z ∈ S
  · obtain ⟨ρ₁, hρ₁, hball₁⟩ := exists_ball_subset_region hβ (hS z hzS).1 (hS z hzS).2
    obtain ⟨ρ₂, hρ₂, hball₂⟩ := exists_ball_inter_finset hzS
    have hρ : 0 < min ρ₁ ρ₂ := lt_min hρ₁ hρ₂
    have hdiff' : ∀ w : ℂ, dist w z < min ρ₁ ρ₂ → w ≠ z → DifferentiableAt ℂ g w := by
      intro w hw hwne
      refine hdiff w (hball₁ w (lt_of_lt_of_le hw (min_le_left _ _))).1
        (hball₁ w (lt_of_lt_of_le hw (min_le_left _ _))).2 (fun hwS => hwne ?_)
      exact hball₂ w (lt_of_lt_of_le hw (min_le_right _ _)) hwS
    have hW : ∀ w : ℂ, dist w z < min ρ₁ ρ₂ →
        DifferentiableAt ℂ (fun w : ℂ => ∑ s ∈ S.erase z, res s / (w - s)) w := by
      intro w hw
      refine differentiableAt_finset_sum_div (res := res) (hw := fun s hs h => ?_)
      have hsS : s ∈ S := (Finset.mem_erase.mp hs).2
      have hwz : w = z := hball₂ w (lt_of_lt_of_le hw (min_le_right _ _)) (h.symm ▸ hsS)
      exact (Finset.mem_erase.mp hs).1 (h.symm.trans hwz)
    have hpole := differentiableAt_update_limUnder_pole (g := g)
      (W := fun w : ℂ => ∑ s ∈ S.erase z, res s / (w - s)) (r := res z) hρ hdiff'
      (hres z hzS) hW
    refine hpole.congr_of_eventuallyEq ?_
    have h1 : (↑(S.erase z) : Set ℂ)ᶜ ∈ 𝓝 z :=
      (Set.Finite.isClosed (S.erase z).finite_toSet).isOpen_compl.mem_nhds
        (by
          simp only [Set.mem_compl_iff, Finset.mem_coe]
          intro h
          rw [Finset.mem_erase] at h
          exact h.1 rfl)
    filter_upwards [h1] with w hw1
    by_cases hw2 : w = z
    · subst hw2
      simp only [gResExt, dif_pos hzS, Function.update_apply]
      simp
    · have hwS : w ∉ S := fun h => hw1 (Finset.mem_erase.mpr ⟨hw2, h⟩)
      rw [Function.update_of_ne (f := fun w : ℂ => (g w - res z / (w - z)) -
            ∑ s ∈ S.erase z, res s / (w - s)) hw2, gResExt_of_notMem hwS,
        ← Finset.sum_erase_add S (fun s => res s / (w - s)) hzS]
      ring
  · have hd : DifferentiableAt ℂ (fun z : ℂ => g z - ∑ s ∈ S, res s / (z - s)) z := by
      refine (hdiff z hz1 hz2 hzS).sub ?_
      exact differentiableAt_finset_sum_div (res := res) (hw := fun s hs h => hzS (h ▸ hs))
    have heq : gResExt g S res =ᶠ[𝓝 z] fun w => g w - ∑ s ∈ S, res s / (w - s) := by
      filter_upwards [(Set.Finite.isClosed S.finite_toSet).isOpen_compl.mem_nhds (by simpa using hzS)]
        with w hw
      exact gResExt_of_notMem (by simpa using hw)
    exact hd.congr_of_eventuallyEq heq

/-! ## Linearity of the boundary functional in a finite sum of poles -/

lemma intervalIntegrable_vert_sub_inv {c : ℝ} {s : ℂ} (h : s.re < c) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun y : ℝ => ((c : ℂ) + (y : ℂ) * Complex.I - s)⁻¹) volume (-T) T := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le (by linarith : (-T:ℝ) ≤ T)]
  refine ContinuousOn.inv₀ (by fun_prop) (fun y hy => ?_)
  intro hzero
  have hz : ((c : ℂ) + (y : ℂ) * Complex.I - s).re = 0 := by rw [hzero]; simp
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero] at hz
  linarith

lemma intervalIntegrable_horiz_sub_inv {r : ℝ} {s : ℂ} (h : r ≠ s.im) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => ((x : ℂ) + (r : ℂ) * Complex.I - s)⁻¹) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.inv₀ (by fun_prop) (fun x hx => ?_)
  intro hzero
  have hz : ((x : ℂ) + (r : ℂ) * Complex.I - s).im = 0 := by rw [hzero]; simp
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at hz
  exact h (sub_eq_zero.mp hz)

/-- `Bfun` is additive over a finite sum of shifted inverse powers. -/
lemma Bfun_inv_sum {β c T : ℝ} (S : Finset ℂ) (res : ℂ → ℂ)
    (h1 : ∀ s ∈ S, IntervalIntegrable
      (fun y : ℝ => ((c : ℂ) + (y : ℂ) * Complex.I - s)⁻¹) volume (-T) T)
    (h2 : ∀ s ∈ S, IntervalIntegrable
      (fun y : ℝ => (gam β y - s)⁻¹ * gamDot β y) volume (-T) T)
    (h3 : ∀ s ∈ S, IntervalIntegrable
      (fun x : ℝ => ((x : ℂ) + (T : ℂ) * Complex.I - s)⁻¹) volume (phi β T) c)
    (h4 : ∀ s ∈ S, IntervalIntegrable
      (fun x : ℝ => ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I - s)⁻¹) volume (phi β (-T)) c) :
    Bfun β c (fun z => ∑ s ∈ S, res s / (z - s)) T
      = ∑ s ∈ S, res s * Bfun β c (fun z => (z - s)⁻¹) T := by
  have hv : (∫ y in (-T)..T, (∑ s ∈ S, res s / (((c : ℂ) + (y : ℂ) * Complex.I) - s)))
      = ∑ s ∈ S, res s * ∫ y in (-T)..T, (((c : ℂ) + (y : ℂ) * Complex.I) - s)⁻¹ := by
    rw [intervalIntegral.integral_finset_sum (s := S)
      (f := fun s (y : ℝ) => res s / (((c : ℂ) + (y : ℂ) * Complex.I) - s))
      (fun s hs => (h1 s hs).const_mul (res s))]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have hfun₁ : (fun y : ℝ => res s / (((c : ℂ) + (y : ℂ) * Complex.I) - s))
        = fun y : ℝ => res s * (((c : ℂ) + (y : ℂ) * Complex.I) - s)⁻¹ := by
      funext y; rw [div_eq_mul_inv]
    rw [hfun₁, intervalIntegral.integral_const_mul]
  have hw : (∫ y in (-T)..T, (∑ s ∈ S, res s / (gam β y - s)) * gamDot β y)
      = ∑ s ∈ S, res s * ∫ y in (-T)..T, (gam β y - s)⁻¹ * gamDot β y := by
    have hpt : (fun y : ℝ => (∑ s ∈ S, res s / (gam β y - s)) * gamDot β y)
        = fun y : ℝ => ∑ s ∈ S, res s * ((gam β y - s)⁻¹ * gamDot β y) := by
      funext y
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun s _ => by rw [div_eq_mul_inv]; ring)
    rw [hpt, intervalIntegral.integral_finset_sum (s := S)
      (f := fun s (y : ℝ) => res s * ((gam β y - s)⁻¹ * gamDot β y))
      (fun s hs => (h2 s hs).const_mul (res s))]
    exact Finset.sum_congr rfl (fun s _ => by rw [intervalIntegral.integral_const_mul])
  have ht : (∫ x in (phi β T)..c, (∑ s ∈ S, res s / (((x : ℂ) + (T : ℂ) * Complex.I) - s)))
      = ∑ s ∈ S, res s * ∫ x in (phi β T)..c, (((x : ℂ) + (T : ℂ) * Complex.I) - s)⁻¹ := by
    rw [intervalIntegral.integral_finset_sum (s := S)
      (f := fun s (x : ℝ) => res s / (((x : ℂ) + (T : ℂ) * Complex.I) - s))
      (fun s hs => (h3 s hs).const_mul (res s))]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have hfun₁ : (fun x : ℝ => res s / (((x : ℂ) + (T : ℂ) * Complex.I) - s))
        = fun x : ℝ => res s * (((x : ℂ) + (T : ℂ) * Complex.I) - s)⁻¹ := by
      funext x; rw [div_eq_mul_inv]
    rw [hfun₁, intervalIntegral.integral_const_mul]
  have hb : (∫ x in (phi β (-T))..c,
        (∑ s ∈ S, res s / (((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - s)))
      = ∑ s ∈ S, res s *
          ∫ x in (phi β (-T))..c, (((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - s)⁻¹ := by
    rw [intervalIntegral.integral_finset_sum (s := S)
      (f := fun s (x : ℝ) => res s / (((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - s))
      (fun s hs => (h4 s hs).const_mul (res s))]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have hfun₁ : (fun x : ℝ => res s / (((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - s))
        = fun x : ℝ => res s * (((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - s)⁻¹ := by
      funext x; rw [div_eq_mul_inv]
    rw [hfun₁, intervalIntegral.integral_const_mul]
  have hR : (∑ s ∈ S, res s * Bfun β c (fun z => (z - s)⁻¹) T)
      = ∑ s ∈ S, res s * (Complex.I * (∫ y in (-T)..T, (((c : ℂ) + (y : ℂ) * Complex.I) - s)⁻¹)
        - (∫ y in (-T)..T, (gam β y - s)⁻¹ * gamDot β y)
        - (∫ x in (phi β T)..c, (((x : ℂ) + (T : ℂ) * Complex.I) - s)⁻¹)
        + (∫ x in (phi β (-T))..c, (((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - s)⁻¹)) := by
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Bfun]
  rw [Bfun]
  rw [hv, hw, ht, hb, hR, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun s _ => by ring)


/-! ## Congruence and additivity of the boundary functional -/

lemma Bfun_congr {β c T : ℝ} {X Y : ℂ → ℂ}
    (hv : ∀ y ∈ Set.uIcc (-T) T,
      X ((c : ℂ) + (y : ℂ) * Complex.I) = Y ((c : ℂ) + (y : ℂ) * Complex.I))
    (hw : ∀ y ∈ Set.uIcc (-T) T, X (gam β y) = Y (gam β y))
    (ht : ∀ x ∈ Set.uIcc (phi β T) c,
      X ((x : ℂ) + (T : ℂ) * Complex.I) = Y ((x : ℂ) + (T : ℂ) * Complex.I))
    (hb : ∀ x ∈ Set.uIcc (phi β (-T)) c,
      X ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) = Y ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) :
    Bfun β c X T = Bfun β c Y T := by
  have e1 : (∫ y in (-T)..T, X ((c : ℂ) + (y : ℂ) * Complex.I))
      = ∫ y in (-T)..T, Y ((c : ℂ) + (y : ℂ) * Complex.I) :=
    intervalIntegral.integral_congr fun y hy => hv y hy
  have e2 : (∫ y in (-T)..T, X (gam β y) * gamDot β y)
      = ∫ y in (-T)..T, Y (gam β y) * gamDot β y :=
    intervalIntegral.integral_congr fun y hy => by rw [hw y hy]
  have e3 : (∫ x in (phi β T)..c, X ((x : ℂ) + (T : ℂ) * Complex.I))
      = ∫ x in (phi β T)..c, Y ((x : ℂ) + (T : ℂ) * Complex.I) :=
    intervalIntegral.integral_congr fun x hx => ht x hx
  have e4 : (∫ x in (phi β (-T))..c, X ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      = ∫ x in (phi β (-T))..c, Y ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) :=
    intervalIntegral.integral_congr fun x hx => hb x hx
  rw [Bfun, Bfun, e1, e2, e3, e4]

lemma Bfun_add {β c T : ℝ} {X Y : ℂ → ℂ}
    (h1 : IntervalIntegrable (fun y : ℝ => X ((c : ℂ) + (y : ℂ) * Complex.I)) volume (-T) T)
    (h1' : IntervalIntegrable (fun y : ℝ => Y ((c : ℂ) + (y : ℂ) * Complex.I)) volume (-T) T)
    (h2 : IntervalIntegrable (fun y : ℝ => X (gam β y) * gamDot β y) volume (-T) T)
    (h2' : IntervalIntegrable (fun y : ℝ => Y (gam β y) * gamDot β y) volume (-T) T)
    (h3 : IntervalIntegrable (fun x : ℝ => X ((x : ℂ) + (T : ℂ) * Complex.I)) volume (phi β T) c)
    (h3' : IntervalIntegrable (fun x : ℝ => Y ((x : ℂ) + (T : ℂ) * Complex.I)) volume (phi β T) c)
    (h4 : IntervalIntegrable (fun x : ℝ => X ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      volume (phi β (-T)) c)
    (h4' : IntervalIntegrable (fun x : ℝ => Y ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      volume (phi β (-T)) c) :
    Bfun β c (fun z => X z + Y z) T = Bfun β c X T + Bfun β c Y T := by
  have e2 : (∫ y in (-T)..T, (X (gam β y) + Y (gam β y)) * gamDot β y)
      = (∫ y in (-T)..T, X (gam β y) * gamDot β y)
        + ∫ y in (-T)..T, Y (gam β y) * gamDot β y := by
    rw [show (fun y : ℝ => (X (gam β y) + Y (gam β y)) * gamDot β y)
        = fun y : ℝ => X (gam β y) * gamDot β y + Y (gam β y) * gamDot β y from by
      funext y; ring]
    exact intervalIntegral.integral_add h2 h2'
  rw [Bfun, Bfun, Bfun,
    intervalIntegral.integral_add h1 h1', e2,
    intervalIntegral.integral_add h3 h3', intervalIntegral.integral_add h4 h4']
  ring

/-! ## The boundary integral of the residue-removed function vanishes -/

lemma Bfun_gResExt_zero {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {g : ℂ → ℂ} {S : Finset ℂ}
    {res : ℂ → ℂ}
    (hS : ∀ s ∈ S, phi β s.im < s.re ∧ s.re < c)
    (hdiff : ∀ z : ℂ, phi β z.im ≤ z.re → z.re ≤ c → z ∉ S → DifferentiableAt ℂ g z)
    (hres : ∀ s ∈ S, Tendsto (fun z : ℂ => (z - s) * g z) (nhdsWithin s ({s}ᶜ : Set ℂ))
      (nhds (res s)))
    {T : ℝ} (hT : 0 < T) :
    Bfun β c (gResExt g S res) T = 0 := by
  have hd : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ T → phi β z.im ≤ z.re → z.re ≤ c →
      DifferentiableAt ℂ (gResExt g S res) z :=
    fun z _ _ h3 h4 => gResExt_differentiableAt hβ hS hdiff hres h3 h4
  have hBh : Bh β c (gResExt g S res) T = 0 := by
    have h := graph_region_cauchy_mono (gResExt g S res) (phi β) (PhiPos β) c 0 T hT.le
      (fun y _ => (phi_lt_c hβ hc y).le) (continuous_phi β).continuousOn
      (continuousOn_PhiPos β T) (fun y hy => hasDerivAt_phi_pos β hy.1)
      (phi_monotoneOn_nonneg hβ) hd
    rw [Bh_eq_GR]
    exact h
  have hBl : Bl β c (gResExt g S res) T = 0 := by
    have hH : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ T → phi β z.im ≤ z.re → z.re ≤ c →
        DifferentiableAt ℂ (fun z => conj (gResExt g S res (conj z))) z := by
      intro z h1 h2 h3 h4
      have hz : DifferentiableAt ℂ (gResExt g S res) (conj z) := by
        refine gResExt_differentiableAt hβ hS hdiff hres ?_ ?_
        · rw [Complex.conj_im, Complex.conj_re, phi_even]
          exact h3
        · simpa using h4
      exact (differentiableAt_conj_conj_iff (f := gResExt g S res)).mpr (by simpa using hz)
    have hmono := graph_region_cauchy_mono (fun z => conj (gResExt g S res (conj z)))
      (phi β) (PhiPos β) c 0 T hT.le (fun y _ => (phi_lt_c hβ hc y).le)
      (continuous_phi β).continuousOn (continuousOn_PhiPos β T)
      (fun y hy => hasDerivAt_phi_pos β hy.1) (phi_monotoneOn_nonneg hβ) hH
    have hfun1 : (fun u : ℝ => phi β (-u)) = phi β := by
      funext u; exact phi_even β u
    have hfun2 : (fun u : ℝ => -PhiNeg β (-u)) = PhiPos β := by
      funext u
      simp only [PhiPos, PhiNeg]
      ring
    have hr := GR_conj_reflect (gResExt g S res) (phi β) (PhiNeg β) c (-T) 0
    have hcongr := GR_congr (F := fun z => conj (gResExt g S res (conj z))) (c := c)
      (a := 0) (b := T) hfun1 hfun2
    rw [Bl_eq_GR, hr]
    simp only [neg_zero, neg_neg]
    rw [hcongr]
    rw [show GR (fun z => conj (gResExt g S res (conj z))) (phi β) (PhiPos β) c 0 T
      = 0 from hmono]
    simp
  have hv : Continuous (fun y : ℝ => gResExt g S res ((c : ℂ) + (y : ℂ) * Complex.I)) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hy : ((c : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
    have hr : ((c : ℂ) + (y : ℂ) * Complex.I).re = c := by simp
    exact (gResExt_differentiableAt hβ hS hdiff hres
      (by rw [hy, hr]; exact (phi_lt_c hβ hc y).le) (by rw [hr])).continuousAt.comp (by fun_prop)
  have hgm : Continuous (fun y : ℝ => gResExt g S res (gam β y)) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hy : (gam β y).im = y := gam_im β y
    have hr : (gam β y).re = phi β y := by simp [gam]
    refine (gResExt_differentiableAt hβ hS hdiff hres ?_ ?_).continuousAt.comp
      (gam_continuous β).continuousAt
    · rw [hy, hr]
    · rw [hr]; exact (phi_lt_c hβ hc y).le
  have hw1 : IntervalIntegrable (fun y : ℝ => gResExt g S res (gam β y) * gamDotNeg β y)
      volume (-T) 0 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith : -T ≤ 0)]
    exact hgm.continuousOn.mul (continuousOn_gamDotNeg β T)
  have hw2 : IntervalIntegrable (fun y : ℝ => gResExt g S res (gam β y) * gamDotPos β y)
      volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT.le]
    exact hgm.continuousOn.mul (continuousOn_gamDotPos β T)
  have hw2' : IntervalIntegrable (fun y : ℝ => gResExt g S res (gam β y) * gamDot β y)
      volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT.le]
    exact hgm.continuousOn.mul (continuousOn_gamDot_nonneg β T)
  rw [Bfun_eq_Bh_Bl (X := gResExt g S res) hT (hv.intervalIntegrable _ _)
      (hv.intervalIntegrable _ _) (intervalIntegrable_gamDot_left hT.le hw1) hw2' hw1 hw2,
    hBh, hBl]
  ring


/-! ## Continuity of the extension along the contour -/

lemma continuous_gResExt_vert {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {g : ℂ → ℂ} {S : Finset ℂ}
    {res : ℂ → ℂ}
    (hS : ∀ s ∈ S, phi β s.im < s.re ∧ s.re < c)
    (hdiff : ∀ z : ℂ, phi β z.im ≤ z.re → z.re ≤ c → z ∉ S → DifferentiableAt ℂ g z)
    (hres : ∀ s ∈ S, Tendsto (fun z : ℂ => (z - s) * g z) (nhdsWithin s ({s}ᶜ : Set ℂ))
      (nhds (res s))) :
    Continuous (fun y : ℝ => gResExt g S res ((c : ℂ) + (y : ℂ) * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hy : ((c : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
  have hr : ((c : ℂ) + (y : ℂ) * Complex.I).re = c := by simp
  exact (gResExt_differentiableAt hβ hS hdiff hres
    (by rw [hy, hr]; exact (phi_lt_c hβ hc y).le) (by rw [hr])).continuousAt.comp (by fun_prop)

lemma continuous_gResExt_gam {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {g : ℂ → ℂ} {S : Finset ℂ}
    {res : ℂ → ℂ}
    (hS : ∀ s ∈ S, phi β s.im < s.re ∧ s.re < c)
    (hdiff : ∀ z : ℂ, phi β z.im ≤ z.re → z.re ≤ c → z ∉ S → DifferentiableAt ℂ g z)
    (hres : ∀ s ∈ S, Tendsto (fun z : ℂ => (z - s) * g z) (nhdsWithin s ({s}ᶜ : Set ℂ))
      (nhds (res s))) :
    Continuous (fun y : ℝ => gResExt g S res (gam β y)) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hy : (gam β y).im = y := gam_im β y
  have hr : (gam β y).re = phi β y := by simp [gam]
  refine (gResExt_differentiableAt hβ hS hdiff hres ?_ ?_).continuousAt.comp
    (gam_continuous β).continuousAt
  · rw [hy, hr]
  · rw [hr]; exact (phi_lt_c hβ hc y).le

lemma continuousOn_gResExt_horiz {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {g : ℂ → ℂ} {S : Finset ℂ}
    {res : ℂ → ℂ}
    (hS : ∀ s ∈ S, phi β s.im < s.re ∧ s.re < c)
    (hdiff : ∀ z : ℂ, phi β z.im ≤ z.re → z.re ≤ c → z ∉ S → DifferentiableAt ℂ g z)
    (hres : ∀ s ∈ S, Tendsto (fun z : ℂ => (z - s) * g z) (nhdsWithin s ({s}ᶜ : Set ℂ))
      (nhds (res s))) (r : ℝ) :
    ContinuousOn (fun x : ℝ => gResExt g S res ((x : ℂ) + (r : ℂ) * Complex.I))
      (Set.uIcc (phi β r) c) := by
  rw [Set.uIcc_of_le (le_of_lt (phi_lt_c hβ hc r))]
  intro x hx
  have hi : ((x : ℂ) + (r : ℂ) * Complex.I).im = r := by simp
  have hr : ((x : ℂ) + (r : ℂ) * Complex.I).re = x := by simp
  exact ContinuousAt.comp_continuousWithinAt
    (f := fun x : ℝ => (x : ℂ) + (r : ℂ) * Complex.I) (g := gResExt g S res)
    (gResExt_differentiableAt hβ hS hdiff hres (by rw [hi, hr]; exact hx.1) (by rw [hr]; exact hx.2)).continuousAt
    (by fun_prop)

/-! ## The boundary integral equals `2πi` times the sum of the residues -/

lemma Bfun_eq_sum_res {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {g : ℂ → ℂ} {S : Finset ℂ}
    {res : ℂ → ℂ}
    (hS : ∀ s ∈ S, phi β s.im < s.re ∧ s.re < c)
    (hdiff : ∀ z : ℂ, phi β z.im ≤ z.re → z.re ≤ c → z ∉ S → DifferentiableAt ℂ g z)
    (hres : ∀ s ∈ S, Tendsto (fun z : ℂ => (z - s) * g z) (nhdsWithin s ({s}ᶜ : Set ℂ))
      (nhds (res s)))
    {T : ℝ} (hT : 0 < T) (hTin : ∀ s ∈ S, -T < s.im ∧ s.im < T) :
    Bfun β c g T = 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, res s := by
  have hTle : (-T : ℝ) ≤ T := by linarith
  have hcontv := continuous_gResExt_vert hβ hc hS hdiff hres
  have hcontg := continuous_gResExt_gam hβ hc hS hdiff hres
  -- integrability of the pole sum on each piece
  have hvS : IntervalIntegrable
      (fun y : ℝ => ∑ s ∈ S, res s / (((c : ℂ) + (y : ℂ) * Complex.I) - s)) volume (-T) T := by
    have hfun : (fun y : ℝ => ∑ s ∈ S, res s / (((c : ℂ) + (y : ℂ) * Complex.I) - s))
        = ∑ s ∈ S, (fun y : ℝ => res s * (((c : ℂ) + (y : ℂ) * Complex.I) - s)⁻¹) := by
      funext y
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl (fun s _ => by rw [div_eq_mul_inv])
    rw [hfun]
    exact IntervalIntegrable.sum S (fun s hs =>
      (intervalIntegrable_vert_sub_inv (hS s hs).2 hT.le).const_mul (res s))
  have hwS : IntervalIntegrable
      (fun y : ℝ => (∑ s ∈ S, res s / (gam β y - s)) * gamDot β y) volume (-T) T := by
    have hfun : (fun y : ℝ => (∑ s ∈ S, res s / (gam β y - s)) * gamDot β y)
        = ∑ s ∈ S, (fun y : ℝ => res s * ((gam β y - s)⁻¹ * gamDot β y)) := by
      funext y
      rw [Finset.sum_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun s _ => by rw [div_eq_mul_inv]; ring)
    rw [hfun]
    exact IntervalIntegrable.sum S (fun s hs =>
      (intervalIntegrable_curve_sub_inv hβ (hS s hs).1 hT (hTin s hs).1 (hTin s hs).2).const_mul (res s))
  have htS : IntervalIntegrable
      (fun x : ℝ => ∑ s ∈ S, res s / (((x : ℂ) + (T : ℂ) * Complex.I) - s))
      volume (phi β T) c := by
    have hfun : (fun x : ℝ => ∑ s ∈ S, res s / (((x : ℂ) + (T : ℂ) * Complex.I) - s))
        = ∑ s ∈ S, (fun x : ℝ => res s * (((x : ℂ) + (T : ℂ) * Complex.I) - s)⁻¹) := by
      funext x
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl (fun s _ => by rw [div_eq_mul_inv])
    rw [hfun]
    exact IntervalIntegrable.sum S (fun s hs =>
      (intervalIntegrable_horiz_sub_inv (r := T) (by linarith [hTin s hs]) _ _).const_mul (res s))
  have hbS : IntervalIntegrable
      (fun x : ℝ => ∑ s ∈ S, res s / (((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - s))
      volume (phi β (-T)) c := by
    have hfun : (fun x : ℝ => ∑ s ∈ S, res s / (((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - s))
        = ∑ s ∈ S, (fun x : ℝ => res s * (((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - s)⁻¹) := by
      funext x
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl (fun s _ => by rw [div_eq_mul_inv])
    rw [hfun]
    exact IntervalIntegrable.sum S (fun s hs =>
      (intervalIntegrable_horiz_sub_inv (r := -T) (by linarith [hTin s hs]) _ _).const_mul (res s))
  -- integrability of the extension on each piece
  have hgv : IntervalIntegrable
      (fun y : ℝ => gResExt g S res ((c : ℂ) + (y : ℂ) * Complex.I)) volume (-T) T :=
    hcontv.intervalIntegrable _ _
  have hgw : IntervalIntegrable
      (fun y : ℝ => gResExt g S res (gam β y) * gamDot β y) volume (-T) T := by
    refine intervalIntegrable_gamDot hT.le ?_ ?_
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by linarith : (-T:ℝ) ≤ 0)]
      exact hcontg.continuousOn.mul (continuousOn_gamDotNeg β T)
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hT.le]
      exact hcontg.continuousOn.mul (continuousOn_gamDot_nonneg β T)
  have hgt : IntervalIntegrable
      (fun x : ℝ => gResExt g S res ((x : ℂ) + (T : ℂ) * Complex.I)) volume (phi β T) c :=
    (continuousOn_gResExt_horiz hβ hc hS hdiff hres T).intervalIntegrable
  have hgb : IntervalIntegrable
      (fun x : ℝ => gResExt g S res ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      volume (phi β (-T)) c :=
    (continuousOn_gResExt_horiz hβ hc hS hdiff hres (-T)).intervalIntegrable
  have hcongr : Bfun β c g T
      = Bfun β c (fun z => gResExt g S res z + ∑ s ∈ S, res s / (z - s)) T := by
    refine Bfun_congr ?_ ?_ ?_ ?_
    · intro y hy
      have hz : ((c : ℂ) + (y : ℂ) * Complex.I) ∉ S := by
        intro h
        have h2 := (hS _ h).2
        have h1 : ((c : ℂ) + (y : ℂ) * Complex.I).re = c := by simp
        rw [h1] at h2
        exact absurd h2 (lt_irrefl c)
      rw [gResExt_of_notMem hz]; ring
    · intro y hy
      have hz : gam β y ∉ S := fun h => by
        have hlt := (hS (gam β y) h).1
        have hre : (gam β y).re = phi β y := by simp [gam]
        rw [gam_im, hre] at hlt
        exact absurd hlt (lt_irrefl _)
      rw [gResExt_of_notMem hz]; ring
    · intro x hx
      have hz : ((x : ℂ) + (T : ℂ) * Complex.I) ∉ S := by
        intro h
        have h2 := (hTin _ h).2
        have h1 : ((x : ℂ) + (T : ℂ) * Complex.I).im = T := by simp
        rw [h1] at h2
        exact absurd h2 (lt_irrefl T)
      rw [gResExt_of_notMem hz]; ring
    · intro x hx
      have hz : ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ∉ S := by
        intro h
        have h2 := (hTin _ h).1
        have h1 : ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im = -T := by simp
        rw [h1] at h2
        exact absurd h2 (lt_irrefl (-T))
      rw [gResExt_of_notMem hz]; ring
  rw [hcongr, Bfun_add (X := gResExt g S res) (Y := fun z => ∑ s ∈ S, res s / (z - s))
    hgv hvS hgw hwS hgt htS hgb hbS,
    Bfun_inv_sum S res (fun s hs => intervalIntegrable_vert_sub_inv (hS s hs).2 hT.le)
      (fun s hs => intervalIntegrable_curve_sub_inv hβ (hS s hs).1 hT (hTin s hs).1 (hTin s hs).2)
      (fun s hs => intervalIntegrable_horiz_sub_inv (r := T) (by linarith [hTin s hs]) _ _)
      (fun s hs => intervalIntegrable_horiz_sub_inv (r := -T) (by linarith [hTin s hs]) _ _)]
  have hsum : (∑ s ∈ S, res s * Bfun β c (fun z => (z - s)⁻¹) T)
      = ∑ s ∈ S, res s * (2 * (Real.pi : ℂ) * Complex.I) := by
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [Bfun_sub_inv (β := β) (c := c) hβ hc hT (hS s hs).1 (hS s hs).2 (hTin s hs).1 (hTin s hs).2]
  rw [hsum, Bfun_gResExt_zero hβ hc hS hdiff hres hT, zero_add, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun s _ => by ring)

/-- Contour shift with finitely many simple poles. -/
theorem contour_shift_residue_multi {β c : ℝ} (hβ : 0 < β) (hc : 0 < c)
    (g : ℂ → ℂ) (S : Finset ℂ) (res : ℂ → ℂ)
    (hS : ∀ s ∈ S, -(β / Real.log (|s.im| + 2)) < s.re ∧ s.re < c)
    (hdiff : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ c → z ∉ S →
      DifferentiableAt ℂ g z)
    (hres : ∀ s ∈ S, Filter.Tendsto (fun z : ℂ => (z - s) * g z)
      (nhdsWithin s ({s}ᶜ : Set ℂ)) (nhds (res s)))
    (hint1 : MeasureTheory.Integrable
      (fun t : ℝ => g ((c : ℂ) + (t : ℂ) * Complex.I) * Complex.I))
    (hint0 : MeasureTheory.Integrable (fun t : ℝ =>
      g (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t))
    (hhoriz : Filter.Tendsto (fun T : ℝ =>
      (∫ u in (-(β / Real.log (T + 2)))..c, g ((u : ℂ) + (T : ℂ) * Complex.I))
        - (∫ u in (-(β / Real.log (T + 2)))..c, g ((u : ℂ) - (T : ℂ) * Complex.I)))
      Filter.atTop (nhds 0)) :
    (∫ t : ℝ, g ((c : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
      = (∫ t : ℝ, g (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t)
        + 2 * Real.pi * Complex.I * ∑ s ∈ S, res s := by
  have hint_g : MeasureTheory.Integrable (fun t : ℝ => g ((c : ℂ) + (t : ℂ) * Complex.I)) :=
    (hint1.div_const Complex.I).congr (Filter.Eventually.of_forall (fun t => by
      change g ((c : ℂ) + (t : ℂ) * Complex.I) * Complex.I / Complex.I
        = g ((c : ℂ) + (t : ℂ) * Complex.I)
      rw [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ Complex.I_ne_zero, mul_one]))
  have hd_unf : ∀ t : ℝ, t ≠ 0 →
      deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t
        = gamDot β t := fun t ht => by
    have h := (hasDerivAt_gam (β := β) ht).deriv
    have hfun : (gam β) = (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ)
        + (s : ℂ) * Complex.I)) := by funext s; simp [gam, phi]
    rw [hfun] at h
    exact h
  have hint_c : MeasureTheory.Integrable (fun t : ℝ => g (gam β t) * gamDot β t) :=
    hint0.congr (by
      filter_upwards [ae_ne_zero] with t ht
      rw [hd_unf t ht]
      congr 1)
  have hbig : ∀ᶠ T : ℝ in Filter.atTop, ∀ s ∈ S, -T < s.im ∧ s.im < T := by
    refine Filter.eventually_atTop.2 ⟨1 + ∑ s ∈ S, |s.im|, fun T hT => ?_⟩
    intro s hs
    have h1 : |s.im| ≤ ∑ s' ∈ S, |s'.im| :=
      Finset.single_le_sum (fun i _ => abs_nonneg i.im) hs
    constructor <;> linarith [neg_abs_le s.im, le_abs_self s.im]
  have hkey : ∀ᶠ T : ℝ in Filter.atTop,
      Complex.I * (∫ y in (-T)..T, g ((c : ℂ) + (y : ℂ) * Complex.I))
        - (∫ y in (-T)..T, g (gam β y) * gamDot β y)
      = 2 * (Real.pi : ℂ) * Complex.I * (∑ s ∈ S, res s) + horizTerm β c g T := by
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ), hbig] with T hT hTin
    have hB := Bfun_eq_sum_res (β := β) (c := c) hβ hc hS hdiff hres hT hTin
    have hh := Bfun_eq_horiz (β := β) (c := c) (g := g) hT
    rw [hB] at hh
    rw [hh]; ring
  have h1 : Tendsto (fun T : ℝ => ∫ y in (-T)..T, g ((c : ℂ) + (y : ℂ) * Complex.I))
      Filter.atTop (𝓝 (∫ y : ℝ, g ((c : ℂ) + (y : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral hint_g tendsto_neg_atTop_atBot tendsto_id
  have h2 : Tendsto (fun T : ℝ => ∫ y in (-T)..T, g (gam β y) * gamDot β y)
      Filter.atTop (𝓝 (∫ y : ℝ, g (gam β y) * gamDot β y)) :=
    intervalIntegral_tendsto_integral hint_c tendsto_neg_atTop_atBot tendsto_id
  have hlim : Tendsto (fun T : ℝ => Complex.I *
        (∫ y in (-T)..T, g ((c : ℂ) + (y : ℂ) * Complex.I))
        - (∫ y in (-T)..T, g (gam β y) * gamDot β y)) Filter.atTop
      (𝓝 (Complex.I * (∫ y : ℝ, g ((c : ℂ) + (y : ℂ) * Complex.I))
        - (∫ y : ℝ, g (gam β y) * gamDot β y))) :=
    (h1.const_mul Complex.I).sub h2
  have h3 : Tendsto (horizTerm β c g) Filter.atTop (𝓝 0) := horizTerm_tendsto hβ hhoriz
  have hlim2 : Tendsto (fun T : ℝ =>
      2 * (Real.pi : ℂ) * Complex.I * (∑ s ∈ S, res s) + horizTerm β c g T)
      Filter.atTop (𝓝 (2 * (Real.pi : ℂ) * Complex.I * (∑ s ∈ S, res s) + 0)) :=
    tendsto_const_nhds.add h3
  have huniq : Complex.I * (∫ y : ℝ, g ((c : ℂ) + (y : ℂ) * Complex.I))
      - (∫ y : ℝ, g (gam β y) * gamDot β y)
      = 2 * (Real.pi : ℂ) * Complex.I * (∑ s ∈ S, res s) + 0 :=
    tendsto_nhds_unique (hlim.congr' hkey) hlim2
  rw [add_zero] at huniq
  have hlhs : (∫ t : ℝ, g ((c : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
      = Complex.I * (∫ t : ℝ, g ((c : ℂ) + (t : ℂ) * Complex.I)) := by
    rw [MeasureTheory.integral_mul_const Complex.I (fun t : ℝ =>
      g ((c : ℂ) + (t : ℂ) * Complex.I)), mul_comm]
  have hrhs : (∫ t : ℝ, g (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t)
      = ∫ t : ℝ, g (gam β t) * gamDot β t := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_ne_zero] with t ht
    rw [hd_unf t ht]
    congr 1
  rw [hlhs, hrhs, ← huniq]
  ring

end

end Commons.Analysis.Complex
