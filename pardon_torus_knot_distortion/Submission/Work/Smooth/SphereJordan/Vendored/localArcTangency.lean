import Mathlib
import Submission.Work.Smooth.SphereJordan.localArcCore
import Submission.Work.Smooth.SphereJordan.localComplementBasic
import Submission.Work.Smooth.SphereJordan.Vendored.localArcHgen

/-!
# The local-arc analysis at a tangency point

Two active centres `a b` of `S = ⋃ w ∈ Q, closedBall w r` with `b - x = -(a - x)` (two externally
tangent discs at the frontier point `x`) and a unit direction `u` perpendicular to `a - x` with
`⟪u, w - x⟫ < 0` for every *other* active centre `w`: this is the configuration at a "cusp".

The profile of `S` along the directions `u * z` is the elementary function `r * |z.im|`
(`mC_ge_abs_im`, `mC_eq_abs_im`), so the local complement of `S` on the `u`-side of `x` is the
open cusp parametrised by

`cuspParam x u r (ρ, s) = x + ρ * (u * eicC (s * arcsin (ρ / (2 r))))`.

`cuspSet_eq_image` identifies the two, `cuspSet_preconnected` is the resulting connectedness and
`frontierLocallyArc_of_cusp` is the main theorem: if this cusp lies in the component of `q` in the
complement and the *other* side of `x` is not in that component, then the frontier of the component
is locally an arc at `x`, parametrised by the two halves of the boundary of the cusp.
-/

namespace Work.Smooth.SphereJordan

open Set Metric

noncomputable section

open scoped Classical

/-! ## Elementary complex-number facts -/

/-- A complex number with zero real part and norm `r` has `|im| = r`. -/
theorem abs_im_of_re_eq_zero {f : ℂ} {r : ℝ} (hf : f.re = 0) (hn : ‖f‖ = r) : |f.im| = r := by
  have h2 : ‖f‖ ^ 2 = f.re ^ 2 + f.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hf, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, hn] at h2
  have hr : 0 ≤ r := by rw [← hn]; positivity
  have h3 : |f.im| ^ 2 = r ^ 2 := by rw [sq_abs, ← h2]
  have h4 := (sq_eq_sq_iff_abs_eq_abs (|f.im|) r).mp h3
  simpa [abs_abs, abs_of_nonneg hr] using h4

/-- The real part of `star z * f`. -/
theorem star_mul_re (z f : ℂ) : (star z * f).re = z.re * f.re + z.im * f.im := by
  rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The norm of `star u * (w - x)` for an active centre `w`. -/
theorem norm_star_mul_sub {Q : Finset ℂ} {r : ℝ} {x u w : ℂ} (hu : ‖u‖ = 1)
    (hw : w ∈ actC Q r x) : ‖star u * (w - x)‖ = r := by
  rw [norm_mul, norm_star, hu, one_mul, ← dist_eq_norm, dist_comm]
  exact (mem_actC.mp hw).2

/-- A unit complex number satisfies `u * star u = 1`. -/
theorem mul_star_self {u : ℂ} (hu : ‖u‖ = 1) : u * star u = 1 := by
  have h : u * (starRingEnd ℂ) u = 1 := by
    rw [RCLike.mul_conj, hu]
    norm_num
  simpa [Complex.star_def] using h

/-- A unit complex number satisfies `star u * u = 1`. -/
theorem star_mul_self {u : ℂ} (hu : ‖u‖ = 1) : star u * u = 1 := by
  have h := mul_star_self (u := star u) (by rw [norm_star, hu])
  rwa [star_star] at h

/-- `star u * (u * z) = z` for a unit `u`. -/
theorem star_mul_self_mul {u z : ℂ} (hu : ‖u‖ = 1) : star u * (u * z) = z := by
  rw [← mul_assoc, star_mul_self hu, one_mul]

theorem eicC_re (θ : ℝ) : (eicC θ).re = Real.cos θ := Complex.exp_ofReal_mul_I_re θ

theorem eicC_im (θ : ℝ) : (eicC θ).im = Real.sin θ := Complex.exp_ofReal_mul_I_im θ

/-! ## The radial profile in the tangency configuration -/

/-- **The profile is at least `r |z.im|`.**  In the tangency configuration the two antipodal
active centres `a`, `b` already give the value `r * |z.im|` at the direction `u * z`. -/
theorem mC_ge_abs_im {Q : Finset ℂ} {r : ℝ} {x a b u z : ℂ} {hA : (actC Q r x).Nonempty}
    (ha : a ∈ actC Q r x) (hb : b ∈ actC Q r x) (hab : b - x = -(a - x))
    (hu : ‖u‖ = 1) (hua : (star u * (a - x)).re = 0) (hz : ‖z‖ = 1) :
    r * |z.im| ≤ mC Q r x hA (u * z) := by
  have him : |(star u * (a - x)).im| = r := abs_im_of_re_eq_zero hua (norm_star_mul_sub hu ha)
  have hb1 : (star (u * z) * (a - x)).re ≤ mC Q r x hA (u * z) := le_mC ha
  have hb2 : (star (u * z) * (b - x)).re ≤ mC Q r x hA (u * z) := le_mC hb
  have h1 : (star (u * z) * (a - x)).re = z.im * (star u * (a - x)).im := by
    rw [star_mul, mul_assoc, star_mul_re, hua, mul_zero, zero_add]
  have h2 : (star (u * z) * (b - x)).re = -(z.im * (star u * (a - x)).im) := by
    rw [hab, mul_neg, Complex.neg_re, h1]
  rw [h1] at hb1
  rw [h2] at hb2
  have hkey : r * |z.im| = |z.im * (star u * (a - x)).im| := by
    rw [abs_mul, him]; ring
  rw [hkey]
  rcases le_total (z.im * (star u * (a - x)).im) 0 with h | h
  · rw [abs_of_nonpos h]; exact hb2
  · rw [abs_of_nonneg h]; exact hb1

/-- **The profile is exactly `r |z.im|` on the `u`-side of `x`.**  The other active centres have
non-positive contribution there. -/
theorem mC_eq_abs_im {Q : Finset ℂ} {r : ℝ} {x a b u z : ℂ} {hA : (actC Q r x).Nonempty}
    (ha : a ∈ actC Q r x) (hb : b ∈ actC Q r x) (hab : b - x = -(a - x))
    (hu : ‖u‖ = 1) (hua : (star u * (a - x)).re = 0)
    (hother : ∀ w ∈ actC Q r x, w ≠ a → w ≠ b → (star u * (w - x)).re < 0)
    (hz : ‖z‖ = 1) (hzre : 0 ≤ z.re) :
    mC Q r x hA (u * z) = r * |z.im| := by
  refine le_antisymm ?_ (mC_ge_abs_im ha hb hab hu hua hz)
  have him : |(star u * (a - x)).im| = r := abs_im_of_re_eq_zero hua (norm_star_mul_sub hu ha)
  rw [mC]
  refine Finset.sup'_le hA (fun w => (star (u * z) * (w - x)).re) (fun w hw => ?_)
  have hcomp : (star (u * z) * (w - x)).re
      = z.re * (star u * (w - x)).re + z.im * (star u * (w - x)).im := by
    rw [star_mul, mul_assoc, star_mul_re]
  rcases eq_or_ne w a with hwa | hwa
  · rw [hcomp, hwa, hua, mul_zero, zero_add]
    calc z.im * (star u * (a - x)).im ≤ |z.im * (star u * (a - x)).im| := le_abs_self _
      _ = |z.im| * r := by rw [abs_mul, him]
      _ = r * |z.im| := by ring
  rcases eq_or_ne w b with hwb | hwb
  · have hbre : (star u * (b - x)).re = 0 := by
      rw [hab, mul_neg, Complex.neg_re, hua, neg_zero]
    have hbim : (star u * (b - x)).im = -((star u * (a - x)).im) := by
      rw [hab, mul_neg, Complex.neg_im]
    rw [hcomp, hwb, hbre, hbim, mul_zero, zero_add]
    calc z.im * -((star u * (a - x)).im) ≤ |z.im * -((star u * (a - x)).im)| := le_abs_self _
      _ = |z.im| * r := by rw [abs_mul, abs_neg, him]
      _ = r * |z.im| := by ring
  · have hwre : (star u * (w - x)).re < 0 := hother w hw hwa hwb
    have hwim : |(star u * (w - x)).im| ≤ r := by
      calc |(star u * (w - x)).im| ≤ ‖star u * (w - x)‖ := Complex.abs_im_le_norm _
        _ = r := norm_star_mul_sub hu hw
    rw [hcomp]
    have h1 : z.re * (star u * (w - x)).re ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hzre (le_of_lt hwre)
    have h2 : z.im * (star u * (w - x)).im ≤ |z.im| * r := by
      calc z.im * (star u * (w - x)).im ≤ |z.im * (star u * (w - x)).im| := le_abs_self _
        _ = |z.im| * |(star u * (w - x)).im| := by rw [abs_mul]
        _ ≤ |z.im| * r := mul_le_mul_of_nonneg_left hwim (abs_nonneg _)
    linarith

/-! ## The cusp -/

/-- The angular half-width of the cusp at radius `ρ`. -/
def betaS (r ρ : ℝ) : ℝ := Real.arcsin (ρ / (2 * r))

theorem betaS_pos {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) : 0 < betaS r ρ :=
  Real.arcsin_pos.mpr (div_pos hρ (by linarith))

theorem betaS_lt_pi_div_two {r ρ : ℝ} (hr : 0 < r) (hρ : ρ < 2 * r) :
    betaS r ρ < Real.pi / 2 :=
  Real.arcsin_lt_pi_div_two.mpr ((div_lt_one (by linarith)).mpr hρ)

theorem betaS_sin {r ρ : ℝ} (hr : 0 < r) (hρ0 : 0 < ρ) (hρ : ρ ≤ 2 * r) :
    Real.sin (betaS r ρ) = ρ / (2 * r) := by
  refine Real.sin_arcsin ?_ ?_
  · rw [le_div_iff₀ (by linarith)]; linarith
  · rw [div_le_one (by linarith)]; exact hρ

/-- The parametrisation of the open cusp on the `u`-side of `x`. -/
def cuspParam (x u : ℂ) (r : ℝ) (p : ℝ × ℝ) : ℂ :=
  x + ((p.1 : ℝ) : ℂ) * (u * eicC (p.2 * betaS r p.1))

/-- The local complement on the `u`-side of `x`. -/
def cuspSet (Q : Finset ℂ) (r : ℝ) (x u : ℂ) (ε : ℝ) : Set ℂ :=
  {y : ℂ | y ∈ (⋃ w ∈ Q, Metric.closedBall w r)ᶜ ∧ dist y x < ε ∧ 0 < (star u * (y - x)).re}

/-- The parameter box of the cusp. -/
def cuspBox (ε : ℝ) : Set (ℝ × ℝ) := Set.Ioo 0 ε ×ˢ Set.Ioo (-1) 1

theorem continuous_cuspParam (x u : ℂ) (r : ℝ) : Continuous (cuspParam x u r) := by
  have hβ : Continuous fun p : ℝ × ℝ => betaS r p.1 :=
    Real.continuous_arcsin.comp (continuous_fst.div_const (2 * r))
  have h3 : Continuous fun p : ℝ × ℝ => eicC (p.2 * betaS r p.1) :=
    continuous_eicC.comp (continuous_snd.mul hβ)
  have h1 : Continuous fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp continuous_fst
  show Continuous fun p : ℝ × ℝ => x + ((p.1 : ℝ) : ℂ) * (u * eicC (p.2 * betaS r p.1))
  exact continuous_const.add (h1.mul (continuous_const.mul h3))

theorem cuspParam_mem_cuspSet {Q : Finset ℂ} {r : ℝ} (hr : 0 < r) {x u a b : ℂ}
    {hA : (actC Q r x).Nonempty} {ε : ℝ} (hε2r : ε ≤ 2 * r)
    (ha : a ∈ actC Q r x) (hb : b ∈ actC Q r x) (hab : b - x = -(a - x))
    (hu : ‖u‖ = 1) (hua : (star u * (a - x)).re = 0)
    (hother : ∀ w ∈ actC Q r x, w ≠ a → w ≠ b → (star u * (w - x)).re < 0)
    (hmodel : ∀ (u' : ℂ) (ρ : ℝ), ‖u'‖ = 1 → 0 < ρ → ρ < ε →
      (x + ρ * u' ∈ ⋃ w ∈ Q, Metric.closedBall w r ↔ ρ ≤ 2 * mC Q r x hA u'))
    {p : ℝ × ℝ} (hp : p ∈ cuspBox ε) :
    cuspParam x u r p ∈ cuspSet Q r x u ε := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hp1a, hp1b⟩ := hp1
  obtain ⟨hp2a, hp2b⟩ := hp2
  set ρ : ℝ := p.1 with hρdef
  set s : ℝ := p.2 with hsdef
  set θ : ℝ := s * betaS r ρ with hθdef
  have hρ0 : 0 < ρ := hp1a
  have hρlt : ρ < ε := hp1b
  have hρ2r : ρ < 2 * r := lt_of_lt_of_le hρlt hε2r
  have hβ0 : 0 < betaS r ρ := betaS_pos hr hρ0
  have hβπ : betaS r ρ < Real.pi / 2 := betaS_lt_pi_div_two hr hρ2r
  have hβsin : Real.sin (betaS r ρ) = ρ / (2 * r) := betaS_sin hr hρ0 hρ2r.le
  have hs1 : |s| < 1 := abs_lt.mpr ⟨hp2a, hp2b⟩
  have hθβ : |θ| < betaS r ρ := by
    rw [hθdef, abs_mul, abs_of_pos hβ0]
    calc |s| * betaS r ρ < 1 * betaS r ρ := mul_lt_mul_of_pos_right hs1 hβ0
      _ = betaS r ρ := one_mul _
  have hθπ : |θ| < Real.pi / 2 := lt_trans hθβ hβπ
  have hpoint : cuspParam x u r p = x + ρ * (u * eicC θ) := by
    rw [cuspParam, hθdef, hsdef, hρdef]
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le θ, hθπ], by linarith [le_abs_self θ, hθπ]⟩
  have hzre : 0 < (eicC θ).re := by rw [eicC_re]; exact hcos
  refine ⟨?_, ?_, ?_⟩
  · rw [hpoint, Set.mem_compl_iff]
    intro hmem
    have hu' : ‖u * eicC θ‖ = 1 := by rw [norm_mul, hu, norm_eicC, mul_one]
    have hle := (hmodel (u * eicC θ) ρ hu' hρ0 hρlt).mp hmem
    have hprof : mC Q r x hA (u * eicC θ) = r * |(eicC θ).im| :=
      mC_eq_abs_im ha hb hab hu hua hother (norm_eicC θ) hzre.le
    rw [hprof] at hle
    have habs : |(eicC θ).im| = Real.sin |θ| := by
      rw [eicC_im, Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [hθπ, Real.pi_pos])]
    rw [habs] at hle
    have hlt : Real.sin |θ| < Real.sin (betaS r ρ) := by
      refine (Real.strictMonoOn_sin.lt_iff_lt ?_ ?_).mpr hθβ
      · rw [Set.mem_Icc]; exact ⟨by linarith [abs_nonneg θ, Real.pi_pos], le_of_lt hθπ⟩
      · rw [Set.mem_Icc]
        exact ⟨by linarith [le_of_lt hβ0, Real.pi_pos], le_of_lt hβπ⟩
    rw [hβsin] at hlt
    have h2 : 2 * r * Real.sin |θ| < 2 * r * (ρ / (2 * r)) :=
      mul_lt_mul_of_pos_left hlt (by linarith)
    rw [mul_div_cancel₀ ρ (by linarith : (2 : ℝ) * r ≠ 0)] at h2
    linarith
  · rw [hpoint, dist_eq_norm]
    have h1 : x + ρ * (u * eicC θ) - x = (ρ : ℂ) * (u * eicC θ) := by ring
    rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0, norm_mul, hu, one_mul,
      norm_eicC, mul_one]
    exact hρlt
  · rw [hpoint]
    have h1 : star u * (x + ρ * (u * eicC θ) - x) = (ρ : ℂ) * (star u * (u * eicC θ)) := by ring
    rw [h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      star_mul_self_mul hu, eicC_re]
    exact mul_pos hρ0 hcos

theorem cuspSet_subset_cuspParam {Q : Finset ℂ} {r : ℝ} (hr : 0 < r) {x u a b : ℂ}
    {hA : (actC Q r x).Nonempty} {ε : ℝ} (hε2r : ε ≤ 2 * r)
    (ha : a ∈ actC Q r x) (hb : b ∈ actC Q r x) (hab : b - x = -(a - x))
    (hu : ‖u‖ = 1) (hua : (star u * (a - x)).re = 0)
    (hother : ∀ w ∈ actC Q r x, w ≠ a → w ≠ b → (star u * (w - x)).re < 0)
    (hmodel : ∀ (u' : ℂ) (ρ : ℝ), ‖u'‖ = 1 → 0 < ρ → ρ < ε →
      (x + ρ * u' ∈ ⋃ w ∈ Q, Metric.closedBall w r ↔ ρ ≤ 2 * mC Q r x hA u'))
    {y : ℂ} (hy : y ∈ cuspSet Q r x u ε) :
    ∃ p ∈ cuspBox ε, cuspParam x u r p = y := by
  obtain ⟨hyS, hyd, hys⟩ := hy
  have hyne : y ≠ x := by
    intro h
    rw [h] at hys
    simp at hys
  set ρ : ℝ := dist y x with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; exact dist_pos.mpr hyne
  have hρlt : ρ < ε := hyd
  have hρ2r : ρ < 2 * r := lt_of_lt_of_le hρlt hε2r
  have hnorm_yx : ‖y - x‖ = ρ := by rw [hρdef, dist_eq_norm]
  set w : ℂ := (y - x) / (ρ : ℂ) with hwdef
  have hwnorm : ‖w‖ = 1 := by
    rw [hwdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0, hnorm_yx]
    exact div_self (ne_of_gt hρ0)
  have hyw : y = x + ρ * w := by
    have hρne : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hρ0)
    rw [hwdef, mul_comm (ρ : ℂ), div_mul_cancel₀ (y - x) hρne]
    ring
  set z : ℂ := star u * w with hzdef
  have hznorm : ‖z‖ = 1 := by rw [hzdef, norm_mul, norm_star, hu, one_mul, hwnorm]
  have hwuz : w = u * z := by rw [hzdef, ← mul_assoc, mul_star_self hu, one_mul]
  have hzre_pos : 0 < z.re := by
    have h1 : (star u * (y - x)).re = ρ * z.re := by
      have h2 : star u * (x + ρ * w - x) = (ρ : ℂ) * z := by rw [hzdef]; ring
      rw [hyw, h2, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [h1] at hys
    by_contra hcon
    push_neg at hcon
    nlinarith [hys, hρ0]
  have hmC : 2 * mC Q r x hA w < ρ := by
    have hnot : x + ρ * w ∉ ⋃ w ∈ Q, Metric.closedBall w r := by rw [← hyw]; exact hyS
    by_contra hcon
    push_neg at hcon
    exact hnot ((hmodel w ρ hwnorm hρ0 hρlt).mpr hcon)
  have hprof : mC Q r x hA w = r * |z.im| := by
    rw [hwuz]
    exact mC_eq_abs_im ha hb hab hu hua hother hznorm hzre_pos.le
  rw [hprof] at hmC
  have hzim : |z.im| < ρ / (2 * r) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  set φ : ℝ := z.arg with hφdef
  have hzexp : eicC φ = z := by
    have h := Complex.norm_mul_exp_arg_mul_I z
    rw [hznorm] at h
    simp only [Complex.ofReal_one, one_mul] at h
    simpa [eicC, hφdef] using h
  have hcosφ : Real.cos φ = z.re := by rw [← hzexp, eicC_re]
  have hφπ : |φ| < Real.pi / 2 := by
    have hcos : 0 < Real.cos φ := by rw [hcosφ]; exact hzre_pos
    have hmem2 : Real.pi / 2 ∈ Set.Icc 0 Real.pi :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hlt : φ < Real.pi / 2 := by
      by_contra hcon
      push_neg at hcon
      have h1 : φ ∈ Set.Icc 0 Real.pi := ⟨by linarith [hcon, Real.pi_pos], Complex.arg_le_pi z⟩
      have h3 := Real.strictAntiOn_cos.antitoneOn hmem2 h1 hcon
      rw [Real.cos_pi_div_two] at h3
      linarith
    have hgt : -(Real.pi / 2) < φ := by
      by_contra hcon
      push_neg at hcon
      have h1 : -φ ∈ Set.Icc 0 Real.pi :=
        ⟨by linarith [hcon, Real.pi_pos], by linarith [Complex.neg_pi_lt_arg z]⟩
      have hle : Real.pi / 2 ≤ -φ := by linarith
      have h3 := Real.strictAntiOn_cos.antitoneOn hmem2 h1 hle
      rw [Real.cos_pi_div_two, Real.cos_neg] at h3
      linarith
    exact abs_lt.mpr ⟨hgt, hlt⟩
  have hsinlt : |φ| < betaS r ρ := by
    have habs : |z.im| = Real.sin |φ| := by
      rw [← hzexp, eicC_im,
        Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [hφπ, Real.pi_pos])]
    rw [habs] at hzim
    rw [← betaS_sin hr hρ0 hρ2r.le] at hzim
    have hm1 : |φ| ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [abs_nonneg φ, Real.pi_pos], le_of_lt hφπ⟩
    have hm2 : betaS r ρ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [le_of_lt (betaS_pos hr hρ0), Real.pi_pos],
        le_of_lt (betaS_lt_pi_div_two hr hρ2r)⟩
    exact (Real.strictMonoOn_sin.lt_iff_lt hm1 hm2).mp hzim
  set t : ℝ := φ / betaS r ρ with htdef
  have hβ0 : 0 < betaS r ρ := betaS_pos hr hρ0
  have ht1 : |t| < 1 := by
    rw [htdef, abs_div, abs_of_pos hβ0]
    rw [div_lt_one hβ0]
    exact hsinlt
  have ht_eq : eicC (t * betaS r ρ) = z := by
    rw [htdef, div_mul_cancel₀ φ (ne_of_gt hβ0)]
    exact hzexp
  refine ⟨(ρ, t), ⟨⟨hρ0, hρlt⟩, abs_lt.mp ht1⟩, ?_⟩
  show cuspParam x u r (ρ, t) = y
  rw [cuspParam, ht_eq, hyw, hwuz]

theorem cuspSet_eq_image {Q : Finset ℂ} {r : ℝ} (hr : 0 < r) {x u a b : ℂ}
    {hA : (actC Q r x).Nonempty} {ε : ℝ} (hε2r : ε ≤ 2 * r)
    (ha : a ∈ actC Q r x) (hb : b ∈ actC Q r x) (hab : b - x = -(a - x))
    (hu : ‖u‖ = 1) (hua : (star u * (a - x)).re = 0)
    (hother : ∀ w ∈ actC Q r x, w ≠ a → w ≠ b → (star u * (w - x)).re < 0)
    (hmodel : ∀ (u' : ℂ) (ρ : ℝ), ‖u'‖ = 1 → 0 < ρ → ρ < ε →
      (x + ρ * u' ∈ ⋃ w ∈ Q, Metric.closedBall w r ↔ ρ ≤ 2 * mC Q r x hA u')) :
    cuspSet Q r x u ε = cuspParam x u r '' cuspBox ε := by
  ext y
  constructor
  · intro hy
    obtain ⟨p, hp, hpeq⟩ := cuspSet_subset_cuspParam hr hε2r ha hb hab hu hua hother hmodel hy
    exact ⟨p, hp, hpeq⟩
  · rintro ⟨p, hp, rfl⟩
    exact cuspParam_mem_cuspSet hr hε2r ha hb hab hu hua hother hmodel hp

theorem cuspSet_preconnected {Q : Finset ℂ} {r : ℝ} (hr : 0 < r) {x u a b : ℂ}
    {hA : (actC Q r x).Nonempty} {ε : ℝ} (hε2r : ε ≤ 2 * r)
    (ha : a ∈ actC Q r x) (hb : b ∈ actC Q r x) (hab : b - x = -(a - x))
    (hu : ‖u‖ = 1) (hua : (star u * (a - x)).re = 0)
    (hother : ∀ w ∈ actC Q r x, w ≠ a → w ≠ b → (star u * (w - x)).re < 0)
    (hmodel : ∀ (u' : ℂ) (ρ : ℝ), ‖u'‖ = 1 → 0 < ρ → ρ < ε →
      (x + ρ * u' ∈ ⋃ w ∈ Q, Metric.closedBall w r ↔ ρ ≤ 2 * mC Q r x hA u')) :
    IsPreconnected (cuspSet Q r x u ε) := by
  rw [cuspSet_eq_image hr hε2r ha hb hab hu hua hother hmodel, cuspBox]
  exact (isPreconnected_Ioo.prod isPreconnected_Ioo).image _
    (continuous_cuspParam x u r).continuousOn

/-! ## The local-arc theorem at a cusp -/

theorem dist_cuspParam {x u : ℂ} {r : ℝ} (hu : ‖u‖ = 1) (p : ℝ × ℝ) :
    dist (cuspParam x u r p) x = |p.1| := by
  have h1 : cuspParam x u r p - x = ((p.1 : ℝ) : ℂ) * (u * eicC (p.2 * betaS r p.1)) := by
    rw [cuspParam]; ring
  rw [dist_eq_norm, h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul, hu, one_mul,
    norm_eicC, mul_one]

theorem star_mul_cuspParam_sub {x u : ℂ} {r : ℝ} (hu : ‖u‖ = 1) (p : ℝ × ℝ) :
    (star u * (cuspParam x u r p - x)).re = p.1 * Real.cos (p.2 * betaS r p.1) := by
  have h1 : cuspParam x u r p - x = ((p.1 : ℝ) : ℂ) * (u * eicC (p.2 * betaS r p.1)) := by
    rw [cuspParam]; ring
  have h2 : star u * (((p.1 : ℝ) : ℂ) * (u * eicC (p.2 * betaS r p.1)))
      = ((p.1 : ℝ) : ℂ) * (star u * (u * eicC (p.2 * betaS r p.1))) := by ring
  rw [h1, h2, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    star_mul_self_mul hu, eicC_re]

/-- At the two boundary directions of the cusp the profile is exactly the radius. -/
theorem two_mul_mC_eicC_beta {Q : Finset ℂ} {r : ℝ} {x a b u : ℂ} {hA : (actC Q r x).Nonempty}
    (hr : 0 < r) (ha : a ∈ actC Q r x) (hb : b ∈ actC Q r x) (hab : b - x = -(a - x))
    (hu : ‖u‖ = 1) (hua : (star u * (a - x)).re = 0)
    (hother : ∀ w ∈ actC Q r x, w ≠ a → w ≠ b → (star u * (w - x)).re < 0)
    {ρ c : ℝ} (hρ0 : 0 < ρ) (hρ : ρ < 2 * r) (hc : c = 1 ∨ c = -1) :
    2 * mC Q r x hA (u * eicC (c * betaS r ρ)) = ρ := by
  have hβ0 : 0 < betaS r ρ := betaS_pos hr hρ0
  have hβπ : betaS r ρ < Real.pi / 2 := betaS_lt_pi_div_two hr hρ
  have hsinpos : 0 < Real.sin (betaS r ρ) :=
    Real.sin_pos_of_pos_of_lt_pi hβ0 (by linarith [hβπ, Real.pi_pos])
  have hcs : Real.cos (c * betaS r ρ) = Real.cos (betaS r ρ) := by
    rcases hc with h | h
    · rw [h, one_mul]
    · rw [h, neg_mul, one_mul, Real.cos_neg]
  have hzre : 0 ≤ (eicC (c * betaS r ρ)).re := by
    rw [eicC_re, hcs]
    exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [hβ0], by linarith [hβπ]⟩).le
  have hprof := mC_eq_abs_im (hA := hA) ha hb hab hu hua hother (norm_eicC _) hzre
  have him : |(eicC (c * betaS r ρ)).im| = Real.sin (betaS r ρ) := by
    rw [eicC_im]
    rcases hc with h | h
    · rw [h, one_mul, abs_of_pos hsinpos]
    · rw [h, neg_mul, one_mul, Real.sin_neg, abs_neg, abs_of_pos hsinpos]
  rw [hprof, him, betaS_sin hr hρ0 hρ.le]
  field_simp

/-- A unit complex number in the open right half-plane whose imaginary part has the size of the
cusp half-width is one of the two boundary directions of the cusp. -/
theorem eq_eicC_beta_of_unit {z : ℂ} (hz : ‖z‖ = 1) (hzre : 0 < z.re) {ρ r : ℝ}
    (hr : 0 < r) (hρ0 : 0 < ρ) (hρ : ρ < 2 * r) (him : |z.im| = ρ / (2 * r)) :
    z = eicC (betaS r ρ) ∨ z = eicC (-(betaS r ρ)) := by
  have hβ0 : 0 < betaS r ρ := betaS_pos hr hρ0
  have hβπ : betaS r ρ < Real.pi / 2 := betaS_lt_pi_div_two hr hρ
  set φ : ℝ := z.arg with hφdef
  have hzexp : eicC φ = z := by
    have h := Complex.norm_mul_exp_arg_mul_I z
    rw [hz] at h
    simp only [Complex.ofReal_one, one_mul] at h
    simpa [eicC, hφdef] using h
  have hcosφ : Real.cos φ = z.re := by rw [← hzexp, eicC_re]
  have hφπ : |φ| < Real.pi / 2 := by
    have hcos : 0 < Real.cos φ := by rw [hcosφ]; exact hzre
    have hmem2 : Real.pi / 2 ∈ Set.Icc 0 Real.pi :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hlt : φ < Real.pi / 2 := by
      by_contra hcon
      push_neg at hcon
      have h1 : φ ∈ Set.Icc 0 Real.pi := ⟨by linarith [hcon, Real.pi_pos], Complex.arg_le_pi z⟩
      have h3 := Real.strictAntiOn_cos.antitoneOn hmem2 h1 hcon
      rw [Real.cos_pi_div_two] at h3
      linarith
    have hgt : -(Real.pi / 2) < φ := by
      by_contra hcon
      push_neg at hcon
      have h1 : -φ ∈ Set.Icc 0 Real.pi :=
        ⟨by linarith [hcon, Real.pi_pos], by linarith [Complex.neg_pi_lt_arg z]⟩
      have hle : Real.pi / 2 ≤ -φ := by linarith
      have h3 := Real.strictAntiOn_cos.antitoneOn hmem2 h1 hle
      rw [Real.cos_pi_div_two, Real.cos_neg] at h3
      linarith
    exact abs_lt.mpr ⟨hgt, hlt⟩
  have hφeq : |φ| = betaS r ρ := by
    have h1 : Real.sin |φ| = |z.im| := by
      rw [← hzexp, eicC_im]
      exact (Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [hφπ, Real.pi_pos])).symm
    have h2 : Real.sin |φ| = Real.sin (betaS r ρ) := by
      rw [h1, him, betaS_sin hr hρ0 hρ.le]
    have hm1 : |φ| ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [abs_nonneg φ, Real.pi_pos], le_of_lt hφπ⟩
    have hm2 : betaS r ρ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [le_of_lt hβ0, Real.pi_pos], le_of_lt hβπ⟩
    exact Real.strictMonoOn_sin.injOn hm1 hm2 h2
  rcases le_total 0 φ with h | h
  · left
    rw [abs_of_nonneg h] at hφeq
    rw [← hφeq]
    exact hzexp.symm
  · right
    rw [abs_of_nonpos h] at hφeq
    rw [← neg_eq_iff_eq_neg.mp hφeq]
    exact hzexp.symm

theorem frontierLocallyArc_of_cusp {Q : Finset ℂ} {r : ℝ} (hr : 0 < r) {q x u a b : ℂ}
    {hA : (actC Q r x).Nonempty} {ε : ℝ} (hε : 0 < ε) (hε2r : ε ≤ 2 * r)
    (hxq : x ∈ frontier (connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q))
    (ha : a ∈ actC Q r x) (hb : b ∈ actC Q r x) (hab : b - x = -(a - x))
    (hu : ‖u‖ = 1) (hua : (star u * (a - x)).re = 0)
    (hother : ∀ w ∈ actC Q r x, w ≠ a → w ≠ b → (star u * (w - x)).re < 0)
    (hmodel : ∀ (u' : ℂ) (ρ : ℝ), ‖u'‖ = 1 → 0 < ρ → ρ < ε →
      (x + ρ * u' ∈ ⋃ w ∈ Q, Metric.closedBall w r ↔ ρ ≤ 2 * mC Q r x hA u'))
    (hmeet : ∃ y ∈ (⋃ w ∈ Q, Metric.closedBall w r)ᶜ, dist y x < ε ∧
      0 < (star u * (y - x)).re ∧
      y ∈ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q)
    (hdisj : ∀ y ∈ (⋃ w ∈ Q, Metric.closedBall w r)ᶜ, dist y x < ε →
      (star u * (y - x)).re < 0 →
      y ∉ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q) :
    ∃ γ : ℝ → ℂ, Continuous γ ∧ Function.Injective γ ∧ γ 0 = x ∧
      γ '' Set.Ioo (-1) 1 = frontier (connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q)
        ∩ Metric.ball x ε := by
  classical
  set S : Set ℂ := ⋃ w ∈ Q, Metric.closedBall w r with hSdef
  set comp : Set ℂ := connectedComponentIn Sᶜ q with hcompdef
  have hSclosed : IsClosed S := isClosed_ballUAux Q r
  have hxS : x ∈ frontier S := frontier_componentIn_subset hSclosed hxq
  have hSsub : ∀ y ∈ S, y ∉ comp := fun y hy hyc => (connectedComponentIn_subset Sᶜ q hyc) hy
  have hfrS : ∀ {y : ℂ}, y ∈ frontier S → y ∈ S := fun hy => hSclosed.closure_eq ▸ hy.1
  set C : Set ℂ := cuspSet Q r x u ε with hCdef
  have hCeq : C = cuspParam x u r '' cuspBox ε :=
    cuspSet_eq_image hr hε2r ha hb hab hu hua hother hmodel
  have hCpre : IsPreconnected C :=
    cuspSet_preconnected hr hε2r ha hb hab hu hua hother hmodel
  obtain ⟨y₀, hy₀S, hy₀d, hy₀s, hy₀c⟩ := hmeet
  have hy₀C : y₀ ∈ C := ⟨hy₀S, hy₀d, hy₀s⟩
  have hCcomp : C ⊆ comp := by
    have h1 : C ⊆ connectedComponentIn Sᶜ y₀ :=
      hCpre.subset_connectedComponentIn hy₀C (fun z hz => hz.1)
    have h2 : connectedComponentIn Sᶜ y₀ = comp := by
      rw [hcompdef]
      exact (connectedComponentIn_eq hy₀c).symm
    rwa [h2] at h1
  have hxclosureC : x ∈ closure C := by
    refine Metric.mem_closure_iff.mpr fun δ hδ => ?_
    have hcont : Continuous fun t : ℝ => cuspParam x u r (t, 0) :=
      (continuous_cuspParam x u r).comp (continuous_id.prodMk continuous_const)
    obtain ⟨η, hη0, hη⟩ := Metric.continuous_iff.mp hcont 0 δ hδ
    refine ⟨cuspParam x u r (min (η / 2) (ε / 2), 0), ?_, ?_⟩
    · rw [hCeq]
      refine ⟨_, ⟨⟨lt_min (by linarith) (by linarith),
        lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩,
        by norm_num⟩, rfl⟩
    · have hmin_pos : 0 < min (η / 2) (ε / 2) := lt_min (by linarith) (by linarith)
      have hmin_lt : min (η / 2) (ε / 2) < η :=
        lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have h1 : dist (cuspParam x u r (min (η / 2) (ε / 2), 0)) (cuspParam x u r (0, 0)) < δ :=
        hη _ (by rw [Real.dist_eq, sub_zero, abs_of_pos hmin_pos]; exact hmin_lt)
      rw [show cuspParam x u r (0, 0) = x from by rw [cuspParam]; simp] at h1
      rw [dist_comm]
      exact h1
  have hxfr : x ∈ frontier comp :=
    ⟨closure_mono hCcomp hxclosureC, fun hxint => hSsub x (hfrS hxS) (interior_subset hxint)⟩
  have hdoor : ∀ (ρ c : ℝ), 0 < ρ → ρ < ε → (c = 1 ∨ c = -1) →
      cuspParam x u r (ρ, c) ∈ frontier comp ∧ cuspParam x u r (ρ, c) ∈ Metric.ball x ε := by
    intro ρ c hρ0 hρε hc
    have hρ2r : ρ < 2 * r := lt_of_lt_of_le hρε hε2r
    have hclos : cuspParam x u r (ρ, c) ∈ closure C := by
      refine Metric.mem_closure_iff.mpr fun δ hδ => ?_
      have hcont : Continuous fun s : ℝ => cuspParam x u r (ρ, s) :=
        (continuous_cuspParam x u r).comp (continuous_const.prodMk continuous_id)
      obtain ⟨η, hη0, hη⟩ := Metric.continuous_iff.mp hcont c δ hδ
      set m : ℝ := min (η / 2) (1 / 2) with hmdef
      have hm0 : 0 < m := lt_min (by linarith) (by norm_num)
      have hmle : m ≤ 1 / 2 := min_le_right _ _
      have hmη : m < η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hcabs : |c| = 1 := by rcases hc with h | h <;> rw [h] <;> norm_num
      refine ⟨cuspParam x u r (ρ, c * (1 - m)), ?_, ?_⟩
      · rw [hCeq]
        refine ⟨_, ⟨⟨hρ0, hρε⟩, ?_⟩, rfl⟩
        rcases hc with h | h <;> rw [h] <;> rw [Set.mem_Ioo] <;> constructor <;>
          linarith [hm0, hmle]
      · have hdist : dist (c * (1 - m)) c < η := by
          rw [Real.dist_eq, show c * (1 - m) - c = c * (-m) from by ring, abs_mul, abs_neg,
            hcabs, one_mul, abs_of_pos hm0]
          exact hmη
        rw [dist_comm]
        exact hη _ hdist
    have hfrS' : cuspParam x u r (ρ, c) ∈ frontier S := by
      have hρeq : ρ = 2 * mC Q r x hA (u * eicC (c * betaS r ρ)) :=
        (two_mul_mC_eicC_beta hr ha hb hab hu hua hother hρ0 hρ2r hc).symm
      have hnorm : ‖u * eicC (c * betaS r ρ)‖ = 1 := by
        rw [norm_mul, hu, norm_eicC, mul_one]
      rw [show cuspParam x u r (ρ, c) = x + ρ * (u * eicC (c * betaS r ρ)) from rfl]
      exact (frontier_iff_eq_mC hmodel hnorm hρ0 hρε).mpr hρeq
    refine ⟨⟨closure_mono hCcomp hclos,
      fun hint => hSsub _ (hfrS hfrS') (interior_subset hint)⟩, ?_⟩
    rw [Metric.mem_ball, dist_cuspParam hu, abs_of_pos hρ0]
    exact hρε
  have hsub : frontier comp ∩ Metric.ball x ε ⊆ ({x} : Set ℂ) ∪
      (fun p : ℝ × ℝ => cuspParam x u r p) '' (Set.Ioo 0 ε ×ˢ ({1, -1} : Set ℝ)) := by
    rintro y ⟨hyfr, hyball⟩
    by_cases hyx : y = x
    · exact Or.inl hyx
    have hyd : dist y x < ε := by rw [Metric.mem_ball] at hyball; exact hyball
    have hdpos : 0 < dist y x := dist_pos.mpr hyx
    set ρ : ℝ := dist y x with hρdef
    have hρ0 : 0 < ρ := hdpos
    have hρlt : ρ < ε := hyd
    have hρ2r : ρ < 2 * r := lt_of_lt_of_le hρlt hε2r
    have hhy : ‖y - x‖ = ρ := by rw [hρdef, dist_eq_norm]
    set w : ℂ := (y - x) / (ρ : ℂ) with hwdef
    have hwnorm : ‖w‖ = 1 := by
      rw [hwdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0, hhy]
      exact div_self (ne_of_gt hρ0)
    have hyw : y = x + ρ * w := by
      have hρne : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hρ0)
      rw [hwdef, mul_comm (ρ : ℂ), div_mul_cancel₀ (y - x) hρne]
      ring
    set z : ℂ := star u * w with hzdef
    have hznorm : ‖z‖ = 1 := by rw [hzdef, norm_mul, norm_star, hu, one_mul, hwnorm]
    have hwuz : w = u * z := by rw [hzdef, ← mul_assoc, mul_star_self hu, one_mul]
    have hprofs : mC Q r x hA (u * z) = ρ / 2 := by
      have hun : ‖u * z‖ = 1 := by rw [norm_mul, hu, hznorm, mul_one]
      have hS : x + ρ * (u * z) ∈ frontier S := by
        rw [show x + ρ * (u * z) = y from by rw [hyw, hwuz]]
        exact frontier_componentIn_subset hSclosed hyfr
      have h3 := (frontier_iff_eq_mC hmodel hun hρ0 hρlt).mp hS
      linarith
    have him1 : r * |z.im| ≤ ρ / 2 := by
      rw [← hprofs]
      exact mC_ge_abs_im (hA := hA) ha hb hab hu hua hznorm
    have hzim1 : |z.im| < 1 := by
      have h1 : |z.im| ≤ ρ / (2 * r) := by
        rw [le_div_iff₀ (by linarith)]
        linarith
      have h2 : ρ / (2 * r) < 1 := by rw [div_lt_one (by linarith)]; linarith
      linarith
    have hzre_ne : z.re ≠ 0 := by
      intro h0
      have h1 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      rw [hznorm, h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] at h1
      have h2 : (|z.im|) ^ 2 = (1 : ℝ) ^ 2 := by rw [sq_abs, one_pow]; linarith [h1]
      have h3 : |z.im| = 1 := by simpa using (sq_eq_sq_iff_abs_eq_abs (|z.im|) (1 : ℝ)).mp h2
      linarith [hzim1, h3]
    have hzre : 0 < z.re := by
      rcases lt_or_gt_of_ne hzre_ne with h | h
      · exfalso
        have hcont : Continuous fun y' : ℂ => (star u * (y' - x)).re := by fun_prop
        have hneg : (star u * (y - x)).re < 0 := by
          have h1 : (star u * (y - x)).re = ρ * z.re := by
            have h2 : star u * (x + ρ * w - x) = (ρ : ℂ) * z := by rw [hzdef]; ring
            rw [hyw, h2, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
              mul_comm]
          rw [h1]
          exact mul_neg_of_pos_of_neg hρ0 h
        obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball y hyball
        obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.isOpen_iff.mp (isOpen_lt hcont continuous_const) y hneg
        obtain ⟨y', hy'comp, hy'd⟩ :=
          Metric.mem_closure_iff.mp hyfr.1 (min δ₁ δ₂) (lt_min hδ₁ hδ₂)
        have hy'd' : dist y' y < min δ₁ δ₂ := by rwa [dist_comm] at hy'd
        have hy'ball : y' ∈ Metric.ball x ε :=
          hδ₁' (Metric.mem_ball.mpr (lt_of_lt_of_le hy'd' (min_le_left _ _)))
        have hy'neg : (star u * (y' - x)).re < 0 :=
          hδ₂' (Metric.mem_ball.mpr (lt_of_lt_of_le hy'd' (min_le_right _ _)))
        exact hdisj y' (connectedComponentIn_subset Sᶜ q hy'comp) hy'ball hy'neg hy'comp
      · exact h
    have himeq : |z.im| = ρ / (2 * r) := by
      have h2 : mC Q r x hA (u * z) = r * |z.im| :=
        mC_eq_abs_im (hA := hA) ha hb hab hu hua hother hznorm hzre.le
      rw [h2] at hprofs
      rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)] at hprofs
      rw [eq_div_iff (by linarith : (2 * r) ≠ 0)]
      linarith
    rcases eq_eicC_beta_of_unit hznorm hzre hr hρ0 hρ2r himeq with hcase | hcase
    · refine Or.inr ⟨(ρ, 1), ⟨⟨hρ0, hρlt⟩, Or.inl rfl⟩, ?_⟩
      show x + ((ρ : ℝ) : ℂ) * (u * eicC (1 * betaS r ρ)) = y
      rw [show (1 : ℝ) * betaS r ρ = betaS r ρ from one_mul _, ← hcase]
      rw [hyw, hwuz]
    · refine Or.inr ⟨(ρ, -1), ⟨⟨hρ0, hρlt⟩, Or.inr rfl⟩, ?_⟩
      show x + ((ρ : ℝ) : ℂ) * (u * eicC ((-1 : ℝ) * betaS r ρ)) = y
      rw [show (-1 : ℝ) * betaS r ρ = -(betaS r ρ) from by ring, ← hcase]
      rw [hyw, hwuz]
  set γ : ℝ → ℂ := fun s => if 0 ≤ s then cuspParam x u r (ε * s, 1)
      else cuspParam x u r (ε * (-s), -1) with hγdef
  have hγval : ∀ s : ℝ, γ s = (if 0 ≤ s then cuspParam x u r (ε * s, 1)
      else cuspParam x u r (ε * (-s), -1)) := fun s => by rw [hγdef]
  have hγ0 : γ 0 = x := by
    rw [hγval 0, if_pos (le_refl (0 : ℝ)), mul_zero]
    show x + ((0 : ℝ) : ℂ) * (u * eicC (1 * betaS r 0)) = x
    simp
  have hγdist : ∀ s : ℝ, dist (γ s) x = ε * |s| := by
    intro s
    rw [hγval s]
    by_cases hs : 0 ≤ s
    · rw [if_pos hs, dist_cuspParam hu, abs_mul, abs_of_pos hε, abs_of_nonneg hs]
    · rw [if_neg hs, dist_cuspParam hu, abs_mul, abs_of_pos hε, abs_neg,
        abs_of_neg (lt_of_not_ge hs)]
  have hcont : Continuous γ := by
    rw [hγdef]
    refine Continuous.if ?_ ?_ ?_
    · intro s hs
      have hs0 : s = 0 := by
        rw [show {t : ℝ | 0 ≤ t} = Set.Ici (0 : ℝ) from rfl, frontier_Ici] at hs
        exact hs
      subst hs0
      simp [cuspParam]
    · exact (continuous_cuspParam x u r).comp (by fun_prop)
    · exact (continuous_cuspParam x u r).comp (by fun_prop)
  have hmain : ∀ a b : ℝ, 0 ≤ a → b < 0 → γ a = γ b → False := by
    intro a b ha hb heqab
    have hdist : ε * |a| = ε * |b| := by
      have h1 := hγdist a
      rw [heqab, hγdist b] at h1
      exact h1.symm
    have hsabs : |a| = |b| := mul_left_cancel₀ (ne_of_gt hε) hdist
    have hpos : 0 < a := by
      rcases eq_or_lt_of_le ha with h | h
      · rw [← h, abs_zero] at hsabs
        exact absurd (abs_eq_zero.mp hsabs.symm) (ne_of_lt hb)
      · exact h
    have hρne : ((ε : ℂ) * (a : ℂ)) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hε))
        (Complex.ofReal_ne_zero.mpr (ne_of_gt hpos))
    have h1 : cuspParam x u r (ε * a, 1) = cuspParam x u r (ε * a, -1) := by
      have hγa : γ a = cuspParam x u r (ε * a, 1) := by rw [hγval a, if_pos ha]
      have hγb : γ b = cuspParam x u r (ε * a, -1) := by
        rw [hγval b, if_neg (not_le.mpr hb)]
        rw [abs_of_nonneg ha, abs_of_neg hb] at hsabs
        rw [show -b = a from by linarith [hsabs]]
      rw [hγa, hγb] at heqab
      exact heqab
    have h3 : ((ε : ℂ) * (a : ℂ)) * (u * eicC (betaS r (ε * a)))
        = ((ε : ℂ) * (a : ℂ)) * (u * eicC (-(betaS r (ε * a)))) := by
      have h4 := congrArg (fun z => z - x) h1
      simpa [cuspParam, Complex.ofReal_mul] using h4
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hu
      norm_num at hu
    have h5 : eicC (betaS r (ε * a)) = eicC (-(betaS r (ε * a))) :=
      mul_left_cancel₀ hu0 (mul_left_cancel₀ hρne h3)
    have hβ0 : 0 < betaS r (ε * a) := betaS_pos hr (mul_pos hε hpos)
    have hβle : betaS r (ε * a) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
    exact eicC_ne_of_sub_mem (by linarith) (by linarith [hβle, Real.pi_pos]) h5
  refine ⟨γ, hcont, ?_, hγ0, ?_⟩
  · intro s s' heq
    have hdist : ε * |s| = ε * |s'| := by
      have h1 := hγdist s
      rw [heq, hγdist s'] at h1
      exact h1.symm
    have hsabs : |s| = |s'| := mul_left_cancel₀ (ne_of_gt hε) hdist
    rcases lt_trichotomy s 0 with hs | hs | hs <;> rcases lt_trichotomy s' 0 with hs' | hs' | hs'
    · rw [abs_of_neg hs, abs_of_neg hs'] at hsabs
      linarith
    · rw [hs', abs_zero] at hsabs
      exact absurd (abs_eq_zero.mp hsabs) (ne_of_lt hs)
    · exact (hmain s' s (le_of_lt hs') hs heq.symm).elim
    · rw [hs, abs_zero] at hsabs
      exact absurd (abs_eq_zero.mp hsabs.symm) (ne_of_lt hs')
    · rw [hs, hs']
    · rw [hs, abs_zero] at hsabs
      exact absurd (abs_eq_zero.mp hsabs.symm) (ne_of_gt hs')
    · exact (hmain s s' (le_of_lt hs) hs' heq).elim
    · rw [hs', abs_zero] at hsabs
      exact absurd (abs_eq_zero.mp hsabs) (ne_of_gt hs)
    · rw [abs_of_pos hs, abs_of_pos hs'] at hsabs
      exact mul_left_cancel₀ (ne_of_gt hε) (by rw [hsabs])
  · apply Subset.antisymm
    · rintro y ⟨s, hs, rfl⟩
      rcases lt_trichotomy s 0 with hsneg | hszero | hspos
      · have hρ0 : 0 < ε * (-s) := mul_pos hε (by linarith)
        have hρlt : ε * (-s) < ε := by nlinarith [hε, hs.1]
        rw [hγval s, if_neg (not_le.mpr hsneg)]
        exact hdoor (ε * (-s)) (-1) hρ0 hρlt (Or.inr rfl)
      · rw [hszero, hγ0]
        exact ⟨hxfr, by rw [Metric.mem_ball, dist_self]; exact hε⟩
      · have hρ0 : 0 < ε * s := mul_pos hε hspos
        have hρlt : ε * s < ε := by nlinarith [hε, hs.2]
        rw [hγval s, if_pos (le_of_lt hspos)]
        exact hdoor (ε * s) 1 hρ0 hρlt (Or.inl rfl)
    · intro y hy
      rcases hsub hy with h | ⟨p, hp, hpeq⟩
      · refine ⟨0, by norm_num, ?_⟩
        rw [hγ0, h]
      · obtain ⟨hp1, hp2⟩ := hp
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp2
        rcases hp2 with h1 | h1
        · have hρ0 : 0 < p.1 := hp1.1
          have hρlt : p.1 < ε := hp1.2
          have hq0 : 0 < p.1 / ε := div_pos hρ0 hε
          have hq1 : p.1 / ε < 1 := by rw [div_lt_one hε]; exact hρlt
          refine ⟨p.1 / ε, ⟨by linarith, hq1⟩, ?_⟩
          rw [hγval (p.1 / ε), if_pos (le_of_lt hq0)]
          rw [show ε * (p.1 / ε) = p.1 from by field_simp]
          rw [show (p.1, 1) = p from Prod.ext rfl h1.symm]
          exact hpeq
        · have hρ0 : 0 < p.1 := hp1.1
          have hρlt : p.1 < ε := hp1.2
          have hq0 : 0 < p.1 / ε := div_pos hρ0 hε
          have hq1 : p.1 / ε < 1 := by rw [div_lt_one hε]; exact hρlt
          refine ⟨-(p.1 / ε), ⟨by linarith [hq1], by linarith [hq0]⟩, ?_⟩
          rw [hγval (-(p.1 / ε)), if_neg (by linarith [hq0])]
          rw [show ε * - -(p.1 / ε) = p.1 from by rw [neg_neg]; field_simp]
          rw [show (p.1, -1) = p from Prod.ext rfl h1.symm]
          exact hpeq

/-- **The other side of the cusp is empty when a third active centre exists.** -/
theorem cusp_excludes {Q : Finset ℂ} {r : ℝ} {x u a b w₀ : ℂ} {hA : (actC Q r x).Nonempty}
    (hr : 0 < r) (ha : a ∈ actC Q r x) (hb : b ∈ actC Q r x) (hab : b - x = -(a - x))
    (hu : ‖u‖ = 1) (hua : (star u * (a - x)).re = 0)
    (hxS : x ∈ ⋃ w ∈ Q, Metric.closedBall w r)
    (hw₀ : w₀ ∈ actC Q r x) (hδ : (star u * (w₀ - x)).re < 0)
    {ε : ℝ} (hε : 0 < ε) (hε2r : ε ≤ 2 * r)
    (hmodel : ∀ (u' : ℂ) (ρ : ℝ), ‖u'‖ = 1 → 0 < ρ → ρ < ε →
      (x + ρ * u' ∈ ⋃ w ∈ Q, Metric.closedBall w r ↔ ρ ≤ 2 * mC Q r x hA u')) :
    ∃ ε' > 0, ε' ≤ ε ∧ ∀ y ∈ (⋃ w ∈ Q, Metric.closedBall w r)ᶜ, dist y x < ε' →
      0 < (star u * (y - x)).re := by
  set δ : ℝ := -((star u * (w₀ - x)).re) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  refine ⟨min ε (min δ (2 * r)) / 2, ?_, ?_, ?_⟩
  · exact div_pos (lt_min hε (lt_min hδpos (by linarith))) (by norm_num)
  · linarith [min_le_left ε (min δ (2 * r))]
  · intro y hyS hyd
    have hyne : y ≠ x := by
      intro h
      rw [h] at hyS
      exact hyS hxS
    set ρ : ℝ := dist y x with hρdef
    have hρ0 : 0 < ρ := by rw [hρdef]; exact dist_pos.mpr hyne
    have hρlt : ρ < ε := lt_of_lt_of_le hyd (by linarith [min_le_left ε (min δ (2 * r))])
    have hρδ : ρ < δ / 2 := by
      have h2 : min δ (2 * r) ≤ δ := min_le_left _ _
      linarith [hyd, min_le_right ε (min δ (2 * r))]
    have hρr : ρ < r := by
      have h2 : min δ (2 * r) ≤ 2 * r := min_le_right _ _
      linarith [hyd, min_le_right ε (min δ (2 * r))]
    have hhy : ‖y - x‖ = ρ := by rw [hρdef, dist_eq_norm]
    set w : ℂ := (y - x) / (ρ : ℂ) with hwdef
    have hwnorm : ‖w‖ = 1 := by
      rw [hwdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0, hhy]
      exact div_self (ne_of_gt hρ0)
    have hyw : y = x + ρ * w := by
      have hρne : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hρ0)
      rw [hwdef, mul_comm (ρ : ℂ), div_mul_cancel₀ (y - x) hρne]
      ring
    set z : ℂ := star u * w with hzdef
    have hznorm : ‖z‖ = 1 := by rw [hzdef, norm_mul, norm_star, hu, one_mul, hwnorm]
    have hwuz : w = u * z := by rw [hzdef, ← mul_assoc, mul_star_self hu, one_mul]
    have hmC : 2 * mC Q r x hA w < ρ := by
      have hnot : x + ρ * w ∉ ⋃ w ∈ Q, Metric.closedBall w r := by rw [← hyw]; exact hyS
      by_contra hcon
      push_neg at hcon
      exact hnot ((hmodel w ρ hwnorm hρ0 hρlt).mpr hcon)
    have hI : |z.im| < ρ / (2 * r) := by
      have h1 : 2 * (r * |z.im|) < ρ := by
        have h2 := mC_ge_abs_im (hA := hA) ha hb hab hu hua hznorm
        rw [← hwuz] at h2
        linarith
      rw [lt_div_iff₀ (by linarith)]
      linarith
    have hcon : (star w * (w₀ - x)).re < ρ / 2 := by
      have h1 : (star w * (w₀ - x)).re ≤ mC Q r x hA w := le_mC hw₀
      linarith
    have hstar : (star w * (w₀ - x)).re
        = z.re * (star u * (w₀ - x)).re + z.im * (star u * (w₀ - x)).im := by
      rw [hwuz, star_mul, mul_assoc, star_mul_re]
    have hImg : |(star u * (w₀ - x)).im| ≤ r := by
      calc |(star u * (w₀ - x)).im| ≤ ‖star u * (w₀ - x)‖ := Complex.abs_im_le_norm _
        _ = r := norm_star_mul_sub hu hw₀
    have hre : (star u * (w₀ - x)).re = -δ := by rw [hδdef, neg_neg]
    have h5 : |z.im| * r < ρ / 2 := by
      have h6 := mul_lt_mul_of_pos_right hI hr
      have h6' : (ρ / (2 * r)) * r = ρ / 2 := by field_simp
      rwa [h6'] at h6
    have h4 : z.im * (star u * (w₀ - x)).im < ρ / 2 := by
      have h7 : z.im * (star u * (w₀ - x)).im ≤ |z.im| * r := by
        calc z.im * (star u * (w₀ - x)).im ≤ |z.im * (star u * (w₀ - x)).im| := le_abs_self _
          _ = |z.im| * |(star u * (w₀ - x)).im| := by rw [abs_mul]
          _ ≤ |z.im| * r := mul_le_mul_of_nonneg_left hImg (abs_nonneg _)
      linarith
    have h4b : -(ρ / 2) < z.im * (star u * (w₀ - x)).im := by
      have h7 : -( |z.im| * r) ≤ z.im * (star u * (w₀ - x)).im := by
        have h7a := neg_le_abs (z.im * (star u * (w₀ - x)).im)
        rw [abs_mul] at h7a
        have h7b : |z.im| * |(star u * (w₀ - x)).im| ≤ |z.im| * r :=
          mul_le_mul_of_nonneg_left hImg (abs_nonneg _)
        linarith
      linarith
    have hkey : (-z.re) * δ < ρ := by
      have h8 : -(z.re * δ) + z.im * (star u * (w₀ - x)).im < ρ / 2 := by
        have h8a : z.re * (-δ) + z.im * (star u * (w₀ - x)).im < ρ / 2 := by
          rw [hstar, hre] at hcon
          exact hcon
        have h8b : z.re * (-δ) = -(z.re * δ) := by ring
        rwa [h8b] at h8a
      have h9 : -(z.re * δ) < ρ := by linarith [h4b, h8]
      have h10 : (-z.re) * δ = -(z.re * δ) := by ring
      rwa [h10]
    have hzre : 0 < z.re := by
      by_contra hcon2
      push_neg at hcon2
      have h9 : |z.re| * δ < ρ := by
        rw [abs_of_nonpos hcon2]
        linarith
      have h10 : |z.re| < 1 / 2 := by
        have h11 : |z.re| * δ < δ / 2 := lt_trans h9 hρδ
        have h12 : |z.re| < (δ / 2) / δ := by rw [lt_div_iff₀ hδpos]; linarith
        calc |z.re| < (δ / 2) / δ := h12
          _ = 1 / 2 := by field_simp
      have h13 : |z.im| < 1 / 2 := by
        have h14 : ρ / (2 * r) < 1 / 2 := by
          rw [div_lt_iff₀ (by linarith)]; linarith
        linarith
      have h15 : z.re ^ 2 + z.im ^ 2 = 1 := by
        have h1 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; ring
        rw [hznorm] at h1
        linarith
      have h16 : |z.re| ^ 2 = z.re ^ 2 := sq_abs _
      have h17 : |z.im| ^ 2 = z.im ^ 2 := sq_abs _
      have h18 : |z.re| ^ 2 < (1 / 2 : ℝ) ^ 2 := by nlinarith [h10, abs_nonneg z.re]
      have h19 : |z.im| ^ 2 < (1 / 2 : ℝ) ^ 2 := by nlinarith [h13, abs_nonneg z.im]
      rw [h16] at h18
      rw [h17] at h19
      nlinarith [h15, h18, h19]
    have hfin : (star u * (y - x)).re = ρ * z.re := by
      have h2 : star u * (x + ρ * w - x) = (ρ : ℂ) * z := by rw [hzdef]; ring
      rw [hyw, h2, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        mul_comm]
    rw [hfin]
    exact mul_pos hρ0 hzre

end

end Work.Smooth.SphereJordan
