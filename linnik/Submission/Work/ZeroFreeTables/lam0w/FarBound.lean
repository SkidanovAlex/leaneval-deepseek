/-
# ZeroFreeTables/lam0w/Aux — auxiliary lemmas for the wide HB Lemma 8.3

The single clean fact proved here is the far-cost bound for a single `P₃`-term used by
the near-zero extraction of the `P₃` engine: a zero `u` outside the `δ`-window contributes
at most `8(a+λ₁)/(δL)` in absolute value to the near sum.

This is a clean replacement of `Work.ZeroFreeTables.P9.P3term_abs_le_of_far` (which is
stated with a `sorry` in the workspace), so that lemmas depending on it are axiom-free.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.Table4.HB83_base

open Complex DirichletCharacter
namespace Work.ZeroFreeTables.lam0w

/-- **Far-cost bound for a single `P₃`-term.**  If the zero `u` lies outside the `δ`-window
around `1 + i·Im s` and `λ₁ ≤ (1 - u.re)L`, then
`|Re P₃((a+λ₁)/((s-u)L))| ≤ 8(a+λ₁)/(δL)`.

(Replacing the `sorry`ed `P9.P3term_abs_le_of_far` by a proof: `|s-u| > δ` because
`Re(s-u) ≥ 1 - u.re`, and `|s-u| ≥ 1 - u.re` because `Re(s-u) = 1 - u.re + a/L`; the
two bounds give `‖w‖ ≤ min(α/(δL), 1 + a/((1-u.re)L)) ≤ 3/2` and the claim follows from
`|Re P₃(w)| ≤ ‖w‖+‖w‖²+(2/3)‖w‖³`.) -/
theorem P3termFar {a lam₁ L δ : ℝ} (hL : 0 < L) (ha : 0 < a)
    (hlam₁ : 0 ≤ lam₁) (hδ : 0 < δ) (haδ : 2 * a ≤ δ * L) {s u : ℂ}
    (hsre : s.re = 1 + a / L) (hmin : lam₁ ≤ (1 - u.re) * L)
    (hfar : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖) :
    |(Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re|
      ≤ 8 * (a + lam₁) / (δ * L) := by
  have hα0 : 0 < a + lam₁ := by linarith
  have h1ure : 0 ≤ 1 - u.re := by
    have h0 : 0 ≤ (1 - u.re) * L := le_trans hlam₁ hmin
    exact (mul_nonneg_iff_of_pos_right hL).mp h0
  set w : ℂ := (((a + lam₁ : ℝ)) : ℂ) / ((s - u) * (L : ℂ)) with hwdef
  have hnorm : ‖w‖ = (a + lam₁) / (‖s - u‖ * L) := by
    rw [hwdef]
    simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα0,
      abs_of_pos hL]
  have hre : (1 : ℝ) - u.re ≤ ‖s - u‖ := by
    have h1 : (s - u).re = 1 + a / L - u.re := by rw [Complex.sub_re, hsre]
    have h2 : (1 : ℝ) - u.re ≤ (s - u).re := by rw [h1]; have : 0 < a / L := div_pos ha hL; linarith
    exact le_trans h2 (Complex.re_le_norm _)
  have hgt : δ < ‖s - u‖ := by
    have hsq1 : ((1:ℝ) - u.re)^2 ≤ (1 + a / L - u.re)^2 := by
      apply pow_le_pow_left₀ h1ure
      have : 0 < a / L := div_pos ha hL; linarith
    have hnorm2 : ‖s - u‖^2 = (1 + a/L - u.re)^2 + (s.im - u.im)^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hsre]; ring
    have hfn : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖^2
        = (1 - u.re)^2 + (s.im - u.im)^2 := by
      have heq : (1 : ℂ) + (s.im : ℂ) * Complex.I - u
          = ((1 - u.re : ℝ) : ℂ) + ((s.im - u.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im]
      rw [heq, Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
    have h1 : δ^2 < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖^2 := by
      nlinarith [hfar, hδ, norm_nonneg ((1 : ℂ) + (s.im : ℂ) * Complex.I - u)]
    rw [hfn] at h1
    have : δ^2 < ‖s - u‖^2 := by rw [hnorm2]; linarith
    nlinarith [hδ, norm_nonneg (s-u), this]
  have hnw : ‖w‖ ≤ (a + lam₁) / (δ * L) := by
    rw [hnorm]
    apply div_le_div_of_nonneg_left (by linarith) (by positivity) (by nlinarith)
  have hP3 : |(P3 w).re| ≤ ‖w‖ + ‖w‖^2 + (2/3) * ‖w‖^3 := by
    have h1 : |(P3 w).re| ≤ ‖P3 w‖ := Complex.abs_re_le_norm _
    have h2 : ‖P3 w‖ ≤ ‖w‖ + ‖w‖^2 + (2/3) * ‖w‖^3 := by
      have h : P3 w = w + w^2 + ((2:ℂ)/3) * w^3 := by
        unfold Work.ZeroFreeTables.P3; push_cast; ring
      calc ‖w + w ^ 2 + ((2:ℂ)/3) * w ^ 3‖
          ≤ ‖w + w^2‖ + ‖((2:ℂ)/3) * w^3‖ := norm_add_le _ _
        _ ≤ (‖w‖ + ‖w^2‖) + (2/3) * ‖w^3‖ := by
            have h23 : ‖((2:ℂ)/3) * w^3‖ = (2/3) * ‖w^3‖ := by
              rw [norm_mul, norm_div, Complex.norm_ofNat, Complex.norm_ofNat]
            have h12 := norm_add_le w (w^2)
            rw [h23]; linarith
        _ = ‖w‖ + ‖w‖^2 + (2/3) * ‖w‖^3 := by rw [norm_pow, norm_pow]
    linarith
  have hw : w = ((a + lam₁) / ((s - u) * (L : ℂ))) := by rw [hwdef]; push_cast; ring
  rw [← hw]
  set A : ℝ := (a + lam₁) / (δ * L) with hAdef
  have hA0 : 0 ≤ A := div_nonneg (by linarith) (by positivity)
  have hnwA : ‖w‖ ≤ A := hnw
  have hgoal : 8 * A = 8 * (a + lam₁) / (δ * L) := by rw [hAdef]; ring
  by_cases hB : A ≤ 1
  · have ht0 := norm_nonneg w
    have h2 : ‖w‖^2 ≤ A^2 := pow_le_pow_left₀ ht0 hnwA 2
    have h3 : ‖w‖^3 ≤ A^3 := pow_le_pow_left₀ ht0 hnwA 3
    have hAA : A + A^2 + (2/3)*A^3 ≤ (8/3)*A := by nlinarith [hA0, hB, sq_nonneg A]
    have h85 : (8/3)*A ≤ 8*A := by nlinarith [hA0]
    rw [← hgoal]
    linarith [hP3, h2, h3, hAA, h85]
  · simp only [not_le] at hB
    have h32 : ‖w‖ ≤ 3/2 := by
      by_cases hcase : δ ≤ 1 - u.re
      · have h1ure' : 0 < 1 - u.re := lt_of_lt_of_le hδ hcase
        have hB' : ‖w‖ ≤ (a + lam₁) / ((1 - u.re) * L) := by
          rw [hnorm]
          apply div_le_div_of_nonneg_left (by linarith) (by positivity) (by nlinarith [hre])
        have hbound : (a + lam₁) ≤ (3/2) * ((1 - u.re) * L) := by
          have ha' : a ≤ δ * L / 2 := by linarith
          have hc : δ * L ≤ (1 - u.re) * L := by nlinarith [hcase, hL]
          nlinarith [ha', hmin, hc]
        have hq : (a + lam₁) / ((1 - u.re) * L) ≤ 3/2 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [hbound]
        linarith [hB', hq]
      · simp only [not_le] at hcase
        have hlam1 : lam₁ < δ * L := by nlinarith [hmin, hcase, hL]
        have halpha : a + lam₁ < (3/2) * (δ * L) := by nlinarith [haδ, hlam1]
        have h3 : A < 3/2 := by
          rw [hAdef, div_lt_iff₀ (by positivity)]; linarith
        linarith [hnwA]
    have ht0 := norm_nonneg w
    have h2 : ‖w‖^2 ≤ (3/2)^2 := pow_le_pow_left₀ ht0 h32 2
    have h3 : ‖w‖^3 ≤ (3/2)^3 := pow_le_pow_left₀ ht0 h32 3
    have h6 : ‖w‖ + ‖w‖^2 + (2/3) * ‖w‖^3 ≤ 8 := by nlinarith [h2, h3, ht0]
    have h8 : 8 ≤ 8 * A := by nlinarith [hB]
    rw [← hgoal]
    linarith [hP3, h6, h8]


/-- The `P₃`-argument of the near-zero sum, written in the `P3AB` normal form: for
`s.re = 1 + a/L` and `u.re = 1 - lam/L`, `Re P₃(al/((s-u)L)) = P3AB al (a+lam) ((s.im-u.im)L)`. -/
lemma reP3_div_eq_P3AB {al a lam L : ℝ} {s u : ℂ} (hL : L ≠ 0)
    (hs : s.re = 1 + a / L) (hu : u.re = 1 - lam / L) :
    (Work.ZeroFreeTables.P3 (((a : ℂ) + (al : ℂ)) / ((s - u) * (L : ℂ)))).re
      = Work.ZeroFreeTables.Table4.P3AB (a + al) (a + lam) ((s.im - u.im) * L) := by
  unfold Work.ZeroFreeTables.Table4.P3AB
  have h1 : (s - u) * (L : ℂ)
      = ((a + lam : ℝ) : ℂ) + (((s.im - u.im) * L : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_re, Complex.I_re, Complex.I_im, zero_mul, sub_zero, Complex.sub_im]
      rw [hs, hu]; field_simp; ring
    · simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, add_zero]
      ring
  rw [h1]
  congr 1
  push_cast
  ring

end Work.ZeroFreeTables.lam0w
