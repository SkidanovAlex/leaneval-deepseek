import Mathlib
import Submission.Work.EQ.FanSep.centre_numbers
import Submission.Work.EQ.fan_base

set_option maxHeartbeats 1600000

/-! Positivity of the radicand `(P₁ + a/2)² + P₂²` for a point `P` close to an axis centre
`c = -1/2 + 2ℤ`, when `P` also satisfies the semi-projective bound `‖P₂/(P₁ - a/2)‖ ≤ τ`.
This is what keeps the principal square root in `invBranch` on its analytic branch. -/

namespace Work.EQ.FanTri

open Work.EQ Complex

noncomputable section

theorem radicand_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {c : ℝ} {P : ℂ × ℂ} {ρ τ : ℝ}
    (hc : ∃ k : ℤ, c = -1 / 2 + 2 * (k : ℝ)) (hρ0 : 0 ≤ ρ) (hτ0 : 0 ≤ τ)
    (hρg : ρ ≤ (1 - a) / 16) (hτg : τ ≤ eqLam a / 8)
    (hPx : ‖P.1 - (c : ℂ)‖ ≤ ρ) (hPb : P.1 - (a / 2 : ℂ) ≠ 0)
    (hPw : ‖P.2 / (P.1 - (a / 2 : ℂ))‖ ≤ τ) :
    0 < (((P.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + P.2 ^ 2)).re := by
  obtain ⟨k, rfl⟩ := hc
  obtain ⟨hcn1, hcn2⟩ := FanSep.centre_numbers ha0 ha1
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  set X : ℝ := -1 / 2 + 2 * (k : ℝ) with hXdef
  set s : ℝ := |X + a / 2| with hsdef
  have hsg : (1 - a) / 2 ≤ s := by
    have h := (hcn1 k).1
    rw [FanSep.norm_ofReal_add_eq_abs] at h
    rw [hsdef, hXdef]
    linarith
  have hs0 : 0 < s := by linarith
  have hratio : |X - a / 2| * eqLam a ≤ s := by
    have h := hcn2 k
    rw [FanSep.norm_ofReal_sub_eq_abs, FanSep.norm_ofReal_add_eq_abs] at h
    rw [hsdef, hXdef]
    linarith [h]
  have hcd : |X - a / 2| ≤ s / eqLam a := by
    rw [le_div_iff₀ hlam0]; linarith [hratio]
  have hPb' : P.1 - ((a / 2 : ℝ) : ℂ) ≠ 0 := by simpa using hPb
  -- the two coordinate estimates on `P`
  have hPxc : ‖P.1 - (X : ℂ)‖ ≤ ρ := by rw [hXdef]; exact hPx
  have hP1 : ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ ≤ ρ + s / eqLam a := by
    have hsplit : P.1 - ((a / 2 : ℝ) : ℂ)
        = (P.1 - (X : ℂ)) + ((X : ℂ) - ((a / 2 : ℝ) : ℂ)) := by
      rw [hXdef]; ring
    have h1 : ‖(P.1 - (X : ℂ)) + ((X : ℂ) - ((a / 2 : ℝ) : ℂ))‖
        ≤ ‖P.1 - (X : ℂ)‖ + |X - a / 2| := by
      have h1' := norm_add_le (P.1 - (X : ℂ)) ((X : ℂ) - ((a / 2 : ℝ) : ℂ))
      rwa [FanSep.norm_ofReal_sub_eq_abs] at h1'
    rw [hsplit]
    linarith [h1, hPxc]
  have hP2 : ‖P.2‖ ≤ τ * (ρ + s / eqLam a) := by
    have hdecomp : ‖P.2‖ = ‖P.2 / (P.1 - ((a / 2 : ℝ) : ℂ))‖ * ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ := by
      rw [norm_div]; field_simp
    have h4 : ‖P.2 / (P.1 - ((a / 2 : ℝ) : ℂ))‖ ≤ τ := by simpa using hPw
    rw [hdecomp]
    exact mul_le_mul h4 hP1 (norm_nonneg _) hτ0
  have hP2' : ‖P.2‖ ≤ s * (9 / 64) := by
    have h3 : ‖P.2‖ ≤ τ * ρ + τ * (s / eqLam a) := by
      have he : τ * (ρ + s / eqLam a) = τ * ρ + τ * (s / eqLam a) := by ring
      linarith [hP2]
    have hρs : ρ ≤ s / 8 := by linarith [hρg, hsg]
    have ha : τ * ρ ≤ s / 64 := by
      have h1 : τ * ρ ≤ (eqLam a / 8) * ρ := mul_le_mul_of_nonneg_right hτg hρ0
      have h2 : (eqLam a / 8) * ρ ≤ ρ / 8 := by nlinarith [hρ0, hlam1]
      have h4 : ρ / 8 ≤ s / 64 := by linarith
      linarith [h1, h2, h4]
    have hb : τ * (s / eqLam a) ≤ s / 8 := by
      have h1 : τ * (s / eqLam a) ≤ (eqLam a / 8) * (s / eqLam a) :=
        mul_le_mul_of_nonneg_right hτg (by positivity)
      have h2 : (eqLam a / 8) * (s / eqLam a) = s / 8 := by field_simp
      linarith [h1]
    have h5 : s / 64 + s / 8 ≤ s * (9 / 64) := by nlinarith [hs0]
    linarith [h3, ha, hb, h5]
  -- the imaginary part of `P.1`
  have him : |P.1.im| ≤ ρ := by
    have h := Complex.abs_im_le_norm (P.1 - (X : ℂ))
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    linarith [h, hPxc]
  have hredev : |P.1.re - X| ≤ ρ := by
    have h := Complex.abs_re_le_norm (P.1 - (X : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at h
    linarith [h, hPxc]
  -- the real part of the radicand
  have hre : (((P.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + P.2 ^ 2)).re
      = ((P.1 + ((a / 2 : ℝ) : ℂ)).re ^ 2 - (P.1 + ((a / 2 : ℝ) : ℂ)).im ^ 2)
        + (P.2.re ^ 2 - P.2.im ^ 2) := by
    rw [Complex.add_re, pow_two, pow_two, Complex.mul_re, Complex.mul_re]; ring
  have hrez : (P.1 + ((a / 2 : ℝ) : ℂ)).re = X + a / 2 + (P.1.re - X) := by
    simp only [Complex.add_re, Complex.ofReal_re]; rw [hXdef]; ring
  have hreim : (P.1 + ((a / 2 : ℝ) : ℂ)).im = P.1.im := by
    simp only [Complex.add_im, Complex.ofReal_im, add_zero]
  have hAre : (s - ρ) ^ 2 ≤ (P.1 + ((a / 2 : ℝ) : ℂ)).re ^ 2 := by
    rw [hrez]
    have h2 : s - ρ ≤ |X + a / 2 + (P.1.re - X)| := by
      have h4 : |X + a / 2| - |P.1.re - X| ≤ |X + a / 2 + (P.1.re - X)| := by
        have h5 := abs_sub_abs_le_abs_sub (X + a / 2) (-(P.1.re - X))
        rw [abs_neg] at h5
        have h7 : X + a / 2 - -(P.1.re - X) = X + a / 2 + (P.1.re - X) := by ring
        rwa [h7] at h5
      have h6 : |X + a / 2| = s := hsdef.symm
      linarith [h4, hredev, h6]
    have h5 : 0 ≤ s - ρ := by linarith [hρg, hsg]
    calc (s - ρ) ^ 2 ≤ |X + a / 2 + (P.1.re - X)| ^ 2 := pow_le_pow_left₀ h5 h2 2
      _ = (X + a / 2 + (P.1.re - X)) ^ 2 := sq_abs _
  have hBim : (P.1 + ((a / 2 : ℝ) : ℂ)).im ^ 2 ≤ ρ ^ 2 := by
    rw [hreim]
    have h := abs_le.mp him
    nlinarith [h.1, h.2]
  have hCim : P.2.re ^ 2 - P.2.im ^ 2 ≥ -‖P.2‖ ^ 2 := by
    have h4 : P.2.im ^ 2 ≤ ‖P.2‖ ^ 2 := by
      have h5 : |P.2.im| ≤ ‖P.2‖ := Complex.abs_im_le_norm P.2
      nlinarith [abs_nonneg P.2.im, h5, sq_abs P.2.im]
    nlinarith [sq_nonneg P.2.re, h4]
  have hmain : (((P.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + P.2 ^ 2)).re
      ≥ (s - ρ) ^ 2 - ρ ^ 2 - ‖P.2‖ ^ 2 := by
    rw [hre]; linarith [hAre, hBim, hCim]
  have hfinal : (s - ρ) ^ 2 - ρ ^ 2 - ‖P.2‖ ^ 2 > 0 := by
    have h1 : ρ ≤ s / 8 := by linarith [hρg, hsg]
    have h2 : ‖P.2‖ ^ 2 ≤ (s * (9 / 64)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hP2' 2
    nlinarith [h1, h2, hs0]
  linarith [hmain, hfinal]

end

end Work.EQ.FanTri
