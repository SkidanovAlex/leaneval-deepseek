import Mathlib
import Submission.Work.FIArea6Hecke.chiTildeDefs
import Submission.Work.FIArea5.S16Hecke.heckeL_inv_halfPlane
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea5.S16Hecke.splitPrimaryClass
import Submission.Work.FIArea5.S16Hecke.inertPrimaryClass
import Submission.Work.FIArea6Hecke.R.chiTrivLocalPrime

set_option autoImplicit false

namespace Work.FIArea6HeckeV2

open Work.FIArea5.S16Hecke
open Work.FIArea6Hecke

noncomputable section

/-! ### The elementary API of the auxiliary character `χ̃ = χ / (χ ∘ conj)`

These are the three facts needed to feed `χ̃` into the local Hecke theory
(`heckeFp_mul_heckeGp`, `heckeLam_localRec`, `heckeLam_prime_norm_le_two`). -/

/-- Conjugation preserves the units modulo `4d`. -/
lemma isUnitMod4d_star' {d : ℕ} {z : GaussianInt} (hz : IsUnitMod4d d z) :
    IsUnitMod4d d (star z) := by
  obtain ⟨w, hw⟩ := hz
  obtain ⟨c, hc⟩ := hw
  refine ⟨star w, star c, ?_⟩
  have h : star (z * w - 1) = star z * star w - 1 := by simp
  rw [← h, hc]
  simp

/-- A strict character modulo `4d` has modulus `1` on the units modulo `4d`. -/
lemma norm_chi_eq_one_of_isUnitMod4d' {d : ℕ} {chi : GaussianInt → ℂ}
    (hchi : IsCharMod4dStrict d chi) {z : GaussianInt} (hz : IsUnitMod4d d z) :
    ‖chi z‖ = 1 := by
  obtain ⟨hchar, -⟩ := hchi
  obtain ⟨h1, hmul, hbd, hper, -⟩ := hchar
  obtain ⟨w, hw⟩ := hz
  have hzw : chi (z * w) = chi 1 := hper (z * w) 1 (by simpa using hw)
  rw [h1, hmul] at hzw
  have hnorm : ‖chi z‖ * ‖chi w‖ = 1 := by rw [← norm_mul, hzw, norm_one]
  have hzle : ‖chi z‖ ≤ 1 := hbd z
  have hwle : ‖chi w‖ ≤ 1 := hbd w
  have hznn : 0 ≤ ‖chi z‖ := norm_nonneg _
  have hwnn : 0 ≤ ‖chi w‖ := norm_nonneg _
  nlinarith [hnorm, hzle, hwle, hznn, hwnn]

lemma chiTilde_one' {d : ℕ} {chi : GaussianInt → ℂ} (hchi : IsCharMod4dStrict d chi) :
    chiTilde chi 1 = 1 := by
  obtain ⟨⟨h1, -, -, -, -⟩, -⟩ := hchi
  simp [chiTilde, h1]

lemma chiTilde_mul' {d : ℕ} {chi : GaussianInt → ℂ} (hchi : IsCharMod4dStrict d chi) :
    ∀ z w : GaussianInt, chiTilde chi (z * w) = chiTilde chi z * chiTilde chi w := by
  obtain ⟨⟨-, hmul, -, -, -⟩, -⟩ := hchi
  intro z w
  simp only [chiTilde]
  rw [star_mul, hmul, hmul]
  ring

lemma chiTilde_norm_le_one' {d : ℕ} {chi : GaussianInt → ℂ} (hchi : IsCharMod4dStrict d chi) :
    ∀ z : GaussianInt, ‖chiTilde chi z‖ ≤ 1 := by
  intro z
  by_cases hz : IsUnitMod4d d z
  · have h1 : ‖chi z‖ = 1 := norm_chi_eq_one_of_isUnitMod4d' hchi hz
    have h2 : ‖chi (star z)‖ = 1 := norm_chi_eq_one_of_isUnitMod4d' hchi (isUnitMod4d_star' hz)
    rw [chiTilde, norm_div, h1, h2, div_one]
  · rw [chiTilde, hchi.2 z hz, zero_div]
    simp

/-! ### The `heckeGp` normal form -/

/-- `heckeGp` at the prime `⟨p, hp⟩` written with `p : ℕ` (the coercion is definitional). -/
lemma heckeGp_natPrime (chi : GaussianInt → ℂ) (k : ℤ) (p : ℕ) (hp : p.Prime) (s : ℂ) :
    heckeGp chi k ⟨p, hp⟩ s
      = 1 - heckeLam chi k p * (((p : ℕ) : ℂ) ^ (-s))
          + ((heckeLam chi k p) ^ 2 - heckeLam chi k (p ^ 2))
              * ((((p : ℕ) : ℂ) ^ (-s)) ^ 2) := rfl

/-! ### The analytic core estimate -/

/-- For `‖A‖ ≤ 2`, `‖C‖ ≤ 1` and `0 ≤ t ≤ 1/3`, the modulus of `1 - A t + C t²` is bounded
below sharply enough that its negative logarithm is at most `A.re·t + 26t²`.  This is the
second-order Taylor bound `-log|1-z| = Re z + O(|z|²)` for `z = At - Ct²` in the regime
`|z| ≤ 2t + t² ≤ 7/9 < 1`, realised through the real part instead of the complex logarithm. -/
lemma log_norm_core (A C : ℂ) (hA : ‖A‖ ≤ 2) (hC : ‖C‖ ≤ 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / 3) :
    -Real.log ‖1 - A * (t : ℂ) + C * (t : ℂ) ^ 2‖ ≤ A.re * t + 26 * t ^ 2 := by
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  have ht7 : (2 + t) * t ≤ 7 / 9 := by nlinarith
  set y : ℝ := A.re * t - C.re * t ^ 2 with hy
  have hyb : |y| ≤ (2 + t) * t := by
    have h1 : |A.re| ≤ 2 := le_trans (Complex.abs_re_le_norm A) hA
    have h2 : |C.re| ≤ 1 := le_trans (Complex.abs_re_le_norm C) hC
    have hm1 : |A.re| * t ≤ 2 * t := mul_le_mul_of_nonneg_right h1 ht0
    have hm2 : |C.re| * t ^ 2 ≤ 1 * t ^ 2 := mul_le_mul_of_nonneg_right h2 ht2
    have h3 : |y| ≤ |A.re| * t + |C.re| * t ^ 2 := by
      rw [hy]
      refine le_trans (abs_sub _ _) ?_
      rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg ht2]
    nlinarith [h3, hm1, hm2]
  have hy7 : y ≤ 7 / 9 := le_trans (le_abs_self y) (le_trans hyb ht7)
  have h1y : 0 < 1 - y := by linarith
  set u : ℂ := A * (t : ℂ) - C * (t : ℂ) ^ 2 with hu
  have hure : u.re = y := by
    have e1 : (A * (t : ℂ)).re = A.re * t := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
    have e2 : (C * (t : ℂ) ^ 2).re = C.re * t ^ 2 := by
      have h2re : ((t : ℂ) ^ 2).re = t ^ 2 := by
        rw [← Complex.ofReal_pow]; exact Complex.ofReal_re _
      have h2im : ((t : ℂ) ^ 2).im = 0 := by
        rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _
      rw [Complex.mul_re, h2re, h2im]; ring
    rw [hu, hy, Complex.sub_re, e1, e2]
  have heq : 1 - A * (t : ℂ) + C * (t : ℂ) ^ 2 = 1 - u := by rw [hu]; ring
  have hkey : 1 - y ≤ ‖1 - u‖ := by
    have h := Complex.abs_re_le_norm (1 - u)
    rw [Complex.sub_re, Complex.one_re, hure] at h
    rwa [abs_of_pos h1y] at h
  have hlog : Real.log (1 - y) ≤ Real.log ‖1 - u‖ := Real.log_le_log h1y hkey
  have hlogbound : -Real.log (1 - y) ≤ y + (9 / 2) * y ^ 2 := by
    have hpos : 0 < 1 / (1 - y) := by rw [one_div]; exact inv_pos.mpr h1y
    have h := Real.log_le_sub_one_of_pos hpos
    rw [one_div, Real.log_inv] at h
    have h2 : (1 - y)⁻¹ - 1 = y / (1 - y) := by field_simp; ring
    rw [h2] at h
    have h4 : y / (1 - y) = y + y ^ 2 / (1 - y) := by field_simp; ring
    have h5 : y ^ 2 / (1 - y) ≤ y ^ 2 / (2 / 9) :=
      div_le_div_of_nonneg_left (sq_nonneg y) (by norm_num) (by linarith)
    have h6 : y ^ 2 / (2 / 9) = (9 / 2) * y ^ 2 := by ring
    rw [h6] at h5
    rw [h4] at h
    linarith
  have hy2 : y ^ 2 ≤ (49 / 9) * t ^ 2 := by
    have hb : y ^ 2 ≤ ((2 + t) * t) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (by positivity : 0 ≤ (2 + t) * t)]
      exact hyb
    have hc : (2 + t) ^ 2 ≤ (7 / 3) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 + t),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 3)]
      linarith
    calc y ^ 2 ≤ ((2 + t) * t) ^ 2 := hb
      _ = (2 + t) ^ 2 * t ^ 2 := by ring
      _ ≤ (7 / 3) ^ 2 * t ^ 2 := mul_le_mul_of_nonneg_right hc ht2
      _ = (49 / 9) * t ^ 2 := by norm_num
  have hyt : y ≤ A.re * t + t ^ 2 := by
    have hcr : C.re * t ^ 2 ≥ -t ^ 2 := by
      have h : |C.re| ≤ 1 := le_trans (Complex.abs_re_le_norm C) hC
      nlinarith [neg_abs_le C.re, ht2]
    rw [hy]; linarith
  have hA2 : A.re ≤ 2 := le_trans (Complex.re_le_norm A) hA
  have hfin : y + (9 / 2) * y ^ 2 ≤ A.re * t + 26 * t ^ 2 := by
    have h9 : (9 / 2) * y ^ 2 ≤ (9 / 2) * ((49 / 9) * t ^ 2) :=
      mul_le_mul_of_nonneg_left hy2 (by norm_num)
    nlinarith [hyt, h9, ht2, hA2]
  rw [heq]
  linarith [hlog, hlogbound, hfin]

/-! ### The target -/

theorem exists_log_heckeFp_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ}, 1 ≤ d → ∀ {chi : GaussianInt → ℂ},
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi → ∀ (m : ℤ) {σ : ℝ}, 1 < σ →
      ∀ (p : ℕ) (hp : p.Prime),
      Real.log ‖Work.FIArea5.S16Hecke.heckeFp (Work.FIArea6Hecke.chiTilde chi) (2 * m)
          ⟨p, hp⟩ (σ : ℂ)‖
        ≤ (Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.chiTilde chi) (2 * m) p).re * (p : ℝ) ^ (-σ)
            + C * (p : ℝ) ^ (-2 * σ) := by
  refine ⟨26, by norm_num, ?_⟩
  intro d hd chi hchi m σ hσ p hp
  have h1 : chiTilde chi 1 = 1 := chiTilde_one' hchi
  have hmul : ∀ z w : GaussianInt, chiTilde chi (z * w) = chiTilde chi z * chiTilde chi w :=
    chiTilde_mul' hchi
  have hb : ∀ z : GaussianInt, ‖chiTilde chi z‖ ≤ 1 := chiTilde_norm_le_one' hchi
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hp_lt : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  set t : ℝ := (p : ℝ) ^ (-σ) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hX : (((p : ℕ) : ℂ)) ^ (-(σ : ℂ)) = (t : ℂ) := by
    rw [ht, ← Complex.ofReal_natCast p, ← Complex.ofReal_neg]
    exact (Complex.ofReal_cpow (Nat.cast_nonneg p) (-σ)).symm
  by_cases hp2 : p = 2
  · subst hp2
    have hlam2 : heckeLam (chiTilde chi) (2 * m) 2 = 0 :=
      heckeLam_prime_eq_zero_of_ne_one_mod_four (p := 2) (by norm_num) (by norm_num)
    have hlam4 : heckeLam (chiTilde chi) (2 * m) 4 = 0 :=
      heckeLam_even (chiTilde chi) (2 * m) (by norm_num)
    have hG : heckeGp (chiTilde chi) (2 * m) ⟨2, hp⟩ (σ : ℂ) = 1 := by
      rw [heckeGp_natPrime, hlam2, show (2 : ℕ) ^ 2 = 4 by norm_num, hlam4]
      ring
    have hF : heckeFp (chiTilde chi) (2 * m) ⟨2, hp⟩ (σ : ℂ) = 1 := by
      have h := heckeFp_mul_heckeGp (chiTilde chi) (2 * m) ⟨2, hp⟩ (σ : ℂ) hmul h1 hb
        (by simpa using hσ0)
      rw [hG, mul_one] at h
      exact h
    rw [hF, norm_one, Real.log_one, hlam2, Complex.zero_re, zero_mul, zero_add]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)
  · have hp3 : 3 ≤ p := by
      have h2 := hp.two_le
      omega
    have ht13 : t ≤ 1 / 3 := by
      have hle : t ≤ (p : ℝ) ^ (-1 : ℝ) := by
        rw [ht]
        exact (Real.rpow_le_rpow_left_iff hp_lt).mpr (by linarith)
      rw [Real.rpow_neg_one, inv_eq_one_div] at hle
      have h3' : 1 / (p : ℝ) ≤ 1 / 3 :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) (by exact_mod_cast hp3)
      linarith
    have ha2 : ‖heckeLam (chiTilde chi) (2 * m) p‖ ≤ 2 := by
      by_cases h4 : p % 4 = 1
      · exact heckeLam_prime_norm_le_two hp h4 hb
      · rw [heckeLam_prime_eq_zero_of_ne_one_mod_four (p := p) hp h4, norm_zero]
        norm_num
    have hc1 : ‖(heckeLam (chiTilde chi) (2 * m) p) ^ 2
        - heckeLam (chiTilde chi) (2 * m) (p ^ 2)‖ ≤ 1 :=
      (heckeLam_localRec (chiTilde chi) (2 * m) p hp hmul hb).2
    have hG : heckeGp (chiTilde chi) (2 * m) ⟨p, hp⟩ (σ : ℂ)
        = 1 - heckeLam (chiTilde chi) (2 * m) p * (t : ℂ)
            + ((heckeLam (chiTilde chi) (2 * m) p) ^ 2
                - heckeLam (chiTilde chi) (2 * m) (p ^ 2)) * (t : ℂ) ^ 2 := by
      rw [heckeGp_natPrime, hX]
    have hcore := log_norm_core (heckeLam (chiTilde chi) (2 * m) p)
      ((heckeLam (chiTilde chi) (2 * m) p) ^ 2 - heckeLam (chiTilde chi) (2 * m) (p ^ 2))
      ha2 hc1 ht0 ht13
    have hFG := heckeFp_mul_heckeGp (chiTilde chi) (2 * m) ⟨p, hp⟩ (σ : ℂ) hmul h1 hb
      (by simpa using hσ0)
    have hnorm : ‖heckeFp (chiTilde chi) (2 * m) ⟨p, hp⟩ (σ : ℂ)‖
        * ‖heckeGp (chiTilde chi) (2 * m) ⟨p, hp⟩ (σ : ℂ)‖ = 1 := by
      rw [← norm_mul, hFG, norm_one]
    have hGne : ‖heckeGp (chiTilde chi) (2 * m) ⟨p, hp⟩ (σ : ℂ)‖ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hnorm
      exact one_ne_zero hnorm.symm
    have hFne : ‖heckeFp (chiTilde chi) (2 * m) ⟨p, hp⟩ (σ : ℂ)‖ ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hnorm
      exact one_ne_zero hnorm.symm
    have hlogsplit : Real.log ‖heckeFp (chiTilde chi) (2 * m) ⟨p, hp⟩ (σ : ℂ)‖
        = -Real.log ‖heckeGp (chiTilde chi) (2 * m) ⟨p, hp⟩ (σ : ℂ)‖ := by
      have h := Real.log_mul hFne hGne
      rw [hnorm, Real.log_one] at h
      linarith
    rw [hlogsplit, hG]
    refine le_trans hcore ?_
    have ht2eq : t ^ 2 = (p : ℝ) ^ (-2 * σ) := by
      rw [ht, sq, ← Real.rpow_add (Nat.cast_pos.mpr hp.pos)]
      congr 1
      ring
    rw [ht2eq, ht]

end

end Work.FIArea6HeckeV2
