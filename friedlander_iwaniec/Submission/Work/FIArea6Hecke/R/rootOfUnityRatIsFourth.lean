import Mathlib
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs

namespace Work.FIArea6Hecke.R

/-- **Twice the real part of a rational root of unity is an integer.**

If `ζ : ℂ` is a root of unity (`ζ ^ m = 1` with `m > 0`) and both coordinates of `ζ` are rational,
then `2 * ζ.re` is an integer.  The reason is that `ζ` and its conjugate `starRingEnd ℂ ζ` are
algebraic integers (they are roots of `X^m - 1`), hence so is their sum `ζ + conj ζ = 2 ζ.re`, which
is a *rational* algebraic integer and therefore an integer.

This is used for `ζ = ξ` and for `ζ = -I * ξ`, whose real part is `ξ.im`; together the two
applications show that both `2 ξ.re` and `2 ξ.im` are integers. -/
theorem two_re_isInt_of_rootOfUnity (ζ : ℂ) (c d : ℚ) (hre : ζ.re = (c : ℝ)) (him : ζ.im = (d : ℝ))
    (m : ℕ) (hm : 0 < m) (h : ζ ^ m = 1) : ∃ k : ℤ, (k : ℚ) = 2 * c := by
  -- `ζ` is integral over `ℤ`.
  have hI : IsIntegral ℤ ζ := IsIntegral.of_pow hm (by rw [h]; exact isIntegral_one)
  -- so is its complex conjugate `starRingEnd ℂ ζ`.
  have hIc : IsIntegral ℤ (starRingEnd ℂ ζ) :=
    IsIntegral.of_pow hm (by rw [← map_pow, h, map_one]; exact isIntegral_one)
  -- hence their sum, which is `2 * c`, is integral over `ℤ`.
  have hsum : IsIntegral ℤ (ζ + starRingEnd ℂ ζ) := hI.add hIc
  have h2c : ζ + starRingEnd ℂ ζ = ((2 * c : ℚ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.add_re, Complex.conj_re, hre]
      have : ((2 * c : ℚ) : ℂ).re = ((2 : ℝ) * c) := by norm_num [Complex.ofReal_re]
      rw [this]; ring
    · rw [Complex.add_im, Complex.conj_im, him]
      have : ((2 * c : ℚ) : ℂ).im = 0 := by norm_num [Complex.ofReal_im]
      rw [this]; ring
  rw [h2c] at hsum
  -- `2 * c` is a rational algebraic integer, so it is an ordinary integer.
  have hq : IsIntegral ℤ (2 * c : ℚ) := IsIntegral.ratCast_iff.mp hsum
  obtain ⟨k, hk⟩ := (hq.exists_int_iff_exists_rat).mp ⟨2 * c, rfl⟩
  exact ⟨k, hk.symm⟩

/-- A root of unity in `ℂ` all of whose coordinates are rational is one of `1, -1, i, -i`
(the roots of unity in `ℚ(i)` are the fourth roots of unity). -/
theorem rootOfUnityRatIsFourth (ξ : ℂ) (a b : ℚ) (hre : ξ.re = (a : ℝ)) (him : ξ.im = (b : ℝ))
    (n : ℕ) (hn : 0 < n) (h : ξ ^ n = 1) :
    ξ = 1 ∨ ξ = -1 ∨ ξ = Complex.I ∨ ξ = -Complex.I := by
  -- `ξ` lies on the unit circle, so `a^2 + b^2 = 1`.
  have hnorm : Complex.normSq ξ = 1 := by
    have hp : (Complex.normSq ξ) ^ n = 1 := by
      have := congrArg Complex.normSq h
      simpa using this
    exact (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg ξ) (Nat.pos_iff_ne_zero.mp hn)).mp hp
  have hsq : a ^ 2 + b ^ 2 = 1 := by
    have h' : (a : ℝ) * (a : ℝ) + (b : ℝ) * (b : ℝ) = 1 := by
      have := Complex.normSq_apply ξ
      rw [hnorm, hre, him] at this
      linarith [this]
    have : ((a ^ 2 + b ^ 2 : ℚ) : ℝ) = 1 := by push_cast; linarith [h']
    exact_mod_cast this
  -- `2 a` and `2 b` are integers: apply the previous lemma to `ξ` and to `-I * ξ`.
  obtain ⟨A, hA⟩ := two_re_isInt_of_rootOfUnity ξ a b hre him n hn h
  have hb_re : (-Complex.I * ξ).re = (b : ℝ) := by rw [Complex.mul_re]; simp [hre, him]
  have hb_im : (-Complex.I * ξ).im = ((-a : ℚ) : ℝ) := by rw [Complex.mul_im]; simp [hre, him]
  have h4 : (-Complex.I * ξ) ^ (4 * n) = 1 := by
    rw [mul_pow]
    have hI4 : (-Complex.I) ^ (4 * n) = 1 := by
      rw [pow_mul]; norm_num [Complex.ext_iff, Complex.I_mul_I]
    have hξ4 : ξ ^ (4 * n) = 1 := by rw [mul_comm 4 n, pow_mul, h, one_pow]
    rw [hI4, hξ4, one_mul]
  obtain ⟨B, hB⟩ :=
    two_re_isInt_of_rootOfUnity (-Complex.I * ξ) b (-a) hb_re hb_im (4 * n) (by positivity) h4
  -- Thus `A = 2a`, `B = 2b` are integers with `A^2 + B^2 = 4`.
  have hAB : A ^ 2 + B ^ 2 = 4 := by
    have : ((A ^ 2 + B ^ 2 : ℤ) : ℚ) = 4 := by push_cast [hA, hB]; nlinarith [hsq]
    exact_mod_cast this
  have hξeq : ξ = (a : ℝ) + (b : ℝ) * Complex.I := by rw [← Complex.re_add_im ξ, hre, him]
  -- Bounding `A` and `B` and enumerating leaves only the four expected pairs.
  have hA2 : A ^ 2 ≤ 4 := by nlinarith [sq_nonneg B]
  have hAub : A ≤ 2 := by by_contra hc; push Not at hc; nlinarith [sq_nonneg (A - 3)]
  have hAlb : -2 ≤ A := by by_contra hc; push Not at hc; nlinarith [sq_nonneg (A + 3)]
  have hBub : B ≤ 2 := by by_contra hc; push Not at hc; nlinarith [sq_nonneg (B - 3)]
  have hBlb : -2 ≤ B := by by_contra hc; push Not at hc; nlinarith [sq_nonneg (B + 3)]
  have key2 : (A = 2 ∧ B = 0) ∨ (A = -2 ∧ B = 0) ∨ (A = 0 ∧ B = 2) ∨ (A = 0 ∧ B = -2) := by
    interval_cases A <;> interval_cases B <;> omega
  rcases key2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    have ha : a = 1 := by norm_num at hA; linarith
    have hb0 : b = 0 := by norm_num at hB; linarith
    rw [hξeq, ha, hb0]; norm_num
  · right; left
    have ha : a = -1 := by norm_num at hA; linarith
    have hb0 : b = 0 := by norm_num at hB; linarith
    rw [hξeq, ha, hb0]; norm_num
  · right; right; left
    have ha : a = 0 := by norm_num at hA; linarith
    have hb1 : b = 1 := by norm_num at hB; linarith
    rw [hξeq, ha, hb1]; norm_num
  · right; right; right
    have ha : a = 0 := by norm_num at hA; linarith
    have hb1 : b = -1 := by norm_num at hB; linarith
    rw [hξeq, ha, hb1]; norm_num

end Work.FIArea6Hecke.R
