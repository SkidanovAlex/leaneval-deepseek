import Mathlib
import Submission.Work.Resample.buDefs
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auPiBound
import Submission.Work.Resample.buNIdent
import Submission.Work.Resample.buZClose
import Submission.Work.Resample.notGuardBound
import Submission.Work.Resample.auHExpClose
import Submission.Work.Resample.tdivScale

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- `auPi p = (Work.Fx.uval (auPrec p) : ℤ)` is nonnegative: it is the flooring division of the
nonnegative integer `Nval p = Dval p · 2^(2p+1) + 2^(qq p − 1)` by the positive power `2^(qq p)`. -/
private lemma auPi_nonneg (p : ℕ) : (0 : ℤ) ≤ auPi p := by
  rw [auPi, Work.Fx.uval]
  apply Int.fdiv_nonneg
  · rw [Work.Fx.Nval]
    exact add_nonneg (mul_nonneg (Int.natCast_nonneg _) (by positivity)) (by positivity)
  · positivity

lemma exp_neg_sub_le (x y : ℝ) (hy : 0 ≤ y) (hyx : y ≤ x) :
    Real.exp (-y) - Real.exp (-x) ≤ x - y := by
  have h1 : Real.exp (-x) = Real.exp (-y) * Real.exp (-(x - y)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : 1 - Real.exp (-(x - y)) ≤ x - y := by
    have := Real.add_one_le_exp (-(x - y))
    linarith
  have h5 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h6 : 0 ≤ 1 - Real.exp (-(x - y)) := by
    have h := Real.exp_le_one_iff.mpr (show -(x - y) ≤ 0 by linarith)
    linarith
  calc Real.exp (-y) - Real.exp (-x)
      = Real.exp (-y) * (1 - Real.exp (-(x - y))) := by rw [h1]; ring
    _ ≤ 1 * (x - y) := mul_le_mul h5 h3 h6 (by norm_num)
    _ = x - y := one_mul _

lemma exp_neg_lipschitz (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  rcases le_total y x with hle | hle
  · have h1 : Real.exp (-y) - Real.exp (-x) ≤ x - y := exp_neg_sub_le x y hy hle
    have h2 : Real.exp (-x) - Real.exp (-y) ≤ 0 := by
      have : Real.exp (-x) ≤ Real.exp (-y) := Real.exp_le_exp.mpr (by linarith)
      linarith
    rw [abs_of_nonpos h2, abs_of_nonneg (by linarith : (0:ℝ) ≤ x - y)]
    linarith
  · have h1 : Real.exp (-x) - Real.exp (-y) ≤ y - x := exp_neg_sub_le y x hx hle
    have h2 : (0:ℝ) ≤ Real.exp (-x) - Real.exp (-y) := by
      have : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
      linarith
    rw [abs_of_nonneg h2, abs_of_nonpos (by linarith : x - y ≤ 0)]
    linarith

lemma guardTrueBoundW (p : ℕ) (hp : 100 ≤ p) (Z : ℤ) (u : ℝ) (hZ0 : 0 ≤ Z) (hu0 : 0 ≤ u)
    (hZu : |(Z : ℝ) - (2 : ℝ) ^ auPrec p * u| ≤ 1 + u / 3)
    (hguard : (Z : ℝ) ≤ ((p : ℝ) + 10) * (2 : ℝ) ^ auPrec p) :
    |Real.exp (-((Z : ℝ) / (2 : ℝ) ^ auPrec p)) - Real.exp (-u)| ≤ 1 / (2 : ℝ) ^ p := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (2:ℝ)^(auPrec p) := ⟨_, rfl⟩
  have hApos : 0 < A := by rw [hA]; positivity
  have hAge : (2:ℝ) ≤ A := by
    rw [hA]
    have hp1 : (1:ℕ) ≤ auPrec p := by simp only [auPrec]; omega
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hp1
  have hZuA : |(Z:ℝ) - A * u| ≤ 1 + u/3 := by rw [hA]; exact hZu
  have hgA : (Z:ℝ) ≤ ((p:ℝ) + 10) * A := by rw [hA]; exact hguard
  have hpR : (0:ℝ) ≤ (p:ℝ) := by positivity
  -- step 1: `u ≤ 2p+21`
  have hu_le : u ≤ 2*(p:ℝ) + 21 := by
    have h1 : -(1 + u/3) ≤ (Z:ℝ) - A*u := (abs_le.mp hZuA).1
    have h3 : A*u ≤ ((p:ℝ) + 10) * A + 1 + u/3 := by linarith
    have h5 : A/2 ≤ A - 1/3 := by linarith
    have h4 : u * (A/2) ≤ ((p:ℝ) + 10) * A + 1 := by nlinarith [hu0, hApos, h5, h3]
    have h6 : u ≤ (2 * (((p:ℝ) + 10) * A + 1)) / A := by
      rw [le_div_iff₀ hApos, mul_comm]
      linarith [h4]
    have h7 : (2 * (((p:ℝ) + 10) * A + 1)) / A = 2*(p:ℝ) + 20 + 2/A := by
      field_simp
      ring
    have h8 : 2/A ≤ 1 := by
      rw [div_le_one hApos]; linarith
    linarith [h6, h7, h8]
  -- step 2: `|Z/A - u| ≤ (2p+24)/(3A)`
  have hd : |(Z:ℝ)/A - u| ≤ (1 + u/3)/A := by
    have hsplit : (Z:ℝ)/A - u = ((Z:ℝ) - A*u)/A := by field_simp
    rw [hsplit, abs_div, abs_of_pos hApos]
    exact div_le_div_of_nonneg_right hZuA (le_of_lt hApos)
  have hd2 : |(Z:ℝ)/A - u| ≤ (2*(p:ℝ) + 24) / (3*A) := by
    refine le_trans hd ?_
    have hnum : 1 + u/3 ≤ (2*(p:ℝ) + 24)/3 := by linarith [hu_le]
    calc (1 + u/3)/A ≤ ((2*(p:ℝ) + 24)/3)/A := div_le_div_of_nonneg_right hnum (le_of_lt hApos)
      _ = (2*(p:ℝ) + 24)/(3*A) := by rw [div_div]
  -- step 3: final arithmetic
  have hnat : 2*p + 24 ≤ 3 * 2^(2*p+100) := by
    have h1 : p + 1 ≤ 2^p := by
      have := Nat.lt_two_pow_self (n := p); omega
    have h2 : 2^p ≤ 2^(2*p+100) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2*p + 24 ≤ 3*(p+1) := by omega
      _ ≤ 3 * 2^p := by omega
      _ ≤ 3 * 2^(2*p+100) := by omega
  have hreal : 2*(p:ℝ) + 24 ≤ 3 * (2:ℝ)^(2*p+100) := by
    exact_mod_cast hnat
  have hfin : (2*(p:ℝ) + 24) / (3*A) ≤ 1 / (2:ℝ)^p := by
    have hpow : A = (2:ℝ)^p * (2:ℝ)^(2*p+100) := by
      rw [hA, show auPrec p = p + (2*p+100) by simp only [auPrec]; omega, pow_add]
    have hkey : (2*(p:ℝ) + 24)/(3*A) = ((2*(p:ℝ) + 24)/(3*(2:ℝ)^(2*p+100)))/(2:ℝ)^p := by
      rw [hpow]; field_simp; try ring
    rw [hkey, div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < (2:ℝ)^p)]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 3*(2:ℝ)^(2*p+100))]
    simpa using hreal
  calc |Real.exp (-((Z:ℝ)/(2:ℝ)^(auPrec p))) - Real.exp (-u)|
      = |Real.exp (-((Z:ℝ)/A)) - Real.exp (-u)| := by rw [hA]
    _ ≤ |(Z:ℝ)/A - u| := exp_neg_lipschitz ((Z:ℝ)/A) u (by positivity) hu0
    _ ≤ (2*(p:ℝ) + 24) / (3*A) := hd2
    _ ≤ 1 / (2:ℝ)^p := hfin

/-- The tabulated weight `buWt p α s t ℓ h` (fixed-point Horner recursion `auH` with the same guard
as `auWt`, `auDefs.lean`) approximates `2^p · egW s t α ℓ h` to within `4·2^{-p}`; the true error is
far smaller, since the working precision `auPrec p = 3p + 100` is much larger than `p`.

NOTE (for the prover): `egW s t α ℓ h = exp (-(π · (α² · buN s t ℓ h) / s²))` since
`buBeta s t n = β_n · s`; with `Z = buZ p α s t ℓ h = ⌊2^P π α² N / s²⌋` the true value is
`exp(-Z/2^P)` up to (i) the floor error (relative `≤ (π α² N/s²)·2^{-P}`), (ii) `auPi p ≈ 2^P π`,
(iii) the error of the truncated Taylor recursion `auH` (this is the same analysis as for the `Ã`
weight `auWt`), and (iv) the final `tdiv` by `2^{P-p}` (loss `< 1` in units of `2^p`). Everything is
`O(p²·2^{-2p})`, hence `≤ 4·2^{-p}`. The guarded case (exponent `> p+10`) gives `buWt = 0` and
`egW ≤ e^{-(p+10)} ≤ 4·2^{-p}`; `h ≠ 0` with `0 < s < t` gives `0 ≤ N`, so `-Z ≤ 0` has the right
sign for the recursion. -/
theorem buWtAcc (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (ℓ h : ℤ) (hh : h ≠ 0) :
    |((Work.Resample.buWt p α s t ℓ h : ℝ) / (2 : ℝ) ^ p - Work.Resample.egW s t α ℓ h)|
      ≤ 4 / (2 : ℝ) ^ p := by
  have hs0 : (0 : ℕ) < s := by omega
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs0
  obtain ⟨hNident, hNnn⟩ := buNIdent s t hs0 hst ℓ h hh
  have hNnnR : (0 : ℝ) ≤ (buN s t ℓ h : ℝ) := by exact_mod_cast hNnn
  have hPi0Z : (0 : ℤ) ≤ auPi p := auPi_nonneg p
  have hPi1 := auPiBound p hp
  obtain ⟨hZ0raw, hZc⟩ := buZClose p α s t hp hs ℓ h hNnn hPi0Z hPi1
  -- the fixed-point exponent `Z`, the true exponent `U` and its `π`-free part `W`
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℤ, Z = buZ p α s t ℓ h := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = (α : ℝ) ^ 2 * (buN s t ℓ h : ℝ) / (s : ℝ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = Real.pi * W := ⟨_, rfl⟩
  have hZ0 : 0 ≤ Z := by rw [hZdef]; exact hZ0raw
  have hWnn : 0 ≤ W := by
    rw [hWdef]
    exact div_nonneg (mul_nonneg (sq_nonneg _) hNnnR) (sq_nonneg _)
  have hUnn : 0 ≤ U := by rw [hUdef]; exact mul_nonneg (le_of_lt Real.pi_pos) hWnn
  have hWU : W ≤ U / 3 := by
    have h3 : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
    have := mul_le_mul_of_nonneg_right h3 hWnn
    rw [hUdef]
    linarith
  have hZcU : |(Z : ℝ) - (2 : ℝ) ^ (auPrec p) * U| ≤ 1 + W := by
    rw [hZdef, hUdef, hWdef]
    exact hZc
  have hZu : |(Z : ℝ) - (2 : ℝ) ^ (auPrec p) * U| ≤ 1 + U / 3 := by
    linarith [hZcU, hWU, abs_nonneg ((Z : ℝ) - (2 : ℝ) ^ (auPrec p) * U)]
  have hW_eq : W = (α : ℝ) ^ 2 * (((t : ℝ) * (h : ℝ) / s + Work.ResMath.betaI s t ℓ) ^ 2
      - (Work.ResMath.betaI s t (ℓ + h)) ^ 2) := by
    rw [hWdef, hNident]
    have hs2 : (s : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
  have hegW : egW s t α ℓ h = Real.exp (-U) := by
    have harg : -(Real.pi * (α : ℝ) ^ 2 * (((t : ℝ) * (h : ℝ) / s + Work.ResMath.betaI s t ℓ) ^ 2
        - (Work.ResMath.betaI s t (ℓ + h)) ^ 2)) = -U := by
      rw [hUdef, hW_eq]
      ring
    rw [egW, harg]
  by_cases hg : Z ≤ ((p + 10 : ℕ) : ℤ) * (2 : ℤ) ^ (auPrec p)
  · -- guarded case: the recursion runs, and all four error terms are `≤ 2^{-p}`
    have hZle : (Z : ℝ) ≤ ((p : ℝ) + 10) * (2 : ℝ) ^ (auPrec p) := by
      have h1 : (Z : ℝ) ≤ ((((p + 10 : ℕ) : ℤ) * (2 : ℤ) ^ (auPrec p) : ℤ) : ℝ) := by
        exact_mod_cast hg
      push_cast at h1
      linarith [h1]
    have hbu : buWt p α s t ℓ h
        = Int.tdiv (auH p (-Z) (auNstep p)) ((2 : ℤ) ^ (auPrec p - p)) := by
      rw [buWt, ← hZdef, if_pos hg]
    have h1 := tdivScale p (auH p (-Z) (auNstep p))
    have h2 := auHExpClose p hp Z hZ0 hZle
    have h3 := guardTrueBoundW p hp Z U hZ0 hUnn hZu hZle
    have hsum : 1 / (2 : ℝ) ^ p + 2 / (2 : ℝ) ^ p + 1 / (2 : ℝ) ^ p = 4 / (2 : ℝ) ^ p := by ring
    rw [hbu, hegW]
    have htri1 := abs_sub_le
      (((Int.tdiv (auH p (-Z) (auNstep p)) ((2 : ℤ) ^ (auPrec p - p)) : ℤ) : ℝ) / (2 : ℝ) ^ p)
      (((auH p (-Z) (auNstep p) : ℤ) : ℝ) / (2 : ℝ) ^ (auPrec p))
      (Real.exp (-U))
    have htri2 := abs_sub_le
      (((auH p (-Z) (auNstep p) : ℤ) : ℝ) / (2 : ℝ) ^ (auPrec p))
      (Real.exp (-((Z : ℝ) / (2 : ℝ) ^ (auPrec p)))) (Real.exp (-U))
    linarith [htri1, htri2, h1, h2, h3, hsum]
  · -- guarded case fails: the weight is zero and the true weight is far below `4·2^{-p}`
    have hbu : buWt p α s t ℓ h = 0 := by rw [buWt, ← hZdef, if_neg hg]
    have hgt : ((p : ℝ) + 10) * (2 : ℝ) ^ (auPrec p) < (Z : ℝ) := by
      have h := not_le.mp hg
      have h1 : ((((p + 10 : ℕ) : ℤ) * (2 : ℤ) ^ (auPrec p) : ℤ) : ℝ) < (Z : ℝ) := by
        exact_mod_cast h
      push_cast at h1
      linarith [h1]
    have hle := notGuardBound p hp Z U hZ0 hUnn hZu hgt
    rw [hbu, hegW]
    simpa only [Int.cast_zero, zero_div, zero_sub, abs_neg,
      abs_of_nonneg (Real.exp_pos (-U)).le] using hle

end Work.Resample
