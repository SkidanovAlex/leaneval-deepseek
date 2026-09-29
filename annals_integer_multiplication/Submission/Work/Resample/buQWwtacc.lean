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

/-!
# `Work.Resample.buQWwtacc`: accuracy of the tabulated `B̃` weights

`buWt p α s t ℓ h` is the integer (fixed-point) representative of
`2^p · egW s t α ℓ h` that the word `q` of the one-dimensional `B̃` stage can actually compute: the
Horner recursion `auH` of the exponential, evaluated at the working precision
`auPrec p = 3p + 100`, with the guard that exponents beyond `p + 10` (where the true weight is
already `< 4·2^{-p}`) are stored as `0`.

The theorem below is the error contract of that table: at the working scale `2^{-p}` the tabulated
value differs from the true Gaussian weight `egW s t α ℓ h` by at most `4·2^{-p}`.

The proof combines four estimates that are already established elsewhere in the area:

* `buNIdent` identifies the integer numerator `buN s t ℓ h` of the exponent with `s²` times the
  difference of squares appearing in `egW`, so that `egW s t α ℓ h = exp (-U)` for
  `U = π α² buN / s²`;
* `buZClose` bounds `buZ p α s t ℓ h` (the fixed-point value of `2^P·U`) against `2^P·U`;
* `auHExpClose` bounds the error of the truncated recursion, and `tdivScale` the error of the final
  truncating division by `2^{P-p}`;
* `notGuardBound` covers the guarded branch, where the table stores `0`.

The only genuinely local estimates are the `1`-Lipschitz continuity of `t ↦ e^{-t}` on `[0,∞)`
(`buExpNegLip`) and the guard threshold estimate `buGuardBound`; both are proved below.
-/

/-! ## Two local numerical lemmas -/

/-- `auPi p = uval (auPrec p)` is nonnegative (it is the flooring division of a nonnegative
fixed-point value by a positive power of two). -/
lemma buPi_nonneg (p : ℕ) : (0 : ℤ) ≤ auPi p := by
  rw [auPi, Work.Fx.uval]
  apply Int.fdiv_nonneg
  · rw [Work.Fx.Nval]
    exact add_nonneg (mul_nonneg (Int.natCast_nonneg _) (by positivity)) (by positivity)
  · positivity

/-- `t ↦ e^{-t}` is `1`-Lipschitz on `[0,∞)`: `|e^{-x} - e^{-y}| ≤ |x - y|` for `x, y ≥ 0`. -/
lemma buExpNegLip (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  -- for `0 ≤ b ≤ a`, `e^{-b} - e^{-a} = e^{-b}(1 - e^{-(a-b)}) ≤ (a-b)`
  have key : ∀ a b : ℝ, 0 ≤ b → b ≤ a → Real.exp (-b) - Real.exp (-a) ≤ a - b := by
    intro a b _ hba
    have h1 : Real.exp (-a) = Real.exp (-b) * Real.exp (-(a - b)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h2 : 1 - Real.exp (-(a - b)) ≤ a - b := by
      have h := Real.one_sub_le_exp_neg (a - b)
      linarith
    have h3 : Real.exp (-b) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h4 : (0 : ℝ) ≤ 1 - Real.exp (-(a - b)) := by
      have h := Real.exp_le_one_iff.mpr (show -(a - b) ≤ 0 by linarith)
      linarith
    calc Real.exp (-b) - Real.exp (-a)
        = Real.exp (-b) * (1 - Real.exp (-(a - b))) := by rw [h1]; ring
      _ ≤ 1 * (a - b) := mul_le_mul h3 h2 h4 (by norm_num)
      _ = a - b := one_mul _
  rcases le_total y x with hxy | hyx
  · have h := key x y hy hxy
    have hnn : Real.exp (-x) - Real.exp (-y) ≤ 0 := by
      have hle : Real.exp (-x) ≤ Real.exp (-y) := Real.exp_le_exp.mpr (by linarith)
      linarith
    rw [abs_of_nonpos hnn, abs_of_nonneg (show (0 : ℝ) ≤ x - y by linarith)]
    linarith
  · have h := key y x hx hyx
    have hnn : (0 : ℝ) ≤ Real.exp (-x) - Real.exp (-y) := by
      have hle : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
      linarith
    rw [abs_of_nonneg hnn, abs_of_nonpos (show x - y ≤ 0 by linarith)]
    linarith

/-- Guard-threshold estimate.  If `Z ≥ 0` and `u ≥ 0` satisfy `|Z - 2^P·u| ≤ 1 + u/3` (the
accuracy of the fixed-point exponent `buZ`) and the guard `Z ≤ (p+10)·2^P` holds
(`P = auPrec p`), then `e^{-Z/2^P}` approximates `e^{-u}` to within `2^{-p}`. -/
lemma buGuardBound (p : ℕ) (hp : 100 ≤ p) (Z : ℤ) (u : ℝ) (hZ0 : 0 ≤ Z) (hu0 : 0 ≤ u)
    (hZu : |(Z : ℝ) - (2 : ℝ) ^ auPrec p * u| ≤ 1 + u / 3)
    (hguard : (Z : ℝ) ≤ ((p : ℝ) + 10) * (2 : ℝ) ^ auPrec p) :
    |Real.exp (-((Z : ℝ) / (2 : ℝ) ^ auPrec p)) - Real.exp (-u)| ≤ 1 / (2 : ℝ) ^ p := by
  set A : ℝ := (2 : ℝ) ^ auPrec p with hA
  have hAge : (2 : ℝ) ≤ A := by
    rw [hA]
    have h1 : (1 : ℕ) ≤ auPrec p := by simp only [auPrec]; omega
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h1
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le (by norm_num) hAge
  have hZle : (Z : ℝ) ≤ ((p : ℝ) + 10) * A := by rw [hA]; exact hguard
  have hZu' : |(Z : ℝ) - A * u| ≤ 1 + u / 3 := by rw [hA]; exact hZu
  have hZR : (0 : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hZ0
  -- `u` cannot be large: the guard caps `A·u`
  have hu_le : u ≤ 2 * (p : ℝ) + 21 := by
    have h1 : -(1 + u / 3) ≤ (Z : ℝ) - A * u := (abs_le.mp hZu').1
    have h3 : A * u ≤ ((p : ℝ) + 10) * A + 1 + u / 3 := by linarith
    have h5 : A / 2 ≤ A - 1 / 3 := by linarith
    have h4 : u * (A / 2) ≤ ((p : ℝ) + 10) * A + 1 := by
      have e : u * (A / 2) ≤ u * (A - 1 / 3) := mul_le_mul_of_nonneg_left h5 hu0
      have f : u * (A - 1 / 3) ≤ ((p : ℝ) + 10) * A + 1 := by linarith
      linarith
    have h6 : u ≤ (2 * (((p : ℝ) + 10) * A + 1)) / A := by
      rw [le_div_iff₀ hApos]
      linarith
    have h7 : (2 * (((p : ℝ) + 10) * A + 1)) / A = 2 * (p : ℝ) + 20 + 2 / A := by
      field_simp
      ring
    have h8 : 2 / A ≤ 1 := by
      rw [div_le_one hApos]
      exact hAge
    linarith
  -- hence `|Z/A - u| ≤ (2p+24)/(3A)`
  have hdist : |(Z : ℝ) / A - u| ≤ (2 * (p : ℝ) + 24) / (3 * A) := by
    have hsplit : (Z : ℝ) / A - u = ((Z : ℝ) - A * u) / A := by
      field_simp
    rw [hsplit, abs_div, abs_of_pos hApos]
    have h5 : |(Z : ℝ) - A * u| / A ≤ (1 + u / 3) / A :=
      div_le_div_of_nonneg_right hZu' (le_of_lt hApos)
    have hnum : 1 + u / 3 ≤ (2 * (p : ℝ) + 24) / 3 := by linarith
    have h6 : (1 + u / 3) / A ≤ ((2 * (p : ℝ) + 24) / 3) / A :=
      div_le_div_of_nonneg_right hnum (le_of_lt hApos)
    have h7 : ((2 * (p : ℝ) + 24) / 3) / A = (2 * (p : ℝ) + 24) / (3 * A) := by
      rw [div_div]
    linarith [h5, h6]
  -- and `(2p+24)/(3A) ≤ 2^{-p}`
  have hfinal : (2 * (p : ℝ) + 24) / (3 * A) ≤ 1 / (2 : ℝ) ^ p := by
    have hnat : 2 * p + 24 ≤ 3 * 2 ^ (2 * p + 100) := by
      have h1 : 2 * p + 24 < 2 ^ (2 * p + 24) := Nat.lt_two_pow_self
      have h2 : 2 ^ (2 * p + 24) ≤ 2 ^ (2 * p + 100) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hreal : 2 * (p : ℝ) + 24 ≤ 3 * (2 : ℝ) ^ (2 * p + 100) := by exact_mod_cast hnat
    have hpow : A = (2 : ℝ) ^ p * (2 : ℝ) ^ (2 * p + 100) := by
      rw [hA, show auPrec p = p + (2 * p + 100) by simp only [auPrec]; omega, pow_add]
    have hkey : (2 * (p : ℝ) + 24) / (3 * A)
        = ((2 * (p : ℝ) + 24) / (3 * (2 : ℝ) ^ (2 * p + 100))) / (2 : ℝ) ^ p := by
      rw [hpow]
      field_simp
    rw [hkey, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < (2 : ℝ) ^ p)]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 * (2 : ℝ) ^ (2 * p + 100))]
    simpa using hreal
  calc |Real.exp (-((Z : ℝ) / A)) - Real.exp (-u)|
      ≤ |(Z : ℝ) / A - u| := buExpNegLip ((Z : ℝ) / A) u (by positivity) hu0
    _ ≤ (2 * (p : ℝ) + 24) / (3 * A) := hdist
    _ ≤ 1 / (2 : ℝ) ^ p := hfinal

/-! ## The weight-accuracy contract -/

/-- The tabulated weight `buWt p α s t ℓ h` approximates `2^p · egW s t α ℓ h` with absolute error
at most `4` at the scale `2^{-p}`, i.e. `|buWt/2^p - egW| ≤ 4·2^{-p}`. -/
theorem buQWwtacc (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (ℓ h : ℤ) (hh : h ≠ 0) :
    |((Work.Resample.buWt p α s t ℓ h : ℝ) / (2 : ℝ) ^ p - Work.Resample.egW s t α ℓ h)|
      ≤ 4 / (2 : ℝ) ^ p := by
  have hs0 : 0 < s := by omega
  obtain ⟨hNident, hNnn⟩ := buNIdent s t hs0 hst ℓ h hh
  have hNnnR : (0 : ℝ) ≤ (buN s t ℓ h : ℝ) := by exact_mod_cast hNnn
  have hPi0 : (0 : ℤ) ≤ auPi p := buPi_nonneg p
  have hPi1 := auPiBound p hp
  obtain ⟨hZ0, hZc⟩ := buZClose p α s t hp hs ℓ h hNnn hPi0 hPi1
  -- the true exponent `U = π·α²·buN/s²` and the scaled numerator `W = α²·buN/s²`
  set W : ℝ := (α : ℝ) ^ 2 * (buN s t ℓ h : ℝ) / (s : ℝ) ^ 2 with hW
  set U : ℝ := Real.pi * W with hU
  have hWnn : 0 ≤ W := by
    rw [hW]
    exact div_nonneg (mul_nonneg (sq_nonneg _) hNnnR) (sq_nonneg _)
  have hUnn : 0 ≤ U := by rw [hU]; exact mul_nonneg (le_of_lt Real.pi_pos) hWnn
  have hWU : W ≤ U / 3 := by
    have h3 : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
    have h := mul_le_mul_of_nonneg_left h3 hWnn
    rw [hU]
    linarith
  have hZcU : |((buZ p α s t ℓ h : ℤ) : ℝ) - (2 : ℝ) ^ auPrec p * U| ≤ 1 + W := by
    rw [hU, hW]
    exact hZc
  have hW_eq : W = (α : ℝ) ^ 2 * (((t : ℝ) * (h : ℝ) / (s : ℝ) + Work.ResMath.betaI s t ℓ) ^ 2
      - (Work.ResMath.betaI s t (ℓ + h)) ^ 2) := by
    rw [hW, hNident]
    field_simp
  have hegW : egW s t α ℓ h = Real.exp (-U) := by
    have harg : -(Real.pi * (α : ℝ) ^ 2 * (((t : ℝ) * (h : ℝ) / (s : ℝ)
          + Work.ResMath.betaI s t ℓ) ^ 2 - (Work.ResMath.betaI s t (ℓ + h)) ^ 2)) = -U := by
      rw [hU, hW_eq]
      ring
    rw [egW, harg]
  have hZu : |((buZ p α s t ℓ h : ℤ) : ℝ) - (2 : ℝ) ^ auPrec p * U| ≤ 1 + U / 3 := by
    have hnn := abs_nonneg (((buZ p α s t ℓ h : ℤ) : ℝ) - (2 : ℝ) ^ auPrec p * U)
    linarith
  by_cases hg : buZ p α s t ℓ h ≤ ((p + 10 : ℕ) : ℤ) * (2 : ℤ) ^ (auPrec p)
  · -- the recursion is run: the three error terms `tdiv`, `auH`, `exp` add up to `4·2^{-p}`
    have hbu : buWt p α s t ℓ h
        = Int.tdiv (auH p (-(buZ p α s t ℓ h)) (auNstep p)) ((2 : ℤ) ^ (auPrec p - p)) := by
      rw [buWt]
      exact if_pos hg
    have hZleR : ((buZ p α s t ℓ h : ℤ) : ℝ) ≤ ((p : ℝ) + 10) * (2 : ℝ) ^ auPrec p := by
      have h1 : ((buZ p α s t ℓ h : ℤ) : ℝ)
          ≤ ((((p + 10 : ℕ) : ℤ) * (2 : ℤ) ^ (auPrec p)) : ℝ) := by
        exact_mod_cast hg
      push_cast at h1
      linarith
    have h1 := tdivScale p (auH p (-(buZ p α s t ℓ h)) (auNstep p))
    have h2 := auHExpClose p hp (buZ p α s t ℓ h) hZ0 hZleR
    have h3 := buGuardBound p hp (buZ p α s t ℓ h) U hZ0 hUnn hZu hZleR
    have htri1 := abs_sub_le
      (((Int.tdiv (auH p (-(buZ p α s t ℓ h)) (auNstep p)) ((2 : ℤ) ^ (auPrec p - p)) : ℤ) : ℝ)
        / (2 : ℝ) ^ p)
      (((auH p (-(buZ p α s t ℓ h)) (auNstep p) : ℤ) : ℝ) / (2 : ℝ) ^ auPrec p)
      (Real.exp (-U))
    have htri2 := abs_sub_le
      (((auH p (-(buZ p α s t ℓ h)) (auNstep p) : ℤ) : ℝ) / (2 : ℝ) ^ auPrec p)
      (Real.exp (-(((buZ p α s t ℓ h : ℤ) : ℝ) / (2 : ℝ) ^ auPrec p))) (Real.exp (-U))
    have hsum : 1 / (2 : ℝ) ^ p + 2 / (2 : ℝ) ^ p + 1 / (2 : ℝ) ^ p = 4 / (2 : ℝ) ^ p := by
      ring
    rw [hbu, hegW]
    linarith [htri1, htri2, h1, h2, h3, hsum]
  · -- the guard fails: the table stores `0` and the true weight is below `4·2^{-p}`
    have hbu : buWt p α s t ℓ h = 0 := by
      rw [buWt]
      exact if_neg hg
    have hgt : ((p : ℝ) + 10) * (2 : ℝ) ^ auPrec p < ((buZ p α s t ℓ h : ℤ) : ℝ) := by
      have h1 : ((((p + 10 : ℕ) : ℤ) * (2 : ℤ) ^ (auPrec p)) : ℝ)
          < ((buZ p α s t ℓ h : ℤ) : ℝ) := by
        exact_mod_cast (not_le.mp hg)
      push_cast at h1
      linarith
    have hle := notGuardBound p hp (buZ p α s t ℓ h) U hZ0 hUnn hZu hgt
    rw [hbu, hegW]
    simpa only [Int.cast_zero, zero_div, zero_sub, abs_neg,
      abs_of_nonneg (Real.exp_pos (-U)).le] using hle

end Work.Resample
