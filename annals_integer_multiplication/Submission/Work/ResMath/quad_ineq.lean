import Mathlib
import Submission.Work.ResMath.resE_defs

/-!
# The quadratic inequality `Work.ResMath.quad_ineq`

This is the elementary real inequality used in the proof of Lemma 4.6 of
Harvey–van der Hoeven, *Integer multiplication in time* `O(n log n)` (Annals 193 (2021)):

for `1 < t/s` and an integer `h ≠ 0`,
`2 (t/s - 1) (|h| - 1/2)^2 ≤ (t h / s + β_ℓ)^2 - (β_{ℓ+h})^2`.

Here `β_n = tn/s - ⌊tn/s + 1/2⌋` (`Work.ResMath.betaI`), so `|β_n| ≤ 1/2` for every `n`.
Writing `τ = t/s > 1` and `m = |h| ≥ 1`, `A = τ h`, the right-hand side is bounded
below by `(τ m - 1/2)^2 - 1/4 = τ^2 m^2 - τ m` (using `|A + x| ≥ |A| - |x| ≥ τ m - 1/2`
and `y^2 ≤ 1/4`), so it suffices to prove the purely polynomial inequality
`2 (τ - 1) (m - 1/2)^2 ≤ τ^2 m^2 - τ m` for `τ > 1`, `m ≥ 1`.
-/

namespace Work.ResMath

/-- The polynomial inequality `2 (τ - 1) (m - 1/2)^2 ≤ τ^2 m^2 - τ m` for `τ > 1`, `m ≥ 1`. -/
lemma quad_ineq_aux (τ m : ℝ) (hτ : 1 < τ) (hm : 1 ≤ m) :
    2 * (τ - 1) * (m - 1 / 2) ^ 2 ≤ τ ^ 2 * m ^ 2 - τ * m := by
  nlinarith [sq_nonneg (τ - 1), sq_nonneg (m - 1), hm, hτ,
    mul_nonneg (by linarith : (0 : ℝ) ≤ τ - 1) (by linarith : (0 : ℝ) ≤ m - 1)]

theorem quad_ineq (s t : ℕ) (hs : 0 < s) (hst : s < t) (ℓ : Fin s) (h : ℤ) (hh : h ≠ 0) :
    2 * ((t : ℝ) / s - 1) * (|(h : ℝ)| - 1 / 2) ^ 2
      ≤ ((t : ℝ) * (h : ℝ) / s + betaI s t (ℓ : ℤ)) ^ 2 - (betaI s t ((ℓ : ℤ) + h)) ^ 2 := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have ht : (0 : ℝ) < t := by exact_mod_cast (lt_trans hs hst)
  have hst' : (s : ℝ) < t := by exact_mod_cast hst
  have hτ : 1 < (t : ℝ) / s := by
    rw [lt_div_iff₀ hs']; simpa using hst'
  have hm : (1 : ℝ) ≤ |(h : ℝ)| := by
    have hh1 : (1 : ℤ) ≤ |h| := Int.one_le_abs hh
    rw [← Int.cast_abs]
    exact_mod_cast hh1
  -- `|A| = τ * m` with `A = t h / s`, `τ = t / s`, `m = |h|`
  have hA : |(t : ℝ) * (h : ℝ) / s| = (t : ℝ) / s * |(h : ℝ)| := by
    rw [show (t : ℝ) * (h : ℝ) / s = ((t : ℝ) / s) * (h : ℝ) by ring, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < (t : ℝ) / s)]
  have hx : |betaI s t (ℓ : ℤ)| ≤ 1 / 2 := betaI_abs_le s t _
  have hy : |betaI s t ((ℓ : ℤ) + h)| ≤ 1 / 2 := betaI_abs_le s t _
  have hy2 : (betaI s t ((ℓ : ℤ) + h)) ^ 2 ≤ 1 / 4 := by
    rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num]
    exact sq_le_sq.mpr (by simpa using hy)
  -- `(τ m - 1/2)^2 ≤ (A + x)^2`
  have hsq : ((t : ℝ) / s * |(h : ℝ)| - 1 / 2) ^ 2
      ≤ ((t : ℝ) * (h : ℝ) / s + betaI s t (ℓ : ℤ)) ^ 2 := by
    have htri : (t : ℝ) / s * |(h : ℝ)| - 1 / 2
        ≤ |(t : ℝ) * (h : ℝ) / s + betaI s t (ℓ : ℤ)| := by
      rw [← hA]
      have h1 : |(t : ℝ) * (h : ℝ) / s|
          ≤ |(t : ℝ) * (h : ℝ) / s + betaI s t (ℓ : ℤ)| + |betaI s t (ℓ : ℤ)| := by
        have := abs_add_le ((t : ℝ) * (h : ℝ) / s + betaI s t (ℓ : ℤ))
          (-(betaI s t (ℓ : ℤ)))
        simpa [abs_neg, add_assoc] using this
      linarith
    have hnn : 0 ≤ (t : ℝ) / s * |(h : ℝ)| - 1 / 2 := by nlinarith [hτ, hm]
    calc ((t : ℝ) / s * |(h : ℝ)| - 1 / 2) ^ 2
        = |(t : ℝ) / s * |(h : ℝ)| - 1 / 2| ^ 2 := (sq_abs _).symm
      _ ≤ |(t : ℝ) * (h : ℝ) / s + betaI s t (ℓ : ℤ)| ^ 2 :=
            by simpa [abs_of_nonneg hnn] using pow_le_pow_left₀ hnn htri 2
      _ = ((t : ℝ) * (h : ℝ) / s + betaI s t (ℓ : ℤ)) ^ 2 := sq_abs _
  have hkey := quad_ineq_aux ((t : ℝ) / s) |(h : ℝ)| hτ hm
  have hbridge : ((t : ℝ) / s) ^ 2 * |(h : ℝ)| ^ 2 - (t : ℝ) / s * |(h : ℝ)|
      ≤ ((t : ℝ) * (h : ℝ) / s + betaI s t (ℓ : ℤ)) ^ 2 - (betaI s t ((ℓ : ℤ) + h)) ^ 2 := by
    have heq : ((t : ℝ) / s) ^ 2 * |(h : ℝ)| ^ 2 - (t : ℝ) / s * |(h : ℝ)|
        = ((t : ℝ) / s * |(h : ℝ)| - 1 / 2) ^ 2 - 1 / 4 := by ring
    rw [heq]; linarith [hsq, hy2]
  linarith [hkey, hbridge]

end Work.ResMath
