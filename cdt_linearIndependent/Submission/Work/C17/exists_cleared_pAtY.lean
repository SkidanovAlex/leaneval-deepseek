import Mathlib
import Submission.Work.C17.seventeen_defs

/-!
# Clearing the denominator `(z-1)^d` in `p(yC z)`

With `yC z = z²/(z-1)`, the function `z ↦ pAtY p z = p(yC z)` is a rational function whose only
pole is at `z = 1`, with denominator dividing `(z-1)^d` as soon as `d ≥ p.natDegree`:

  `(z-1)^d · p(yC z) = A(z)`,   `A = ∑_{k ≤ d} (p.coeff k) · X^{2k} · (X-1)^{d-k} ∈ ℚ[X]`.

The substantive point (`exists_cleared_pAtY`) is that this clearing is *lossless*: `A = 0`
iff `p = 0`.  Indeed the term of top degree `d + p.natDegree` of `A` is `(p.coeff p.natDegree)·X^{d+n}`
— every other term has degree `≤ d + k < d + n` — so the leading coefficient of `p` is the coefficient
of `A` in degree `d + p.natDegree`.
-/

namespace Work.C17

open Polynomial

/-- Clearing polynomial: `∑ k ≤ d, (p.coeff k) · X^(2k) · (X-1)^(d-k)`, i.e. `(z-1)^d · p(yC z)`
written as a polynomial in `z`. -/
noncomputable def clearedAtY (p : Polynomial ℚ) (d : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (d + 1), C (p.coeff k) * X ^ (2 * k) * (X - 1) ^ (d - k)

/-- The top coefficient of `(X-1)^m` is `1`. -/
lemma coeff_X_sub_one_pow (m : ℕ) : ((X - 1 : Polynomial ℚ) ^ m).coeff m = 1 := by
  have hmon : (X - C 1 : Polynomial ℚ).Monic := Polynomial.monic_X_sub_C 1
  have hdeg : ((X - C 1 : Polynomial ℚ) ^ m).natDegree = m := by
    rw [hmon.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  have h : ((X - C 1 : Polynomial ℚ) ^ m).coeff m = 1 := by
    have := (hmon.pow m).coeff_natDegree
    rwa [hdeg] at this
  simpa [Polynomial.C_1] using h

/-- Each summand of `clearedAtY p d` has degree at most `d + k`. -/
lemma natDegree_clearedAtY_term_le (p : Polynomial ℚ) {d k : ℕ} (hk : k ≤ d) :
    (C (p.coeff k) * X ^ (2 * k) * (X - 1) ^ (d - k)).natDegree ≤ d + k := by
  have hX : (X - 1 : Polynomial ℚ) = X - C 1 := by rw [Polynomial.C_1]
  have ha : (C (p.coeff k) * X ^ (2 * k) : Polynomial ℚ).natDegree ≤ 2 * k := by
    have h := Polynomial.natDegree_mul_le (p := (C (p.coeff k) : Polynomial ℚ))
      (q := (X ^ (2 * k) : Polynomial ℚ))
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add] at h
    exact h
  have hb : ((X - 1 : Polynomial ℚ) ^ (d - k)).natDegree ≤ d - k := by
    rw [hX]
    have h := Polynomial.natDegree_pow_le (p := (X - C 1 : Polynomial ℚ)) (n := d - k)
    rw [Polynomial.natDegree_X_sub_C, mul_one] at h
    exact h
  have hmain := Polynomial.natDegree_mul_le (p := (C (p.coeff k) * X ^ (2 * k) : Polynomial ℚ))
    (q := ((X - 1 : Polynomial ℚ) ^ (d - k)))
  calc (C (p.coeff k) * X ^ (2 * k) * (X - 1) ^ (d - k) : Polynomial ℚ).natDegree
      ≤ (C (p.coeff k) * X ^ (2 * k) : Polynomial ℚ).natDegree
          + ((X - 1 : Polynomial ℚ) ^ (d - k)).natDegree := hmain
    _ ≤ 2 * k + (d - k) := add_le_add ha hb
    _ = d + k := by omega

/-- The coefficient of `clearedAtY p d` in degree `d + p.natDegree` is the leading coefficient
of `p`: `clearedAtY p d` is `p.natDegree`-shifted at its top. -/
lemma coeff_clearedAtY (p : Polynomial ℚ) (d : ℕ) (hd : p.natDegree ≤ d) :
    (clearedAtY p d).coeff (d + p.natDegree) = p.coeff p.natDegree := by
  have hterm : ∀ k ∈ Finset.range (d + 1),
      ((C (p.coeff k) * X ^ (2 * k) * (X - 1) ^ (d - k) : Polynomial ℚ)).coeff
          (d + p.natDegree)
        = if k = p.natDegree then p.coeff k else 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hk' : k ≤ d := Nat.lt_succ_iff.mp hk
    by_cases hkn : k = p.natDegree
    · subst hkn
      rw [mul_assoc, Polynomial.coeff_C_mul]
      have hidx : d + p.natDegree = (d - p.natDegree) + 2 * p.natDegree := by omega
      have h2 : (X ^ (2 * p.natDegree) * (X - 1) ^ (d - p.natDegree) : Polynomial ℚ).coeff
          (d + p.natDegree) = 1 := by
        rw [hidx, Polynomial.coeff_X_pow_mul]
        exact coeff_X_sub_one_pow (d - p.natDegree)
      rw [h2, mul_one]
      simp
    · rw [if_neg hkn]
      rcases lt_or_gt_of_ne hkn with hlt | hgt
      · apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have := natDegree_clearedAtY_term_le p hk'
        omega
      · have hc : p.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hgt
        simp [hc]
  rw [clearedAtY, Polynomial.finsetSum_coeff]
  trans (∑ k ∈ Finset.range (d + 1), if k = p.natDegree then p.coeff k else 0)
  · exact Finset.sum_congr rfl (fun k hk => hterm k hk)
  · rw [Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_range.mpr (by omega))]

theorem exists_cleared_pAtY (p : Polynomial ℚ) (d : ℕ) (hd : p.natDegree ≤ d) :
    ∃ A : Polynomial ℚ, (A = 0 ↔ p = 0) ∧
      ∀ z : ℂ, z ≠ 1 → (z - 1) ^ d * pAtY p z = A.eval₂ (algebraMap ℚ ℂ) z := by
  refine ⟨clearedAtY p d, ⟨?_, ?_⟩, ?_⟩
  · intro hA
    by_contra hp
    have hcoe := coeff_clearedAtY p d hd
    rw [hA, Polynomial.coeff_zero] at hcoe
    have hz : p.leadingCoeff = 0 := by
      rw [← Polynomial.coeff_natDegree]
      exact hcoe.symm
    exact hp (Polynomial.leadingCoeff_eq_zero.mp hz)
  · intro hp
    rw [hp]
    simp [clearedAtY]
  · intro z hz
    have hpow : ∀ k ≤ d, (z - 1) ^ d * yC z ^ k = z ^ (2 * k) * (z - 1) ^ (d - k) := by
      intro k hk
      have h1 : (z - 1) * yC z = z ^ 2 := by
        rw [yC]; field_simp
      calc (z - 1) ^ d * yC z ^ k
          = ((z - 1) ^ (d - k) * (z - 1) ^ k) * yC z ^ k := by
              rw [← pow_add, Nat.sub_add_cancel hk]
        _ = (z - 1) ^ (d - k) * ((z - 1) ^ k * yC z ^ k) := by ring
        _ = (z - 1) ^ (d - k) * ((z - 1) * yC z) ^ k := by rw [mul_pow]
        _ = (z - 1) ^ (d - k) * (z ^ 2) ^ k := by rw [h1]
        _ = z ^ (2 * k) * (z - 1) ^ (d - k) := by rw [pow_mul]; ring
    have hp1 : pAtY p z
        = ∑ k ∈ Finset.range (d + 1), (algebraMap ℚ ℂ (p.coeff k)) * yC z ^ k := by
      rw [pAtY, Polynomial.eval₂_eq_sum_range' (algebraMap ℚ ℂ) (n := d + 1) (by omega)]
    rw [hp1, Finset.mul_sum]
    simp only [clearedAtY, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_sub, Polynomial.eval₂_one]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hk' : k ≤ d := Nat.lt_succ_iff.mp hk
    rw [show (z - 1) ^ d * ((algebraMap ℚ ℂ) (p.coeff k) * yC z ^ k)
          = (algebraMap ℚ ℂ) (p.coeff k) * ((z - 1) ^ d * yC z ^ k) by ring]
    rw [hpow k hk']
    ring

end Work.C17
