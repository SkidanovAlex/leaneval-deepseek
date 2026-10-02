import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A uniform second-order Taylor remainder bound for complex polynomials

For a polynomial `P : ℂ[X]` we show that the second-order Taylor remainder of `P` at `z`,
evaluated at `z * (1 - x)`, is bounded by a *single* constant (depending only on `P`) times
`‖x‖ ^ 3 * ‖z‖ ^ 3`, uniformly for `‖z‖ ≤ 1` and `‖x‖ ≤ 1 / 2`.

Writing `E = P(z(1-x)) - (P(z) - x z P'(z) + (xz)²/2 P''(z))`, the proof expands everything in
the coefficients `a_k = P.coeff k` of `P`:

  `E = ∑_k a_k z^k * G_k(x)`, with `G_k(x) = (1-x)^k - 1 + k x - k(k-1)/2 x²`.

For each `k` the binomial theorem gives `G_k(x) = ∑_{j=3}^k (k choose j) (-x)^j`, so on
`‖x‖ ≤ 1/2` one has `‖G_k(x)‖ ≤ 2^k ‖x‖^3`; combined with `‖z‖^k ≤ ‖z‖^3` (for `k ≥ 3`, the
only case where `G_k` does not vanish) this yields the claimed bound.
-/

open Polynomial Finset

namespace Work.FatouDeg.Petal

/-- The second-order Taylor remainder of the monomial `w ↦ w^k` at the point `1`, evaluated at
`1 - x`:
`G_k(x) = (1-x)^k - 1 + k x - k(k-1)/2 x²`. -/
noncomputable def remG (k : ℕ) (x : ℂ) : ℂ :=
  (1 - x) ^ k - 1 + (k : ℂ) * x - ((k : ℂ) * ((k : ℂ) - 1)) / 2 * x ^ 2

/-- Binomial form of the remainder `G_k`: all terms of degree `≤ 2` cancel. -/
lemma remG_eq_sum (k : ℕ) (x : ℂ) :
    remG k x = ∑ m ∈ Finset.range (k - 2), (-x) ^ (m + 3) * (k.choose (m + 3) : ℂ) := by
  rcases k with _ | _ | k
  · simp [remG]
  · simp [remG]
  · have hk : k + 2 - 2 = k := by omega
    rw [hk]
    have hpow : (1 - x) ^ (k + 2)
        = ∑ m ∈ Finset.range (k + 3), (-x) ^ m * ((k + 2).choose m : ℂ) := by
      rw [show (1 : ℂ) - x = -x + 1 by ring, add_pow]
      simp only [one_pow, mul_one]
    have h3 : ∑ m ∈ Finset.range 3, (-x) ^ m * ((k + 2).choose m : ℂ)
        = 1 - ((k + 2 : ℕ) : ℂ) * x
          + (((k + 2 : ℕ) : ℂ) * (((k + 2 : ℕ) : ℂ) - 1)) / 2 * x ^ 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      rw [Nat.cast_choose_two]
      simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one]
      ring
    have hsplit : ∑ m ∈ Finset.range (k + 3), (-x) ^ m * ((k + 2).choose m : ℂ)
        = (∑ m ∈ Finset.range 3, (-x) ^ m * ((k + 2).choose m : ℂ))
          + ∑ m ∈ Finset.range k, (-x) ^ (m + 3) * ((k + 2).choose (m + 3) : ℂ) := by
      rw [← Finset.sum_range_add_sum_Ico
        (f := fun m => (-x) ^ m * ((k + 2).choose m : ℂ)) (m := 3) (n := k + 3) (by omega)]
      congr 1
      rw [Finset.sum_Ico_eq_sum_range, show k + 3 - 3 = k by omega]
      apply Finset.sum_congr rfl
      intro m _
      rw [Nat.add_comm 3 m]
    unfold remG
    rw [hpow, hsplit, h3]
    ring

/-- On `‖x‖ ≤ 1/2` the binomial remainder is `O(x³)` with constant `2^k`. -/
lemma remG_bound (k : ℕ) (x : ℂ) (hx : ‖x‖ ≤ 1 / 2) :
    ‖remG k x‖ ≤ (2 : ℝ) ^ k * ‖x‖ ^ 3 := by
  rw [remG_eq_sum]
  have hx1 : ‖x‖ ≤ 1 := by linarith
  calc ‖∑ m ∈ Finset.range (k - 2), (-x) ^ (m + 3) * (k.choose (m + 3) : ℂ)‖
      ≤ ∑ m ∈ Finset.range (k - 2),
          ‖(-x) ^ (m + 3) * (k.choose (m + 3) : ℂ)‖ := norm_sum_le _ _
    _ = ∑ m ∈ Finset.range (k - 2), ‖x‖ ^ (m + 3) * ((k.choose (m + 3) : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [norm_mul, norm_pow, norm_neg, Complex.norm_natCast]
    _ = ‖x‖ ^ 3 * ∑ m ∈ Finset.range (k - 2), ‖x‖ ^ m * ((k.choose (m + 3) : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        rw [pow_add]
        ring
    _ ≤ ‖x‖ ^ 3 * ∑ m ∈ Finset.range (k - 2), ((k.choose (m + 3) : ℕ) : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro m _
        have h1 : ‖x‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg x) hx1
        exact mul_le_of_le_one_left (by positivity) h1
    _ ≤ ‖x‖ ^ 3 * (2 : ℝ) ^ k := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∑ m ∈ Finset.range (k - 2), ((k.choose (m + 3) : ℕ) : ℝ)
            = ∑ j ∈ Finset.Ico 3 (k + 1), ((k.choose j : ℕ) : ℝ) := by
              rw [Finset.sum_Ico_eq_sum_range, show k + 1 - 3 = k - 2 by omega]
              apply Finset.sum_congr rfl
              intro m _
              rw [Nat.add_comm 3 m]
          _ ≤ ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℕ) : ℝ) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro j hj
                rw [Finset.mem_range]
                have := Finset.mem_Ico.mp hj
                omega
              · intro j _ _
                positivity
          _ = (2 : ℝ) ^ k := by
              rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
              norm_num
    _ = (2 : ℝ) ^ k * ‖x‖ ^ 3 := by ring

/-- For `k ≤ 2` the remainder `G_k` vanishes identically. -/
lemma remG_eq_zero_of_lt_three (k : ℕ) (hk : k < 3) (x : ℂ) : remG k x = 0 := by
  interval_cases k
  · simp [remG]
  · simp [remG]
  · simp [remG]; ring

/-- Weighted evaluation identity for the first derivative:
`z * P'(z) = ∑_k (P.coeff k) * k * z^k`. -/
lemma rem_deriv_weight (p : ℂ[X]) (z : ℂ) :
    z * (p.derivative).eval z = p.sum (fun n a => a * (n : ℂ) * z ^ n) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.derivative_add, Polynomial.eval_add, mul_add, hp, hq]
      symm
      apply Polynomial.sum_add_index
      · intro i; ring
      · intro a b1 b2; ring
  | monomial n a =>
      rw [Polynomial.derivative_monomial, Polynomial.eval_monomial]
      rw [Polynomial.sum_monomial_index (f := fun n a => a * (n : ℂ) * z ^ n)]
      · rcases n with _ | m
        · simp
        · rw [Nat.succ_sub_one, pow_succ]; ring
      · ring

/-- Weighted evaluation identity for the second derivative:
`z² * P''(z) = ∑_k (P.coeff k) * k * (k-1) * z^k`. -/
lemma rem_deriv2_weight (p : ℂ[X]) (z : ℂ) :
    z ^ 2 * (p.derivative.derivative).eval z
      = p.sum (fun n a => a * ((n : ℂ) * ((n : ℂ) - 1)) * z ^ n) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.derivative_add, Polynomial.derivative_add, Polynomial.eval_add, mul_add,
        hp, hq]
      symm
      apply Polynomial.sum_add_index
      · intro i; ring
      · intro a b1 b2; ring
  | monomial n a =>
      rw [Polynomial.derivative_monomial, Polynomial.derivative_monomial, Polynomial.eval_monomial]
      rw [Polynomial.sum_monomial_index (f := fun n a => a * ((n : ℂ) * ((n : ℂ) - 1)) * z ^ n)]
      · rcases n with _ | _ | m
        · simp
        · simp
        · rw [pow_succ, pow_succ]; push_cast; ring
      · ring

/-- Merge four `Finset` sums with the same index set into a single sum. -/
lemma rem_sum_merge_four {ι : Type*} (s : Finset ι) (A B C D : ι → ℂ) :
    (∑ k ∈ s, A k) - (∑ k ∈ s, B k) + (∑ k ∈ s, C k) - (∑ k ∈ s, D k)
      = ∑ k ∈ s, (A k - B k + C k - D k) := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- **Uniform second-order Taylor remainder bound for complex polynomials.**

For every `P : ℂ[X]` there is `C ≥ 0` such that for all `z, x : ℂ` with `‖z‖ ≤ 1` and
`‖x‖ ≤ 1/2`,
`‖P(z(1-x)) - (P(z) - x z P'(z) + (xz)²/2 P''(z))‖ ≤ C ‖x‖³ ‖z‖³`. -/
theorem polyTaylor2RemBound (P : Polynomial ℂ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z x : ℂ, ‖z‖ ≤ 1 → ‖x‖ ≤ 1 / 2 →
    ‖P.eval (z * (1 - x)) - (P.eval z - x * z * (Polynomial.derivative P).eval z
      + (x * z) ^ 2 / 2 * ((Polynomial.derivative (Polynomial.derivative P)).eval z))‖
      ≤ C * ‖x‖ ^ 3 * ‖z‖ ^ 3 := by
  refine ⟨(2 : ℝ) ^ (P.natDegree) * ∑ k ∈ P.support, ‖P.coeff k‖, by positivity, ?_⟩
  intro z x hz hx
  have hA : P.eval (z * (1 - x)) = ∑ k ∈ P.support, P.coeff k * (z * (1 - x)) ^ k := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  have hB : P.eval z = ∑ k ∈ P.support, P.coeff k * z ^ k := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  have hC : z * (P.derivative).eval z = ∑ k ∈ P.support, P.coeff k * (k : ℂ) * z ^ k := by
    rw [rem_deriv_weight P z, Polynomial.sum_def]
  have hD : z ^ 2 * (P.derivative.derivative).eval z
      = ∑ k ∈ P.support, P.coeff k * ((k : ℂ) * ((k : ℂ) - 1)) * z ^ k := by
    rw [rem_deriv2_weight P z, Polynomial.sum_def]
  have hE : P.eval (z * (1 - x)) - (P.eval z - x * z * (P.derivative).eval z
      + (x * z) ^ 2 / 2 * ((P.derivative.derivative).eval z))
      = ∑ k ∈ P.support, P.coeff k * z ^ k * remG k x := by
    rw [show P.eval (z * (1 - x)) - (P.eval z - x * z * (P.derivative).eval z
        + (x * z) ^ 2 / 2 * ((P.derivative.derivative).eval z))
        = P.eval (z * (1 - x)) - P.eval z + x * (z * (P.derivative).eval z)
          - (x ^ 2 / 2) * (z ^ 2 * ((P.derivative.derivative).eval z)) by ring]
    rw [hA, hB, hC, hD, Finset.mul_sum, Finset.mul_sum]
    rw [rem_sum_merge_four]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow]; unfold remG; ring
  rw [hE]
  calc ‖∑ k ∈ P.support, P.coeff k * z ^ k * remG k x‖
      ≤ ∑ k ∈ P.support, ‖P.coeff k * z ^ k * remG k x‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ P.support, ‖P.coeff k‖ * ((2 : ℝ) ^ P.natDegree * ‖x‖ ^ 3 * ‖z‖ ^ 3) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkn : k ≤ P.natDegree :=
          Polynomial.le_natDegree_of_ne_zero ((Polynomial.mem_support_iff).mp hk)
        have hzG : ‖z‖ ^ k * ‖remG k x‖
            ≤ (2 : ℝ) ^ P.natDegree * ‖x‖ ^ 3 * ‖z‖ ^ 3 := by
          by_cases hk3 : k ≤ 2
          · have : remG k x = 0 := remG_eq_zero_of_lt_three k (by omega) x
            rw [this, norm_zero, mul_zero]; positivity
          · have hk3' : 3 ≤ k := by omega
            have hG : ‖remG k x‖ ≤ (2 : ℝ) ^ P.natDegree * ‖x‖ ^ 3 := by
              calc ‖remG k x‖ ≤ (2 : ℝ) ^ k * ‖x‖ ^ 3 := remG_bound k x hx
                _ ≤ (2 : ℝ) ^ P.natDegree * ‖x‖ ^ 3 := by
                    apply mul_le_mul_of_nonneg_right _ (by positivity)
                    exact pow_le_pow_right₀ (by norm_num) hkn
            have hzk : ‖z‖ ^ k ≤ ‖z‖ ^ 3 := by
              have hz1 : ‖z‖ ^ (k - 3) ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
              have he : ‖z‖ ^ k = ‖z‖ ^ 3 * ‖z‖ ^ (k - 3) := by
                rw [← pow_add, show 3 + (k - 3) = k by omega]
              rw [he]
              exact mul_le_of_le_one_right (by positivity) hz1
            calc ‖z‖ ^ k * ‖remG k x‖
                ≤ ‖z‖ ^ 3 * ((2 : ℝ) ^ P.natDegree * ‖x‖ ^ 3) :=
                  mul_le_mul hzk hG (norm_nonneg _) (by positivity)
              _ = (2 : ℝ) ^ P.natDegree * ‖x‖ ^ 3 * ‖z‖ ^ 3 := by ring
        rw [norm_mul, norm_mul, norm_pow]
        calc ‖P.coeff k‖ * ‖z‖ ^ k * ‖remG k x‖
            = ‖P.coeff k‖ * (‖z‖ ^ k * ‖remG k x‖) := by ring
          _ ≤ ‖P.coeff k‖ * ((2 : ℝ) ^ P.natDegree * ‖x‖ ^ 3 * ‖z‖ ^ 3) :=
              mul_le_mul_of_nonneg_left hzG (norm_nonneg _)
    _ = (∑ k ∈ P.support, ‖P.coeff k‖) * ((2 : ℝ) ^ P.natDegree * ‖x‖ ^ 3 * ‖z‖ ^ 3) := by
        rw [Finset.sum_mul]
    _ = ((2 : ℝ) ^ P.natDegree * ∑ k ∈ P.support, ‖P.coeff k‖) * ‖x‖ ^ 3 * ‖z‖ ^ 3 := by
        ring

end Work.FatouDeg.Petal
