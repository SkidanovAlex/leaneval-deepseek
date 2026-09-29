import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NormNum.NatFactorial

namespace Commons.Analysis.InfiniteSum

open Finset

/-- The descending factorial `n·(n−1)⋯(n−k+1)`, cast to `ℝ`, equals the product
`∏_{i<k} (n − i)` for every natural `n` (for `n < k` the product contains the
zero factor `n − n`). -/
private lemma descFactorial_cast_prod (n k : ℕ) :
    (Nat.descFactorial n k : ℝ) = ∏ j ∈ Finset.range k, ((n : ℝ) - (j : ℝ)) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Nat.descFactorial_succ, Nat.cast_mul]
      rw [ih, Finset.prod_range_succ]
      by_cases hk : k ≤ n
      · have hsub : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := Nat.cast_sub hk
        rw [hsub]
        ring
      · have hnlt : n < k := Nat.lt_of_not_ge hk
        have hP : (∏ j ∈ Finset.range k, ((n : ℝ) - (j : ℝ))) = 0 := by
          refine Finset.prod_eq_zero (i := n) ?_ ?_
          · exact Finset.mem_range.mpr hnlt
          · simp
        have hzero : ((n - k : ℕ) : ℝ) = 0 := by
          rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hnlt)]
          norm_num
        rw [hP, hzero]
        simp

/-- The moment series of the falling factorials:
`Σₙ (n).descFactorial(k)·Xⁿ = k!·Xᵏ/(1−X)^(k+1)` for `‖X‖ < 1`. -/
private lemma descFactorial_geom_hasSum (k : ℕ) {X : ℝ} (hX : ‖X‖ < 1) :
    HasSum (fun n : ℕ => (Nat.descFactorial n k : ℝ) * X ^ n)
      ((k.factorial : ℝ) * X ^ k / (1 - X) ^ (k + 1)) := by
  let f : ℕ → ℝ := fun n => (Nat.descFactorial n k : ℝ) * X ^ n
  have h0 : HasSum (fun m : ℕ => ((m + k).choose k : ℝ) * X ^ m)
      (1 / (1 - X) ^ (k + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) k hX
  -- multiply the `(m + k).choose k`-series by `k! · X^k`
  have hshift : HasSum (fun m : ℕ => f (m + k))
      ((k.factorial : ℝ) * X ^ k * (1 / (1 - X) ^ (k + 1))) := by
    have h0m := h0.mul_left ((k.factorial : ℝ) * X ^ k)
    refine h0m.congr_fun ?_
    intro m
    dsimp [f]
    have hdf : (Nat.descFactorial (m + k) k : ℝ) =
        (k.factorial : ℝ) * ((m + k).choose k : ℝ) := by
      exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose (m + k) k)
    rw [hdf, pow_add]
    ring
  -- the initial `n < k` terms vanish, so the shifted series has the same sum
  have hfin : (∑ i ∈ Finset.range k, f i) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hil : i < k := Finset.mem_range.mp hi
    dsimp [f]
    have hd : (Nat.descFactorial i k : ℝ) = 0 := by
      rw [descFactorial_cast_prod i k]
      refine Finset.prod_eq_zero (i := i) ?_ ?_
      · exact Finset.mem_range.mpr hil
      · simp
    rw [hd]
    simp
  have hφ : HasSum (fun m : ℕ => f (m + k))
      ((k.factorial : ℝ) * X ^ k / (1 - X) ^ (k + 1) -
        ∑ i ∈ Finset.range k, f i) := by
    convert hshift using 1
    rw [div_eq_mul_inv]
    simp [one_div, hfin]
  exact (hasSum_nat_add_iff' (f := f) k).mp hφ

/-- `Σₙ n⁴·Xⁿ = X(1+11X+11X²+X³)/(1−X)⁵` for real `‖X‖ < 1` (fourth moment of the geometric series). -/
lemma nat_pow4_geom_hasSum {X : ℝ} (hX : ‖X‖ < 1) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 4 * X ^ n) (X * (1 + 11 * X + 11 * X ^ 2 + X ^ 3) / (1 - X) ^ 5) := by
  have hxne1 : X ≠ 1 := by
    intro hx1
    have : ‖X‖ = (1 : ℝ) := by simp [hx1]
    linarith
  have h1m : 1 - X ≠ 0 := sub_ne_zero.mpr (Ne.symm hxne1)
  -- coefficient identity n⁴ = n + 7·n(n−1) + 6·n(n−1)(n−2) + n(n−1)(n−2)(n−3)
  have hc (n : ℕ) : (n : ℝ) ^ 4 =
      (Nat.descFactorial n 1 : ℝ) + 7 * (Nat.descFactorial n 2 : ℝ) +
        6 * (Nat.descFactorial n 3 : ℝ) + (Nat.descFactorial n 4 : ℝ) := by
    rw [descFactorial_cast_prod n 1, descFactorial_cast_prod n 2,
      descFactorial_cast_prod n 3, descFactorial_cast_prod n 4]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero,
      Nat.cast_ofNat, sub_zero]
    ring
  -- the four falling-factorial moment series
  have h1 := descFactorial_geom_hasSum 1 hX
  have h2 := descFactorial_geom_hasSum 2 hX
  have h3 := descFactorial_geom_hasSum 3 hX
  have h4 := descFactorial_geom_hasSum 4 hX
  -- combine them with the Stirling weights 1, 7, 6, 1
  have G : HasSum
      (fun n : ℕ => (((Nat.descFactorial n 1 : ℝ) * X ^ n + 7 * ((Nat.descFactorial n 2 : ℝ) * X ^ n)) +
          6 * ((Nat.descFactorial n 3 : ℝ) * X ^ n)) + (Nat.descFactorial n 4 : ℝ) * X ^ n)
      ((((Nat.factorial 1 : ℝ) * X ^ 1 / (1 - X) ^ 2 +
          7 * ((Nat.factorial 2 : ℝ) * X ^ 2 / (1 - X) ^ 3)) +
        6 * ((Nat.factorial 3 : ℝ) * X ^ 3 / (1 - X) ^ 4)) +
      (Nat.factorial 4 : ℝ) * X ^ 4 / (1 - X) ^ 5) := by
    exact (((h1.add (h2.mul_left 7)).add (h3.mul_left 6)).add h4)
  -- assemble the coefficient of X^n into n⁴
  have hpt : ∀ n : ℕ, (n : ℝ) ^ 4 * X ^ n =
      (((Nat.descFactorial n 1 : ℝ) * X ^ n + 7 * ((Nat.descFactorial n 2 : ℝ) * X ^ n)) +
          6 * ((Nat.descFactorial n 3 : ℝ) * X ^ n)) + (Nat.descFactorial n 4 : ℝ) * X ^ n := by
    intro n
    rw [hc n]
    ring
  have H' : HasSum (fun n : ℕ => (n : ℝ) ^ 4 * X ^ n)
      ((((Nat.factorial 1 : ℝ) * X ^ 1 / (1 - X) ^ 2 +
          7 * ((Nat.factorial 2 : ℝ) * X ^ 2 / (1 - X) ^ 3)) +
        6 * ((Nat.factorial 3 : ℝ) * X ^ 3 / (1 - X) ^ 4)) +
      (Nat.factorial 4 : ℝ) * X ^ 4 / (1 - X) ^ 5) := G.congr_fun hpt
  -- value: X/(1−X)² + 14X²/(1−X)³ + 36X³/(1−X)⁴ + 24X⁴/(1−X)⁵ = X(1+11X+11X²+X³)/(1−X)⁵
  convert H' using 1
  field_simp [h1m]
  ring

end Commons.Analysis.InfiniteSum