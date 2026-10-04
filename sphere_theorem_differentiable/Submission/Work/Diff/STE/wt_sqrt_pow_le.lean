import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

/-!
# The square-root weight inequality for the torus Fourier weight

`wt k = 1 + Σᵢ kᵢ²` is the (squared) weight `⟨k⟩²` on the dual lattice `ℤ^ι`.  This file
proves the *additive* form of the slowly-varying inequality for the square root of the weight,
`√(wt k) ≤ 2 (√(wt l) + √(wt (k - l)))`, and raises it to a power `s`, which is the shape in
which the weighted `ℓ²` (Sobolev) estimates of Layer A consume it.

The two ingredients are

* `wt k ≤ 4 (wt l + wt (k - l))`, proved coordinatewise from `(x + y)² ≤ 2x² + 2y²`;
* `(a + b)^s ≤ 2^s (a^s + b^s)` for `a, b ≥ 0` (Mathlib's `add_pow_le` plus `2^(s-1) ≤ 2^s`).
-/

/-- `√(a + b) ≤ √a + √b` for `a, b ≥ 0`. -/
private lemma sqrt_add_le_sqrt_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), ?_⟩
  have hsq : (Real.sqrt a + Real.sqrt b) ^ 2 = a + b + 2 * (Real.sqrt a * Real.sqrt b) := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]; ring
  rw [hsq]
  nlinarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- `(a + b)^s ≤ 2^s (a^s + b^s)` for `a, b ≥ 0`. -/
private lemma add_pow_le_two_pow_mul (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (s : ℕ) :
    (a + b) ^ s ≤ 2 ^ s * (a ^ s + b ^ s) := by
  have h := add_pow_le ha hb s
  have h2 : (2 : ℝ) ^ (s - 1) ≤ 2 ^ s := pow_le_pow_right₀ (by norm_num) (Nat.sub_le s 1)
  have hZ : 0 ≤ a ^ s + b ^ s := add_nonneg (pow_nonneg ha s) (pow_nonneg hb s)
  exact h.trans (mul_le_mul_of_nonneg_right h2 hZ)

/-- The **additive** slowly varying inequality for `wt`: `wt k ≤ 4 (wt l + wt (k - l))`.

This is the form suited to the square root: `(x + y)² ≤ 2x² + 2y²` coordinatewise gives
`Σ kᵢ² ≤ 2Σ lᵢ² + 2Σ (k - l)ᵢ²`, hence `1 + Σ kᵢ² ≤ 4 ((1 + Σ lᵢ²) + (1 + Σ (k - l)ᵢ²))`. -/
private lemma wt_le_four_add {ι : Type*} [Fintype ι] (k l : ι → ℤ) :
    wt k ≤ 4 * (wt l + wt (k - l)) := by
  classical
  have hcoord : ∀ i : ι,
      ((k i : ℤ) : ℝ) ^ 2 ≤ 2 * ((l i : ℤ) : ℝ) ^ 2 + 2 * (((k - l) i : ℤ) : ℝ) ^ 2 := by
    intro i
    have hkl : ((k - l) i : ℤ) = k i - l i := Pi.sub_apply k l i
    have hcast : ((k i : ℤ) : ℝ) = ((l i : ℤ) : ℝ) + (((k - l) i : ℤ) : ℝ) := by
      rw [hkl]; push_cast; ring
    rw [hcast]
    nlinarith [sq_nonneg (((l i : ℤ) : ℝ) - (((k - l) i : ℤ) : ℝ))]
  have hsum : ∑ i, ((k i : ℤ) : ℝ) ^ 2
      ≤ 2 * (∑ i, ((l i : ℤ) : ℝ) ^ 2) + 2 * (∑ i, (((k - l) i : ℤ) : ℝ) ^ 2) := by
    calc ∑ i, ((k i : ℤ) : ℝ) ^ 2
        ≤ ∑ i, (2 * ((l i : ℤ) : ℝ) ^ 2 + 2 * (((k - l) i : ℤ) : ℝ) ^ 2) :=
          Finset.sum_le_sum fun i _ => hcoord i
      _ = (∑ i, 2 * ((l i : ℤ) : ℝ) ^ 2) + ∑ i, 2 * (((k - l) i : ℤ) : ℝ) ^ 2 :=
          Finset.sum_add_distrib
      _ = 2 * (∑ i, ((l i : ℤ) : ℝ) ^ 2) + 2 * (∑ i, (((k - l) i : ℤ) : ℝ) ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum]
  have hA : (0 : ℝ) ≤ ∑ i, ((l i : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : (0 : ℝ) ≤ ∑ i, (((k - l) i : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  simp only [wt]
  linarith

theorem wt_sqrt_pow_le {ι : Type*} [Fintype ι] (s : ℕ) (k l : ι → ℤ) :
    (Real.sqrt (Work.Diff.STE.wt k)) ^ s
      ≤ 2 ^ (2 * s) * ((Real.sqrt (Work.Diff.STE.wt l)) ^ s
          + (Real.sqrt (Work.Diff.STE.wt (k - l))) ^ s) := by
  classical
  have h4 : wt k ≤ 4 * (wt l + wt (k - l)) := wt_le_four_add k l
  have hwl : 0 ≤ wt l := le_of_lt (wt_pos l)
  have hwm : 0 ≤ wt (k - l) := le_of_lt (wt_pos (k - l))
  have hsqrt : Real.sqrt (wt k) ≤ 2 * (Real.sqrt (wt l) + Real.sqrt (wt (k - l))) := by
    calc Real.sqrt (wt k) ≤ Real.sqrt (4 * (wt l + wt (k - l))) := Real.sqrt_le_sqrt h4
      _ = 2 * Real.sqrt (wt l + wt (k - l)) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
      _ ≤ 2 * (Real.sqrt (wt l) + Real.sqrt (wt (k - l))) := by
          linarith [sqrt_add_le_sqrt_add (wt l) (wt (k - l)) hwl hwm]
  calc (Real.sqrt (wt k)) ^ s
      ≤ (2 * (Real.sqrt (wt l) + Real.sqrt (wt (k - l)))) ^ s :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt s
    _ = 2 ^ s * (Real.sqrt (wt l) + Real.sqrt (wt (k - l))) ^ s := by rw [mul_pow]
    _ ≤ 2 ^ s * (2 ^ s * ((Real.sqrt (wt l)) ^ s + (Real.sqrt (wt (k - l))) ^ s)) := by
        apply mul_le_mul_of_nonneg_left _
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s)
        exact add_pow_le_two_pow_mul (Real.sqrt (wt l)) (Real.sqrt (wt (k - l)))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) s
    _ = 2 ^ (2 * s) * ((Real.sqrt (wt l)) ^ s + (Real.sqrt (wt (k - l))) ^ s) := by
        rw [← mul_assoc, ← pow_add]
        congr 1
        rw [← two_mul]

end Work.Diff.STE
