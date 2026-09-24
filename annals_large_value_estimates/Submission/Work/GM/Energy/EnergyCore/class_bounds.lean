import Mathlib
import Submission.Work.GM.Energy.EnergyCore.FourthMomentDefs

/-!
# GM §11: the four dyadic-class bounds

Writing `n = |W|`, `c = #(clsSet W j)`, `z = 2^j` and `E = E(W)`, the fifth-moment
(LP) estimates of GM §11 rest on two elementary counting facts about a single dyadic
class `U_j = clsSet W j` of representations of `⌊t₁-t₂⌋`:

* `z · c ≤ n²` (every key of `U_j` is represented at least `z` times, and the total
  number of pairs is `n²`), and
* `z² · c ≤ E` (there are `c` keys each with at least `z²` ordered pairs of
  representations, all of which contribute to the additive energy).

The four inequalities below are the purely algebraic consequences of these two facts
that the §11 argument uses (they are the `B`, `B²`, interpolated and squared forms).
-/

namespace Work.GM.Energy.EnergyCore

open Complex Finset
open scoped BigOperators
set_option autoImplicit false

/-! ## The two counting facts, in `ℕ` -/

/-- `z · c ≤ n²`: a whole dyadic class of keys carries `z = 2^j` pairs per key. -/
lemma clsSet_pow_mul_card_le (W : Finset ℝ) (j : ℕ) :
    (2 : ℕ) ^ j * (clsSet W j).card ≤ W.card * W.card := by
  have h1 : (2 : ℕ) ^ j * (clsSet W j).card = ∑ u ∈ clsSet W j, 2 ^ j := by
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    simp
  rw [h1]
  calc ∑ u ∈ clsSet W j, 2 ^ j
      ≤ ∑ u ∈ clsSet W j, repCount W u :=
        Finset.sum_le_sum (fun u hu => clsSet_pow_le hu)
    _ ≤ ∑ u ∈ keySet W, repCount W u :=
        Finset.sum_le_sum_of_subset_of_nonneg (clsSet_subset j)
          (fun _ _ _ => Nat.zero_le _)
    _ = W.card * W.card := sum_repCount

/-- `z² · c ≤ E`: each key of the class contributes at least `z²` to the energy. -/
lemma clsSet_sq_mul_card_le_energy (W : Finset ℝ) (j : ℕ) :
    ((2 : ℕ) ^ j) ^ 2 * (clsSet W j).card ≤ Submission.GM.energy W := by
  calc ((2 : ℕ) ^ j) ^ 2 * (clsSet W j).card
      ≤ ∑ u ∈ clsSet W j, (repCount W u) ^ 2 := clsSet_sq_mul_card_le j
    _ ≤ ∑ u ∈ keySet W, (repCount W u) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (clsSet_subset j)
          (fun _ _ _ => Nat.zero_le _)
    _ ≤ Submission.GM.energy W := sum_repCount_sq_le_energy W

/-! ## The elementary real arithmetic -/

/-- For `z, c ≥ 0`, `z² c^{5/4} = (z²c)^{3/4} (zc)^{1/2}`. -/
lemma rpow_class_identity {z c : ℝ} (hz : 0 ≤ z) (hc : 0 ≤ c) :
    z^2 * c^((5 : ℝ) / 4) = (z^2 * c)^((3 : ℝ) / 4) * (z * c)^((1 : ℝ) / 2) := by
  have hz2 : 0 ≤ z^2 := sq_nonneg z
  have h1 : (z^2)^((3 : ℝ) / 4) = z^((3 : ℝ) / 2) := by
    rw [show (z^2 : ℝ) = z ^ (2 : ℝ) from (Real.rpow_two z).symm,
      ← Real.rpow_mul hz (2 : ℝ) ((3 : ℝ) / 4)]
    norm_num
  have h2 : z^((3 : ℝ) / 2) * z^((1 : ℝ) / 2) = z^2 := by
    rw [← Real.rpow_add_of_nonneg hz (by norm_num : (0 : ℝ) ≤ 3 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [show (3 : ℝ) / 2 + 1 / 2 = 2 by norm_num, Real.rpow_two]
  have h3 : c^((3 : ℝ) / 4) * c^((1 : ℝ) / 2) = c^((5 : ℝ) / 4) := by
    rw [← Real.rpow_add_of_nonneg hc (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  rw [Real.mul_rpow hz2 hc, Real.mul_rpow hz hc, h1]
  rw [show z^((3 : ℝ) / 2) * c^((3 : ℝ) / 4) * (z^((1 : ℝ) / 2) * c^((1 : ℝ) / 2))
        = (z^((3 : ℝ) / 2) * z^((1 : ℝ) / 2)) * (c^((3 : ℝ) / 4) * c^((1 : ℝ) / 2)) by ring]
  rw [h2, h3]

/-- Given `z · c ≤ n²` and `z² · c ≤ E` (with `z ≥ 1`, everything nonnegative), the four
class bounds hold. -/
lemma class_bound_ineqs {z c E n : ℝ} (hz : 0 ≤ z) (hz1 : 1 ≤ z) (hc : 0 ≤ c)
    (hE : 0 ≤ E) (hn : 0 ≤ n) (h1 : z * c ≤ n^2) (h2 : z^2 * c ≤ E) :
    (z * c)^2 ≤ n^4 ∧ z^2 * c ≤ E ∧
      z^2 * c^((5 : ℝ) / 4) ≤ E^((3 : ℝ) / 4) * n ∧ z^2 * c^2 ≤ E * n^2 := by
  have hz2c : 0 ≤ z^2 * c := mul_nonneg (sq_nonneg z) hc
  refine ⟨?_, h2, ?_, ?_⟩
  · have hh := pow_le_pow_left₀ (mul_nonneg hz hc) h1 2
    have hn4 : (n^2)^2 = n^4 := by ring
    linarith
  · rw [rpow_class_identity hz hc]
    refine mul_le_mul (Real.rpow_le_rpow hz2c h2 (by norm_num)) ?_
      (Real.rpow_nonneg (mul_nonneg hz hc) _) (Real.rpow_nonneg hE _)
    have hr := Real.rpow_le_rpow (mul_nonneg hz hc) h1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hs : (n^2)^((1 : ℝ) / 2) = n := by
      rw [show (n^2 : ℝ) = n ^ (2 : ℝ) from (Real.rpow_two n).symm, ← Real.rpow_mul hn]
      rw [show (2 : ℝ) * ((1 : ℝ) / 2) = 1 by norm_num, Real.rpow_one]
    rwa [hs] at hr
  · calc z^2 * c^2 ≤ z^3 * c^2 := by
          have : z^2 ≤ z^3 := by nlinarith [hz, hz1]
          exact mul_le_mul_of_nonneg_right this (sq_nonneg c)
      _ = z^2 * c * (z * c) := by ring
      _ ≤ E * n^2 := mul_le_mul h2 h1 (mul_nonneg hz hc) hE

/-- **The four dyadic-class bounds.**  For any finite `W ⊆ ℝ` and any `j`,
with `c = #(clsSet W j)` and `z = 2^j`:
`(z c)² ≤ |W|⁴`, `z² c ≤ E(W)`, `z² c^{5/4} ≤ E(W)^{3/4} |W|`, and
`z² c² ≤ E(W) |W|²`. -/
theorem class_bounds (W : Finset ℝ) (j : ℕ) :
    ((2 : ℝ) ^ j * (clsSet W j).card) ^ 2 ≤ (W.card : ℝ) ^ 4 ∧
    ((2 : ℝ) ^ j) ^ 2 * (clsSet W j).card ≤ (Submission.GM.energy W : ℝ) ∧
    ((2 : ℝ) ^ j) ^ 2 * ((clsSet W j).card : ℝ) ^ ((5 : ℝ) / 4)
        ≤ (Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ) ∧
    ((2 : ℝ) ^ j) ^ 2 * ((clsSet W j).card : ℝ) ^ 2
        ≤ (Submission.GM.energy W : ℝ) * (W.card : ℝ) ^ 2 := by
  have h1 : (2 : ℝ) ^ j * ((clsSet W j).card : ℝ) ≤ (W.card : ℝ)^2 := by
    have h := (Nat.cast_le (α := ℝ)).mpr (clsSet_pow_mul_card_le W j)
    push_cast at h
    simpa [pow_two] using h
  have h2 : ((2 : ℝ) ^ j)^2 * ((clsSet W j).card : ℝ) ≤ (Submission.GM.energy W : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr (clsSet_sq_mul_card_le_energy W j)
    push_cast at h
    simpa using h
  obtain ⟨c1, c2, c3, c4⟩ :=
    class_bound_ineqs (z := (2 : ℝ) ^ j) (c := ((clsSet W j).card : ℝ))
      (E := (Submission.GM.energy W : ℝ)) (n := (W.card : ℝ))
      (by positivity) (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      (by positivity) (by positivity) (by positivity) h1 h2
  exact ⟨c1, c2, c3, c4⟩

end Work.GM.Energy.EnergyCore
