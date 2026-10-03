/-
# `Work.FIArea2.R6.Hbox6Axis` — definitions for the axis box sum

This module fixes the definitions used by the proof of `Work.FIArea2.R6.hbox6_axis`:
the integer box `boxZ N = [-N,N]`, the divisor function `tauZ` on `ℤ`, the gcd weight
`gcdZ`, the full axis sum `AxisSum`, and its four (disjoint) indicator slices
`A1, A2, A3, A4`.

The target result is
`AxisSum R X Y ≤ C * R^2 * X * Y * (log (R+X+Y+2))^300`,
and `AxisSum R X Y = A1 + A2 + A3 + A4` decomposes the indicator
`u1 = 0 ∨ u2 = 0 ∨ h1 = 0 ∨ h2 = 0` into its four disjoint cases.

Elementary facts (nonnegativity, zero cases, size bounds, sub-multiplicativity of `tauZ`)
are collected here; the four slice bounds and the final assembly live one level up.
-/
import Mathlib
import Submission.Work.FIArea2.sum_tau_pow_le
import Submission.Work.FIArea2.sum_tau_pow_div_le
import Submission.Work.FIArea2.Count.sum_int_natAbs_le
import Submission.Work.FIArea2.Count.sec9_box4_rect_helpers
import Submission.Work.FIArea2.Count.sum_gcd_le_mul_card_divisors

namespace Work.FIArea2.R6.Hbox6Axis

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

set_option exponentiation.threshold 600

/-- The integer box `[-N,N]`, as a `Finset ℤ`. -/
def boxZ (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)

/-- `τ(m) = #(m.natAbs).divisors`, viewed as a real number. -/
def tauZ (m : ℤ) : ℝ := ((m.natAbs).divisors.card : ℝ)

/-- The gcd weight `gcd(|u1|,|u2|)`, viewed as a real number. -/
def gcdZ (u1 u2 : ℤ) : ℝ := (Nat.gcd u1.natAbs u2.natAbs : ℝ)

/-- The axis sum of the Friedlander–Iwaniec box: the full left-hand side of `hbox6_axis`. -/
def AxisSum (R X Y : ℕ) : ℝ :=
  ∑ u1 ∈ boxZ R, ∑ u2 ∈ boxZ R, ∑ h1 ∈ boxZ X, ∑ h2 ∈ boxZ Y,
    (if u1 = 0 ∨ u2 = 0 ∨ h1 = 0 ∨ h2 = 0 then gcdZ u1 u2 else 0)
      * tauZ (u1 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4

/-- The slice `u1 = 0`. -/
def A1 (R X Y : ℕ) : ℝ :=
  ∑ u1 ∈ boxZ R, ∑ u2 ∈ boxZ R, ∑ h1 ∈ boxZ X, ∑ h2 ∈ boxZ Y,
    (if u1 = 0 then gcdZ u1 u2 else 0) * tauZ (u1 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4

/-- The slice `u1 ≠ 0`, `u2 = 0`. -/
def A2 (R X Y : ℕ) : ℝ :=
  ∑ u1 ∈ boxZ R, ∑ u2 ∈ boxZ R, ∑ h1 ∈ boxZ X, ∑ h2 ∈ boxZ Y,
    (if u1 ≠ 0 ∧ u2 = 0 then gcdZ u1 u2 else 0) * tauZ (u1 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4

/-- The slice `u1 ≠ 0`, `u2 ≠ 0`, `h1 = 0`. -/
def A3 (R X Y : ℕ) : ℝ :=
  ∑ u1 ∈ boxZ R, ∑ u2 ∈ boxZ R, ∑ h1 ∈ boxZ X, ∑ h2 ∈ boxZ Y,
    (if (u1 ≠ 0 ∧ u2 ≠ 0) ∧ h1 = 0 then gcdZ u1 u2 else 0)
      * tauZ (u1 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4

/-- The slice `u1 ≠ 0`, `u2 ≠ 0`, `h1 ≠ 0`, `h2 = 0`. -/
def A4 (R X Y : ℕ) : ℝ :=
  ∑ u1 ∈ boxZ R, ∑ u2 ∈ boxZ R, ∑ h1 ∈ boxZ X, ∑ h2 ∈ boxZ Y,
    (if ((u1 ≠ 0 ∧ u2 ≠ 0) ∧ h1 ≠ 0) ∧ h2 = 0 then gcdZ u1 u2 else 0)
      * tauZ (u1 * h1 ^ 2 - u2 * h2 ^ 2) ^ 4

/-! ## Elementary facts -/

lemma tauZ_nonneg (m : ℤ) : 0 ≤ tauZ m := Nat.cast_nonneg _

lemma gcdZ_nonneg (u1 u2 : ℤ) : 0 ≤ gcdZ u1 u2 := Nat.cast_nonneg _

lemma tauZ_zero : tauZ 0 = 0 := by simp [tauZ]

lemma gcdZ_zero_left (u2 : ℤ) : gcdZ 0 u2 = (u2.natAbs : ℝ) := by simp [gcdZ]

lemma gcdZ_zero_right (u1 : ℤ) : gcdZ u1 0 = (u1.natAbs : ℝ) := by simp [gcdZ]

lemma gcdZ_comm (u1 u2 : ℤ) : gcdZ u1 u2 = gcdZ u2 u1 := by
  simp [gcdZ, Nat.gcd_comm]

lemma gcdZ_le_left_of_ne {u1 u2 : ℤ} (h : u1 ≠ 0) : gcdZ u1 u2 ≤ (u1.natAbs : ℝ) := by
  have hpos : 0 < u1.natAbs := Int.natAbs_pos.mpr h
  have := Nat.gcd_le_left (m := u1.natAbs) u2.natAbs hpos
  simp only [gcdZ]
  exact_mod_cast this

lemma gcdZ_le_right_of_ne {u1 u2 : ℤ} (h : u2 ≠ 0) : gcdZ u1 u2 ≤ (u2.natAbs : ℝ) := by
  rw [gcdZ_comm]; exact gcdZ_le_left_of_ne h

lemma tauZ_intCast (n : ℕ) : tauZ (n : ℤ) = ((n.divisors.card : ℝ)) := by simp [tauZ]

/-- `τ(m·n²)⁴ ≤ τ(m)⁴·τ(n)⁸`, for integers. -/
lemma tauZ_mul_sq_pow4_le (m n : ℤ) :
    tauZ (m * n ^ 2) ^ 4 ≤ tauZ m ^ 4 * tauZ n ^ 8 := by
  have h := Work.FIArea2.Count.tau_mul_sq_pow4_le m.natAbs n.natAbs
  have e : (m * n ^ 2).natAbs = m.natAbs * n.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_pow]
  simpa only [tauZ, e] using h

lemma mem_boxZ {N : ℕ} {u : ℤ} : u ∈ boxZ N ↔ -(N : ℤ) ≤ u ∧ u ≤ N := by
  simp [boxZ]

lemma natAbs_le_of_mem_boxZ {N : ℕ} {u : ℤ} (hu : u ∈ boxZ N) : u.natAbs ≤ N := by
  rw [mem_boxZ] at hu
  have h : |u| ≤ (N : ℤ) := abs_le.mpr hu
  have h2 : (u.natAbs : ℤ) ≤ (N : ℤ) := by rw [Int.natCast_natAbs]; exact h
  exact_mod_cast h2

lemma zero_mem_boxZ (N : ℕ) : (0 : ℤ) ∈ boxZ N := by
  rw [mem_boxZ]; constructor <;> simp

lemma gcdZ_le_box (R : ℕ) {u1 u2 : ℤ} (hu1 : u1 ∈ boxZ R) (hu2 : u2 ∈ boxZ R) :
    gcdZ u1 u2 ≤ (R : ℝ) := by
  rcases eq_or_ne u1 0 with h | h
  · subst h
    rw [gcdZ_zero_left]
    exact_mod_cast natAbs_le_of_mem_boxZ hu2
  · exact le_trans (gcdZ_le_left_of_ne h) (by exact_mod_cast natAbs_le_of_mem_boxZ hu1)

/-- `∑_{u ∈ boxZ N} f u = ∑_{u ∈ boxZ N, u ≠ 0} f u + f 0`. -/
lemma sum_boxZ_eq_filter_add (N : ℕ) (f : ℤ → ℝ) :
    ∑ u ∈ boxZ N, f u = ∑ u ∈ (boxZ N).filter (fun u => u ≠ 0), f u + f 0 := by
  have h := Finset.sum_filter_add_sum_filter_not (boxZ N) (fun u => u ≠ 0) f
  rw [← h]
  congr 1
  have hz : (boxZ N).filter (fun u => ¬ u ≠ 0) = {0} := by
    ext u
    simp only [Finset.mem_filter, mem_boxZ, not_not, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, rfl⟩; exact rfl
    · rintro rfl
      exact ⟨⟨by simp, by simp⟩, rfl⟩
  rw [hz, Finset.sum_singleton]

/-- Nonnegativity of a four-fold box sum with nonnegative summand. -/
lemma sum4_nonneg (s1 s2 s3 s4 : Finset ℤ) (F : ℤ → ℤ → ℤ → ℤ → ℝ)
    (h : ∀ a b c d, 0 ≤ F a b c d) :
    0 ≤ ∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4, F a b c d := by
  apply Finset.sum_nonneg; intro a _
  apply Finset.sum_nonneg; intro b _
  apply Finset.sum_nonneg; intro c _
  apply Finset.sum_nonneg; intro d _
  exact h a b c d

lemma A1_nonneg (R X Y : ℕ) : 0 ≤ A1 R X Y := by
  rw [A1]
  refine sum4_nonneg _ _ _ _ _ (fun a b c d => ?_)
  split_ifs with h
  · exact mul_nonneg (gcdZ_nonneg _ _) (pow_nonneg (tauZ_nonneg _) _)
  · rw [zero_mul]

lemma A2_nonneg (R X Y : ℕ) : 0 ≤ A2 R X Y := by
  rw [A2]
  refine sum4_nonneg _ _ _ _ _ (fun a b c d => ?_)
  split_ifs with h
  · exact mul_nonneg (gcdZ_nonneg _ _) (pow_nonneg (tauZ_nonneg _) _)
  · rw [zero_mul]

lemma A3_nonneg (R X Y : ℕ) : 0 ≤ A3 R X Y := by
  rw [A3]
  refine sum4_nonneg _ _ _ _ _ (fun a b c d => ?_)
  split_ifs with h
  · exact mul_nonneg (gcdZ_nonneg _ _) (pow_nonneg (tauZ_nonneg _) _)
  · rw [zero_mul]

lemma A4_nonneg (R X Y : ℕ) : 0 ≤ A4 R X Y := by
  rw [A4]
  refine sum4_nonneg _ _ _ _ _ (fun a b c d => ?_)
  split_ifs with h
  · exact mul_nonneg (gcdZ_nonneg _ _) (pow_nonneg (tauZ_nonneg _) _)
  · rw [zero_mul]

lemma AxisSum_nonneg (R X Y : ℕ) : 0 ≤ AxisSum R X Y := by
  rw [AxisSum]
  refine sum4_nonneg _ _ _ _ _ (fun a b c d => ?_)
  split_ifs with h
  · exact mul_nonneg (gcdZ_nonneg _ _) (pow_nonneg (tauZ_nonneg _) _)
  · rw [zero_mul]


/-! ## Indicator algebra -/

lemma tauZ_neg (m : ℤ) : tauZ (-m) = tauZ m := by simp [tauZ]

lemma tauZ_natAbs (m : ℤ) : tauZ (m.natAbs : ℤ) = tauZ m := by
  simp only [tauZ, Int.natAbs_natCast]

/-- Splitting the axis indicator into its four disjoint cases. -/
lemma indicator_split (g : ℝ) (u1 u2 h1 h2 : ℤ) :
    (if u1 = 0 ∨ u2 = 0 ∨ h1 = 0 ∨ h2 = 0 then g else 0)
      = (if u1 = 0 then g else 0) + (if u1 ≠ 0 ∧ u2 = 0 then g else 0)
        + (if (u1 ≠ 0 ∧ u2 ≠ 0) ∧ h1 = 0 then g else 0)
        + (if ((u1 ≠ 0 ∧ u2 ≠ 0) ∧ h1 ≠ 0) ∧ h2 = 0 then g else 0) := by
  by_cases h1' : u1 = 0
  · simp [h1']
  · by_cases h2' : u2 = 0
    · simp [h1', h2']
    · by_cases h3' : h1 = 0
      · simp [h1', h2', h3']
      · by_cases h4' : h2 = 0
        · simp [h1', h2', h3', h4']
        · simp [h1', h2', h3', h4']

/-- `∑_{x ∈ s} (if x = 0 then g x else 0) = g 0` when `0 ∈ s`. -/
lemma sum_ite_zero (s : Finset ℤ) (h0 : (0 : ℤ) ∈ s) (g : ℤ → ℝ) :
    (∑ x ∈ s, (if x = 0 then g x else 0)) = g 0 := by
  rw [Finset.sum_ite_eq' s 0 g, if_pos h0]

/-- `∑_{x ∈ s} (if x = 0 then g else 0) * t x = g * t 0` when `0 ∈ s`. -/
lemma sum_ite_zero_mul (s : Finset ℤ) (h0 : (0 : ℤ) ∈ s) (g : ℝ) (t : ℤ → ℝ) :
    (∑ x ∈ s, (if x = 0 then g else 0) * t x) = g * t 0 := by
  have h1 : ∀ x : ℤ, (if x = 0 then g else 0) * t x = (if x = 0 then g * t x else 0) := by
    intro x; by_cases h : x = 0 <;> simp [h]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), sum_ite_zero s h0 (fun x => g * t x)]

/-- `∑_{x ∈ s} (if A ∧ x = 0 then g else 0) * t x = if A then g * t 0 else 0` when `0 ∈ s`. -/
lemma sum_ite_and_zero_mul (s : Finset ℤ) (A : Prop) [Decidable A] (h0 : (0 : ℤ) ∈ s)
    (g : ℝ) (t : ℤ → ℝ) :
    (∑ x ∈ s, (if A ∧ x = 0 then g else 0) * t x) = (if A then g * t 0 else 0) := by
  by_cases hA : A
  · have hpt : ∀ x : ℤ, (if A ∧ x = 0 then g else 0) * t x = (if x = 0 then g * t x else 0) := by
      intro x
      by_cases hx : x = 0
      · rw [if_pos ⟨hA, hx⟩, if_pos hx]
      · rw [if_neg (fun h => hx h.2), if_neg hx, zero_mul]
    rw [Finset.sum_congr rfl (fun x _ => hpt x), sum_ite_zero s h0 (fun x => g * t x), if_pos hA]
  · have hpt : ∀ x : ℤ, (if A ∧ x = 0 then g else 0) * t x = 0 := by
      intro x; rw [if_neg (fun h => hA h.1), zero_mul]
    rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_const_zero, if_neg hA]

/-- Dropping a conjunction from an indicator, for nonnegative `g`. -/
lemma ite_and_le_ite (A B : Prop) [Decidable A] [Decidable B] {g : ℝ} (hg : 0 ≤ g) :
    (if A ∧ B then g else 0) ≤ (if B then g else 0) := by
  by_cases hB : B <;> by_cases hA : A <;> simp [hB, hA, hg]

/-! ## Sum manipulations -/

/-- Two-fold nonnegativity of a box sum. -/
lemma sum2_nonneg (s1 s2 : Finset ℤ) (F : ℤ → ℤ → ℝ) (h : ∀ a b, 0 ≤ F a b) :
    0 ≤ ∑ a ∈ s1, ∑ b ∈ s2, F a b := by
  apply Finset.sum_nonneg; intro a _
  apply Finset.sum_nonneg; intro b _
  exact h a b

/-- Four-fold distributivity: splitting a four-term summand. -/
lemma sum4_add4 (s1 s2 s3 s4 : Finset ℤ) (F G H K : ℤ → ℤ → ℤ → ℤ → ℝ) :
    (∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4,
        (F a b c d + G a b c d + H a b c d + K a b c d))
      = (∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4, F a b c d)
        + (∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4, G a b c d)
        + (∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4, H a b c d)
        + (∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4, K a b c d) := by
  simp only [Finset.sum_add_distrib]

/-- `∑_u ∑_h c * (f u * g h) = c * (∑_u f u) * (∑_h g h)`. -/
lemma sum_sum_mul_const (s1 s2 : Finset ℤ) (c : ℝ) (f g : ℤ → ℝ) :
    (∑ u ∈ s1, ∑ h ∈ s2, c * (f u * g h)) = c * ((∑ u ∈ s1, f u) * (∑ h ∈ s2, g h)) := by
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.mul_sum]

/-- Constant sum in the *first* index: `∑_a ∑_b F b = card s1 * ∑_b F b`. -/
lemma sum_sum_const_fst (s1 s2 : Finset ℤ) (F : ℤ → ℝ) :
    (∑ a ∈ s1, ∑ b ∈ s2, F b) = (s1.card : ℝ) * ∑ b ∈ s2, F b := by
  rw [Finset.sum_const, nsmul_eq_mul]

/-- Constant sum in the *second* index: `∑_a ∑_b F a = card s2 * ∑_a F a`. -/
lemma sum_sum_const_snd (s1 s2 : Finset ℤ) (F : ℤ → ℝ) :
    (∑ a ∈ s1, ∑ b ∈ s2, F a) = (s2.card : ℝ) * ∑ a ∈ s1, F a := by
  have h1 : (∑ a ∈ s1, ∑ b ∈ s2, F a) = ∑ a ∈ s1, (s2.card : ℝ) * F a := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h1, Finset.mul_sum]

/-- The cardinality of the box `[-N,N]`. -/
lemma card_boxZ (N : ℕ) : ((boxZ N).card : ℝ) = 2 * (N : ℝ) + 1 := by
  rw [boxZ]; exact Work.FIArea2.Count.card_Icc_int N

/-- Pulling a constant condition out of a sum. -/
lemma sum_ite_const (s : Finset ℤ) (A : Prop) [Decidable A] (F : ℤ → ℝ) :
    (∑ x ∈ s, (if A then F x else 0)) = (if A then ∑ x ∈ s, F x else 0) := by
  by_cases hA : A <;> simp [hA]

/-- Monotonicity of an indicator with a nonnegative weight. -/
lemma ite_le_ite_of {A B : Prop} [Decidable A] [Decidable B] {g : ℝ} (hg : 0 ≤ g)
    (h : A → B) : (if A then g else 0) ≤ (if B then g else 0) := by
  by_cases hB : B
  · by_cases hA : A <;> simp [hA, hB, hg]
  · have hA : ¬ A := fun h' => hB (h h')
    simp [hA, hB]

/-! ## Logarithmic comparisons -/

lemma one_le_log_arg (R X Y : ℕ) (hR : 1 ≤ R) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    1 ≤ Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2) := by
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hpos : (0 : ℝ) < (R : ℝ) + (X : ℝ) + (Y : ℝ) + 2 := by linarith
  rw [Real.le_log_iff_exp_le hpos]
  linarith [Real.exp_one_lt_three]

lemma log_le_log_arg (n R X Y : ℕ) (hn : 1 ≤ n) (hnR : n ≤ R) (hR : 1 ≤ R) (hX : 1 ≤ X)
    (hY : 1 ≤ Y) :
    Real.log (n : ℝ) + 2 ≤ 3 * Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR' : (n : ℝ) ≤ (R : ℝ) := by exact_mod_cast hnR
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hpos : (0 : ℝ) < (n : ℝ) := by linarith
  have harg : (0 : ℝ) < (R : ℝ) + (X : ℝ) + (Y : ℝ) + 2 := by linarith
  have hle : (n : ℝ) ≤ (R : ℝ) + (X : ℝ) + (Y : ℝ) + 2 := by linarith
  have h1 : Real.log (n : ℝ) ≤ Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2) :=
    Real.log_le_log hpos hle
  have h2 : (1 : ℝ) ≤ Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2) := one_le_log_arg R X Y hR hX hY
  linarith

/-- A `log` of a number at least `1` is nonnegative, so `log z + 2 ≥ 0`. -/
lemma log_add_two_nonneg (n : ℕ) (hn : 1 ≤ n) : 0 ≤ Real.log (n : ℝ) + 2 := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have := Real.log_nonneg h1
  linarith

lemma log_two_le_log_arg (N R X Y : ℕ) (hN : 1 ≤ N) (hN2 : N + 2 ≤ R + X + Y + 2)
    (hR : 1 ≤ R) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    Real.log ((N : ℝ) + 2) ≤ Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hle : (N : ℝ) + 2 ≤ (R : ℝ) + (X : ℝ) + (Y : ℝ) + 2 := by
    have h2 : ((N + 2 : ℕ) : ℝ) ≤ ((R + X + Y + 2 : ℕ) : ℝ) := by exact_mod_cast hN2
    have h3 : ((R + X + Y + 2 : ℕ) : ℝ) = (R : ℝ) + (X : ℝ) + (Y : ℝ) + 2 := by push_cast; ring
    push_cast at h2
    linarith [h2, h3]
  exact Real.log_le_log (by linarith) hle

/-! ## The gcd slice -/

/-- `∑_{u1 ∈ [-R,R]} gcd(|u1|,|u2|) ≤ 3 R τ(u2)` for `u2 ∈ [-R,R]`, `u2 ≠ 0`. -/
lemma gcd_slice (R : ℕ) (u2 : ℤ) (hR : 1 ≤ R) (hu2 : u2 ∈ boxZ R) (hu2ne : u2 ≠ 0) :
    (∑ u1 ∈ boxZ R, gcdZ u1 u2) ≤ 3 * (R : ℝ) * tauZ u2 := by
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hτ1 : (1 : ℝ) ≤ tauZ u2 := by
    have habs : 1 ≤ u2.natAbs := by
      have := Int.natAbs_pos.mpr hu2ne; omega
    have hmem : (1 : ℕ) ∈ (u2.natAbs).divisors := by
      rw [Nat.mem_divisors]; exact ⟨one_dvd _, by omega⟩
    have hcard : 1 ≤ (u2.natAbs).divisors.card := Finset.card_pos.mpr ⟨1, hmem⟩
    simp only [tauZ]; exact_mod_cast hcard
  have hzero : gcdZ 0 u2 ≤ (R : ℝ) := by
    rw [gcdZ_zero_left]; exact_mod_cast natAbs_le_of_mem_boxZ hu2
  have hfilter : (∑ u1 ∈ (boxZ R).filter (fun u1 => u1 ≠ 0), gcdZ u1 u2)
      ≤ 2 * (R : ℝ) * tauZ u2 := by
    have h1 := Work.FIArea2.Count.sum_int_natAbs_le R
      (fun n => (Nat.gcd n u2.natAbs : ℝ)) (fun n => by positivity)
    have h2 := Work.FIArea2.Count.sum_gcd_le_mul_card_divisors u2.natAbs R (by omega)
    calc (∑ u1 ∈ (boxZ R).filter (fun u1 => u1 ≠ 0), gcdZ u1 u2)
        = (∑ u1 ∈ (Finset.Icc (-(R : ℤ)) (R : ℤ)).filter (fun u1 => u1 ≠ 0),
            (Nat.gcd u1.natAbs u2.natAbs : ℝ)) := by simp only [boxZ, gcdZ]
      _ ≤ 2 * ∑ a ∈ Finset.Icc 1 R, (Nat.gcd a u2.natAbs : ℝ) := h1
      _ ≤ 2 * ((R : ℝ) * tauZ u2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          simpa only [tauZ] using h2
      _ = 2 * (R : ℝ) * tauZ u2 := by ring
  have hsplit := sum_boxZ_eq_filter_add R (fun u1 => gcdZ u1 u2)
  have hRle : (R : ℝ) ≤ (R : ℝ) * tauZ u2 := by nlinarith [hR1, hτ1]
  rw [hsplit]
  linarith [hfilter, hzero, hRle]

/-! ## Box sums of powers of `τ` -/

/-- `∑_{n ∈ [-N,N]} τ(n)^k`. -/
def Bp (k N : ℕ) : ℝ := ∑ n ∈ boxZ N, tauZ n ^ k

lemma Bp_nonneg (k N : ℕ) : 0 ≤ Bp k N := by
  rw [Bp]; exact Finset.sum_nonneg (fun n _ => pow_nonneg (tauZ_nonneg n) k)

lemma Bp_bound (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      Bp k N ≤ C * (N : ℝ) * (Real.log ((N : ℝ) + 2)) ^ (2 ^ k) := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.FIArea2.sum_tau_pow_le k
  refine ⟨2 * C0 * 3 ^ (2 ^ k), by positivity, ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hbase : Real.log (N : ℝ) + 2 ≤ 3 * Real.log ((N : ℝ) + 2) := by
    have h1 : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : (1 : ℝ) ≤ Real.log ((N : ℝ) + 2) := by
      have hpos : (0 : ℝ) < (N : ℝ) + 2 := by linarith
      rw [Real.le_log_iff_exp_le hpos]
      linarith [Real.exp_one_lt_three]
    linarith
  have hsum : Bp k N ≤ 2 * ∑ a ∈ Finset.Icc 1 N, ((a.divisors.card : ℝ)) ^ k := by
    rw [Bp]
    have h := Work.FIArea2.Count.sum_int_natAbs_le N (fun n => tauZ (n : ℤ) ^ k)
      (fun n => pow_nonneg (tauZ_nonneg (n : ℤ)) k)
    have h' : (∑ u ∈ (boxZ N).filter (fun u => u ≠ 0), tauZ u ^ k)
        ≤ 2 * ∑ a ∈ Finset.Icc 1 N, tauZ (a : ℤ) ^ k := by
      simpa only [boxZ, tauZ_natAbs] using h
    rw [sum_boxZ_eq_filter_add N (fun n => tauZ n ^ k)]
    have hz : tauZ (0 : ℤ) ^ k = 0 := by
      rw [tauZ_zero]; exact zero_pow (by omega)
    rw [hz, add_zero]
    simpa only [tauZ_intCast] using h'
  calc Bp k N ≤ 2 * ∑ a ∈ Finset.Icc 1 N, ((a.divisors.card : ℝ)) ^ k := hsum
    _ ≤ 2 * (C0 * (N : ℝ) * (Real.log (N : ℝ) + 2) ^ (2 ^ k)) :=
        mul_le_mul_of_nonneg_left (hC0 N) (by norm_num)
    _ ≤ 2 * (C0 * (N : ℝ) * (3 * Real.log ((N : ℝ) + 2)) ^ (2 ^ k)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact pow_le_pow_left₀ (by linarith) hbase (2 ^ k)
    _ = 2 * C0 * 3 ^ (2 ^ k) * (N : ℝ) * (Real.log ((N : ℝ) + 2)) ^ (2 ^ k) := by
        rw [mul_pow]; ring

/-! ## The `u`-weighted box sum -/

/-- `∑_{u ∈ [-R,R]} ∑_{h ∈ [-Y,Y]} |u| τ(uh²)⁴`. -/
def Uweight (R Y : ℕ) : ℝ :=
  ∑ u ∈ boxZ R, ∑ h ∈ boxZ Y, (u.natAbs : ℝ) * tauZ (u * h ^ 2) ^ 4

lemma Uweight_nonneg (R Y : ℕ) : 0 ≤ Uweight R Y := by
  rw [Uweight]
  exact sum2_nonneg _ _ _ (fun a b => by positivity)

lemma Uweight_le (R Y : ℕ) :
    Uweight R Y ≤ (R : ℝ) * (Bp 4 R * Bp 8 Y) := by
  have hstep1 : Uweight R Y
      ≤ ∑ u ∈ boxZ R, ∑ h ∈ boxZ Y, (R : ℝ) * (tauZ u ^ 4 * tauZ h ^ 8) := by
    rw [Uweight]
    refine Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (fun h _ => ?_))
    have hle : (u.natAbs : ℝ) ≤ (R : ℝ) := by exact_mod_cast natAbs_le_of_mem_boxZ hu
    have htau : tauZ (u * h ^ 2) ^ 4 ≤ tauZ u ^ 4 * tauZ h ^ 8 := tauZ_mul_sq_pow4_le u h
    exact mul_le_mul hle htau (by positivity) (by positivity)
  refine hstep1.trans (le_of_eq ?_)
  rw [sum_sum_mul_const (boxZ R) (boxZ Y) (R : ℝ)
    (fun u => tauZ u ^ 4) (fun h => tauZ h ^ 8)]
  rw [Bp, Bp]

lemma Uweight_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (R Y : ℕ), 1 ≤ R → 1 ≤ Y →
      Uweight R Y ≤ C * (R : ℝ) ^ 2 * (Y : ℝ)
        * (Real.log ((R : ℝ) + (Y : ℝ) + 2)) ^ 300 := by
  obtain ⟨C4, hC4pos, hC4⟩ := Bp_bound 4 (by norm_num)
  obtain ⟨C8, hC8pos, hC8⟩ := Bp_bound 8 (by norm_num)
  refine ⟨C4 * C8, by positivity, ?_⟩
  intro R Y hR hY
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := by linarith
  have hY0 : (0 : ℝ) ≤ (Y : ℝ) := by linarith
  set L : ℝ := Real.log ((R : ℝ) + (Y : ℝ) + 2) with hLdef
  have hL : (1 : ℝ) ≤ L := by
    have hpos : (0 : ℝ) < (R : ℝ) + (Y : ℝ) + 2 := by linarith
    have h3 : (3 : ℝ) ≤ (R : ℝ) + (Y : ℝ) + 2 := by linarith
    rw [hLdef, Real.le_log_iff_exp_le hpos]
    exact le_trans (le_of_lt Real.exp_one_lt_three) h3
  have hlogR : Real.log ((R : ℝ) + 2) ≤ L := by
    rw [hLdef]
    exact Real.log_le_log (by linarith) (by linarith)
  have hlogY : Real.log ((Y : ℝ) + 2) ≤ L := by
    rw [hLdef]
    exact Real.log_le_log (by linarith) (by linarith)
  have hlogR0 : 0 ≤ Real.log ((R : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hlogY0 : 0 ≤ Real.log ((Y : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hp : (Real.log ((R : ℝ) + 2)) ^ 16 * (Real.log ((Y : ℝ) + 2)) ^ 256 ≤ L ^ 300 := by
    have hp4 := pow_le_pow_left₀ hlogR0 hlogR 16
    have hp8 := pow_le_pow_left₀ hlogY0 hlogY 256
    have hc : (0 : ℝ) ≤ (Real.log ((Y : ℝ) + 2)) ^ 256 := pow_nonneg hlogY0 256
    have hb : (0 : ℝ) ≤ L ^ 16 := pow_nonneg (by linarith : (0 : ℝ) ≤ L) 16
    have hstep : (Real.log ((R : ℝ) + 2)) ^ 16 * (Real.log ((Y : ℝ) + 2)) ^ 256
        ≤ L ^ 16 * L ^ 256 := mul_le_mul hp4 hp8 hc hb
    have hEq : L ^ 16 * L ^ 256 = L ^ 272 := by rw [← pow_add]
    have hmono : L ^ 272 ≤ L ^ 300 := pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith [hstep, hEq.le, hEq.ge, hmono]
  have hT4 := hC4 R hR
  have hT8 := hC8 Y hY
  have h4 : (0 : ℝ) ≤ C4 * (R : ℝ) * (Real.log ((R : ℝ) + 2)) ^ (2 ^ 4) :=
    mul_nonneg (mul_nonneg hC4pos.le hR0) (by positivity)
  have hstep : Bp 4 R * Bp 8 Y
      ≤ (C4 * (R : ℝ) * (Real.log ((R : ℝ) + 2)) ^ (2 ^ 4))
        * (C8 * (Y : ℝ) * (Real.log ((Y : ℝ) + 2)) ^ (2 ^ 8)) :=
    mul_le_mul hT4 hT8 (Bp_nonneg 8 Y) h4
  have hexp : (2 : ℕ) ^ 4 = 16 ∧ (2 : ℕ) ^ 8 = 256 := by norm_num
  calc Uweight R Y ≤ (R : ℝ) * (Bp 4 R * Bp 8 Y) := Uweight_le R Y
    _ ≤ (R : ℝ) * ((C4 * (R : ℝ) * (Real.log ((R : ℝ) + 2)) ^ (2 ^ 4))
          * (C8 * (Y : ℝ) * (Real.log ((Y : ℝ) + 2)) ^ (2 ^ 8))) :=
        mul_le_mul_of_nonneg_left hstep hR0
    _ = C4 * C8 * (R : ℝ) ^ 2 * (Y : ℝ)
          * ((Real.log ((R : ℝ) + 2)) ^ 16 * (Real.log ((Y : ℝ) + 2)) ^ 256) := by
        rw [hexp.1, hexp.2]; ring
    _ ≤ C4 * C8 * (R : ℝ) ^ 2 * (Y : ℝ) * L ^ 300 :=
        mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (C4 * C8) * (R : ℝ) ^ 2 * (Y : ℝ)
          * (Real.log ((R : ℝ) + (Y : ℝ) + 2)) ^ 300 := by rw [← hLdef]

end

end Work.FIArea2.R6.Hbox6Axis
