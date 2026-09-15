import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

namespace Commons.NumberTheory.FriedlanderIwaniec

open scoped BigOperators

private noncomputable def W (n : ℕ) : ℝ := Real.log n / n
private noncomputable def Cχ (n : ℕ) : ℝ := ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ)

private lemma chi4_one {n : ℕ} (h : n % 4 = 1) : Cχ n = 1 := by
  unfold Cχ; rw [ZMod.χ₄_nat_one_mod_four h]; norm_num

private lemma chi4_three {n : ℕ} (h : n % 4 = 3) : Cχ n = -1 := by
  unfold Cχ; rw [ZMod.χ₄_nat_three_mod_four h]; norm_num

private lemma chi4_zero {n : ℕ} (h : n % 4 = 0) : Cχ n = 0 := by
  unfold Cχ
  have h2 : n % 2 = 0 := by omega
  rw [ZMod.χ₄_nat_eq_if_mod_four, if_pos h2]; norm_num

private lemma chi4_two {n : ℕ} (h : n % 4 = 2) : Cχ n = 0 := by
  unfold Cχ
  have h2 : n % 2 = 0 := by omega
  rw [ZMod.χ₄_nat_eq_if_mod_four, if_pos h2]; norm_num

private lemma partial_sum_Cχ (m : ℕ) :
    ∑ i ∈ Finset.range m, Cχ i = if m % 4 = 2 ∨ m % 4 = 3 then 1 else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hm : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have h4 : (m + 1) % 4 = (m % 4 + 1) % 4 := by omega
    rw [h4]
    obtain h0 | h1 | h2 | h3 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    · rw [chi4_zero h0, h0]; norm_num
    · rw [chi4_one h1, h1]; norm_num
    · rw [chi4_two h2, h2]; norm_num
    · rw [chi4_three h3, h3]; norm_num

private lemma partial_sum_Cχ_bound (m : ℕ) : |∑ i ∈ Finset.range m, Cχ i| ≤ 1 := by
  rw [partial_sum_Cχ m]
  split <;> norm_num

private lemma W_nonneg (n : ℕ) : 0 ≤ W n := by
  unfold W
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))) (by positivity)

private lemma W_zero : W 0 = 0 := by simp [W]
private lemma W_one : W 1 = 0 := by simp [W]
private lemma W_two : W 2 = Real.log 2 / 2 := by simp [W]
private lemma W_three : W 3 = Real.log 3 / 3 := by simp [W]

private lemma W_anti {i : ℕ} (hi : 3 ≤ i) : W (i + 1) ≤ W i := by
  unfold W
  push_cast
  have hmem1 : (i : ℝ) ∈ Set.Ici (Real.exp 1) := by
    rw [Set.mem_Ici]
    have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have : (3 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    linarith
  have hmem2 : ((i : ℝ) + 1) ∈ Set.Ici (Real.exp 1) := by
    rw [Set.mem_Ici]
    have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have : (3 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    linarith
  exact Real.log_div_self_antitoneOn hmem1 hmem2 (by linarith)

private lemma TV (N : ℕ) (hN : 3 ≤ N) :
    ∑ i ∈ Finset.range N, |W (i + 1) - W i| ≤ Real.log 2 + 2 * Real.log 3 / 3 - W N := by
  induction N, hN using Nat.le_induction with
  | base =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    rw [W_zero, W_one, W_two, W_three]
    have h2 : (0:ℝ) ≤ Real.log 2 / 2 := by rw [← W_two]; exact W_nonneg 2
    have h3 : (0:ℝ) ≤ Real.log 3 / 3 := by rw [← W_three]; exact W_nonneg 3
    simp only [sub_zero, abs_zero, zero_add]
    rw [abs_of_nonneg h2]
    have habs : |Real.log 3 / 3 - Real.log 2 / 2| ≤ Real.log 3 / 3 + Real.log 2 / 2 := by
      rw [abs_le]; constructor <;> linarith
    linarith
  | succ N hN ih =>
    rw [Finset.sum_range_succ]
    have h := W_anti hN
    rw [abs_of_nonpos (by linarith : W (N + 1) - W N ≤ 0)]
    linarith [ih]

theorem chi4_log_recip_sum_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      |(∑ n ∈ Finset.range (N + 1), (((ZMod.χ₄ (n : ZMod 4) : ℤ)) : ℝ) * Real.log n / n)| ≤ C := by
  refine ⟨Real.log 2 + 2 * Real.log 3 / 3, ?_, ?_⟩
  · have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    linarith
  · intro N
    have hsum : (∑ n ∈ Finset.range (N + 1),
          (((ZMod.χ₄ (n : ZMod 4) : ℤ)) : ℝ) * Real.log n / n)
        = ∑ n ∈ Finset.range (N + 1), Cχ n * W n := by
      apply Finset.sum_congr rfl
      intro n _
      simp only [Cχ, W]
      ring
    rw [hsum]
    by_cases hN : 3 ≤ N
    · have habel := Finset.sum_range_by_parts (fun i => W i) (fun i => Cχ i) (N + 1)
      simp only [smul_eq_mul, Nat.add_sub_cancel] at habel
      have hcomm : (∑ i ∈ Finset.range (N + 1), Cχ i * W i)
          = ∑ i ∈ Finset.range (N + 1), W i * Cχ i := by
        apply Finset.sum_congr rfl; intro i _; ring
      rw [hcomm, habel]
      have hA : |∑ i ∈ Finset.range (N + 1), Cχ i| ≤ 1 := partial_sum_Cχ_bound (N + 1)
      have h1 : |W N * (∑ i ∈ Finset.range (N + 1), Cχ i)| ≤ W N * 1 := by
        rw [abs_mul, abs_of_nonneg (W_nonneg N)]
        exact mul_le_mul_of_nonneg_left hA (W_nonneg N)
      have h2 : |∑ i ∈ Finset.range N,
            (W (i + 1) - W i) * (∑ j ∈ Finset.range (i + 1), Cχ j)|
          ≤ ∑ i ∈ Finset.range N, |W (i + 1) - W i| := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
        intro i _
        rw [abs_mul]
        calc |W (i + 1) - W i| * |∑ j ∈ Finset.range (i + 1), Cχ j|
            ≤ |W (i + 1) - W i| * 1 :=
              mul_le_mul_of_nonneg_left (partial_sum_Cχ_bound (i + 1)) (abs_nonneg _)
          _ = |W (i + 1) - W i| := mul_one _
      have htri : |W N * (∑ i ∈ Finset.range (N + 1), Cχ i)
            - ∑ i ∈ Finset.range N, (W (i + 1) - W i) * (∑ j ∈ Finset.range (i + 1), Cχ j)|
          ≤ |W N * (∑ i ∈ Finset.range (N + 1), Cχ i)|
            + |∑ i ∈ Finset.range N, (W (i + 1) - W i) * (∑ j ∈ Finset.range (i + 1), Cχ j)| := by
        have := abs_add_le (W N * (∑ i ∈ Finset.range (N + 1), Cχ i))
          (-(∑ i ∈ Finset.range N, (W (i + 1) - W i) * (∑ j ∈ Finset.range (i + 1), Cχ j)))
        simpa [sub_eq_add_neg, abs_neg] using this
      calc |W N * (∑ i ∈ Finset.range (N + 1), Cχ i)
              - ∑ i ∈ Finset.range N, (W (i + 1) - W i) * (∑ j ∈ Finset.range (i + 1), Cχ j)|
          ≤ |W N * (∑ i ∈ Finset.range (N + 1), Cχ i)|
              + |∑ i ∈ Finset.range N, (W (i + 1) - W i) * (∑ j ∈ Finset.range (i + 1), Cχ j)| := htri
        _ ≤ W N * 1 + ∑ i ∈ Finset.range N, |W (i + 1) - W i| := add_le_add h1 h2
        _ = W N + ∑ i ∈ Finset.range N, |W (i + 1) - W i| := by ring
        _ ≤ W N + (Real.log 2 + 2 * Real.log 3 / 3 - W N) := by
              linarith [TV N hN]
        _ = Real.log 2 + 2 * Real.log 3 / 3 := by ring
    · have hN' : N ≤ 2 := by omega
      have hCpos : 0 < Real.log 2 + 2 * Real.log 3 / 3 := by
        have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
        linarith
      have hz0 : Cχ 0 * W 0 = 0 := by
        rw [chi4_zero (by norm_num : (0:ℕ) % 4 = 0), W_zero, mul_zero]
      have hz1 : Cχ 1 * W 1 = 0 := by rw [W_one, mul_zero]
      have hz2 : Cχ 2 * W 2 = 0 := by
        rw [chi4_two (by norm_num : (2:ℕ) % 4 = 2), zero_mul]
      interval_cases N
      · rw [Finset.sum_range_succ, Finset.sum_range_zero]
        simp only [zero_add, hz0, abs_zero]
        exact le_of_lt hCpos
      · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
        simp only [hz0, hz1, add_zero, abs_zero]
        exact le_of_lt hCpos
      · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
        simp only [hz0, hz1, hz2, add_zero, abs_zero]
        exact le_of_lt hCpos

end Commons.NumberTheory.FriedlanderIwaniec