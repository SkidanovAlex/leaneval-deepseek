import Mathlib
import Submission.Work.HP.rpow_le_add_one
import Submission.Work.HP.dyadic_pigeonhole

namespace Work.HP

open MeasureTheory
open scoped ENNReal

/-- `Real.rpow` commutes with natural powers: `(x ^ k) ^ y = (x ^ y) ^ k`. -/
lemma rpow_pow_comm {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (k : ℕ) :
    (x ^ k) ^ y = (x ^ y) ^ k := by
  rw [← Real.rpow_natCast_mul hx k y, ← Real.rpow_mul_natCast hx y k]
  congr 1
  ring

/-- Rewriting `(M / 2 ^ ℓ) ^ a` as `M ^ a` times a geometric factor. -/
lemma div_pow_rpow_aux (M a : ℝ) (hM : 0 ≤ M) (ℓ : ℕ) :
    (M / (2 : ℝ) ^ ℓ) ^ a = M ^ a * ((1 / 2 : ℝ) ^ a) ^ ℓ := by
  have h1 : M / (2 : ℝ) ^ ℓ = M * (1 / 2 : ℝ) ^ ℓ := by
    rw [div_eq_mul_inv, ← inv_pow]
    norm_num
  rw [h1, Real.mul_rpow hM (by positivity),
    rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2) a ℓ]

/-- Sum bound: for `0 < a ≤ 1`, the dyadic sum `∑_ℓ min(1, (M/2^ℓ)^a)` is `≲ M + 1`,
uniformly in `M`. -/
lemma dyadic_sum_bound (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ M : ℝ, 0 < M →
      (∑' ℓ : ℕ, (if M / 2 ^ ℓ ≤ 1 then (M / 2 ^ ℓ) ^ a else 1))
        ≤ K * (M + 1) := by
  refine ⟨(1 - (1 / 2 : ℝ) ^ a)⁻¹, ?_, ?_⟩
  · rw [inv_pos]
    have h : (1 / 2 : ℝ) ^ a < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) ha0
    linarith
  · intro M hM
    have hlt : (1 / 2 : ℝ) ^ a < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) ha0
    have hnorm : ‖(1 / 2 : ℝ) ^ a‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) a)]
      exact hlt
    have hterm_le : ∀ ℓ : ℕ,
        (if M / 2 ^ ℓ ≤ 1 then (M / 2 ^ ℓ) ^ a else 1)
          ≤ M ^ a * ((1 / 2 : ℝ) ^ a) ^ ℓ := by
      intro ℓ
      have key : (M / (2 : ℝ) ^ ℓ) ^ a = M ^ a * ((1 / 2 : ℝ) ^ a) ^ ℓ :=
        div_pow_rpow_aux M a hM.le ℓ
      by_cases h : M / (2 : ℝ) ^ ℓ ≤ 1
      · rw [if_pos h, key]
      · rw [if_neg h, ← key]
        exact le_of_lt (Real.one_lt_rpow (not_le.mp h) ha0)
    have hterm_nonneg : ∀ ℓ : ℕ,
        0 ≤ (if M / 2 ^ ℓ ≤ 1 then (M / 2 ^ ℓ) ^ a else 1) := by
      intro ℓ
      by_cases h : M / (2 : ℝ) ^ ℓ ≤ 1
      · rw [if_pos h]
        exact Real.rpow_nonneg (by positivity) a
      · rw [if_neg h]; norm_num
    have hgeom : Summable (fun ℓ : ℕ => M ^ a * ((1 / 2 : ℝ) ^ a) ^ ℓ) :=
      (summable_geometric_of_norm_lt_one hnorm).mul_left (M ^ a)
    have hsum_term : Summable (fun ℓ : ℕ =>
        (if M / 2 ^ ℓ ≤ 1 then (M / 2 ^ ℓ) ^ a else 1)) :=
      Summable.of_nonneg_of_le hterm_nonneg hterm_le hgeom
    have hle := hsum_term.tsum_le_tsum hterm_le hgeom
    have hgeom_tsum :
        (∑' ℓ : ℕ, M ^ a * ((1 / 2 : ℝ) ^ a) ^ ℓ)
          = M ^ a * (1 - (1 / 2 : ℝ) ^ a)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hnorm]
    rw [hgeom_tsum] at hle
    have hMbound : M ^ a ≤ M + 1 := rpow_le_add_one M a hM ha0 ha1
    have hKpos : 0 < (1 - (1 / 2 : ℝ) ^ a)⁻¹ := by
      rw [inv_pos]; linarith
    calc (∑' ℓ : ℕ, (if M / 2 ^ ℓ ≤ 1 then (M / 2 ^ ℓ) ^ a else 1))
        ≤ M ^ a * (1 - (1 / 2 : ℝ) ^ a)⁻¹ := hle
      _ ≤ (M + 1) * (1 - (1 / 2 : ℝ) ^ a)⁻¹ :=
            mul_le_mul_of_nonneg_right hMbound (le_of_lt hKpos)
      _ = (1 - (1 / 2 : ℝ) ^ a)⁻¹ * (M + 1) := by ring

theorem dyadic_sum_tools (n : ℕ) (hn : 3 ≤ n) :
    (∀ (M t : ℝ), 0 < M → 0 < t → t ≤ M → ∃ ℓ : ℕ, M / 2 ^ ℓ < t ∧ t ≤ 2 * (M / 2 ^ ℓ)) ∧
    (∃ K : ℝ, 0 < K ∧ ∀ (M : ℝ), 0 < M →
        (∑' ℓ : ℕ, (if M / 2 ^ ℓ ≤ 1 then (M / 2 ^ ℓ) ^ (((n : ℝ) - 1) / n) else 1))
          ≤ K * (M + 1)) := by
  constructor
  · intro M t hM ht htM
    exact dyadic_pigeonhole M t hM ht htM
  · have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    have ha0 : 0 < ((n : ℝ) - 1) / n := by
      apply div_pos <;> linarith
    have ha1 : ((n : ℝ) - 1) / n ≤ 1 := by
      rw [div_le_one hnpos]; linarith
    exact dyadic_sum_bound (((n : ℝ) - 1) / n) ha0 ha1

end Work.HP
