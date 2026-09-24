import Mathlib
import Submission.Work.GM.S2.hhat_decay_defs
import Submission.Commons.Analysis.PSeries.tsum_int_abs_pow_neg_tail_le

/-!
# The tail sum of `‖ĥ_t(m N)‖` over `|m| > X`

Given the decay hypothesis `‖ĥ_t(ξ)‖ ≤ C_j (1+|t|)^j / |ξ|^j` (GM Lemma 4.3(2),
`hhat_decay`), the sum of `‖ĥ_t(m N)‖` over the integers `m` with `|m| > X` is
`≪ (1+|t|)^j / (N^j X^{j-1})` for `j ≥ 2`.

The proof is elementary: the `m`-th term is at most
`C_j (1+|t|)^j / (|m|^j N^j)`, and the `p`-series tail `Σ_{|m|>X} |m|^{-j}` is
`≤ 4 X^{1-j}` (the lemma `Commons.Analysis.PSeries.tsum_int_abs_pow_neg_tail_le`).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.GM.S2

/-- The `p`-series `Σ_{m ∈ ℤ} |m|^{-j}` converges for `j ≥ 2`. -/
lemma summable_int_abs_pow_inv {j : ℕ} (hj : 2 ≤ j) :
    Summable (fun m : ℤ => ((|(m:ℝ)| : ℝ) ^ j)⁻¹) := by
  refine Summable.of_nonneg_of_le (f := fun k : ℤ => 1 / ((k:ℝ) ^ 2))
    (fun k => inv_nonneg.mpr (pow_nonneg (abs_nonneg _) j)) (fun k => ?_)
    ((Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num))
  by_cases hk : k = 0
  · subst hk
    simp [zero_pow (by omega : j ≠ 0)]
  · have h1 : (1:ℝ) ≤ |(k:ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
    have h2 : |(k:ℝ)|^2 ≤ |(k:ℝ)|^j := by
      calc |(k:ℝ)|^2 = |(k:ℝ)|^2 * 1 := by ring
        _ ≤ |(k:ℝ)|^2 * |(k:ℝ)|^(j-2) := by
            gcongr
            exact one_le_pow₀ h1
        _ = |(k:ℝ)|^j := by rw [← pow_add]; congr 1; omega
    rw [one_div]
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr (by rw [← sq_abs]; exact h2)

/-- Any "guarded" version of the `p`-series is summable. -/
lemma summable_int_guard_abs_pow_inv {j : ℕ} (hj : 2 ≤ j) (p : ℤ → Prop) [DecidablePred p] :
    Summable (fun m : ℤ => (if p m then ((|(m:ℝ)| : ℝ) ^ j)⁻¹ else 0)) := by
  refine Summable.of_nonneg_of_le (f := fun k : ℤ => ((|(k:ℝ)| : ℝ)^j)⁻¹) ?_ ?_
    (summable_int_abs_pow_inv hj)
  · intro k
    split_ifs with h
    · exact inv_nonneg.mpr (pow_nonneg (abs_nonneg _) j)
    · exact le_refl 0
  · intro k
    split_ifs with h
    · exact le_refl _
    · exact inv_nonneg.mpr (pow_nonneg (abs_nonneg _) j)

/-- The `p`-series tail over `ℤ`: for `j ≥ 2` and `X > 0`,
`Σ_{|m| > X} |m|^{-j} ≪ X^{1-j}`, uniformly in `X`. -/
lemma tsum_int_guard_inv_pow_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (X : ℝ), 2 ≤ j → 0 < X →
      (∑' m : ℤ, (if X < |(m:ℝ)| then ((|(m:ℝ)| : ℝ) ^ j)⁻¹ else 0))
        ≤ C * X ^ (1 - (j : ℝ)) := by
  obtain ⟨Cp, hCppos, hCp⟩ := Commons.Analysis.PSeries.tsum_int_abs_pow_neg_tail_le
  refine ⟨Cp, hCppos, ?_⟩
  intro j X hj hX
  set K : ℝ := max X 1 with hKdef
  have hK1 : 1 ≤ K := le_max_right _ _
  have hXK : X ≤ K := le_max_left _ _
  have hL := summable_int_guard_abs_pow_inv hj (fun k : ℤ => X < |(k:ℝ)|)
  have hR := summable_int_guard_abs_pow_inv hj (fun k : ℤ => K ≤ |(k:ℝ)|)
  have hcmp : ∀ k : ℤ, (if X < |(k:ℝ)| then ((|(k:ℝ)| : ℝ) ^ j)⁻¹ else 0)
      ≤ (if K ≤ |(k:ℝ)| then ((|(k:ℝ)| : ℝ) ^ j)⁻¹ else 0) := by
    intro k
    by_cases h : X < |(k:ℝ)|
    · have hk0 : k ≠ 0 := by
        intro hk; rw [hk] at h; simp at h; linarith
      have h1 : (1:ℝ) ≤ |(k:ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
      have hKle : K ≤ |(k:ℝ)| := max_le (le_of_lt h) h1
      rw [if_pos h, if_pos hKle]
    · rw [if_neg h]
      by_cases h2 : K ≤ |(k:ℝ)|
      · rw [if_pos h2]; exact inv_nonneg.mpr (pow_nonneg (abs_nonneg _) j)
      · rw [if_neg h2]
  have hz : (1:ℝ) - (j:ℝ) ≤ 0 := by
    have h2j : (2:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
    linarith
  calc (∑' m : ℤ, (if X < |(m:ℝ)| then ((|(m:ℝ)| : ℝ) ^ j)⁻¹ else 0))
      ≤ (∑' m : ℤ, (if K ≤ |(m:ℝ)| then ((|(m:ℝ)| : ℝ) ^ j)⁻¹ else 0)) :=
        Summable.tsum_le_tsum hcmp hL hR
    _ ≤ Cp * K ^ (1 - (j:ℝ)) := hCp j K hj hK1
    _ ≤ Cp * X ^ (1 - (j:ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hX hXK hz) (le_of_lt hCppos)

theorem hhat_sum_tail
    (hdec : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t ξ : ℝ, ξ ≠ 0 →
      ‖Submission.GM.hhat t ξ‖ ≤ C * (1 + |t|) ^ j / |ξ| ^ j)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ t X : ℝ, 0 < X →
      ∑' (m : {m : ℤ // X < |(m : ℝ)|}), ‖Submission.GM.hhat t ((m : ℝ) * (N : ℝ))‖
        ≤ C * (1 + |t|) ^ j / ((N : ℝ) ^ j * X ^ (j - 1)) := by
  obtain ⟨Cj, hCjpos, hCj⟩ := hdec j
  obtain ⟨Cp, hCppos, hCp⟩ := tsum_int_guard_inv_pow_le
  refine ⟨Cp * Cj, by positivity, ?_⟩
  intro N hN t X hX
  have hXpow : X ^ (1 - (j : ℝ)) = (X ^ (j - 1))⁻¹ := by
    rw [show (1:ℝ) - (j:ℝ) = -((j:ℝ) - 1) by ring, Real.rpow_neg (le_of_lt hX)]
    congr 1
    rw [← Real.rpow_natCast X (j - 1), Nat.cast_sub (by omega : 1 ≤ j)]
    norm_num
  have hstep1 : (∑' (m : {m : ℤ // X < |(m:ℝ)|}), ‖Submission.GM.hhat t ((m:ℝ)*(N:ℝ))‖)
      = ∑' m : ℤ, (if X < |(m:ℝ)| then ‖Submission.GM.hhat t ((m:ℝ)*(N:ℝ))‖ else 0) := by
    refine (tsum_subtype (s := {m : ℤ | X < |(m:ℝ)|})
      (f := fun m : ℤ => ‖Submission.GM.hhat t ((m:ℝ)*(N:ℝ))‖)).trans ?_
    refine tsum_congr (fun m => ?_)
    by_cases h : X < |(m:ℝ)| <;> simp [h]
  have hpt : ∀ m : ℤ, (if X < |(m:ℝ)| then ‖Submission.GM.hhat t ((m:ℝ)*(N:ℝ))‖ else 0)
      ≤ (if X < |(m:ℝ)| then Cj * (1+|t|)^j / ((((|(m:ℝ)| : ℝ))^j) * (N:ℝ)^j) else 0) := by
    intro m
    by_cases h : X < |(m:ℝ)|
    · rw [if_pos h, if_pos h]
      have hm0 : (m:ℝ) ≠ 0 := by
        have hpos : (0:ℝ) < |(m:ℝ)| := lt_of_lt_of_le hX (le_of_lt h)
        exact abs_pos.mp hpos
      have hN0 : (N:ℝ) ≠ 0 := by positivity
      have hne : (m:ℝ)*(N:ℝ) ≠ 0 := mul_ne_zero hm0 hN0
      have hb := hCj t ((m:ℝ)*(N:ℝ)) hne
      simpa [abs_mul, abs_of_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ (N:ℝ)), mul_pow] using hb
    · rw [if_neg h]
      by_cases h2 : X < |(m:ℝ)|
      · rw [if_pos h2]
        exact div_nonneg (mul_nonneg (le_of_lt hCjpos) (pow_nonneg (by positivity) j)) (by positivity)
      · rw [if_neg h2]
  have htor : ∀ m : ℤ, 0 ≤ (if X < |(m:ℝ)| then ‖Submission.GM.hhat t ((m:ℝ)*(N:ℝ))‖ else 0) := by
    intro m; split_ifs with h
    · exact norm_nonneg _
    · exact le_refl 0
  have hRsumm : Summable (fun m : ℤ =>
      (if X < |(m:ℝ)| then Cj * (1+|t|)^j / ((((|(m:ℝ)| : ℝ))^j) * (N:ℝ)^j) else 0)) := by
    have h := (summable_int_guard_abs_pow_inv hj (fun m : ℤ => X < |(m:ℝ)|)).mul_left
      (Cj * (1+|t|)^j * ((N:ℝ)^j)⁻¹)
    refine h.congr (fun m => ?_)
    by_cases hc : X < |(m:ℝ)|
    · rw [if_pos hc, if_pos hc, div_eq_mul_inv, mul_inv]; ring
    · rw [if_neg hc, if_neg hc]; ring
  have hLsumm : Summable (fun m : ℤ =>
      (if X < |(m:ℝ)| then ‖Submission.GM.hhat t ((m:ℝ)*(N:ℝ))‖ else 0)) :=
    Summable.of_nonneg_of_le htor hpt hRsumm
  have hbound : (∑' m : ℤ, (if X < |(m:ℝ)| then ‖Submission.GM.hhat t ((m:ℝ)*(N:ℝ))‖ else 0))
      ≤ (∑' m : ℤ, (if X < |(m:ℝ)| then
          Cj * (1+|t|)^j / ((((|(m:ℝ)| : ℝ))^j) * (N:ℝ)^j) else 0)) :=
    Summable.tsum_le_tsum hpt hLsumm hRsumm
  have hEq : (∑' m : ℤ, (if X < |(m:ℝ)| then
        Cj * (1+|t|)^j / ((((|(m:ℝ)| : ℝ))^j) * (N:ℝ)^j) else 0))
      = (Cj * (1+|t|)^j * ((N:ℝ)^j)⁻¹) *
        (∑' m : ℤ, (if X < |(m:ℝ)| then (((|(m:ℝ)| : ℝ))^j)⁻¹ else 0)) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun m => ?_)
    by_cases hc : X < |(m:ℝ)|
    · rw [if_pos hc, if_pos hc, div_eq_mul_inv, mul_inv]; ring
    · rw [if_neg hc, if_neg hc]; ring
  rw [hstep1]
  calc (∑' m : ℤ, (if X < |(m:ℝ)| then ‖Submission.GM.hhat t ((m:ℝ)*(N:ℝ))‖ else 0))
      ≤ (∑' m : ℤ, (if X < |(m:ℝ)| then
          Cj * (1+|t|)^j / ((((|(m:ℝ)| : ℝ))^j) * (N:ℝ)^j) else 0)) := hbound
    _ = (Cj * (1+|t|)^j * ((N:ℝ)^j)⁻¹) *
        (∑' m : ℤ, (if X < |(m:ℝ)| then (((|(m:ℝ)| : ℝ))^j)⁻¹ else 0)) := hEq
    _ ≤ (Cj * (1+|t|)^j * ((N:ℝ)^j)⁻¹) * (Cp * X ^ (1 - (j:ℝ))) :=
        mul_le_mul_of_nonneg_left (hCp j X hj hX) (by positivity)
    _ = (Cp * Cj) * (1+|t|)^j / ((N:ℝ)^j * X ^ (j - 1)) := by
        rw [hXpow, div_eq_mul_inv, mul_inv]; ring

end Work.GM.S2
