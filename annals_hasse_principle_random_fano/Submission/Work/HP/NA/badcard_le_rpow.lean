import Mathlib
import Submission.Work.HP.NA.Setup

/-!
# Markov-type bound on the number of coefficients with small `σ_Q`

For a modulus `W` and a threshold `C₀`, the number of primitive coefficient vectors `c`
whose invariant `σ(c;W)` lies in `(0, C₀)` is at most
`C₀^κ · ∑_{c primitive} σ(c;W)^{-κ}`: on the bad set `σ(c;W)^{-κ} ≥ C₀^{-κ}`, and the
remaining terms are nonnegative.
-/

namespace Work.HP.NA

/-- `σ_Q` is nonnegative (it is a count divided by a nonnegative real). -/
lemma sigQ_nonneg_aux (d n q : ℕ) (c : Work.HP.Mon d n → ZMod q) :
    0 ≤ Work.HP.NA.sigQ d n q c := by
  unfold Work.HP.NA.sigQ
  refine div_nonneg (Nat.cast_nonneg _) ?_
  positivity

/-- Markov step: for `0 < a < C₀` and `κ > 0` we have `1 ≤ C₀^κ · a^{-κ}`. -/
lemma one_le_mul_rpow_neg {a C₀ κ : ℝ} (ha : 0 < a) (haC : a < C₀) (hκ : 0 < κ) :
    1 ≤ C₀ ^ κ * a ^ (-κ) := by
  have hle : a ^ κ ≤ C₀ ^ κ := Real.rpow_le_rpow ha.le haC.le hκ.le
  have hpos : 0 < a ^ κ := Real.rpow_pos_of_pos ha κ
  rw [Real.rpow_neg ha.le κ, ← div_eq_mul_inv]
  exact (one_le_div hpos).mpr hle

theorem badcard_le_rpow (d n W : ℕ) [NeZero W] (C₀ κ : ℝ) (hC₀ : 0 < C₀) (hκ : 0 < κ) :
    (Nat.card {c : Work.HP.Mon d n → ZMod W // Work.HP.NA.IsPrimGen W c ∧ 0 < Work.HP.NA.sigQ d n W c ∧ Work.HP.NA.sigQ d n W c < C₀} : ℝ)
      ≤ C₀ ^ κ * (∑ c ∈ Work.HP.NA.primFinset d n W, (Work.HP.NA.sigQ d n W c) ^ (-κ)) := by
  classical
  have hcard : Nat.card {c : Work.HP.Mon d n → ZMod W //
      Work.HP.NA.IsPrimGen W c ∧ 0 < Work.HP.NA.sigQ d n W c ∧ Work.HP.NA.sigQ d n W c < C₀}
      = (Finset.univ.filter (fun c : Work.HP.Mon d n → ZMod W =>
          Work.HP.NA.IsPrimGen W c ∧ 0 < Work.HP.NA.sigQ d n W c
            ∧ Work.HP.NA.sigQ d n W c < C₀)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]
  set B : Finset (Work.HP.Mon d n → ZMod W) :=
    Finset.univ.filter (fun c => Work.HP.NA.IsPrimGen W c ∧ 0 < Work.HP.NA.sigQ d n W c
      ∧ Work.HP.NA.sigQ d n W c < C₀) with hB
  set S : Finset (Work.HP.Mon d n → ZMod W) := Work.HP.NA.primFinset d n W with hS
  have hBS : B ⊆ S := by
    intro c hc
    rw [hB] at hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rw [hS]
    simp only [Work.HP.NA.primFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hc.1
  calc (B.card : ℝ)
      = ∑ c ∈ B, (1 : ℝ) := by simp
    _ ≤ ∑ c ∈ B, C₀ ^ κ * (Work.HP.NA.sigQ d n W c) ^ (-κ) := by
        apply Finset.sum_le_sum
        intro c hc
        rw [hB] at hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        exact one_le_mul_rpow_neg hc.2.1 hc.2.2 hκ
    _ = C₀ ^ κ * ∑ c ∈ B, (Work.HP.NA.sigQ d n W c) ^ (-κ) := by
        rw [Finset.mul_sum]
    _ ≤ C₀ ^ κ * ∑ c ∈ S, (Work.HP.NA.sigQ d n W c) ^ (-κ) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.rpow_pos_of_pos hC₀ κ))
        exact Finset.sum_le_sum_of_subset_of_nonneg hBS
          (fun c _ _ => Real.rpow_nonneg (sigQ_nonneg_aux d n W c) _)

end Work.HP.NA
