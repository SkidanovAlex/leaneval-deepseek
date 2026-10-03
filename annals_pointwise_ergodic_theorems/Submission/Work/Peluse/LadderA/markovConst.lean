import Mathlib

namespace Work.Peluse.LadderA

/-- Markov-type counting bound: if `w = 1/|α|` and `2t ≤ w∑f` with `0 ≤ f ≤ 1` and `0 ≤ t ≤ 1`,
then `t ≤ w·#{a | t ≤ f a}`. -/
theorem markovConst {α : Type} [Fintype α] {w : ℝ} (hw : 0 ≤ w) (hwc : w * (Fintype.card α : ℝ) = 1)
    (f : α → ℝ) (h0 : ∀ a, 0 ≤ f a) (h1 : ∀ a, f a ≤ 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hE : 2 * t ≤ w * ∑ a, f a) :
    t ≤ w * ((Finset.univ.filter (fun a => t ≤ f a)).card : ℝ) := by
  classical
  -- Pointwise: `f a ≤ t + (1 - t) * 1_{t ≤ f a}`.
  have hpoint : ∀ a, f a ≤ t + (1 - t) * (if t ≤ f a then (1 : ℝ) else 0) := by
    intro a
    by_cases ha : t ≤ f a
    · rw [if_pos ha]
      have : t + (1 - t) * 1 = 1 := by ring
      rw [this]
      exact h1 a
    · rw [if_neg ha]
      have : t + (1 - t) * 0 = t := by ring
      rw [this]
      exact le_of_lt (not_le.mp ha)
  -- Summing: `∑ f ≤ N·t + (1-t)·#B`.
  have hsum : ∑ a, f a
      ≤ (Fintype.card α : ℝ) * t + (1 - t) * ((Finset.univ.filter (fun a => t ≤ f a)).card : ℝ) := by
    calc ∑ a, f a
        ≤ ∑ a, (t + (1 - t) * (if t ≤ f a then (1 : ℝ) else 0)) :=
          Finset.sum_le_sum (fun a _ => hpoint a)
      _ = (∑ a, (t : ℝ)) + (1 - t) * ∑ a, (if t ≤ f a then (1 : ℝ) else 0) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = (Fintype.card α : ℝ) * t + (1 - t) * ((Finset.univ.filter (fun a => t ≤ f a)).card : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Finset.sum_boole]
          simp [nsmul_eq_mul]
  have hCnn : (0 : ℝ) ≤ w * ((Finset.univ.filter (fun a => t ≤ f a)).card : ℝ) :=
    mul_nonneg hw (Nat.cast_nonneg _)
  -- Multiply the sum bound by `w ≥ 0` and use `w·N = 1`.
  have hkey : w * (∑ a, f a)
      ≤ t + (1 - t) * (w * ((Finset.univ.filter (fun a => t ≤ f a)).card : ℝ)) := by
    have h1 : w * ((Fintype.card α : ℝ) * t) = t := by rw [← mul_assoc, hwc, one_mul]
    have h2 : w * ((1 - t) * ((Finset.univ.filter (fun a => t ≤ f a)).card : ℝ))
        = (1 - t) * (w * ((Finset.univ.filter (fun a => t ≤ f a)).card : ℝ)) := by ring
    calc w * (∑ a, f a)
        ≤ w * ((Fintype.card α : ℝ) * t
              + (1 - t) * ((Finset.univ.filter (fun a => t ≤ f a)).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum hw
      _ = w * ((Fintype.card α : ℝ) * t)
            + w * ((1 - t) * ((Finset.univ.filter (fun a => t ≤ f a)).card : ℝ)) := by
          rw [mul_add]
      _ = t + (1 - t) * (w * ((Finset.univ.filter (fun a => t ≤ f a)).card : ℝ)) := by
          rw [h1, h2]
  have hfin : t ≤ (1 - t) * (w * ((Finset.univ.filter (fun a => t ≤ f a)).card : ℝ)) := by
    linarith [hE, hkey]
  have h1t : (1 : ℝ) - t ≤ 1 := by linarith
  have := mul_le_mul_of_nonneg_right h1t hCnn
  linarith

end Work.Peluse.LadderA
