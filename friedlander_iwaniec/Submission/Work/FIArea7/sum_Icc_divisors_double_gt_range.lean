import Mathlib

namespace Work.FIArea7

open Finset

/-- If `m < Y`, then `m` has no divisor larger than `Y`, so the sum over
`m.divisors` filtered by `Y < ·` vanishes. -/
lemma sum_divisors_filter_gt_eq_zero {M : Type*} [AddCommMonoid M] {m Y : ℕ} (hm : m < Y)
    (g : ℕ → M) : ∑ b ∈ m.divisors.filter (fun b => Y < b), g b = 0 := by
  apply Finset.sum_eq_zero
  intro b hb
  rw [Finset.mem_filter] at hb
  obtain ⟨hbd, hYb⟩ := hb
  have hbm : b ≤ m := Nat.divisor_le hbd
  exfalso
  omega

theorem sum_Icc_divisors_double_gt_range {M : Type*} [AddCommMonoid M] (N Y : ℕ) (hY : 1 ≤ Y)
    (G : ℕ → ℕ → ℕ → M) :
    (∑ a ∈ Finset.Icc (Y + 1) N, ∑ m ∈ Finset.Icc 1 (N / a),
        ∑ b ∈ m.divisors.filter (fun b => Y < b), G a b (a * m))
      = ∑ a ∈ Finset.Icc (Y + 1) (N / Y), ∑ m ∈ Finset.Icc 1 (N / a),
          ∑ b ∈ m.divisors.filter (fun b => Y < b), G a b (a * m) := by
  refine (Finset.sum_subset
    (s₁ := Finset.Icc (Y + 1) (N / Y)) (s₂ := Finset.Icc (Y + 1) N)
    (f := fun a => ∑ m ∈ Finset.Icc 1 (N / a),
        ∑ b ∈ m.divisors.filter (fun b => Y < b), G a b (a * m)) ?_ ?_).symm
  · -- the shortened range is contained in the original range
    intro a ha
    rw [Finset.mem_Icc] at ha ⊢
    exact ⟨ha.1, le_trans ha.2 (Nat.div_le_self N Y)⟩
  · -- the dropped terms `a > N / Y` contribute nothing
    intro a ha hna
    rw [Finset.mem_Icc] at ha
    have hYpos : 0 < Y := by omega
    have hlt : N / Y < a := by
      by_contra h
      exact hna (by rw [Finset.mem_Icc]; exact ⟨ha.1, not_lt.mp h⟩)
    have hNlt : N < a * Y := (Nat.div_lt_iff_lt_mul hYpos).mp hlt
    have hapos : 0 < a := by omega
    apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hdiv : N / a < Y := by
      rw [Nat.div_lt_iff_lt_mul hapos]
      rwa [mul_comm]
    have hmY : m < Y := lt_of_le_of_lt hm.2 hdiv
    exact sum_divisors_filter_gt_eq_zero hmY _

end Work.FIArea7
