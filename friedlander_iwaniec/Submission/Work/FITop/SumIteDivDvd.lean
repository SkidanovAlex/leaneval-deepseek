import Mathlib
import Submission.Work.FITop.Defs
import Submission.ASP.S7c
import Submission.ASP.S8b
import Submission.ASP.S20
import Submission.ASP.S21
import Submission.ASP.S22
import Submission.ASP.S23
import Submission.ASP.S24
import Submission.ASP.S25

namespace Work.FITop

/-- Reindexing a sum over `m` with `b * m ≤ x` into a sum over the multiples `n` of `b` up to `x`.
For `b ≥ 1` the map `m ↦ b * m` is a bijection from
`{m ∈ Icc 1 x : b * m ≤ x}` onto `{n ∈ Icc 1 x : b ∣ n}` (inverse `n ↦ n / b`), and `b * (n / b) = n`
there; hence the two sums are actually **equal**, and the stated `≤` follows. -/
theorem SumIteDivDvd (b x : ℕ) (hb : 1 ≤ b) (f g : ℕ → ℝ) :
    (∑ m ∈ Finset.Icc 1 x, (if b * m ≤ x then f m * g (b * m) else 0))
      ≤ ∑ n ∈ (Finset.Icc 1 x).filter (fun n => b ∣ n), f (n / b) * g n := by
  have hb0 : 0 < b := hb
  have h1 : (∑ m ∈ Finset.Icc 1 x, (if b * m ≤ x then f m * g (b * m) else 0))
      = ∑ m ∈ (Finset.Icc 1 x).filter (fun m => b * m ≤ x), f m * g (b * m) := by
    rw [Finset.sum_filter]
  rw [h1]
  apply le_of_eq
  apply Finset.sum_bij' (fun a _ => b * a) (fun a _ => a / b)
  · -- forward map lands in the multiples of `b`
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha ⊢
    obtain ⟨⟨ha1, ha2⟩, hx⟩ := ha
    refine ⟨⟨?_, hx⟩, ⟨a, rfl⟩⟩
    have : 0 < b * a := Nat.mul_pos hb0 (by omega)
    omega
  · -- inverse map lands back in the allowed range
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha ⊢
    obtain ⟨⟨ha1, ha2⟩, k, hk⟩ := ha
    have hbkx : b * k ≤ x := by rw [← hk]; exact ha2
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk; omega
      · exact h
    have hdiv : a / b = k := by rw [hk, Nat.mul_div_right k hb0]
    rw [hdiv]
    exact ⟨⟨hk1, le_trans (Nat.le_mul_of_pos_left k hb0) hbkx⟩, hbkx⟩
  · -- left inverse
    intro a ha
    exact Nat.mul_div_right a hb0
  · -- right inverse
    intro a ha
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp ha).2
  · -- summands agree
    intro a ha
    rw [Nat.mul_div_right a hb0]

end Work.FITop
