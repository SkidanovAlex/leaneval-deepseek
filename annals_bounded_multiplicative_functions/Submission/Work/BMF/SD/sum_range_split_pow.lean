import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- Splitting a sum over `range (k+1)` (with `1 ≤ k`) into the `j = 0` and `j = 1` terms
together with the tail over `Icc 2 k`. -/
lemma sum_range_two_Icc (k : ℕ) (hk : 1 ≤ k) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.range (k+1), f j = f 0 + f 1 + ∑ j ∈ Finset.Icc 2 k, f j := by
  have h2 : 2 ≤ k + 1 := by omega
  have hsplit := Finset.sum_range_add_sum_Ico (f := f) (m := 2) (n := k+1) h2
  rw [← hsplit, Finset.Ico_add_one_right_eq_Icc]
  have h2' : ∑ j ∈ Finset.range 2, f j = f 0 + f 1 := by
    rw [show (2:ℕ) = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
  rw [h2']

theorem sum_range_split_pow (k : ℕ) (hk : 1 ≤ k) (a : ℕ → ℝ) (n q : ℕ) :
    (∑ j ∈ Finset.range (k+1), a j * ((((n+q:ℕ):ℝ)^j) - ((n:ℝ)^j)))
      = (q:ℝ) * a 1 + ∑ j ∈ Finset.Icc 2 k, a j * ((((n+q:ℕ):ℝ)^j) - ((n:ℝ)^j)) := by
  set f : ℕ → ℝ := fun j => a j * ((((n+q:ℕ):ℝ)^j) - ((n:ℝ)^j)) with hf
  have h0 : f 0 = 0 := by simp [hf]
  have h1 : f 1 = (q:ℝ) * a 1 := by
    simp only [hf, pow_one]
    push_cast
    ring
  rw [sum_range_two_Icc k hk f, h0, h1]
  ring

end Work.BMF.SD
