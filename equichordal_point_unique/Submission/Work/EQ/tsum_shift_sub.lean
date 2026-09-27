import Mathlib

namespace Work.EQ

/-- Telescoping shift identity: for a summable complex sequence `f`, the series of
successive differences sums to `-f 0`. -/
theorem tsum_shift_sub {f : ℕ → ℂ} (hf : Summable f) :
    (∑' n : ℕ, (f (n + 1) - f n)) = -f 0 := by
  -- the shifted sequence is summable
  have h2 : Summable (fun n : ℕ => f (n + 1)) :=
    hf.comp_injective (fun a b h => Nat.succ.inj h)
  -- the tail series equals the full series minus the first term
  have h1 : (∑' n : ℕ, f (n + 1)) = (∑' n : ℕ, f n) - f 0 := by
    have hh := Summable.sum_add_tsum_nat_add 1 hf
    rw [Finset.sum_range_one] at hh
    rw [add_comm] at hh
    rw [eq_sub_iff_add_eq]
    exact hh
  rw [Summable.tsum_sub h2 hf, h1]
  ring

end Work.EQ
