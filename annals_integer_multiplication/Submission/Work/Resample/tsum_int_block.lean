import Mathlib

namespace Work.Resample

/-- Splitting a sum over `ℤ` into the block `K', K'+1, …, K'+L-1`, the upper tail
starting at `K'+L`, and the lower tail ending at `K'-1`.

The three index sets `{K'+i | i < L}`, `{K'+L+j | j : ℕ}` and `{K'-1-j | j : ℕ}`
partition `ℤ`, and a summable `ℤ`-indexed family restricts to a summable family on
each part, so the total sum is the sum of the three parts. -/
theorem tsum_int_block {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℤ → E) (hf : Summable f) (K' : ℤ) (L : ℕ) :
    (∑' n : ℤ, f n)
      = (∑ i ∈ Finset.range L, f (K' + (i : ℤ)))
        + (∑' j : ℕ, f (K' + (L : ℤ) + (j : ℤ)))
        + (∑' j : ℕ, f (K' - 1 - (j : ℤ))) := by
  induction L with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_add, add_zero]
    have h1 : Summable (fun n : ℕ => f (K' + (n:ℤ))) :=
      hf.comp_injective (by intro a b h; exact_mod_cast (add_left_cancel h))
    have h2 : Summable (fun n : ℕ => f (K' + (-((n:ℤ) + 1)))) :=
      hf.comp_injective (by
        intro a b h
        have h1 : (-((a:ℤ) + 1)) = (-((b:ℤ) + 1)) := add_left_cancel h
        have h2 : ((a:ℤ) + 1) = ((b:ℤ) + 1) := neg_inj.mp h1
        exact_mod_cast (add_right_cancel h2))
    have hmain := tsum_of_nat_of_neg_add_one (f := fun n : ℤ => f (K' + n)) h1 h2
    have hshift : (∑' n : ℤ, f (K' + n)) = ∑' n : ℤ, f n := by
      have := Equiv.tsum_eq (Equiv.addLeft K') f
      simpa [Equiv.coe_addLeft] using this
    rw [hshift] at hmain
    have heq : (∑' n : ℕ, f (K' + (-((n:ℤ) + 1)))) = (∑' n : ℕ, f (K' - 1 - (n:ℤ))) := by
      apply tsum_congr; intro n; congr 1; ring
    rw [heq] at hmain
    exact hmain
  | succ L ih =>
    rw [Finset.sum_range_succ]
    have hs : Summable (fun j : ℕ => f (K' + (L:ℤ) + (j:ℤ))) :=
      hf.comp_injective (by intro a b h; exact_mod_cast (add_left_cancel h))
    have hM : (∑' j : ℕ, f (K' + (L:ℤ) + (j:ℤ)))
        = f (K' + (L:ℤ)) + (∑' j : ℕ, f (K' + ((L+1 : ℕ) : ℤ) + (j:ℤ))) := by
      have h := hs.tsum_eq_zero_add
      rw [Nat.cast_zero, add_zero] at h
      rw [h]
      congr 1
      apply tsum_congr
      intro j
      congr 1
      push_cast
      ring
    rw [hM] at ih
    rw [ih]
    ac_rfl

end Work.Resample
