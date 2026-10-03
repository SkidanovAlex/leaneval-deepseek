import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.Ulower

/-- The `M × t` block decomposition of `Finset.range (M * t)`: summing over the first `M * t`
integers is the same as summing over the `M` consecutive blocks of length `t`. -/
private lemma sum_range_mul_aux {A : Type*} [AddCommMonoid A] (f : ℕ → A) (n m : ℕ) :
    ∑ i ∈ Finset.range (n * m), f i
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, f (i * m + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add f (n * m) m, ih, Finset.sum_range_succ]

/-- **Decomposition of an interval of length `t·M` into `M` sub-blocks of length `t`.**  For
`t ≥ 1` and `g : ℕ → ℂ`:

`∑_{y ∈ [b+1, b+tM]} g y = ∑_{m=1}^{M} ∑_{r=1}^{t} g (b + (m−1)t + r)`.

(This is the sub-block decomposition used by the periodisation/splitting step of Peluse's §9.) -/
theorem ss_aux_sum_subblock {t M b : ℕ} (ht : 1 ≤ t) (g : ℕ → ℂ) :
    ∑ y ∈ Finset.Icc (b + 1) (b + t * M), g y
      = ∑ m ∈ Finset.Icc 1 M, ∑ r ∈ Finset.Icc 1 t, g (b + (m - 1) * t + r) := by
  -- Rewrite the left-hand side as a sum over `Finset.range (t * M)` by shifting by `b + 1`.
  have h1 : ∑ y ∈ Finset.Icc (b + 1) (b + t * M), g y
      = ∑ i ∈ Finset.range (t * M), g (b + 1 + i) := by
    rw [← Finset.Ico_add_one_right_eq_Icc (b + 1) (b + t * M),
      Finset.sum_Ico_eq_sum_range g (b + 1) (b + t * M + 1)]
    have hsub : b + t * M + 1 - (b + 1) = t * M := by omega
    rw [hsub]
  -- Rewrite the right-hand side as a double sum over `Finset.range M` and `Finset.range t`.
  have h2 : ∑ m ∈ Finset.Icc 1 M, ∑ r ∈ Finset.Icc 1 t, g (b + (m - 1) * t + r)
      = ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range t, g (b + 1 + (i * t + j)) := by
    rw [← Finset.Ico_add_one_right_eq_Icc 1 M, ← Finset.Ico_add_one_right_eq_Icc 1 t]
    simp only [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel, Nat.add_sub_cancel_left]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    omega
  -- Both sides now agree by the block decomposition of `Finset.range (t * M)`.
  have h3 : ∑ i ∈ Finset.range (t * M), g (b + 1 + i)
      = ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range t, g (b + 1 + (i * t + j)) := by
    rw [Nat.mul_comm t M]
    exact sum_range_mul_aux (fun i => g (b + 1 + i)) M t
  rw [h1, h2, h3]

end Work.Peluse.Ulower
