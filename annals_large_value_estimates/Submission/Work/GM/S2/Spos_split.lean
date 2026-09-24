import Mathlib
import Submission.Work.GM.S2.pair_sum_defs

namespace Work.GM.S2

/-- Reindexing a sum over `Icc 1 n` as a sum over `range n`:
`∑_{1 ≤ m ≤ n} g m = ∑_{i < n} g (i + 1)`. -/
lemma sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, g m = ∑ i ∈ Finset.range n, g (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- Splitting the positive half `Spos N t = ∑'_{k} ĥ_t((k+1)N)` after `⌊Y⌋` terms. -/
theorem Spos_split (N : ℕ) (t Y : ℝ)
    (hsumm : Summable (fun k : ℕ => Submission.GM.hhat t (((k + 1 : ℕ) : ℝ) * (N : ℝ)))) :
    Work.GM.S2.Spos N t
      = (∑ m ∈ Finset.Icc 1 (Nat.floor Y), Submission.GM.hhat t ((m : ℝ) * (N : ℝ)))
        + ∑' k : ℕ, Submission.GM.hhat t (((k + Nat.floor Y + 1 : ℕ) : ℝ) * (N : ℝ)) := by
  rw [Spos]
  rw [← Summable.sum_add_tsum_nat_add (Nat.floor Y) hsumm]
  congr 1
  rw [sum_Icc_one_eq_sum_range (fun m => Submission.GM.hhat t ((m : ℝ) * (N : ℝ)))
      (Nat.floor Y)]

end Work.GM.S2
