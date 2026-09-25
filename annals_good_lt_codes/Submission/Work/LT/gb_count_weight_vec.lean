import Mathlib
import Submission.Work.LT.binom_mono_second
import Submission.Work.LT.gb_count_card_eq_sum_choose
import Submission.Work.LT.gb_choose_le_exp_pow

namespace Work.LT

/-- The number of binary vectors of length `N` with at most `w` ones is at most `(w+1) * (N e / w)^w`, for `2w ≤ N`. -/
theorem gb_count_weight_vec {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ℕ) (hw : 0 < w)
    (hw2 : 2 * w ≤ Fintype.card ι) :
    ((Finset.univ.filter (fun x : ι → ZMod 2 => hammingNorm x ≤ w)).card : ℝ) ≤
      (w + 1) * ((Fintype.card ι : ℝ) * Real.exp 1 / w) ^ w := by
  -- The number of such vectors is `∑_{k=0}^{w} (|ι| choose k)`.
  have hcount := gb_count_card_eq_sum_choose (ι := ι) w
  -- Each summand is at most `(|ι| choose w) ≤ (|ι| e / w)^w`, because `(|ι| choose k)` is
  -- nondecreasing in `k` for `k ≤ w` when `2w ≤ |ι|`.
  have hstep : ∀ k ∈ Finset.range (w + 1),
      ((Fintype.card ι).choose k : ℝ) ≤ ((Fintype.card ι : ℝ) * Real.exp 1 / w) ^ w := by
    intro k hk
    have hk' : k ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact le_trans (by exact_mod_cast binom_mono_second (Fintype.card ι) w k hk' hw2)
      (gb_choose_le_exp_pow (Fintype.card ι) w hw)
  rw [hcount, Nat.cast_sum]
  calc ∑ k ∈ Finset.range (w + 1), ((Fintype.card ι).choose k : ℝ)
      ≤ ∑ _k ∈ Finset.range (w + 1), ((Fintype.card ι : ℝ) * Real.exp 1 / w) ^ w :=
        Finset.sum_le_sum hstep
    _ = (w + 1) * ((Fintype.card ι : ℝ) * Real.exp 1 / w) ^ w := by
        rw [Finset.sum_const, Finset.card_range]
        simp

end Work.LT
