import Mathlib
import Submission.Work.LT.good_base_defs
import Submission.Work.LT.binom_mono_second
import Submission.Work.LT.card_filter_hammingNorm_le
import Submission.Work.LT.choose_le_exp_pow

namespace Work.LT

/-- The number of vectors of `𝔽₂^ι` of Hamming weight at most `w` is at most `(w+1) * (|ι| e / w)^w` (as long as `2w ≤ |ι|`, so that the binomial coefficients increase up to `w`). -/
theorem gb_card_weight {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ℕ) (hw : 0 < w)
    (hw2 : 2 * w ≤ Fintype.card ι) :
    ((Finset.univ.filter (fun v : ι → ZMod 2 => hammingNorm v ≤ w)).card : ℝ) ≤
      (w + 1) * ((Fintype.card ι : ℝ) * Real.exp 1 / w) ^ w := by
  -- The number of such vectors is `∑_{k=0}^{w} (|ι| choose k)`.
  have hcount := card_filter_hammingNorm_le (ι := ι) w
  -- Each summand is at most `(|ι| choose w) ≤ (|ι| e / w)^w`.
  have hstep : ∀ k ∈ Finset.range (w + 1),
      ((Fintype.card ι).choose k : ℝ) ≤ ((Fintype.card ι : ℝ) * Real.exp 1 / w) ^ w := by
    intro k hk
    have hk' : k ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact le_trans (by exact_mod_cast binom_mono_second (Fintype.card ι) w k hk' hw2)
      (choose_le_exp_pow (Fintype.card ι) w hw)
  rw [hcount, Nat.cast_sum]
  calc ∑ k ∈ Finset.range (w + 1), ((Fintype.card ι).choose k : ℝ)
      ≤ ∑ _k ∈ Finset.range (w + 1), ((Fintype.card ι : ℝ) * Real.exp 1 / w) ^ w :=
        Finset.sum_le_sum hstep
    _ = (w + 1) * ((Fintype.card ι : ℝ) * Real.exp 1 / w) ^ w := by
        rw [Finset.sum_const, Finset.card_range]
        simp

end Work.LT
