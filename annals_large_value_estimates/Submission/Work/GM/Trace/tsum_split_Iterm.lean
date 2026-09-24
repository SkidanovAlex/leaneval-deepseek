import Mathlib
import Submission.Work.GM.Trace.Defs
import Submission.Work.GM.Trace.summable_Iterm

namespace Work.GM.Trace

-- Splitting the absolutely convergent triple sum `Σ_m I_m` at `m = 0`, so that the `S₁+S₂+S₃`
-- piece is isolated (GM separates the `m = 0` term of Lemma 4.5).
theorem tsum_split_Iterm (N : ℕ) (W : Finset ℝ)
    (h : Summable (fun m : ℤ × ℤ × ℤ => Submission.GM.Iterm N W m)) :
    (∑' m : ℤ × ℤ × ℤ, Submission.GM.Iterm N W m)
      = Submission.GM.Iterm N W 0 +
        ∑' m : {m : ℤ × ℤ × ℤ // m ≠ 0}, Submission.GM.Iterm N W m := by
  -- `Summable.tsum_eq_add_tsum_ite` splits off the `m = 0` term, leaving the sum of
  -- `if m = 0 then 0 else I_m`; `tsum_subtype` rewrites that as a sum over `{m // m ≠ 0}`.
  have hsub := tsum_subtype (s := ({m : ℤ × ℤ × ℤ | m ≠ 0} : Set (ℤ × ℤ × ℤ)))
    (f := fun m => Submission.GM.Iterm N W m)
  have hL : (∑' n : ℤ × ℤ × ℤ, (if n = 0 then (0 : ℂ) else Submission.GM.Iterm N W n))
      = ∑' m : {m : ℤ × ℤ × ℤ // m ≠ 0}, Submission.GM.Iterm N W m := by
    have h1 : (∑' n : ℤ × ℤ × ℤ, (if n = 0 then (0 : ℂ) else Submission.GM.Iterm N W n))
        = ∑' (n : ℤ × ℤ × ℤ), ({m : ℤ × ℤ × ℤ | m ≠ 0} : Set (ℤ × ℤ × ℤ)).indicator
            (fun m => Submission.GM.Iterm N W m) n := by
      apply tsum_congr
      intro n
      simp only [Set.indicator, Set.mem_ofPred_eq]
      by_cases hn : n = 0 <;> simp [hn]
    exact h1.trans hsub.symm
  rw [h.tsum_eq_add_tsum_ite 0, hL]

end Work.GM.Trace
