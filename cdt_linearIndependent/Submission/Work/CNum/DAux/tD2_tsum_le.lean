import Mathlib
import Submission.Work.CNum.Jfun_defs
import Submission.Work.CNum.tD_bounds
import Submission.Work.CNum.sum_bndJ

namespace Work.CNum.DAux

/-- The second-derivative series of `Jfun` is bounded by `6500` on the arc
`‖w ψ‖ ≤ rJ`.  This follows from the pointwise domination `|tD2 m ψ| ≤ bndJ m`
(`Work.CNum.tD_bounds`) together with the summability and the numerical bound
`∑' m, bndJ (m+1) ≤ 6500` (`Work.CNum.sum_bndJ`). -/
theorem tD2_tsum_le {ψ : ℝ} (hψ : ‖Work.CNum.wf ψ‖ ≤ Work.CNum.rJ) :
    (∑' k : ℕ, Work.CNum.tD2 (k + 1) ψ) ≤ 6500 := by
  obtain ⟨_, _, hnorm, _⟩ := Work.CNum.tD_bounds hψ
  obtain ⟨hsumm, hle⟩ := Work.CNum.sum_bndJ
  have hs : Summable (fun k : ℕ => Work.CNum.tD2 (k + 1) ψ) :=
    hsumm.of_norm_bounded (fun k => hnorm (k + 1) (Nat.le_add_left 1 k))
  have hb : ∀ k : ℕ, Work.CNum.tD2 (k + 1) ψ ≤ Work.CNum.bndJ (k + 1) := fun k =>
    le_trans (le_abs_self _) (by rw [← Real.norm_eq_abs]; exact hnorm (k + 1) (Nat.le_add_left 1 k))
  exact le_trans (Summable.tsum_le_tsum hb hs hsumm) hle

end Work.CNum.DAux
