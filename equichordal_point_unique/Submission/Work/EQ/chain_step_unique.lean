import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.H0_tail_bounded

namespace Work.EQ

/-- **One step of a chain determines the previous one, locally.**

Both `q.1 j` and `q'.1 j` are preimages of the common next point `X = q.1 (j+1) = q'.1 (j+1)`
under the equichordal relation, and regularity of the pairs of `q` and `q'` says that `X` is off
the isotropic lines through `O₁ = (-a/2, 0)`.  Hence each of them is one of the two backward
branches `invBranch a true X`, `invBranch a false X` (`eqRelC_solutions`), and those two branches
are at least `1` apart (`invBranch_separation`).  If the branches differed, the distance between
`q.1 j` and `q'.1 j` would be `≥ 1`, while the triangle inequality together with the two
closeness hypotheses and `2ε ≤ 1` bounds it by `< 2ε ≤ 1`; contradiction. -/
theorem chain_step_unique {a : ℝ} {h : ℂ → ℂ} {p q q' : ChainData} {ε : ℝ} {j : ℤ}
    (hq : IsChain a h q) (hq' : IsChain a h q')
    (hnext : q.1 (j + 1) = q'.1 (j + 1))
    (hcl : ‖q.1 j - p.1 j‖ < ε) (hcl' : ‖q'.1 j - p.1 j‖ < ε)
    (hε : 2 * ε ≤ 1) : q.1 j = q'.1 j := by
  -- regularity of the pair `(q.1 j, q.1 (j+1))` gives that `X = q.1 (j+1)` is off the
  -- isotropic lines through `O₁`
  have hb : bsq (subO1 a (q.1 (j + 1))) ≠ 0 := by
    simpa [bsq, subO1] using (hq.1 j).2.2
  have hb' : bsq (subO1 a (q'.1 (j + 1))) ≠ 0 := by
    simpa [bsq, subO1] using (hq'.1 j).2.2
  have h1 : q.1 j = invBranch a true (q.1 (j + 1)) ∨
      q.1 j = invBranch a false (q.1 (j + 1)) :=
    eqRelC_solutions (hq.1 j).1 hb
  have h2 : q'.1 j = invBranch a true (q'.1 (j + 1)) ∨
      q'.1 j = invBranch a false (q'.1 (j + 1)) :=
    eqRelC_solutions (hq'.1 j).1 hb'
  -- both points are `ε`-close to `p.1 j`, and `2ε ≤ 1`, so they are less than `1` apart
  have hlt : ‖q.1 j - q'.1 j‖ < 1 := by
    have htri : ‖q.1 j - q'.1 j‖ ≤ ‖q.1 j - p.1 j‖ + ‖q'.1 j - p.1 j‖ := by
      have h := norm_sub_le (q.1 j - p.1 j) (q'.1 j - p.1 j)
      have he : (q.1 j - p.1 j) - (q'.1 j - p.1 j) = q.1 j - q'.1 j := by abel
      rwa [he] at h
    linarith
  -- if they are different backward branches of the same point, they are `≥ 1` apart
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · rw [h1, h2, hnext]
  · exfalso
    have hsep : (1 : ℝ) ≤ ‖q.1 j - q'.1 j‖ := by
      rw [h1, h2, hnext]
      exact invBranch_separation hb'
    linarith
  · exfalso
    have hsep : (1 : ℝ) ≤ ‖q.1 j - q'.1 j‖ := by
      rw [h1, h2, hnext, norm_sub_rev]
      exact invBranch_separation hb'
    linarith
  · rw [h1, h2, hnext]

end Work.EQ
