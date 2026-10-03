import Mathlib
import Submission.Work.ORP311.P311Defs

namespace Work.ORP311

open Work.ORVonNeumann

/-- The scalar matrix `x • 1` over `N(G)` with `x = λ(t)` acts on `⊕_{i<n} ℓ²(G)` exactly as the
blockwise left regular operator `regBlk n t`.  Both are diagonal, so it suffices to compare
coordinates: a diagonal matrix has off-diagonal entries `0`, and the diagonal entry is `λ(t)`. -/
theorem matOp_scalar_leftReg {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) (t : G) : Work.ORVonNeumann.Rep.matOp (G := G) (Matrix.scalar (Fin n) (⟨Work.ORVonNeumann.Rep.leftRegOp t, Work.ORVonNeumann.Rep.leftRegOp_mem_groupVonNeumann t⟩ : ↥(Work.ORVonNeumann.groupVonNeumann G))) = Work.ORP311.regBlk (G := G) n t := by
  refine Rep.matOp_ext (fun i => ?_)
  rw [Rep.hcoord_matOp, hcoord_regBlk]
  rw [Finset.sum_eq_single i]
  · simp [Matrix.scalar_apply]
  · intro j _ hj
    simp [Matrix.scalar_apply, Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ i) h

end Work.ORP311
