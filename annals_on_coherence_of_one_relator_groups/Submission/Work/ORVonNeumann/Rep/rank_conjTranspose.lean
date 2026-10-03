import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnRankFunction
import Submission.Work.ORVonNeumann.Rep.vnKeyRank
import Submission.Work.ORVonNeumann.Rep.vnMatOpAdjoint

namespace Work.ORVonNeumann.Rep

/-- The rank of a matrix over `N(G)` is invariant under the conjugate transpose.  Indeed,
`rk C† = m - dim_G (ker (matOp C†)†) = m - dim_G (ker (matOp C))`, and the latter equals
`n - dim_G (ker (matOp C)†) = rk C` by the key rank identity `vnKeyRank`. -/
theorem rank_conjTranspose {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n m : ℕ} (C : Matrix (Fin n) (Fin m) (↥(Work.ORVonNeumann.groupVonNeumann G))) : (Work.ORVonNeumann.Rep.vnRankFunction (G := G)).rank C.conjTranspose = (Work.ORVonNeumann.Rep.vnRankFunction (G := G)).rank C := by
  rw [SylvesterRankFunction.rank_eq, SylvesterRankFunction.rank_eq]
  simp only [vnRankFunction, vnRank_eq]
  rw [show ContinuousLinearMap.adjoint (matOp (G := G) (Matrix.conjTranspose C))
      = matOp (G := G) C from by
    rw [vnMatOpAdjoint, Matrix.conjTranspose_conjTranspose]]
  exact vnKeyRank (G := G) C

end Work.ORVonNeumann.Rep
