import Mathlib
import Submission.Work.BW.DefsB

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MvPolynomial

/-- A product of `X_{i1}`-powers times `X_{i0}`-powers over the rows `i ≥ 1` is multihomogeneous
of multidegree the sum of the per-factor degrees `a i • e_{i+1} + b i • e_{i+1}`. -/
theorem prodX_mem_homPiece {N : ℕ} (a b : Fin N → ℕ) :
    (∏ i : Fin N, MvPolynomial.X ((i.succ : Fin (N + 1)), 1) ^ (a i) *
        MvPolynomial.X ((i.succ : Fin (N + 1)), 0) ^ (b i)) ∈
      homPiece N (∑ i : Fin N, (a i • Finsupp.single (i.succ : Fin (N + 1)) 1
        + b i • Finsupp.single (i.succ : Fin (N + 1)) 1)) := by
  rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]
  refine MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun i : Fin N => (MvPolynomial.X ((i.succ : Fin (N + 1)), 1) ^ (a i) *
        MvPolynomial.X ((i.succ : Fin (N + 1)), 0) ^ (b i) : MR N))
    (fun i : Fin N => a i • Finsupp.single (i.succ : Fin (N + 1)) 1
        + b i • Finsupp.single (i.succ : Fin (N + 1)) 1) ?_
  intro i _
  have hX1 : MvPolynomial.IsWeightedHomogeneous (mdeg N)
      ((MvPolynomial.X ((i.succ : Fin (N + 1)), 1) : MR N) ^ (a i))
      (a i • (Finsupp.single (i.succ : Fin (N + 1)) 1 : Fin (N + 1) →₀ ℕ)) := by
    simpa [mdeg] using
      (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (mdeg N)
        ((i.succ : Fin (N + 1)), 1)).pow (a i)
  have hX0 : MvPolynomial.IsWeightedHomogeneous (mdeg N)
      ((MvPolynomial.X ((i.succ : Fin (N + 1)), 0) : MR N) ^ (b i))
      (b i • (Finsupp.single (i.succ : Fin (N + 1)) 1 : Fin (N + 1) →₀ ℕ)) := by
    simpa [mdeg] using
      (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (mdeg N)
        ((i.succ : Fin (N + 1)), 0)).pow (b i)
  exact hX1.mul hX0

end Work.BW
