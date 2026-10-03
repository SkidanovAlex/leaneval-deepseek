import Mathlib
import Submission.Work.ORP311.P311Defs

namespace Work.ORP311

open Work.ORVonNeumann

/-- The blockwise left regular operator `regBlk n t` commutes with the block diagonal right
regular action `diagOp n g`, i.e. it is equivariant for the group von Neumann algebra
`N(G)`.

The proof is coordinatewise: on the `i`-th coordinate the two operators act by
`λ(t) ∘ ρ(g)` and `ρ(g) ∘ λ(t)` respectively, and these agree because the left and right
regular representations of `G` commute. -/
theorem regBlk_equivariant {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) (t : G) : Work.ORVonNeumann.Rep.Equivariant (G := G) (Work.ORP311.regBlk (G := G) n t) := by
  intro g
  apply ContinuousLinearMap.ext
  intro x
  apply Rep.hsum_ext
  intro i
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  -- `hcoord i (regBlk n t y) = λ(t) (hcoord i y)`.
  rw [show Rep.hcoord (G := G) n i (regBlk (G := G) n t (Rep.diagOp (G := G) n g x))
        = Rep.leftRegOp t (Rep.hcoord (G := G) n i (Rep.diagOp (G := G) n g x)) from
      congrArg (fun f : Rep.HSum (G := G) n →L[ℂ] l2 G => f (Rep.diagOp (G := G) n g x))
        (hcoord_regBlk (G := G) n t i)]
  -- `hcoord i (diagOp n g y) = ρ(g) (hcoord i y)`, at both occurrences.
  simp only [Rep.hcoord_diagOp_apply]
  -- and again the coordinate formula for `regBlk` on the right-hand side.
  rw [show Rep.hcoord (G := G) n i (regBlk (G := G) n t x)
        = Rep.leftRegOp t (Rep.hcoord (G := G) n i x) from
      congrArg (fun f : Rep.HSum (G := G) n →L[ℂ] l2 G => f x)
        (hcoord_regBlk (G := G) n t i)]
  -- `λ(t)` and `ρ(g)` commute.
  exact congrArg (fun f : l2 G →L[ℂ] l2 G => f (Rep.hcoord (G := G) n i x))
    (Rep.leftRegOp_commute_rightRegOp t g)

end Work.ORP311
