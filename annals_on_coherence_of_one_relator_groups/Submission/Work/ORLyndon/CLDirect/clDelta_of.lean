import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs
import Submission.Work.ORLyndon.FoxComp

namespace Work.ORLyndon.CLDirect

/-- `clDelta` on a generator. Sketch: `foxFD (of q) = Finsupp.single q 1` via `Finsupp.ext`, `foxFD_apply`, `foxD_of`, `Finsupp.single_apply` (mind the `if` direction in `foxD_of`; `Submission.Work.ORLyndon.FoxComp` has `foxFD_of`); then `Finsupp.sum_single_index`, `map_one`, `one_mul`. -/
theorem clDelta_of {X : Type*} [DecidableEq X] {K : Type*} [Field K] {u : FreeGroup X}
    (D : Work.ORLyndon.CLDirect.CLData u) (l : ℕ)
    (q : FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X))) :
    Work.ORLyndon.CLDirect.clDelta (K := K) D l (FreeGroup.of q) =
      MonoidAlgebra.of K _ (Work.ORLyndon.presentRho (u ^ l) (D.s q)) := by
  classical
  -- `foxFD` of a generator, with the *classical* `DecidableEq` instance that `clDelta`
  -- uses internally for the quotient type.
  have hkey :
      (@Work.ORLyndon.foxFD
          (FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X))) K _
          (Classical.decEq _) (FreeGroup.of q)) = Finsupp.single q 1 :=
    @Work.ORLyndon.foxFD_of _ K (Classical.decEq _) _ q
  rw [Work.ORLyndon.CLDirect.clDelta, hkey]
  -- sum over a Dirac mass
  have hsum : (Finsupp.single q (1 : MonoidAlgebra K (FreeGroup (FreeGroup X ⧸
        Subgroup.normalClosure ({u} : Set (FreeGroup X)))))).sum
        (fun a c => Work.ORLyndon.CLDirect.clPi (K := K) D l c *
          MonoidAlgebra.of K _ (Work.ORLyndon.presentRho (u ^ l) (D.s a)))
      = Work.ORLyndon.CLDirect.clPi (K := K) D l (1 : MonoidAlgebra K (FreeGroup
          (FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X))))) *
          MonoidAlgebra.of K _ (Work.ORLyndon.presentRho (u ^ l) (D.s q)) :=
    Finsupp.sum_single_index (by simp)
  rw [hsum]
  simp only [map_one, one_mul]

end Work.ORLyndon.CLDirect
