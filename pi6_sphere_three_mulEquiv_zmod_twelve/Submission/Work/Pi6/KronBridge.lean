import Submission.Work.Pi6.Interfaces
import Submission.Work.Cohomology.KroneckerH
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port
set_option synthInstance.maxHeartbeats 400000
/-! Lead glue (2026-09-29): the Kronecker pairing in the interface types `Coh`/`HR`; everything is `rfl` to `Work.Cohomology.kronH`. Use `exact`/`Iff.rfl`/`show`, never `rw`, to move between the two. -/
namespace Work.Pi6
noncomputable section
/-- The Kronecker pairing in the interface's own types (`Coh`, `HR`). -/
noncomputable def kronL (R : Type) [CommRing R] (X : Type) [TopologicalSpace X] (n : ℕ) :
    Work.Pi6.Coh R X n →ₗ[R] (Work.Pi6.HR R X n →ₗ[R] R) :=
  Work.Cohomology.kronH R (TopCat.toSSet.obj (TopCat.of X)) n
theorem kronL_apply (R : Type) [CommRing R] (X : Type) [TopologicalSpace X] (n : ℕ)
    (x : Work.Pi6.Coh R X n) (c : Work.Pi6.HR R X n) :
    kronL R X n x c = Work.Cohomology.kronH R (TopCat.toSSet.obj (TopCat.of X)) n x c := rfl
theorem kronL_bijective_iff (R : Type) [CommRing R] (X : Type) [TopologicalSpace X] (n : ℕ) :
    Function.Bijective (kronL R X n) ↔
      Function.Bijective (Work.Cohomology.kronH R (TopCat.toSSet.obj (TopCat.of X)) n) := Iff.rfl
/-- Class of a cocycle, in `Coh`. -/
theorem kronL_cls (R : Type) [CommRing R] (X : Type) [TopologicalSpace X] (n : ℕ)
    (α : Work.Cohomology.Cochain R (TopCat.toSSet.obj (TopCat.of X)) n)
    (hα : Work.Cohomology.cochainDiff R (TopCat.toSSet.obj (TopCat.of X)) α = 0)
    (c : Work.Pi6.HR R X n) :
    kronL R X n (Work.Cohomology.cohomologyClassOf R (TopCat.toSSet.obj (TopCat.of X)) α hα) c =
      Work.Cohomology.kronH R (TopCat.toSSet.obj (TopCat.of X)) n
        (Work.Cohomology.cohomologyClassOf R (TopCat.toSSet.obj (TopCat.of X)) α hα) c := rfl
end
end Work.Pi6
