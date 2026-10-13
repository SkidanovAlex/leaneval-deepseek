/-
Area DSCOH (curric-46) — the normalization comparison: the sorting deformation retraction of the
unnormalized Čech complex onto the semi-ordered one (Stacks Project, Section 20.23, `01FG`,
Lemma 20.23.6).  The section `semiLift` of `semiProj` is defined in `Norm.SortSection`, where it is
also proved to be a section; the chain-map property and the existence of the homotopy are the
inputs `Norm.semiLift_chain` and `Norm.semiLift_homotopy`.
-/
import Mathlib
import Submission.Work.DSCOH.Norm.Complexes
import Submission.Work.DSCOH.Norm.SortSection
import Submission.Work.DSCOH.Norm.semiLift_chain
import Submission.Work.DSCOH.Norm.semiLift_homotopy

namespace Work.DSCOH.Norm

open CategoryTheory

universe u v w

/-- **The sorting deformation retraction** (Stacks 20.23.6, the "first homotopy").  There is a
section `psi` of the projection `semiProj` from Mathlib's unnormalized Čech complex onto the
semi-ordered (nondecreasing tuples) complex which is a chain map, together with a homotopy `h`
witnessing that `semiProj ≫ psi` is homotopic to the identity in every degree. -/
theorem allT_homotopy_semiT {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
    {ι : Type w} [Fintype ι] [LinearOrder ι]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : CategoryTheory.Functor (Opposite (TopologicalSpace.Opens X)) (ModuleCat A))
    (U : ι → TopologicalSpace.Opens X) :
    ∃ psi : ∀ n : ℕ, Work.DSCOH.Norm.semiTerm P U n ⟶
        ((CategoryTheory.cechComplexFunctor U).obj P).X n,
      (∀ n : ℕ, psi n ≫ Work.DSCOH.Norm.semiProj P U n =
          𝟙 (Work.DSCOH.Norm.semiTerm P U n)) ∧
      (∀ n : ℕ, psi n ≫ ((CategoryTheory.cechComplexFunctor U).obj P).d n (n + 1) =
          Work.DSCOH.Norm.semiD P U n ≫ psi (n + 1)) ∧
        ∃ h : ∀ n : ℕ, ((CategoryTheory.cechComplexFunctor U).obj P).X (n + 1) ⟶
            ((CategoryTheory.cechComplexFunctor U).obj P).X n,
          (((CategoryTheory.cechComplexFunctor U).obj P).d 0 1 ≫ h 0 +
              Work.DSCOH.Norm.semiProj P U 0 ≫ psi 0 =
            𝟙 (((CategoryTheory.cechComplexFunctor U).obj P).X 0)) ∧
          ∀ n : ℕ,
            h n ≫ ((CategoryTheory.cechComplexFunctor U).obj P).d n (n + 1) +
                ((CategoryTheory.cechComplexFunctor U).obj P).d (n + 1) (n + 2) ≫ h (n + 1) +
              Work.DSCOH.Norm.semiProj P U (n + 1) ≫ psi (n + 1) =
            𝟙 (((CategoryTheory.cechComplexFunctor U).obj P).X (n + 1)) := by
  obtain ⟨h, h0, hs⟩ := semiLift_homotopy P U
  exact ⟨semiLift P U, fun n => semiLift_semiProj P U n, fun n => semiLift_chain P U n, h, h0, hs⟩

end Work.DSCOH.Norm
