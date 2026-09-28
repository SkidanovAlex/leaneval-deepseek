import Mathlib
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Cohomology.inclUV_injective

/-!
# Injectivity of the Mayer–Vietoris lifts `Simp(U) ⟶ small(U,V)`

The simplicial maps `smallLiftU U V : Simp(U) ⟶ small(U,V)` and
`smallLiftV U V : Simp(V) ⟶ small(U,V)` of `Submission/Work/Cohomology/SmallSES.lean` are the
lifts of the inclusions `U ↪ X`, `V ↪ X` to the subcomplex of small simplices.  On `n`-simplices
they are *literally* push-forward of singular simplices along the inclusion (this is
`SSet.Subcomplex.lift_app_coe`), so they are injective because the inclusions `U ↪ X` and
`V ↪ X` are injective continuous maps.

This is the "injectivity at the level of simplices" input to the middle-exactness of the
Mayer–Vietoris sequence.
-/


open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial
open Work.Cohomology

namespace Work.Cohomology

noncomputable section

/-- **`smallLiftU` is injective on singular simplices.**  It is the lift of the inclusion
`U ↪ X`, whose action on `n`-simplices is just postcomposition with the (injective) inclusion. -/
theorem smallLiftU_injective {X : TopCat} (U V : Set X) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((smallLiftU U V).app n) := by
  intro a b h
  have h1 : (TopCat.toSSet.map (inclUX U)).app n a = (TopCat.toSSet.map (inclUX U)).app n b := by
    have h2 := congrArg
      (fun t : (smallSSet U V).obj n => (t : (TopCat.toSSet.obj X).obj n)) h
    rwa [smallLiftU, SSet.Subcomplex.lift_app_coe, SSet.Subcomplex.lift_app_coe] at h2
  exact toSSet_map_app_injective (inclUX U) (fun a b h => Subtype.ext h) n h1

/-- **`smallLiftV` is injective on singular simplices.**  It is the lift of the inclusion
`V ↪ X`, whose action on `n`-simplices is just postcomposition with the (injective) inclusion. -/
theorem smallLiftV_injective {X : TopCat} (U V : Set X) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((smallLiftV U V).app n) := by
  intro a b h
  have h1 : (TopCat.toSSet.map (inclVX V)).app n a = (TopCat.toSSet.map (inclVX V)).app n b := by
    have h2 := congrArg
      (fun t : (smallSSet U V).obj n => (t : (TopCat.toSSet.obj X).obj n)) h
    rwa [smallLiftV, SSet.Subcomplex.lift_app_coe, SSet.Subcomplex.lift_app_coe] at h2
  exact toSSet_map_app_injective (inclVX V) (fun a b h => Subtype.ext h) n h1

theorem smallLift_injective {X : TopCat} (U V : Set X) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((smallLiftU U V).app n) ∧
    Function.Injective ((smallLiftV U V).app n) :=
  ⟨smallLiftU_injective U V n, smallLiftV_injective U V n⟩

end

end Work.Cohomology
