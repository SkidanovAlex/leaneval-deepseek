import Mathlib
import Submission.Work.DSG4a.Data

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits
universe u
/-- If a complex `C` of `A`-modules represents `RΓ(X, 𝒪_X)` in the derived category (an
isomorphism `e : ι(RΓ) ≅ Q(C)`) then the finiteness and the vanishing above `N` of the
cohomology of `RΓ(X,𝒪_X)` — the output `Work.DSG4a.CohData` of the frozen area `COH` — pass to
`C`.

Recipe: `DerivedCategory.homologyFunctorFactors (ModuleCat A) i` identifies
`(homologyFunctor i).obj (Q.obj C)` with `C.homology i` (apply `.app C`); apply
`homologyFunctor i` to `e` and transport `Module.Finite` / `IsZero` along the resulting
isomorphisms (`Module.Finite.equiv_iff` on the underlying linear equivalences of a `ModuleCat`
iso; `IsZero.of_iso`). -/
theorem cechHomology_finite_isZero {A : Type u} [CommRing A] [HasDerivedCategory (ModuleCat.{u} A)]
    {X : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ AlgebraicGeometry.Spec (.of A)}
    [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅ DerivedCategory.Q.obj C)
    (h : Work.DSG4a.CohData A X f) :
    ∃ N : ℤ, ∀ i : ℤ, Module.Finite A (C.homology i) ∧ (N < i → IsZero (C.homology i)) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun i => ⟨?_, ?_⟩⟩
  · -- the isomorphism `Hⁱ(RΓ(X,𝒪)) ≅ C.homology i` induced by `e`
    let iso : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          (DerivedCategory.Plus.ι.obj (DSMap.RG A X f)) ≅ C.homology i :=
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e) ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app C
    exact (Module.Finite.equiv_iff (CategoryTheory.Iso.toLinearEquiv iso)).mp (hN i).1
  · intro hi
    let iso : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          (DerivedCategory.Plus.ι.obj (DSMap.RG A X f)) ≅ C.homology i :=
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e) ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app C
    exact IsZero.of_iso ((hN i).2 hi) iso.symm

end Work.DSG4a
