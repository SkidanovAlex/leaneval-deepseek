import Mathlib
import Submission.Work.DSMX0U.Basic

namespace Work.DSMX0U

open CategoryTheory AlgebraicGeometry Limits

universe a

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- **The coherence input of the area `MX0U`.**

For a projective `X` over a Noetherian ring `A` (`f : X ⟶ Spec A` proper and `IsProjOver`, i.e.
a closed immersion `X ↪ ℙ^N_A` over `A`) and *every* finite affine cover `U` of `X`, the
cohomology of the Čech complex `DSMap.cechZ A X f U` is a finitely generated `A`-module and
vanishes in all sufficiently high degrees.

This is the conjunction of the two frozen areas `F1` (the Čech complex computes `RΓ(X, 𝒪_X)`,
`DSMap.area_F1_cech`) and `COH` (finiteness and boundedness of `H^i(X, 𝒪_X)`,
`DSMap.area_COH`), transferred from the derived category to the explicit Čech complex along the
canonical isomorphism `H^i(Q(Č(U))) ≅ H^i(Č(U))` (`DerivedCategory.homologyFunctorFactors`). -/
theorem cechZ_homology_finite {A : Type a} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{a}} (f : X ⟶ Spec (.of A)) [IsProper f] (hp : DSMap.IsProjOver A f)
    {ι : Type a} [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcov : ⨆ i, U i = ⊤) :
    ∃ N : ℤ, ∀ i : ℤ, Module.Finite A ((DSMap.cechZ A X f U).homology i) ∧
      (N < i → CategoryTheory.Limits.IsZero ((DSMap.cechZ A X f U).homology i)) := by
  -- The derived-category instances needed to speak about `RΓ(X, 𝒪_X)`.
  letI : HasDerivedCategory (ModuleCat.{a} A) := HasDerivedCategory.standard _
  letI : HasDerivedCategory (SheafOfModules X.ringCatSheaf) := HasDerivedCategory.standard _
  -- `SheafOfModules X.ringCatSheaf` is a Grothendieck abelian category, hence has enough
  -- injectives (`Scheme.Modules X` is the same category, with the instance registered there).
  haveI hEn : EnoughInjectives (SheafOfModules X.ringCatSheaf) :=
    inferInstanceAs (EnoughInjectives (Scheme.Modules X))
  -- A proper morphism is quasi-compact (needed by `F1`).
  haveI hQC : QuasiCompact f := by
    have h := (inferInstance : IsProper f)
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.2
  -- `COH`: finiteness and boundedness of `H^i(RΓ(X, 𝒪_X))`.
  obtain ⟨N, hN⟩ := DSMap.area_COH A X f hp
  -- `F1`: `RΓ(X, 𝒪_X)` is the Čech complex of the cover `U`.
  obtain ⟨cc, e, -, -⟩ := DSMap.area_F1_cech A X f U hU hcov
  refine ⟨N, fun i => ⟨?_, ?_⟩⟩
  · -- finiteness: transport along `H^i(ι RΓ) ≅ H^i(Q(Č(U))) ≅ H^i(Č(U))`.
    have iso := (DerivedCategory.homologyFunctor (ModuleCat.{a} A) i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{a} A) i).app (DSMap.cechZ A X f U)
    haveI := (hN i).1
    exact Module.Finite.equiv iso.toLinearEquiv
  · -- vanishing above `N`: the same transport, now of `IsZero`.
    intro hi
    have iso := (DerivedCategory.homologyFunctor (ModuleCat.{a} A) i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{a} A) i).app (DSMap.cechZ A X f U)
    exact IsZero.of_iso ((hN i).2 hi) iso.symm

end Work.DSMX0U
