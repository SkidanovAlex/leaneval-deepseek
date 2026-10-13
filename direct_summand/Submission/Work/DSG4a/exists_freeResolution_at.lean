import Mathlib
import Submission.Work.DSG4a.exists_freeResolution_above

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits
universe u
/-- A finitely generated module over a Noetherian ring has a complex of finitely generated free
modules, vanishing in degrees `> i`, with a quasi-isomorphism onto the single-object complex on
`M` placed in degree `i`.

Recipe: `Work.DSG4a.exists_freeResolution_above` gives the case `i = 0`: a complex `F₀` with
finitely generated free terms, `F₀.IsStrictlyLE 0`, and a quasi-isomorphism
`q₀ : F₀ ⟶ (single _ _ 0).obj M`.  Take `F := F₀⟦-i⟧` (the shift by `-i`,
`CochainComplex.shiftFunctor`), which still has finitely generated free terms and is
`IsStrictlyLE i`; the shifted map `F₀⟦-i⟧ ⟶ ((single _ _ 0).obj M)⟦-i⟧` is a quasi-isomorphism
(homology of a shift: `((homologyFunctor C _ 0).shiftIso a i' _ rfl).app K`, cf. `isLE_shift` in
`Mathlib/Algebra/Homology/Embedding/CochainComplex.lean`), and
`((single _ _ 0).obj M)⟦-i⟧ ≅ (single _ _ i).obj M` (`CochainComplex.exists_iso_single` applies:
that complex is strictly supported in degree `i`). -/
theorem exists_freeResolution_at {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (i : ℤ) :
    ∃ F : CochainComplex (ModuleCat.{u} A) ℤ,
      (∀ j, Module.Finite A (F.X j)) ∧ (∀ j, Module.Free A (F.X j)) ∧ F.IsStrictlyLE i ∧
      ∃ q : F ⟶ (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) i).obj
          (ModuleCat.of A M), QuasiIso q := by
  -- the `i = 0` case
  obtain ⟨F₀, hfin, hfree, hle, q₀, hq⟩ := Work.DSG4a.exists_freeResolution_above (A := A) M
  -- make the strict support of `F₀` available to the shift lemmas
  have hle' : F₀.IsStrictlyLE 0 := hle
  -- the compatibility of the single functors with the shift gives
  -- `((single _ _ 0).obj M)⟦-i⟧ ≅ (single _ _ i).obj M`
  have hiso : ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M))⟦-i⟧ ≅
      (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) i).obj (ModuleCat.of A M) :=
    ((CochainComplex.singleFunctors (ModuleCat.{u} A)).shiftIso (-i) i 0 (by omega)).app
      (ModuleCat.of A M)
  refine ⟨F₀⟦-i⟧, fun j => hfin (j + (-i)), fun j => hfree (j + (-i)),
    CochainComplex.isStrictlyLE_shift F₀ 0 (-i) i (by omega), ?_⟩
  refine ⟨(shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) (-i)).map q₀ ≫ hiso.hom, ?_⟩
  exact quasiIso_comp _ _

end Work.DSG4a
