import Mathlib
import Submission.Work.DSG4a.exists_freeResolution_at

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits
universe u
/-- A cochain complex of `A`-modules with `D.IsStrictlyGE n`, whose cohomology is finitely
generated and concentrated in the single degree `n`, has a model: a complex `F` with finitely
generated free terms, vanishing in degrees `> n` (`F.IsStrictlyLE n` — the one-sided boundedness
that makes `F` K-projective, `CochainComplex.isKProjective_of_projective`), together with a
quasi-isomorphism `F ⟶ D`.

Recipe: `D.truncLE n` is strictly supported in the single degree `n` (because `D` is strictly
`≥ n` and the truncation is strictly `≤ n`), so `CochainComplex.exists_iso_single` gives
`D.truncLE n ≅ (single _ _ n).obj M` with `M := (D.truncLE n).X n`; the canonical map
`D.ιTruncLE n : D.truncLE n ⟶ D` is a quasi-isomorphism (`quasiIsoAt_ιTruncLE` in degrees
`≤ n`, and both homology groups vanish in degrees `> n` by strict boundedness and the
hypothesis).  `M` is finitely generated (it is isomorphic to `D.homology n`, via the map induced
on homology by `ιTruncLE`), so `Work.DSG4a.exists_freeResolution_at M n` provides `F₀` with
finitely generated free terms, `F₀.IsStrictlyLE n` and a quasi-isomorphism `F₀ ⟶ M[n]`; compose
with `M[n] ≅ D.truncLE n ⟶ D`. -/
theorem exists_model_concentrated {A : Type u} [CommRing A] [IsNoetherianRing A]
    (D : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) [D.IsStrictlyGE n]
    (hcon : ∀ i, i ≠ n → IsZero (D.homology i))
    (hfin : Module.Finite A (D.homology n)) :
    ∃ F : CochainComplex (ModuleCat.{u} A) ℤ,
      (∀ j, Module.Finite A (F.X j)) ∧ (∀ j, Module.Free A (F.X j)) ∧ F.IsStrictlyLE n ∧
      ∃ q : F ⟶ D, QuasiIso q := by
  obtain ⟨M, ⟨e⟩⟩ := CochainComplex.exists_iso_single (D.truncLE n) n
  haveI := hfin
  have hMfin : Module.Finite A M := by
    have iso3 : M ≅ ((HomologicalComplex.single (ModuleCat.{u} A)
        (ComplexShape.up ℤ) n).obj M).homology n :=
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n M).symm
    have iso2 : ((HomologicalComplex.single (ModuleCat.{u} A)
        (ComplexShape.up ℤ) n).obj M).homology n ≅ (D.truncLE n).homology n :=
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) n).mapIso e).symm
    have iso1 : (D.truncLE n).homology n ≅ D.homology n :=
      _root_.isoOfQuasiIsoAt (D.ιTruncLE n) n
    exact Module.Finite.equiv ((iso3 ≪≫ iso2 ≪≫ iso1).symm.toLinearEquiv)
  obtain ⟨F, hFfin, hFfree, hFLE, q₀, hq₀⟩ :=
    Work.DSG4a.exists_freeResolution_at (A := A) M n
  haveI hqι : QuasiIso (D.ιTruncLE n) := by
    rw [_root_.quasiIso_iff]
    intro q
    by_cases hq : q ≤ n
    · exact CochainComplex.quasiIsoAt_ιTruncLE D n q hq
    · push_neg at hq
      refine (_root_.quasiIsoAt_iff_isIso_homologyMap (D.ιTruncLE n) q).2 ?_
      refine IsZero.isIso ?_ (hcon q (by omega)) _
      exact IsZero.of_iso
        (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) n M q (by omega))
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) q).mapIso e)
  refine ⟨F, hFfin, hFfree, hFLE, q₀ ≫ e.inv ≫ D.ιTruncLE n, ?_⟩
  exact inferInstance

end Work.DSG4a
