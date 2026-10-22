import Mathlib
import Submission.Work.ANALYTIC.CechPt.CoordDefs
import Submission.Work.ANALYTIC.Final

/-!
# `Work.ANALYTIC.CechPt.kMap_solidEquiv`

The Haar coordinate map `kMap T : ℤ̃[T] ⟶ ∏_ℕ ℤ` of `Submission/Work/ANALYTIC/CechPt/CoordDefs.lean`
is the solidification of the reduced null sequence of REFS/03 §4, so it is a solid-equivalence.

`kMap T` is `kLCZ T ≫ prodZisoProdLCZ.inv` (`CoordDefs.lean`), and `kLCZ T` is the `ℕ`-indexed
lift of the Haar functionals `κ̃_j`.  The substance is classical and already available in the shared
library as separate lemmas:

* `Work.ANALYTIC.kT_solidEquiv_gRed` — the reduced null sequence `gRed T : P ⟶ ℤ̃[T]` is a
  solid-equivalence;
* `Work.ANALYTIC.g_kappaLCZ` — the comparison of coordinates: `g T ≫ κ_j = cBounded ≫ coord_j`;
* `Work.ANALYTIC.solidEquiv_cBoundedIncl` — the standard map `P ⟶ ∏^bnd ℤ ⟶ ∏ℤ` is a
  solid-equivalence, together with `Work.ANALYTIC.prodZModel_isoCoord`, which identifies the
  coordinates of `∏^bnd ℤ` with the model `∏ᶜ (fun _ : ℕ => LCZ)` (so the `j`-th coordinate is
  exactly `coordLCZ j`).

Putting these together, `gRed T ≫ kLCZ T` is the standard map; two-out-of-three
(`ToolkitProp.of_comp_left`) then gives `SolidEquiv (map (kLCZ T))`, and composing with the
isomorphism `prodZisoProdLCZ` gives the statement for `kMap T`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ANALYTIC.CechPt

/-- **The `LCZ`-model of the Haar coordinate map is a solid-equivalence.**
This is the substance of `Work.ANALYTIC.exists_kTilde` for the *specific* map `kLCZ T`. -/
theorem kLCZ_solidEquiv (T : LightProfinite.{0}) [Infinite T] :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map (Work.ANALYTIC.kLCZ T)) := by
  -- the reduced null sequence `gRed T` is a solid-equivalence
  have hgr : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map (Work.ATOM.gRed T)) :=
    Work.ANALYTIC.kT_solidEquiv_gRed T
  -- the comparison of `gRed T ≫ kLCZ T` with the standard map `P ⟶ ∏^bnd ℤ ⟶ ∏ᶜ LCZ`
  obtain ⟨e, he⟩ := Work.ANALYTIC.prodZModel_isoCoord
  let stdLCZ : LightCondensed.P ⟶ Work.ANALYTIC.prodLCZ :=
    Work.ANALYTIC.cBounded ≫ Work.ANALYTIC.boundedSeqIncl ≫ e.hom
  have hcomp : Work.ATOM.gRed T ≫ Work.ANALYTIC.kLCZ T = stdLCZ := by
    refine Limits.Pi.hom_ext _ _ fun j => ?_
    have h1 : (Work.ATOM.gRed T ≫ Work.ANALYTIC.kLCZ T) ≫
        CategoryTheory.Limits.Pi.π (fun _ : ℕ => Work.ATOM.ZS.Unred.LCZ) j
        = Work.ATOM.g T ≫ Work.ANALYTIC.kappaLCZ T j := by
      rw [Work.ANALYTIC.kLCZ, Category.assoc, Limits.Pi.lift_comp_π,
        show Work.ATOM.gRed T =
          Work.ATOM.g T ≫ Work.ATOM.qred T (Work.ATOM.levelData T).s₀ from rfl,
        Category.assoc, Work.ANALYTIC.kappaTilde_spec]
    have h2 : stdLCZ ≫ CategoryTheory.Limits.Pi.π (fun _ : ℕ => Work.ATOM.ZS.Unred.LCZ) j
        = Work.ANALYTIC.cBounded ≫ Work.ANALYTIC.coordLCZ j := by
      rw [show stdLCZ =
          Work.ANALYTIC.cBounded ≫ Work.ANALYTIC.boundedSeqIncl ≫ e.hom from rfl,
        Category.assoc, he j]
    rw [h1, h2]
    exact Work.ANALYTIC.g_kappaLCZ T j
  -- the standard map is a solid-equivalence
  have hstd : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map stdLCZ) := by
    have h1 : Submission.Blueprint.SolidEquiv
        ((DerivedCategory.singleFunctor LightCondAb 0).map
          ((Work.ANALYTIC.cBounded ≫ Work.ANALYTIC.boundedSeqIncl) ≫ e.hom)) := by
      rw [Functor.map_comp]
      exact Work.TOOLKIT.toolkit_prop.comp _ _ Work.ANALYTIC.solidEquiv_cBoundedIncl
        (Work.TOOLKIT.toolkit_prop.of_iso _
          (Functor.map_isIso (DerivedCategory.singleFunctor LightCondAb 0) e.hom))
    simpa only [stdLCZ, Category.assoc] using h1
  -- two out of three
  have hgk : Submission.Blueprint.SolidEquiv
      (((DerivedCategory.singleFunctor LightCondAb 0).map (Work.ATOM.gRed T)) ≫
        ((DerivedCategory.singleFunctor LightCondAb 0).map (Work.ANALYTIC.kLCZ T))) := by
    rw [← Functor.map_comp, hcomp]
    exact hstd
  exact Work.TOOLKIT.toolkit_prop.of_comp_left _ _ hgr hgk

/-- **The Haar coordinate map `kMap T : ℤ̃[T] ⟶ ∏_ℕ ℤ` is a solid-equivalence.** -/
theorem kMap_solidEquiv (T : LightProfinite.{0}) [Infinite T] :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map (Work.ANALYTIC.CechPt.kMap T)) := by
  rw [Work.ANALYTIC.CechPt.kMap, Functor.map_comp]
  refine Work.TOOLKIT.toolkit_prop.comp _ _ (kLCZ_solidEquiv T) ?_
  exact Work.TOOLKIT.toolkit_prop.of_iso _
    (Functor.map_isIso (DerivedCategory.singleFunctor LightCondAb 0)
      Work.ANALYTIC.prodZisoProdLCZ.inv)

end Work.ANALYTIC.CechPt
