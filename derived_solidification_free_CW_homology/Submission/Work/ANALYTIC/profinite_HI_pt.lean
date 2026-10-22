import Mathlib
import ChallengeDeps
import Submission.Work.ANALYTIC.PrTop
import Submission.Work.ANALYTIC.Basic
import Submission.Work.ANALYTIC.solidEquiv_splitEpi
import Submission.Work.ANALYTIC.CechPt.Bridge
import Submission.Work.ANALYTIC.CechPt.DAssembly
import Submission.Work.ANALYTIC.CechPt.doubleDualUnit_solidEquiv
import Submission.Work.RESOL.Main
import Submission.Work.ATOM.Main
import Submission.Work.DERFORMAL.Main
import Submission.Work.TOOLKIT.Main
import Submission.Work.FLAT.Main

/-!
# The point case of homotopy invariance of `ℤ[−]` (area ANALYTIC, base case of AN5)

The statement `Work.ANALYTIC.profinite_HI_pt` is the case `S = PUnit` of
`Work.ANALYTIC.profinite_HI`: the projection `prTop ∗ : ∗ × [0,1] ⟶ ∗` induces a
solid-equivalence `ℤ[∗ × [0,1]] ⟶ ℤ[∗]`.

Since `ℤ[−]` is a functor and `i₀ ≫ prTop = 𝟙` (`Work.ANALYTIC.i₀_prTop`), the map in question
is a split epimorphism in `LightCondAb`; hence (`Work.ANALYTIC.solidEquiv_splitEpi`) the
statement is *equivalent* to the solid-nullness of the kernel of that split epimorphism.  The
kernel is, up to the canonical isomorphisms `ℤ[∗ × [0,1]] ≅ ℤ[[0,1]]` and `ℤ[∗] ≅ ℤ`, the
augmentation kernel `ker (ℤ[[0,1]] ⟶ ℤ)`; the mathematical content of the statement is therefore
that the interval is *solid-contractible*: `L■ ℤ[[0,1]] ≅ ℤ`.

This file isolates that content as `solidNull_kernel_pt` (the part that is delegated/built
separately) and performs the reduction.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- The point, as a topological space. -/
abbrev ptTop : TopCat.{0} := LightProfinite.toTopCat.obj (LightProfinite.of PUnit.{1})

/-- The map `ℤ[prTop ∗] : ℤ[∗ × [0,1]] ⟶ ℤ[∗]` of free light condensed abelian groups. -/
abbrev prLightCondPt :
    freeLightCondAbOfTopFunctor.obj (TopCat.of (↥ptTop × unitInterval)) ⟶
      freeLightCondAbOfTopFunctor.obj ptTop :=
  freeLightCondAbOfTopFunctor.map (prTop ptTop)

/-- `prLightCondPt` is a split epimorphism, with section induced by `i₀`. -/
theorem i0_prLightCondPt :
    freeLightCondAbOfTopFunctor.map (Submission.Blueprint.i₀ ptTop) ≫
      prLightCondPt = 𝟙 _ := by
  rw [prLightCondPt, ← Functor.map_comp, i₀_prTop]
  simp

/-! ## Reduction of the goal to the augmented interval

The map `prTop ∗ : ∗ × [0,1] ⟶ ∗` factors, through the homeomorphism
`h : ∗ × [0,1] ≅ [0,1]`, as `h ≫ (terminal map [0,1] ⟶ ∗)`.  Since `ℤ[h]` is an isomorphism, the
goal is equivalent to the solid-equivalence of the *augmentation of the interval*
`augI : ℤ[[0,1]] ⟶ ℤ[∗] ≅ ℤ`. -/

/-- The point of `∗`, as a type-theoretic point. -/
instance : Subsingleton ↥ptTop := ⟨fun a b => by cases a; cases b; rfl⟩

instance : Unique ↥ptTop := ⟨⟨PUnit.unit⟩, fun a => Subsingleton.elim _ _⟩

/-- The unique map `[0,1] ⟶ ∗`. -/
def termI : TopCat.of unitInterval ⟶ ptTop :=
  TopCat.ofHom ⟨fun _ => (PUnit.unit : ↥ptTop), continuous_const⟩

/-- The homeomorphism `∗ × [0,1] ≅ [0,1]` (the second projection). -/
noncomputable def ptProdHomeo : TopCat.of (↥ptTop × unitInterval) ≅ TopCat.of unitInterval :=
  TopCat.isoOfHomeo (Homeomorph.uniqueProd ↥ptTop ↥unitInterval)

/-- The factorisation `prTop ∗ = (∗ × [0,1] ≅ [0,1]) ≫ ([0,1] ⟶ ∗)`. -/
theorem prTop_ptTop_factors : prTop ptTop = ptProdHomeo.hom ≫ termI := by
  ext x
  exact Subsingleton.elim _ _

/-- The augmentation of the interval: `ℤ[[0,1]] ⟶ ℤ[∗]`, induced by `[0,1] ⟶ ∗`. -/
abbrev augI : freeLightCondAbOfTopFunctor.obj (TopCat.of unitInterval) ⟶
    freeLightCondAbOfTopFunctor.obj ptTop :=
  freeLightCondAbOfTopFunctor.map termI

/-- **The mathematical content**: the kernel of `ℤ[prTop ∗]` is solid-null, i.e. the interval
`[0,1]` is solid-contractible.  (This is the base case of AN5; it is proved via the Čech
resolution of the Cantor cover of the interval.) -/
theorem solidNull_kernel_pt_of_augI
    (h : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map augI)) :
    SolidNull ((DerivedCategory.singleFunctor LightCondAb 0).obj
      (Limits.kernel prLightCondPt)) := by
  have hfact : prLightCondPt =
      freeLightCondAbOfTopFunctor.map ptProdHomeo.hom ≫ augI := by
    rw [prLightCondPt, augI, ← Functor.map_comp, prTop_ptTop_factors]
  haveI h1 : IsIso (freeLightCondAbOfTopFunctor.map ptProdHomeo.hom) := Functor.map_isIso _ _
  haveI h2 : IsIso ((DerivedCategory.singleFunctor LightCondAb 0).map
      (freeLightCondAbOfTopFunctor.map ptProdHomeo.hom)) := Functor.map_isIso _ _
  have hiso : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map
        (freeLightCondAbOfTopFunctor.map ptProdHomeo.hom)) :=
    (Work.TOOLKIT.toolkit_prop).of_iso _ h2
  have h2 : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map prLightCondPt) := by
    rw [hfact, Functor.map_comp]
    exact (Work.TOOLKIT.toolkit_prop).comp _ _ hiso h
  exact (solidEquiv_splitEpi _ _ i0_prLightCondPt).mp h2

/-- **The mathematical content**: the kernel of `ℤ[prTop ∗]` is solid-null, i.e. the interval
`[0,1]` is solid-contractible. -/
theorem solidNull_kernel_pt :
    SolidNull ((DerivedCategory.singleFunctor LightCondAb 0).obj
      (Limits.kernel prLightCondPt)) := by
  obtain ⟨t₀, t, ht0, ht1, ht2⟩ := Work.ANALYTIC.CechPt.dualCech_contractible
  have hsigma : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map Work.ANALYTIC.CechPt.sigmaAug) :=
    Work.ANALYTIC.CechPt.solidEquiv_sigmaAug
      (fun T => Work.ANALYTIC.CechPt.doubleDualUnit_solidEquiv T) t₀ t ht0 ht1 ht2
  set e : freeLightCondAbOfTopFunctor.obj ptTop ⟶
      (free ℤ).obj (LightProfinite.toCondensed Work.ATOM.pt) :=
    (free ℤ).map (lightProfiniteToLightCondSetIsoTopCatToLightCondSet.inv.app Work.ATOM.pt)
    with he
  have heq : Work.ANALYTIC.CechPt.sigmaAug = augI ≫ e := rfl
  have hiso : IsIso ((DerivedCategory.singleFunctor LightCondAb 0).map e) :=
    Functor.map_isIso _ _
  have hee : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map e) :=
    (Work.TOOLKIT.toolkit_prop).of_iso _ hiso
  have h1 : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map augI ≫
        (DerivedCategory.singleFunctor LightCondAb 0).map e) := by
    rw [← Functor.map_comp, ← heq]
    exact hsigma
  exact solidNull_kernel_pt_of_augI ((Work.TOOLKIT.toolkit_prop).of_comp_right _ _ hee h1)

/-- **AN5, base case (`S = PUnit`).**  The projection `∗ × [0,1] ⟶ ∗` induces a
solid-equivalence on free light condensed abelian groups. -/
theorem profinite_HI_pt :
    Submission.Blueprint.SolidEquiv
      (CategoryTheory.Functor.map (DerivedCategory.singleFunctor LightCondAb 0)
        (CategoryTheory.Functor.map
          _root_.LightCondensed.Solid.freeLightCondAbOfTopFunctor
          (Work.ANALYTIC.prTop
            (LightProfinite.toTopCat.obj (LightProfinite.of PUnit.{1}))))) :=
  (solidEquiv_splitEpi _ _ i0_prLightCondPt).mpr solidNull_kernel_pt

end Work.ANALYTIC
