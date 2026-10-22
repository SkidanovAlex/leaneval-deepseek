import Mathlib
import Submission.Work.TOOLKIT.Main
import Submission.Work.ANALYTIC.HICond
import Submission.Work.ANALYTIC.single_coproduct_bijective
import Submission.Work.ANALYTIC.solidEquiv_biprod

/-!
# Coproducts of solid-equivalences of free light condensed abelian groups

`Work.ANALYTIC.solidEquiv_single_free_sigma`: if `g x : X x ⟶ Y x` is a family of maps of light
condensed sets such that `ℤ[-]` applied to `g x` and placed in degree `0` is a solid-equivalence
for every `x`, then the same holds for the coproduct `Limits.Sigma.map g`.

## Strategy

Write `sC := CochainComplex.singleFunctor LightCondAb 0` (the complex concentrated in degree `0`)
and `zFree := ℤ[-]`.  Both `sC` (right adjoint: the kernel of `d 0 1`, see
`Work.ANALYTIC.single_coproduct_bijective`) and `zFree` (a left adjoint) preserve small
coproducts, hence there is a comparison isomorphism

`sigmaCmp X : (∐_x sC (zFree (X x))) ⟶ sC (zFree (∐ X))`

(`isIso_sigmaCmp`), and the naturality square `sigmaCmp_naturality`

`Sigma.map (fun x => sC.map (zFree.map (g x))) ≫ sigmaCmp Y
   = sigmaCmp X ≫ sC.map (zFree.map (Sigma.map g))`

is checked on the coproduct components.  Applying the localization functor `Q` gives a square of
isomorphisms conjugating `Q (Sigma.map (fun x => sC.map (zFree.map (g x))))` to the map of the
statement; the `sigma` field of `Work.TOOLKIT.toolkit_prop` makes the former a solid-equivalence,
and two-out-of-three for `SolidEquiv` (`of_comp_left`, `of_comp_right`, `of_iso`) transfers this
to the latter.
-/

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open Submission.Blueprint

noncomputable section

set_option linter.style.haveILetI false

/-! ## The two functors and their coproduct comparisons -/

/-- The free light condensed abelian group functor `ℤ[-]`. -/
abbrev zFree : LightCondSet ⥤ LightCondAb := LightCondensed.free (R := ℤ)

/-- The cochain complex with `A` in degree `0` and `0` elsewhere. -/
abbrev sC : LightCondAb ⥤ CochainComplex LightCondAb ℤ := CochainComplex.singleFunctor LightCondAb 0

/-- The inverse of the comparison map `∐_j sC (A j) ⟶ sC (∐ A)`; it exists because
`CochainComplex.singleFunctor LightCondAb 0` preserves small coproducts. -/
noncomputable def sCinv {J : Type} (A : J → LightCondAb) [HasCoproduct A] :
    sC.obj (∐ A) ⟶ ∐ fun j => sC.obj (A j) :=
  Classical.choose ((single_coproduct_bijective J A (∐ fun j => sC.obj (A j))).2
    (fun j => Limits.Sigma.ι (fun j => sC.obj (A j)) j))

/-- The characteristic property of `sCinv`: its components are the coprojections. -/
lemma sC_map_ι_comp_sCinv {J : Type} (A : J → LightCondAb) [HasCoproduct A] (j : J) :
    sC.map (Limits.Sigma.ι A j) ≫ sCinv A = Limits.Sigma.ι (fun j => sC.obj (A j)) j :=
  congrFun (Classical.choose_spec ((single_coproduct_bijective J A (∐ fun j => sC.obj (A j))).2
    (fun j => Limits.Sigma.ι (fun j => sC.obj (A j)) j))) j

/-- **`singleFunctor LightCondAb 0` preserves small coproducts.**  The comparison map
`Sigma.desc (fun j => sC.map (Sigma.ι A j))` is an isomorphism, with inverse `sCinv`. -/
noncomputable def sC_coprodIso {J : Type} (A : J → LightCondAb) [HasCoproduct A] :
    (∐ fun j => sC.obj (A j)) ≅ sC.obj (∐ A) where
  hom := Limits.Sigma.desc (fun j => sC.map (Limits.Sigma.ι A j))
  inv := sCinv A
  hom_inv_id := by
    apply Limits.Sigma.hom_ext
    intro j
    rw [Category.comp_id, ← Category.assoc, Limits.Sigma.ι_comp_desc, sC_map_ι_comp_sCinv]
  inv_hom_id := by
    apply (single_coproduct_bijective J A (sC.obj (∐ A))).1
    funext j
    show sC.map (Limits.Sigma.ι A j)
        ≫ (sCinv A ≫ Limits.Sigma.desc (fun j => sC.map (Limits.Sigma.ι A j)))
      = sC.map (Limits.Sigma.ι A j) ≫ 𝟙 (sC.obj (∐ A))
    rw [Category.comp_id, ← Category.assoc, sC_map_ι_comp_sCinv, Limits.Sigma.ι_comp_desc]

/-- The component of the coproduct comparison isomorphism of `sC`. -/
lemma ι_comp_sC_coprodIso_hom {J : Type} (A : J → LightCondAb) [HasCoproduct A] (j : J) :
    Limits.Sigma.ι (fun j => sC.obj (A j)) j ≫ (sC_coprodIso A).hom
      = sC.map (Limits.Sigma.ι A j) :=
  Limits.Sigma.ι_comp_desc _ j

/-- The component of the inverse of the coproduct comparison isomorphism of `sC`. -/
lemma sC_map_ι_comp_sC_coprodIso_inv {J : Type} (A : J → LightCondAb) [HasCoproduct A]
    (j : J) :
    sC.map (Limits.Sigma.ι A j) ≫ (sC_coprodIso A).inv
      = Limits.Sigma.ι (fun j => sC.obj (A j)) j :=
  sC_map_ι_comp_sCinv A j

/-- The component of `(sC_coprodIso A).hom`, in the form needed for rewriting in a composition. -/
lemma ι_comp_sC_coprodIso_hom_assoc {J : Type} (A : J → LightCondAb) [HasCoproduct A] (j : J)
    {W : CochainComplex LightCondAb ℤ} (h : sC.obj (∐ A) ⟶ W) :
    Limits.Sigma.ι (fun j => sC.obj (A j)) j ≫ (sC_coprodIso A).hom ≫ h
      = sC.map (Limits.Sigma.ι A j) ≫ h := by
  rw [← Category.assoc, ι_comp_sC_coprodIso_hom]

/-- The comparison isomorphism `ℤ[∐ X] ≅ ∐ ℤ[X x]` for the free functor (a left adjoint). -/
noncomputable def zFree_coprodIso {J : Type} (X : J → LightCondSet) [HasCoproduct X]
    [HasCoproduct fun j => zFree.obj (X j)] :
    zFree.obj (∐ X) ≅ ∐ fun j => zFree.obj (X j) :=
  (asIso (sigmaComparison zFree X)).symm

/-- The component of the coproduct comparison isomorphism of `zFree`. -/
lemma zFree_map_ι_comp_zFree_coprodIso_hom {J : Type} (X : J → LightCondSet) [HasCoproduct X]
    [HasCoproduct fun j => zFree.obj (X j)] (j : J) :
    zFree.map (Limits.Sigma.ι X j) ≫ (zFree_coprodIso X).hom
      = Limits.Sigma.ι (fun j => zFree.obj (X j)) j :=
  map_ι_comp_inv_sigmaComparison zFree X j

/-- The inverse component of the coproduct comparison isomorphism of `zFree`. -/
lemma ι_comp_zFree_coprodIso_inv {J : Type} (X : J → LightCondSet) [HasCoproduct X]
    [HasCoproduct fun j => zFree.obj (X j)] (j : J) :
    Limits.Sigma.ι (fun j => zFree.obj (X j)) j ≫ (zFree_coprodIso X).inv
      = zFree.map (Limits.Sigma.ι X j) :=
  ι_comp_sigmaComparison zFree X j

/-! ## The comparison `∐_x sC (zFree (X x)) ⟶ sC (zFree (∐ X))` -/

/-- The comparison map from the coproduct of the complexes `sC (zFree (X x))` to the complex
`sC (zFree (∐ X))`. -/
noncomputable def sigmaCmp {J : Type} (X : J → LightCondSet) [HasCoproduct X] :
    (∐ fun x => sC.obj (zFree.obj (X x))) ⟶ sC.obj (zFree.obj (∐ X)) :=
  Limits.Sigma.desc (fun x => sC.map (zFree.map (Limits.Sigma.ι X x)))

/-- The characteristic property of `sigmaCmp`. -/
lemma ι_comp_sigmaCmp {J : Type} (X : J → LightCondSet) [HasCoproduct X] (x : J) :
    Limits.Sigma.ι (fun x => sC.obj (zFree.obj (X x))) x ≫ sigmaCmp X
      = sC.map (zFree.map (Limits.Sigma.ι X x)) :=
  Limits.Sigma.ι_comp_desc _ x

/-- The characteristic property of `sigmaCmp`, in the form needed in a composition. -/
lemma ι_comp_sigmaCmp_assoc {J : Type} (X : J → LightCondSet) [HasCoproduct X] (x : J)
    {W : CochainComplex LightCondAb ℤ} (h : sC.obj (zFree.obj (∐ X)) ⟶ W) :
    Limits.Sigma.ι (fun x => sC.obj (zFree.obj (X x))) x ≫ sigmaCmp X ≫ h
      = sC.map (zFree.map (Limits.Sigma.ι X x)) ≫ h := by
  rw [← Category.assoc, ι_comp_sigmaCmp]

/-- `sigmaCmp` is an isomorphism: it is the composite of the coproduct comparisons of `zFree`
and of `sC`. -/
lemma isIso_sigmaCmp {J : Type} (X : J → LightCondSet) [HasCoproduct X] :
    IsIso (sigmaCmp X) := by
  have h : sigmaCmp X = (sC_coprodIso (fun x => zFree.obj (X x))).hom ≫
      sC.map ((zFree_coprodIso X).inv) := by
    apply Limits.Sigma.hom_ext
    intro x
    rw [ι_comp_sigmaCmp, ι_comp_sC_coprodIso_hom_assoc, ← sC.map_comp,
      ι_comp_zFree_coprodIso_inv]
  rw [h]
  infer_instance

/-! ## The naturality square -/

/-- A component of `Sigma.map`, in the form needed in a composition. -/
lemma Sigma_map_component_assoc {J : Type} (K L : J → CochainComplex LightCondAb ℤ)
    [HasCoproduct K] [HasCoproduct L] (f : ∀ j, K j ⟶ L j) (j : J)
    {W : CochainComplex LightCondAb ℤ}
    (h : (∐ L) ⟶ W) :
    Limits.Sigma.ι K j ≫ Limits.Sigma.map f ≫ h = f j ≫ Limits.Sigma.ι L j ≫ h := by
  rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc]

/-- The naturality square of the comparison `sigmaCmp`, at the level of cochain complexes. -/
lemma sigmaCmp_naturality {J : Type} (X Y : J → LightCondSet.{0}) [HasCoproduct X]
    [HasCoproduct Y] (g : ∀ x, X x ⟶ Y x) :
    Limits.Sigma.map (fun x => sC.map (zFree.map (g x))) ≫ sigmaCmp Y
      = sigmaCmp X ≫ sC.map (zFree.map (Limits.Sigma.map g)) := by
  apply Limits.Sigma.hom_ext
  intro x
  rw [Sigma_map_component_assoc (fun x => sC.obj (zFree.obj (X x)))
      (fun x => sC.obj (zFree.obj (Y x))) (fun x => sC.map (zFree.map (g x))) x,
    ι_comp_sigmaCmp_assoc, ι_comp_sigmaCmp]
  simp only [← Functor.map_comp, Limits.Sigma.ι_map]

/-! ## The theorem -/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed in
/-- **Coproducts of solid-equivalences of free light condensed abelian groups.**  If for every
`x : ι` the map `g x : X x ⟶ Y x` of light condensed sets induces a solid-equivalence after
applying `ℤ[-]` and placing in degree `0`, then so does the coproduct `Limits.Sigma.map g`

  `∐_x X x ⟶ ∐_x Y x`.

Route: `single` (`singleFunctor` in degree `0`) and `free ℤ` both commute with coproducts (they are
left adjoints), so `single.map (free.map (Sigma.map g))` is conjugate by the canonical
isomorphisms `∐_x single (free (X x)) ≅ single (free (∐ X))` to `Limits.Sigma.map (fun x =>
single.map (free.map (g x)))`; `Submission.Blueprint.ToolkitProp.sigma`
(`Work.TOOLKIT.toolkit_prop`) then applies to the family of maps of complexes
`x ↦ single (free (g x))`, and conjugation by isomorphisms is
`ToolkitProp.of_comp_left`/`of_comp_right`/`of_iso`.  The binary analogue is already proved in
`Submission/Work/ANALYTIC/solidEquiv_biprod.lean` and the coproduct-preservation of `single` in
`Submission/Work/ANALYTIC/solidNull_coproduct.lean`. -/
theorem solidEquiv_single_free_sigma {ι : Type} (X Y : ι → LightCondSet.{0})
    [HasCoproduct X] [HasCoproduct Y] (g : ∀ x, X x ⟶ Y x)
    (h : ∀ x, Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map
        ((LightCondensed.free (R := ℤ)).map (g x)))) :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map
        ((LightCondensed.free (R := ℤ)).map (Limits.Sigma.map g))) := by
  haveI : IsIso (sigmaCmp X) := isIso_sigmaCmp X
  haveI : IsIso (sigmaCmp Y) := isIso_sigmaCmp Y
  have hf : ∀ x, SolidEquiv (DerivedCategory.Q.map (sC.map (zFree.map (g x)))) := fun x => by
    have hx := h x
    rw [← DerivedCategory.Q_map_single_map] at hx
    exact hx
  have hsigma : SolidEquiv (DerivedCategory.Q.map
      (Limits.Sigma.map (fun x => sC.map (zFree.map (g x))))) :=
    Work.TOOLKIT.solidEquiv_sigma ι (fun x => sC.obj (zFree.obj (X x)))
      (fun x => sC.obj (zFree.obj (Y x))) (fun x => sC.map (zFree.map (g x))) hf
  have hc : DerivedCategory.Q.map (Limits.Sigma.map (fun x => sC.map (zFree.map (g x))))
        ≫ DerivedCategory.Q.map (sigmaCmp Y)
      = DerivedCategory.Q.map (sigmaCmp X)
        ≫ DerivedCategory.Q.map (sC.map (zFree.map (Limits.Sigma.map g))) := by
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
      sigmaCmp_naturality X Y g]
  have h1 : SolidEquiv (DerivedCategory.Q.map
      (Limits.Sigma.map (fun x => sC.map (zFree.map (g x))))
        ≫ DerivedCategory.Q.map (sigmaCmp Y)) :=
    Work.TOOLKIT.toolkit_prop.comp
      (DerivedCategory.Q.map (Limits.Sigma.map (fun x => sC.map (zFree.map (g x)))))
      (DerivedCategory.Q.map (sigmaCmp Y)) hsigma
      (Work.TOOLKIT.toolkit_prop.of_iso _ inferInstance)
  rw [hc] at h1
  have h2 : SolidEquiv (DerivedCategory.Q.map (sC.map (zFree.map (Limits.Sigma.map g)))) :=
    Work.TOOLKIT.toolkit_prop.of_comp_left (DerivedCategory.Q.map (sigmaCmp X))
      (DerivedCategory.Q.map (sC.map (zFree.map (Limits.Sigma.map g))))
      (Work.TOOLKIT.toolkit_prop.of_iso (DerivedCategory.Q.map (sigmaCmp X)) inferInstance) h1
  rw [← DerivedCategory.Q_map_single_map]
  exact h2

end

end Work.ANALYTIC
