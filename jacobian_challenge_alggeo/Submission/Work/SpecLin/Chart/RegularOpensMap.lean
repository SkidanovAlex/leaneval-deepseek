/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The morphism `W → 𝔸¹` attached to a rational function regular on `W`

For a curve `C` over a field `K` and a rational function `x : K(C)`, the open subscheme
`W = regularOpens C x` consists of the points at which `x` is regular.  This file
constructs

* `Work.SpecLin.Chart.regularOpensSection`: `x` as an element of `Γ(C, W)`;
* `Work.SpecLin.Chart.regularOpensMap`: the `K`-morphism `W.toScheme ⟶ 𝔸¹_K`
  (= `Spec (Polynomial K)`) whose pullback of the coordinate is `x`.
-/
import Mathlib
import Submission.Work.SpecLin.Chart.Regular
import Submission.Work.CurveBasics.All

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TopCat TopCat.Presheaf Opposite
open scoped Classical

universe u

namespace Work.SpecLin.Chart

open Work.CurveBasics

variable {K : Type u} [Field K]

/-! ## The generic point is not a place -/

/-- The generic point of a curve is not a closed point. -/
theorem genericPoint_ne_place_point (C : Curve K) (Q : C.Place) :
    Q.point ≠ genericPoint C.left := by
  intro h
  have hcl : closure ({genericPoint C.left} : Set C.left) = Set.univ :=
    (genericPoint_spec C.left)
  have hclosed : IsClosed ({genericPoint C.left} : Set C.left) := h ▸ Q.isClosed
  rw [hclosed.closure_eq] at hcl
  have hsub : Subsingleton C.left := ⟨fun x y => by
    have hx : x ∈ ({genericPoint C.left} : Set C.left) := hcl.symm ▸ Set.mem_univ x
    have hy : y ∈ ({genericPoint C.left} : Set C.left) := hcl.symm ▸ Set.mem_univ y
    rw [Set.mem_singleton_iff] at hx hy
    rw [hx, hy]⟩
  exact not_subsingleton C.left hsub

/-- The generic point lies in `regularOpens C x`. -/
theorem genericPoint_mem_regularOpens (C : Curve K) (x : C.functionField) :
    genericPoint C.left ∈ regularOpens C x := by
  rw [mem_regularOpens]
  intro Q hQ
  exact absurd hQ (genericPoint_ne_place_point C Q)

/-- `regularOpens C x` is nonempty. -/
instance nonempty_regularOpens (C : Curve K) (x : C.functionField) :
    Nonempty (regularOpens C x) :=
  ⟨genericPoint C.left, genericPoint_mem_regularOpens C x⟩

/-! ## Sections over an open where a rational function is regular -/

/-- Every nonempty open of a curve contains the generic point. -/
theorem genericPoint_mem_of_nonempty {C : Curve K} (V : C.left.Opens) [Nonempty V] :
    genericPoint C.left ∈ V := by
  obtain ⟨x⟩ := (inferInstance : Nonempty V)
  exact (genericPoint_spec C.left).mem_open_set_iff V.isOpen |>.mpr ⟨x.1, trivial, x.2⟩

/-- Restricting a section along an `Opens`-morphism does not change its germ at the generic
point. -/
theorem germToFunctionField_map_eq {C : Curve K} {U V : C.left.Opens} (i : V ⟶ U)
    [Nonempty U] [Nonempty V] (s : Γ(C.left, U)) :
    (C.germToFunctionField V).hom ((C.left.presheaf.map i.op) s)
      = (C.germToFunctionField U).hom s := by
  have hg : ∀ {W : C.left.Opens} (h1 h2 : (genericPoint C.left) ∈ W),
      C.left.presheaf.germ W (genericPoint C.left) h1
        = C.left.presheaf.germ W (genericPoint C.left) h2 :=
    fun h1 h2 => congrArg _ (Subsingleton.elim h1 h2)
  have hstep := TopCat.Presheaf.germ_res_apply C.left.presheaf i (genericPoint C.left)
    (genericPoint_mem_of_nonempty V) s
  rw [show C.germToFunctionField V
        = C.left.presheaf.germ V (genericPoint C.left)
            (genericPoint_mem_of_nonempty V) from hg _ _,
      show C.germToFunctionField U
        = C.left.presheaf.germ U (genericPoint C.left) _ from hg _ _]
  exact hstep

/-- A rational function which is regular at every place of an open `W` is a section over
`W`. -/
theorem mem_range_germToFunctionField_of_regularOn (C : Curve K) (W : C.left.Opens)
    [Nonempty W] (f : C.functionField) (hf : C.RegularOn W f) :
    f ∈ (C.germToFunctionField W).hom.range := by
  classical
  let ι := {i : C.left.affineOpens // genericPoint C.left ∈ (i.1 : C.left.Opens) ∧ i.1 ≤ W}
  haveI hind : ∀ i : ι, Nonempty (i.1.1 : C.left.Opens) :=
    fun i => ⟨genericPoint C.left, i.2.1⟩
  let Vc : C.left.Opens := ⨆ i : ι, ((i.1.1) : C.left.Opens)
  have hcov : W = Vc := by
    apply le_antisymm
    · intro z hz
      obtain ⟨-, ⟨V, hV, rfl⟩, hzV, hVW⟩ :=
        (C.left.isBasis_affineOpens : _).exists_subset_of_mem_open hz W.isOpen
      have hηV : genericPoint C.left ∈ V :=
        (genericPoint_spec C.left).mem_open_set_iff V.isOpen |>.mpr ⟨z, trivial, hzV⟩
      exact le_iSup (fun i : ι => ((i.1.1) : C.left.Opens)) ⟨⟨V, hV⟩, hηV, hVW⟩ hzV
    · apply iSup_le; intro i; exact i.2.2
  haveI hVcne : Nonempty Vc := hcov ▸ ‹Nonempty W›
  have hkey : f ∈ (C.germToFunctionField Vc).hom.range := by
    have hsheaf : C.left.presheaf.IsSheafUniqueGluing :=
      (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing C.left.presheaf).mp (C.left.sheaf).2
    have hmem : ∀ i : ι, f ∈ (C.germToFunctionField (i.1.1)).hom.range := fun i =>
      (Work.CurveBasics.BaseChange.mem_range_germ_iff (C := C) (i.1.1) i.1.2 f).mpr
        (fun Q hQ => hf Q (i.2.2 hQ))
    let sf : ∀ i : ι, Γ(C.left, (i.1.1 : C.left.Opens)) := fun i => Classical.choose (hmem i)
    have hsf : ∀ i : ι, (C.germToFunctionField (i.1.1)).hom (sf i) = f :=
      fun i => Classical.choose_spec (hmem i)
    have hgerm : ∀ {U : C.left.Opens} (h1 h2 : genericPoint C.left ∈ U),
        C.left.presheaf.germ U (genericPoint C.left) h1
          = C.left.presheaf.germ U (genericPoint C.left) h2 :=
      fun h1 h2 => congrArg _ (Subsingleton.elim h1 h2)
    have hcompat : C.left.presheaf.IsCompatible (fun i : ι => ((i.1.1) : C.left.Opens)) sf := by
      intro i j
      let Ui : C.left.Opens := i.1.1
      let Uj : C.left.Opens := j.1.1
      let Uij : C.left.Opens := Ui ⊓ Uj
      have hηij : genericPoint C.left ∈ Uij := ⟨i.2.1, j.2.1⟩
      haveI : Nonempty Uij := ⟨genericPoint C.left, hηij⟩
      change C.left.presheaf.map (TopologicalSpace.Opens.infLELeft Ui Uj).op (sf i)
        = C.left.presheaf.map (TopologicalSpace.Opens.infLERight Ui Uj).op (sf j)
      apply Scheme.germToFunctionField_injective C.left Uij
      have h1 : C.left.presheaf.germ Uij (genericPoint C.left) hηij
            (C.left.presheaf.map (TopologicalSpace.Opens.infLELeft Ui Uj).op (sf i)) = f := by
        rw [TopCat.Presheaf.germ_res_apply]
        exact (congrArg (fun m => (ConcreteCategory.hom m) (sf i))
          (hgerm _ ((TopologicalSpace.Opens.infLELeft Ui Uj).le hηij)).symm).trans (hsf i)
      have h2 : C.left.presheaf.germ Uij (genericPoint C.left) hηij
            (C.left.presheaf.map (TopologicalSpace.Opens.infLERight Ui Uj).op (sf j)) = f := by
        rw [TopCat.Presheaf.germ_res_apply]
        exact (congrArg (fun m => (ConcreteCategory.hom m) (sf j))
          (hgerm _ ((TopologicalSpace.Opens.infLERight Ui Uj).le hηij)).symm).trans (hsf j)
      rw [show C.left.germToFunctionField Uij
            = C.left.presheaf.germ Uij (genericPoint C.left) hηij from hgerm _ _]
      rw [h1, h2]
    obtain ⟨g, hg, -⟩ := hsheaf (fun i : ι => ((i.1.1) : C.left.Opens)) sf hcompat
    have hιne : Nonempty ι := by
      obtain ⟨z, hz⟩ := ‹Nonempty W›
      obtain ⟨-, ⟨V, hV, rfl⟩, hzV, hVW⟩ :=
        (C.left.isBasis_affineOpens : _).exists_subset_of_mem_open hz W.isOpen
      have hηV : genericPoint C.left ∈ V :=
        (genericPoint_spec C.left).mem_open_set_iff V.isOpen |>.mpr ⟨z, trivial, hzV⟩
      exact ⟨⟨⟨V, hV⟩, hηV, hVW⟩⟩
    obtain ⟨i⟩ := hιne
    refine ⟨g, ?_⟩
    rw [← germToFunctionField_map_eq (C := C)
      (TopologicalSpace.Opens.leSupr (fun i : ι => ((i.1.1) : C.left.Opens)) i) g]
    rw [hg i]
    exact hsf i
  obtain ⟨g, hg⟩ := hkey
  exact ⟨_, (germToFunctionField_map_eq (C := C) (homOfLE (le_of_eq hcov)) g).trans hg⟩

/-- `x`, viewed as a section of the structure sheaf over `regularOpens C x`. -/
noncomputable def regularOpensSection (C : Curve K) (x : C.functionField) :
    Γ(C.left, regularOpens C x) :=
  Classical.choose (mem_range_germToFunctionField_of_regularOn C (regularOpens C x) x
    (regularOn_regularOpens C x))

/-- The section `regularOpensSection C x` restricts to `x`. -/
theorem germToFunctionField_regularOpensSection (C : Curve K) (x : C.functionField) :
    (C.germToFunctionField (regularOpens C x)).hom (regularOpensSection C x) = x :=
  Classical.choose_spec (mem_range_germToFunctionField_of_regularOn C (regularOpens C x) x
    (regularOn_regularOpens C x))


/-! ## The structure ring homomorphism and `toSpecΓ` -/

/-- The structure ring homomorphism `K ⟶ Γ(X, ⊤)` of a `K`-scheme, read through
`Γ(Spec K, ⊤) ≅ K`. -/
noncomputable def structureRingHom {K : Type u} [Field K] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of K))] : K →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (X ↘ Spec (CommRingCat.of K)).appTop).hom

/-- The canonical morphism `Scheme.toSpecΓ` is a morphism over `Spec K`. -/
theorem toSpecΓ_comp_structureRingHom {K : Type u} [Field K] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of K))] :
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (structureRingHom X)) =
      X ↘ Spec (CommRingCat.of K) := by
  have h1 : CommRingCat.ofHom (structureRingHom X)
      = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (X ↘ Spec (CommRingCat.of K)).appTop := rfl
  rw [h1, Spec.map_comp]
  rw [← Scheme.toSpecΓ_naturality_assoc (X ↘ Spec (CommRingCat.of K))]
  rw [toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-! ## The morphism `W ⟶ 𝔸¹_K` -/

/-- The section `x` of the structure sheaf of `W = regularOpens C x`, read in
`Γ(W.toScheme, ⊤)`. -/
noncomputable def regularOpensTopSection (C : Curve K) (x : C.functionField) :
    Γ((regularOpens C x).toScheme, ⊤) :=
  (Scheme.Opens.topIso (regularOpens C x)).inv (regularOpensSection C x)

/-- The `K`-algebra homomorphism `K[X] → Γ(W, ⊤)` sending `X` to the section `x`. -/
noncomputable def regularOpensCoeff (C : Curve K) (x : C.functionField) :
    Polynomial K →+* Γ((regularOpens C x).toScheme, ⊤) :=
  Polynomial.eval₂RingHom (structureRingHom (regularOpens C x).toScheme)
    (regularOpensTopSection C x)

/-- The morphism `W = regularOpens C x ⟶ 𝔸¹_K = Spec K[X]` whose pullback of the coordinate
is the section `x`. -/
noncomputable def regularOpensMap (C : Curve K) (x : C.functionField) :
    (regularOpens C x).toScheme ⟶ Spec (CommRingCat.of (Polynomial K)) :=
  (regularOpens C x).toScheme.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (regularOpensCoeff C x))

/-- The pullback of a polynomial along `regularOpensMap` is its value at the section `x`. -/
theorem ΓSpecIso_inv_comp_regularOpensMap_appTop (C : Curve K) (x : C.functionField) :
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv ≫
        (regularOpensMap C x).appTop =
      CommRingCat.ofHom (regularOpensCoeff C x) := by
  have h1 : (regularOpensMap C x).appTop =
      (Spec.map (CommRingCat.ofHom (regularOpensCoeff C x))).appTop ≫
        ((regularOpens C x).toScheme.toSpecΓ).appTop :=
    Scheme.Hom.comp_appTop _ _
  rw [h1, Scheme.toSpecΓ_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  simp

/-- `regularOpensMap` is a morphism over `Spec K`. -/
theorem regularOpensMap_over (C : Curve K) (x : C.functionField) :
    regularOpensMap C x ≫ Spec.map (CommRingCat.ofHom Polynomial.C) =
      (regularOpens C x).toScheme ↘ Spec (CommRingCat.of K) := by
  have hcomp : (regularOpensCoeff C x).comp Polynomial.C =
      structureRingHom (regularOpens C x).toScheme := by
    ext k
    simp only [RingHom.comp_apply, regularOpensCoeff, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C]
  have h2 : (CommRingCat.ofHom Polynomial.C) ≫ (CommRingCat.ofHom (regularOpensCoeff C x)) =
      CommRingCat.ofHom (structureRingHom (regularOpens C x).toScheme) := by
    ext z
    rw [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom, ConcreteCategory.hom_ofHom]
    exact congrArg (fun f => f z) hcomp
  rw [regularOpensMap, Category.assoc, ← Spec.map_comp, h2]
  exact toSpecΓ_comp_structureRingHom _

end Work.SpecLin.Chart
