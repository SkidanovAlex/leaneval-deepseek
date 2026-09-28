import Mathlib
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.Defs
import Submission.Work.StemsB.Fibrations
import Submission.Work.Thom.Cohomology
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.StemsB.AToolsR
import Submission.Work.Thom.relCohHomeomorph
import Submission.Work.Thom.CapGlue.isIso_relComplexMap_homeomorph

/-!
# `Work.Serre.ThomCylAt` is invariant under a homeomorphism of the target

`Work.Serre.ThomCylAt r N q` is the statement that the pair `(cyl q, range (cylIncl q))` carries a
Thom class for the map `q` (a class `U` whose mixed cup product with the pullback along the
retraction `cylRetract q` is an isomorphism in the range `m + r + 1 ≤ N + 1`).

A homeomorphism `e : Γ ≃ₜ Γ'` together with a continuous map `q' : C(X,Γ)` satisfying
`q' = e.symm ∘ q` makes `q` and `q'` "the same" map, so `ThomCylAt` is the same proposition for
both.  The proof is the standard one for a naturality statement:

* the two mapping cylinders are homeomorphic (the identity on `X × I` and `e` on the target):
  `cylHomeoOfHomeo`, and it carries `range (cylIncl q')` onto `range (cylIncl q)`;
* relative cohomology is invariant under a homeomorphism of pairs
  (`Work.Thom.CapGlue.isIso_relComplexMap_homeomorph`), which transports the Thom class `U` to
  `U' = (cylHomeo)^* U`;
* naturality of the mixed cup product (`Work.StemsB.mixedCupC_pairNaturalR`) identifies the
  `q'`-cup map with the composite of the `q`-cup map with the isomorphism `(cylHomeo)^*` and the
  isomorphism `(e.symm)^*` of the coefficient-side cohomology `H^m(Γ;ℚ) ≅ H^m(Γ';ℚ)`.

The mapping-cylinder homeomorphism is constructed in this file: for compatible maps
`f : C(P,X)`, `g : C(P,X')`, `φ : C(X,X')` with `φ ∘ f = g` there is an induced map
`cylMap f g φ : C(cyl f, cyl g)`, and it is a homeomorphism when `φ` is one.
-/

namespace Work.Serre

set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

noncomputable section

/-! ## Maps of mapping cylinders

For continuous maps `f : C(P,X)`, `g : C(P,X')` and `φ : C(X,X')` with `φ ∘ f = g`, the gluing
relation of `cyl f` is carried into that of `cyl g` by the map which is the identity on `P × I` and
`φ` on the target.  This gives `Work.Serre.cylMap f g φ : C(cyl f, cyl g)`. -/

section CylMap

variable {P X X' : Type} [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace X']

/-- The map on `(P × I) ⊕ X` underlying the map of mapping cylinders induced by `φ`. -/
def cylRelMap (φ : C(X, X')) : (P × unitInterval) ⊕ X → (P × unitInterval) ⊕ X' :=
  Sum.elim (fun a => (Sum.inl a : (P × unitInterval) ⊕ X')) (fun x => Sum.inr (φ x))

omit [TopologicalSpace P] in
@[simp] theorem cylRelMap_inl (φ : C(X, X')) (a : P × unitInterval) :
    cylRelMap (X := X) (X' := X') φ (Sum.inl a : (P × unitInterval) ⊕ X) = Sum.inl a := rfl

omit [TopologicalSpace P] in
@[simp] theorem cylRelMap_inr (φ : C(X, X')) (x : X) :
    cylRelMap (X := X) (X' := X') φ (Sum.inr x : (P × unitInterval) ⊕ X) = Sum.inr (φ x) :=
  rfl

theorem continuous_cylRelMap (φ : C(X, X')) : Continuous (cylRelMap (P := P) φ) := by
  show Continuous (Sum.elim (fun a => (Sum.inl a : (P × unitInterval) ⊕ X'))
    (fun x => Sum.inr (φ x)))
  exact Continuous.sumElim continuous_inl (continuous_inr.comp φ.continuous)

/-- A relation step is carried to a relation step. -/
theorem cylRel_map (f : C(P, X)) (g : C(P, X')) (φ : C(X, X')) (hφ : ∀ p, φ (f p) = g p)
    {a b : (P × unitInterval) ⊕ X} (hab : cylRel f a b) :
    cylRel g (cylRelMap φ a) (cylRelMap φ b) := by
  obtain ⟨p, rfl, rfl⟩ := hab
  exact ⟨p, rfl, by simp only [cylRelMap_inr, hφ p]⟩

/-- The gluing relation of `cyl f` is carried into that of `cyl g`. -/
theorem cylRelMap_eqvGen (f : C(P, X)) (g : C(P, X')) (φ : C(X, X')) (hφ : ∀ p, φ (f p) = g p)
    (a b : (P × unitInterval) ⊕ X) (hab : Relation.EqvGen (cylRel f) a b) :
    Relation.EqvGen (cylRel g) (cylRelMap φ a) (cylRelMap φ b) := by
  induction hab with
  | rel x y h => exact Relation.EqvGen.rel _ _ (cylRel_map f g φ hφ h)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- The function underlying the map of mapping cylinders induced by `φ`. -/
def cylMapFun (f : C(P, X)) (g : C(P, X')) (φ : C(X, X')) (hφ : ∀ p, φ (f p) = g p) :
    cyl f → cyl g :=
  Quotient.lift (fun a => Quotient.mk'' (cylRelMap φ a))
    (fun a b hab => Quotient.sound (cylRelMap_eqvGen f g φ hφ a b hab))

theorem continuous_cylMapFun (f : C(P, X)) (g : C(P, X')) (φ : C(X, X'))
    (hφ : ∀ p, φ (f p) = g p) : Continuous (cylMapFun f g φ hφ) := by
  show Continuous (Quotient.lift (fun a => Quotient.mk'' (cylRelMap φ a)) _)
  exact Continuous.quotient_lift (continuous_quotient_mk'.comp (continuous_cylRelMap φ)) _

/-- **The map of mapping cylinders induced by a compatible map** `φ : C(X,X')`, `φ ∘ f = g`. -/
def cylMap (f : C(P, X)) (g : C(P, X')) (φ : C(X, X')) (hφ : ∀ p, φ (f p) = g p) :
    C(cyl f, cyl g) :=
  ⟨cylMapFun f g φ hφ, continuous_cylMapFun f g φ hφ⟩

theorem cylMap_apply_inl (f : C(P, X)) (g : C(P, X')) (φ : C(X, X')) (hφ : ∀ p, φ (f p) = g p)
    (a : P × unitInterval) :
    cylMap f g φ hφ (Quotient.mk'' (Sum.inl a)) = Quotient.mk'' (Sum.inl a) := by
  change cylMapFun f g φ hφ (Quotient.mk'' (Sum.inl a)) = Quotient.mk'' (Sum.inl a)
  simp only [cylMapFun, Quotient.lift_mk, cylRelMap_inl]

theorem cylMap_apply_inr (f : C(P, X)) (g : C(P, X')) (φ : C(X, X')) (hφ : ∀ p, φ (f p) = g p)
    (x : X) :
    cylMap f g φ hφ (Quotient.mk'' (Sum.inr x)) = Quotient.mk'' (Sum.inr (φ x)) := by
  change cylMapFun f g φ hφ (Quotient.mk'' (Sum.inr x)) = Quotient.mk'' (Sum.inr (φ x))
  simp only [cylMapFun, Quotient.lift_mk, cylRelMap_inr]

@[simp] theorem cylRetract_mk_inl (f : C(P, X)) (a : P × unitInterval) :
    cylRetract f (Quotient.mk'' (Sum.inl a) : cyl f) = f a.1 := by
  change Quotient.lift (cylRetractFun f) (cylRetractFun_rel f)
    (Quotient.mk'' (Sum.inl a) : cyl f) = f a.1
  rw [Quotient.lift_mk]
  rfl

@[simp] theorem cylRetract_mk_inr (f : C(P, X)) (x : X) :
    cylRetract f (Quotient.mk'' (Sum.inr x) : cyl f) = x := by
  change Quotient.lift (cylRetractFun f) (cylRetractFun_rel f)
    (Quotient.mk'' (Sum.inr x) : cyl f) = x
  rw [Quotient.lift_mk]
  rfl

/-- The retraction of the mapping cylinder is compatible with the induced map of cylinders. -/
theorem cylRetract_cylMap_eq (f : C(P, X)) (g : C(P, X')) (φ : X ≃ₜ X')
    (hφ : ∀ p, φ (f p) = g p) :
    cylRetract f = ((φ.symm : C(X', X)).comp (cylRetract g)).comp (cylMap f g (φ : C(X, X')) hφ) := by
  apply ContinuousMap.ext
  intro x
  refine Quotient.inductionOn
    (motive := fun y => cylRetract f y = φ.symm (cylRetract g (cylMap f g φ hφ y))) x ?_
  intro a
  cases a with
  | inl pt =>
    rw [cylMap_apply_inl]
    simp only [cylRetract_mk_inl]
    rw [← hφ pt.1]
    exact (φ.symm_apply_apply (f pt.1)).symm
  | inr z =>
    rw [cylMap_apply_inr]
    simp only [cylRetract_mk_inr]
    exact (φ.symm_apply_apply z).symm

end CylMap

/-! ## The homeomorphism of mapping cylinders induced by a homeomorphism of the target -/

section CylHomeo

variable {P X X' : Type} [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace X']

/-- **The homeomorphism of mapping cylinders induced by a homeomorphism `φ : X ≃ₜ X'` compatible
with the maps `f : C(P,X)`, `g : C(P,X')`.** -/
def cylHomeoOfHomeo (f : C(P, X)) (g : C(P, X')) (φ : X ≃ₜ X')
    (hc : ∀ p, φ (f p) = g p) (hd : ∀ p, φ.symm (g p) = f p) : cyl f ≃ₜ cyl g where
  toFun := cylMap f g (φ : C(X, X')) hc
  invFun := cylMap g f (φ.symm : C(X', X)) hd
  left_inv := by
    intro x
    refine Quotient.inductionOn
      (motive := fun y => cylMap g f (φ.symm : C(X', X)) hd
        (cylMap f g (φ : C(X, X')) hc y) = y) x ?_
    intro a
    cases a with
    | inl pt => rw [cylMap_apply_inl, cylMap_apply_inl]
    | inr z =>
      rw [cylMap_apply_inr, cylMap_apply_inr]
      exact congrArg (fun w => Quotient.mk'' (Sum.inr w : (P × unitInterval) ⊕ X))
        (φ.symm_apply_apply z)
  right_inv := by
    intro y
    refine Quotient.inductionOn
      (motive := fun z => cylMap f g (φ : C(X, X')) hc
        (cylMap g f (φ.symm : C(X', X)) hd z) = z) y ?_
    intro a
    cases a with
    | inl pt => rw [cylMap_apply_inl, cylMap_apply_inl]
    | inr z =>
      rw [cylMap_apply_inr, cylMap_apply_inr]
      exact congrArg (fun w => Quotient.mk'' (Sum.inr w : (P × unitInterval) ⊕ X'))
        (φ.apply_symm_apply z)

/-- The homeomorphism of cylinders is the identity on the bottom copy of the source. -/
theorem cylHomeoOfHomeo_apply_cylIncl (f : C(P, X)) (g : C(P, X')) (φ : X ≃ₜ X')
    (hc : ∀ p, φ (f p) = g p) (hd : ∀ p, φ.symm (g p) = f p) (p : P) :
    cylHomeoOfHomeo f g φ hc hd (cylIncl f p) = cylIncl g p :=
  cylMap_apply_inl f g (φ : C(X, X')) hc (p, 0)

/-- The inverse of the homeomorphism of cylinders is the identity on the bottom copy of the
source. -/
theorem cylHomeoOfHomeo_symm_apply_cylIncl (f : C(P, X)) (g : C(P, X')) (φ : X ≃ₜ X')
    (hc : ∀ p, φ (f p) = g p) (hd : ∀ p, φ.symm (g p) = f p) (p : P) :
    (cylHomeoOfHomeo f g φ hc hd).symm (cylIncl g p) = cylIncl f p :=
  cylMap_apply_inl g f (φ.symm : C(X', X)) hd (p, 0)

end CylHomeo

/-! ## The pullback of absolute cohomology along a homeomorphism is an isomorphism -/

/-- **The pullback `CohMap e` along a homeomorphism `e` is an isomorphism**, with inverse
`CohMap e.symm`.  (The category-theoretic form of the invariance of singular cohomology under
homeomorphism, in the workspace's own `Coh`/`CohMap` vocabulary.) -/
theorem isIso_CohMap_of_homeo {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (R : Type) [CommRing R] (n : ℕ) :
    IsIso (Work.Thom.CohMap (e : C(A, B)) R n) := by
  have h1 : (e : C(A, B)).comp (e.symm : C(B, A)) = ContinuousMap.id B := by
    ext y
    exact e.apply_symm_apply y
  have h2 : (e.symm : C(B, A)).comp (e : C(A, B)) = ContinuousMap.id A := by
    ext x
    exact e.symm_apply_apply x
  refine IsIso.mk ⟨Work.Thom.CohMap (e.symm : C(B, A)) R n, ?_, ?_⟩
  · rw [← Work.Thom.CohMap_comp (f := (e.symm : C(B, A))) (g := (e : C(A, B))), h1,
      Work.Thom.CohMap_id]
  · rw [← Work.Thom.CohMap_comp (f := (e : C(A, B))) (g := (e.symm : C(B, A))), h2,
      Work.Thom.CohMap_id]

/-! ## The invariance theorem -/

/-- **`Work.Serre.ThomCylAt` only depends on the map `q` up to homeomorphism of the target.**
If `e : Γ ≃ₜ Γ'` and `q' : C(X,Γ)`, `q : C(X,Γ')` satisfy `q' = e.symm ∘ q`, then the Thom case for
`q` implies the Thom case for `q'` (with the class transported along the induced homeomorphism of
mapping cylinders). -/
theorem thomCylAt_of_homeo (r N : ℕ) {Γ Γ' : Type} [TopologicalSpace Γ] [TopologicalSpace Γ']
    (e : Γ ≃ₜ Γ') {X : Type} [TopologicalSpace X] (q : C(X, Γ')) (q' : C(X, Γ))
    (hq' : ∀ x, q' x = e.symm (q x)) (h : Work.Serre.ThomCylAt r N q) :
    Work.Serre.ThomCylAt r N q' := by
  classical
  obtain ⟨U, hU⟩ := h
  -- the compatibility of `q` and `q'` through the homeomorphism `e`
  have he_q : ∀ x : X, e (q' x) = q x := fun x => by
    rw [hq' x]
    exact e.apply_symm_apply (q x)
  have hd : ∀ x : X, e.symm (q x) = q' x := fun x => (hq' x).symm
  -- the induced homeomorphism of mapping cylinders
  let H : cyl q' ≃ₜ cyl q := cylHomeoOfHomeo q' q e he_q hd
  have hHI : ∀ p : X, H (cylIncl q' p) = cylIncl q p := fun p =>
    cylHomeoOfHomeo_apply_cylIncl q' q e he_q hd p
  have hHs : ∀ p : X, H.symm (cylIncl q p) = cylIncl q' p := fun p =>
    cylHomeoOfHomeo_symm_apply_cylIncl q' q e he_q hd p
  -- it carries one subspace onto the other
  have he : ∀ y : cyl q', y ∈ Set.range (cylIncl q') ↔ H y ∈ Set.range (cylIncl q) := by
    intro y
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p, hHI p⟩
    · rintro ⟨p, hp⟩
      refine ⟨p, ?_⟩
      rw [← hHs p, hp, H.symm_apply_apply]
  have hf : ∀ y ∈ Set.range (cylIncl q'), H y ∈ Set.range (cylIncl q) := fun y hy => (he y).mp hy
  -- the transported Thom class
  refine ⟨(Work.Thom.relCohMap (H : C(cyl q', cyl q)) (Set.range (cylIncl q'))
      (Set.range (cylIncl q)) hf ℚ (r + 1)).hom U, ?_⟩
  intro m hm
  -- the three isomorphisms
  haveI hI2 : IsIso (ModuleCat.ofHom
      (((Work.Thom.mixedCupC ℚ (Set.range (cylIncl q)) m (r + 1)).flip U) ∘ₗ
        (Work.Thom.CohMap (cylRetract q) ℚ m).hom)) := hU m hm
  haveI hI3 : IsIso (Work.Thom.CohMap (e.symm : C(Γ', Γ)) ℚ m) :=
    isIso_CohMap_of_homeo e.symm ℚ m
  haveI hI1 : IsIso (Work.Thom.relCohMap (H : C(cyl q', cyl q)) (Set.range (cylIncl q'))
      (Set.range (cylIncl q)) hf ℚ (m + (r + 1))) :=
    Work.Thom.CapGlue.isIso_relComplexMap_homeomorph (Set.range (cylIncl q'))
      (Set.range (cylIncl q)) H he ℚ (m + (r + 1))
  -- the cylinder retraction is compatible with the homeomorphism
  have hcyl : cylRetract q'
      = ((e.symm : C(Γ', Γ)).comp (cylRetract q)).comp (H : C(cyl q', cyl q)) :=
    cylRetract_cylMap_eq (f := q') (g := q) (φ := e) he_q
  have hGm : Work.Thom.CohMap (cylRetract q') ℚ m
      = (Work.Thom.CohMap (e.symm : C(Γ', Γ)) ℚ m ≫
          Work.Thom.CohMap (cylRetract q) ℚ m) ≫
        Work.Thom.CohMap (H : C(cyl q', cyl q)) ℚ m := by
    rw [← Work.Thom.CohMap_comp (f := cylRetract q) (g := (e.symm : C(Γ', Γ))),
      ← Work.Thom.CohMap_comp (f := (H : C(cyl q', cyl q)))
        (g := (e.symm : C(Γ', Γ)).comp (cylRetract q))]
    rw [hcyl]
  -- the `q'`-cup map is the composite of the `q`-cup map with the two isomorphisms
  have hZ : ModuleCat.ofHom
        (((Work.Thom.mixedCupC ℚ (Set.range (cylIncl q')) m (r + 1)).flip
            ((Work.Thom.relCohMap (H : C(cyl q', cyl q)) (Set.range (cylIncl q'))
              (Set.range (cylIncl q)) hf ℚ (r + 1)).hom U)) ∘ₗ
          (Work.Thom.CohMap (cylRetract q') ℚ m).hom)
      = (Work.Thom.CohMap (e.symm : C(Γ', Γ)) ℚ m) ≫
        ModuleCat.ofHom
          (((Work.Thom.mixedCupC ℚ (Set.range (cylIncl q)) m (r + 1)).flip U) ∘ₗ
            (Work.Thom.CohMap (cylRetract q) ℚ m).hom) ≫
        Work.Thom.relCohMap (H : C(cyl q', cyl q)) (Set.range (cylIncl q'))
          (Set.range (cylIncl q)) hf ℚ (m + (r + 1)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [hGm]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact (Work.StemsB.mixedCupC_pairNaturalR ℚ (H : C(cyl q', cyl q))
      (Set.range (cylIncl q')) (Set.range (cylIncl q)) hf m (r + 1)
      ((Work.Thom.CohMap (cylRetract q) ℚ m).hom
        ((Work.Thom.CohMap (e.symm : C(Γ', Γ)) ℚ m).hom z)) U).symm
  rw [hZ]
  exact IsIso.comp_isIso' hI3 (IsIso.comp_isIso' hI2 hI1)

end

end Work.Serre
