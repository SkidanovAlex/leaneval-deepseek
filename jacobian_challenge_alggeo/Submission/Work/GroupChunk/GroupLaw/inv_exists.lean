/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — the inverse of the group chunk

The inverse `inv : G D ⟶ G D` of the glued group chunk, with `cls (p ≫ inv) = - cls p`.

Construction: on the `i`-th chart the inverse is glued from the local maps
`ν i j : Sym^g ⤏ Sym^g`, `x ↦ |E i + E j - x|` (the RESID engine applied to `a = 𝟙` and the
constant map at the degree-`2g` divisor `E i + E j`), over the open cover of the chart by the
opens `Uν i j`.  On `Uν i j` the value of `ν i j` is a point of `V` whose class with respect
to the centre `E j` is `-picOf i`; composing with the `j`-th chart map therefore gives a local
piece of the inverse.  The pieces agree on overlaps (the class map is injective), and they
cover the chart: by COV the class `-picOf i y` is represented in some chart, which is exactly
the condition that `y` lie in `Wν i j`.
-/
import Mathlib
import Submission.Work.GroupChunk.Group
import Submission.Work.GroupChunk.Transitions
import Submission.Work.GroupChunk.Gluing.Data
import Submission.Work.GroupChunk.Defs
import Submission.Work.GroupChunk.AbelJacobi
import Submission.Work.GroupChunk.Gluing.Transitions
import Submission.Work.GroupChunk.Desc.desc_exists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.GroupChunk.GroupLaw

noncomputable section

open Work.GCBasics

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
  [SpecLin.DivBase C] [D : Input C P0] [IsSeparated (GSch D).hom]

/-! ## The reflection `ν i j` -/

/-- The constant map `Sym^g C ⟶ Sym^{2g} C` at the divisor `E i + E j`. -/
def bnd (i j : D.Idx) : D.Sym D.g ⟶ D.Sym (D.g + D.g) :=
  CartesianMonoidalCategory.liftEquiv (constE i (D.Sym D.g), constE j (D.Sym D.g))
    ≫ D.addMap D.g D.g

theorem divOf_bnd (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (D.Sym D.g) F) :
    (D.symGeom (D.g + D.g)).divOf (p ≫ bnd i j)
      = bcKF F (D.EDiv i) + bcKF F (D.EDiv j) := by
  rw [bnd, ← Category.assoc, D.addMap_divOf, constE_divOf, constE_divOf]

/-- The reflection `ν i j : Sym^g ⤏ Sym^g`, `x ↦ |E i + E j - x|`. -/
def nu (i j : D.Idx) : (D.Sym D.g).left ⤏ (D.Sym D.g).left :=
  Classical.choose (@D.resid_exists (D.Sym D.g) (inferInstance : IsIntegral (D.Sym D.g).left)
      (LocallyOfFiniteType.isLocallyNoetherian (D.Sym D.g).hom) D.normal_Sym D.g D.g (𝟙 (D.Sym D.g)) (bnd i j) le_rfl)

theorem nu_spec (i j : D.Idx) :
    Resid C D.symGeom (inferInstance : IsReduced (D.Sym D.g).left)
      (by haveI := D.isProper_Sym D.g; exact inferInstance) (𝟙 (D.Sym D.g)) (bnd i j) (nu i j) :=
  Classical.choose_spec
    (@D.resid_exists (D.Sym D.g) (inferInstance : IsIntegral (D.Sym D.g).left)
      (LocallyOfFiniteType.isLocallyNoetherian (D.Sym D.g).hom) D.normal_Sym D.g D.g (𝟙 (D.Sym D.g)) (bnd i j) le_rfl)

theorem nu_isOver (i j : D.Idx) : (nu i j).IsOver (Spec (CommRingCat.of K)) :=
  (nu_spec i j).isOver

theorem nu_toPartialMap_isOver (i j : D.Idx) :
    ((nu i j).toPartialMap).IsOver (Spec (CommRingCat.of K)) := by
  have h1 : ((nu i j).toPartialMap).toRationalMap.IsOver (Spec (CommRingCat.of K)) := by
    rw [Scheme.RationalMap.toRationalMap_toPartialMap]
    exact nu_isOver i j
  exact (Scheme.PartialMap.isOver_toRationalMap_iff_of_isSeparated
    (S := Spec (CommRingCat.of K))).mp h1

abbrev nuPM (i j : D.Idx) : (D.Sym D.g).left.PartialMap (D.Sym D.g).left :=
  (nu i j).toPartialMap

theorem nuPM_hom_comp (i j : D.Idx) :
    (nuPM i j).hom ≫ (D.Sym D.g).hom = (nuPM i j).domain.ι ≫ (D.Sym D.g).hom :=
  (nu_toPartialMap_isOver i j).1

/-- The value of `ν i j` at a point of its domain. -/
abbrev nuVal (i j : D.Idx) {F : Type u} [Field F] [Algebra K F] (p : FPt (D.Sym D.g) F)
    (hp : RPt.LandsIn p (nu i j).domain) : FPt (D.Sym D.g) F :=
  value (inferInstance : IsReduced (D.Sym D.g).left)
    (by haveI := D.isProper_Sym D.g; exact inferInstance) (nu i j) (nu_isOver i j) p hp

/-- **VALUE** of the reflection: `divOf (ν i j x) + x ~ E i + E j`. -/
theorem nu_value (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (D.Sym D.g) F) (hp : RPt.LandsIn p (nu i j).domain) :
    LinEquiv C (D.divOf D.g (nuVal i j p hp) + D.divOf D.g p)
      (bcKF F (D.EDiv i) + bcKF F (D.EDiv j)) := by
  have h := (nu_spec i j).value p hp
  rw [divOf_bnd i j p] at h
  simpa only [Category.comp_id] using h

/-- **DEFINED** of the reflection. -/
theorem nu_mem_domain (i j : D.Idx) (x : (D.Sym D.g).left)
    (hx : ell C (bcKF (resField (D.Sym D.g) x) (D.EDiv i)
      + bcKF (resField (D.Sym D.g) x) (D.EDiv j)
      - D.divOf D.g (resPt (D.Sym D.g) x)) = 1) :
    x ∈ (nu i j).domain := by
  refine (nu_spec i j).mem_domain x ?_
  rw [divOf_bnd]
  simpa only [Category.comp_id] using hx

/-! ## The opens `Wν i j` and the local pieces -/

/-- The open `Wν i j ⊆ Sym^g`: the points of the domain of `ν i j` whose value lies in the
chart `V`. -/
def Wnu (i j : D.Idx) : (D.Sym D.g).left.Opens :=
  (nuPM i j).domain.ι ''ᵁ ((nuPM i j).hom ⁻¹ᵁ D.V)

theorem Wnu_le_domain (i j : D.Idx) : Wnu i j ≤ (nuPM i j).domain :=
  Scheme.Opens.ι_image_le _ _

/-- The value of `ν i j` on `Wν i j`, as a morphism of `K`-schemes. -/
def nuOnW (i j : D.Idx) : Opens.toOver (Wnu i j) ⟶ D.Sym D.g :=
  Over.homMk (Scheme.homOfLE (D.Sym D.g).left (U := Wnu i j) (Wnu_le_domain i j)
      ≫ (nuPM i j).hom) (by
    change (Scheme.homOfLE (D.Sym D.g).left (U := Wnu i j) (Wnu_le_domain i j)
        ≫ (nuPM i j).hom) ≫ (D.Sym D.g).hom = (Wnu i j).ι ≫ (D.Sym D.g).hom
    rw [Category.assoc, nuPM_hom_comp, ← Category.assoc, Scheme.homOfLE_ι])

theorem range_nuOnW_le_V (i j : D.Idx) : Set.range (nuOnW i j).left ⊆ (D.V : Set _) := by
  have hpre : (Scheme.homOfLE (D.Sym D.g).left (Wnu_le_domain i j)
      ≫ (nuPM i j).hom) ⁻¹ᵁ D.V = ⊤ := by
    have hS : (nuPM i j).hom ⁻¹ᵁ D.V = (nuPM i j).domain.ι ⁻¹ᵁ Wnu i j := by
      rw [Wnu]
      exact (Scheme.Hom.preimage_image_eq (nuPM i j).domain.ι _).symm
    rw [Scheme.Hom.comp_preimage, hS, ← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι,
      Scheme.Opens.ι_preimage_self]
  rintro z ⟨w, rfl⟩
  have h1 : w ∈ (Scheme.homOfLE (D.Sym D.g).left (Wnu_le_domain i j)
      ≫ (nuPM i j).hom) ⁻¹ᵁ D.V := by
    rw [hpre]; exact trivial
  exact h1

/-- The transition domain `Uν i j ⊆ V` of the reflection. -/
def Unu (i j : D.Idx) : (Opens.toOver D.V).left.Opens := D.V.ι ⁻¹ᵁ Wnu i j

/-- The composite inclusion `Uν i j ⊆ Sym^g`. -/
def Unuι (i j : D.Idx) : Opens.toOver (Unu i j) ⟶ D.Sym D.g :=
  Opens.ιOver (Unu i j) ≫ Opens.ιOver D.V

theorem Unuι_def (i j : D.Idx) :
    Unuι i j = Opens.ιOver (Unu i j) ≫ Opens.ιOver D.V := rfl

theorem range_Unuι_le_Wnu (i j : D.Idx) :
    Set.range (Unuι i j).left ⊆ (Wnu i j : Set (D.Sym D.g).left) := by
  rintro _ ⟨y, rfl⟩
  exact y.2

/-- The identification of `Uν i j` with the corresponding open of `Wν i j`. -/
def UnuToW (i j : D.Idx) : Opens.toOver (Unu i j) ⟶ Opens.toOver (Wnu i j) :=
  Over.homMk (IsOpenImmersion.lift (Wnu i j).ι (Unuι i j).left
    (by rw [Scheme.Opens.range_ι]; exact range_Unuι_le_Wnu i j)) (by
    change IsOpenImmersion.lift (Wnu i j).ι (Unuι i j).left _ ≫ (Wnu i j).ι ≫ (D.Sym D.g).hom
      = (Unuι i j).left ≫ (D.Sym D.g).hom
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Over.Hom.w])

theorem UnuToW_ιOver (i j : D.Idx) : UnuToW i j ≫ Opens.ιOver (Wnu i j) = Unuι i j := by
  apply Over.OverMorphism.ext
  show IsOpenImmersion.lift (Wnu i j).ι (Unuι i j).left _ ≫ (Wnu i j).ι = (Unuι i j).left
  rw [IsOpenImmersion.lift_fac]

/-- The value of `ν i j` on `Uν i j`: a morphism `Uν i j ⟶ Sym^g`. -/
def nuHom (i j : D.Idx) : Opens.toOver (Unu i j) ⟶ D.Sym D.g :=
  UnuToW i j ≫ nuOnW i j

theorem nuHom_range (i j : D.Idx) : Set.range (nuHom i j).left ⊆ (D.V : Set _) := by
  rw [show (nuHom i j).left = (UnuToW i j).left ≫ (nuOnW i j).left from rfl]
  rintro z ⟨y, rfl⟩
  exact range_nuOnW_le_V i j ⟨(UnuToW i j).left y, rfl⟩

/-- The value of `ν i j` on `Uν i j`, factored through the chart `V`. -/
def tqnu (i j : D.Idx) : Opens.toOver (Unu i j) ⟶ Opens.toOver D.V :=
  Classical.choose (exists_factor_of_range_subset D.V (nuHom i j) (nuHom_range i j))

theorem tqnu_ιOver (i j : D.Idx) : tqnu i j ≫ Opens.ιOver D.V = nuHom i j :=
  (Classical.choose_spec (exists_factor_of_range_subset D.V (nuHom i j) (nuHom_range i j))).1

/-! ## The value and the class of `ν i j` on `Uν i j` -/

theorem nuOnW_value (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Opens.toOver (Wnu i j)) F)
    (hp : RPt.LandsIn (p ≫ Opens.ιOver (Wnu i j)) (nu i j).domain) :
    p ≫ nuOnW i j = nuVal i j _ hp := by
  let g : Opens.toOver (Wnu i j) ⟶ Opens.toOver (nu i j).domain :=
    Over.homMk (Scheme.homOfLE (D.Sym D.g).left (Wnu_le_domain i j)) (by
      change Scheme.homOfLE (D.Sym D.g).left (Wnu_le_domain i j) ≫
        (nuPM i j).domain.ι ≫ (D.Sym D.g).hom = (Wnu i j).ι ≫ (D.Sym D.g).hom
      rw [← Category.assoc, Scheme.homOfLE_ι])
  let q : RPt (Opens.toOver (nu i j).domain) F := p ≫ g
  have hgs : g ≫ Opens.ιOver (nu i j).domain = Opens.ιOver (Wnu i j) := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Opens.ιOver_left]
    change Scheme.homOfLE (D.Sym D.g).left (Wnu_le_domain i j) ≫ (nuPM i j).domain.ι
      = (Wnu i j).ι
    rw [Scheme.homOfLE_ι]
  have hq : q ≫ Opens.ιOver (nu i j).domain = p ≫ Opens.ιOver (Wnu i j) := by
    show p ≫ g ≫ Opens.ιOver (nu i j).domain = p ≫ Opens.ιOver (Wnu i j)
    rw [hgs]
  have hval := value_left_eq (X := D.Sym D.g) (Y := D.Sym D.g) (hred := inferInstance)
    (hsep := inferInstance) (nu i j) (nu_isOver i j)
    (p ≫ Opens.ιOver (Wnu i j)) hp q hq
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  rw [show (nuOnW i j).left = Scheme.homOfLE (D.Sym D.g).left (Wnu_le_domain i j)
      ≫ (nu i j).toPartialMap.hom from rfl]
  rw [show (nuVal i j (p ≫ Opens.ιOver (Wnu i j)) hp).left =
      (value (inferInstance : IsReduced (D.Sym D.g).left)
      (inferInstance : IsSeparated (D.Sym D.g).hom) (nu i j) (nu_isOver i j)
      (p ≫ Opens.ιOver (Wnu i j)) hp).left from rfl]
  rw [hval]
  show p.left ≫ (Scheme.homOfLE (D.Sym D.g).left (Wnu_le_domain i j)
      ≫ (nu i j).toPartialMap.hom)
    = (p.left ≫ Scheme.homOfLE (D.Sym D.g).left (Wnu_le_domain i j))
      ≫ (nu i j).toPartialMap.hom
  rw [Category.assoc]

/-- `picOf j a = -picOf i b` in terms of linear equivalence. -/
theorem picOf_eq_neg_iff (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (a b : FPt (D.Sym D.g) F) :
    D.picOf j a = - D.picOf i b ↔
      LinEquiv C (D.divOf D.g a - D.divOf D.g (D.EF j))
        (D.divOf D.g (D.EF i) - D.divOf D.g b) := by
  have hneg : - D.picOf i b = Pic0.mk (-(D.divOf D.g b - D.divOf D.g (D.EF i)))
      (by
        have hb : Ddeg C F (D.divOf D.g b) = (D.g : ℤ) := (D.symGeom D.g).divOf_deg b
        have hi : Ddeg C F (D.divOf D.g (D.EF i)) = (D.g : ℤ) :=
          (D.symGeom D.g).divOf_deg (D.EF i)
        rw [map_neg, map_sub, hb, hi, sub_self, neg_zero]) := by
    rw [Input.picOf_def]
    exact (Pic0.mk_neg _ _).symm
  rw [hneg, Input.picOf_def]
  constructor
  · intro h
    have h' := (Pic0.mk_eq_iff _ _).mp h
    rwa [show (-(D.divOf D.g b - D.divOf D.g (D.EF i)) : Dv C F)
      = D.divOf D.g (D.EF i) - D.divOf D.g b from by abel] at h'
  · intro h
    refine (Pic0.mk_eq_iff _ _).mpr ?_
    rwa [show (-(D.divOf D.g b - D.divOf D.g (D.EF i)) : Dv C F)
      = D.divOf D.g (D.EF i) - D.divOf D.g b from by abel]

/-- `picOf j a = -picOf i b` in terms of linear equivalence, with the base divisors
`bcKF F (D.EDiv ·)`. -/
theorem picOf_eq_neg_iff' (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (a b : FPt (D.Sym D.g) F) :
    D.picOf j a = - D.picOf i b ↔
      LinEquiv C (D.divOf D.g a - bcKF F (D.EDiv j))
        (bcKF F (D.EDiv i) - D.divOf D.g b) := by
  rw [picOf_eq_neg_iff, Input.EF_divOf, Input.EF_divOf]

/-- **The class of the reflection**: `picOf j (ν i j x) = -picOf i x`. -/
theorem nuHom_picOf (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver (Unu i j)) F) :
    D.picOf j (q ≫ nuHom i j) = - D.picOf i (q ≫ Unuι i j) := by
  have hYX : ((q ≫ UnuToW i j) ≫ Opens.ιOver (Wnu i j)) = (q ≫ Unuι i j) := by
    rw [Category.assoc, UnuToW_ιOver i j]
  have hqX : RPt.LandsIn ((q ≫ UnuToW i j) ≫ Opens.ιOver (Wnu i j)) (nu i j).domain :=
    Wnu_le_domain i j (landsIn_ιOver_self (Wnu i j) (q ≫ UnuToW i j))
  have hT : q ≫ nuHom i j
      = nuVal i j ((q ≫ UnuToW i j) ≫ Opens.ιOver (Wnu i j)) hqX := by
    rw [show nuHom i j = UnuToW i j ≫ nuOnW i j from rfl, ← Category.assoc]
    exact nuOnW_value i j (q ≫ UnuToW i j) hqX
  rw [hT, ← hYX]
  refine (picOf_eq_neg_iff' i j _ _).mpr ?_
  refine (linEquiv_add_iff_sub _ _ _ _).mpr ?_
  exact nu_value i j ((q ≫ UnuToW i j) ≫ Opens.ιOver (Wnu i j)) hqX

theorem tqnu_picOf (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver (Unu i j)) F) :
    D.picOf j ((q ≫ tqnu i j) ≫ Opens.ιOver D.V) = - D.picOf i (q ≫ Unuι i j) := by
  have h : (q ≫ tqnu i j) ≫ Opens.ιOver D.V = q ≫ nuHom i j := by
    rw [Category.assoc, tqnu_ιOver]
  rw [h]
  exact nuHom_picOf i j q

/-- The underlying morphism of the value of `ν i j` is the partial map applied to the (unique)
factorisation of the point through the domain. -/
theorem nuVal_apply (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (D.Sym D.g) F) (h : RPt.LandsIn q (nu i j).domain) :
    (nuVal i j q h).left (IsLocalRing.closedPoint F)
      = (nuPM i j).hom ((Classical.choose
          (RPt.factor_of_closed_landsIn (nu i j).domain q h)).left
            (IsLocalRing.closedPoint F)) := by
  simp only [nuVal, value]
  rfl

/-- The image in `Sym^g` of a point of the domain of `ν i j` is the image point of
`Q ≫ ιOver`. -/
theorem nu_domain_ι_apply_eq (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (D.Sym D.g) F) (Q : FPt (Opens.toOver (nu i j).domain) F)
    (hQ : Q ≫ Opens.ιOver (nu i j).domain = q) :
    (nuPM i j).domain.ι (Q.left (IsLocalRing.closedPoint F))
      = q.left (IsLocalRing.closedPoint F) := by
  have h := congrArg Over.Hom.left hQ
  rw [Over.comp_left, Opens.ιOver_left] at h
  exact congrArg (fun g : (specOf K F).left ⟶ (D.Sym D.g).left =>
    g (IsLocalRing.closedPoint F)) h

/-- The value of `ν i j` at a field point, computed with any factorisation of the point
through the domain. -/
theorem nuVal_eq_of_factor (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (D.Sym D.g) F) (h : RPt.LandsIn q (nu i j).domain)
    (Q : FPt (Opens.toOver (nu i j).domain) F)
    (hQ : Q ≫ Opens.ιOver (nu i j).domain = q) :
    (nuVal i j q h).left (IsLocalRing.closedPoint F)
      = (nuPM i j).hom (Q.left (IsLocalRing.closedPoint F)) := by
  rw [nuVal_apply]
  have huniq := (Classical.choose_spec
    (RPt.factor_of_closed_landsIn (nu i j).domain q h)).2
  have h' : Q.left (IsLocalRing.closedPoint F)
      = (Classical.choose (RPt.factor_of_closed_landsIn (nu i j).domain q h)).left
          (IsLocalRing.closedPoint F) :=
    congrArg (fun r : FPt (Opens.toOver (nu i j).domain) F =>
      r.left (IsLocalRing.closedPoint F)) (huniq Q hQ)
  rw [← h']

/-- A point whose `ν i j`-value lies in `V` lands in `Wν i j`. -/
theorem landsIn_Wnu_of_nuPM_hom_mem_V (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (D.Sym D.g) F) (Q : FPt (Opens.toOver (nu i j).domain) F)
    (hQ : Q ≫ Opens.ιOver (nu i j).domain = q)
    (hV : (nuPM i j).hom (Q.left (IsLocalRing.closedPoint F)) ∈ D.V) :
    RPt.LandsIn q (Wnu i j) := by
  have hQι := nu_domain_ι_apply_eq i j q Q hQ
  have hqmem : q.left (IsLocalRing.closedPoint F) ∈ (nuPM i j).domain := by
    rw [← hQι]
    exact (Q.left (IsLocalRing.closedPoint F)).2
  have hι_inj : Function.Injective (nuPM i j).domain.ι := fun a b h => Subtype.val_injective h
  have hpt : (⟨q.left (IsLocalRing.closedPoint F), hqmem⟩ : (nuPM i j).domain)
      = Q.left (IsLocalRing.closedPoint F) :=
    hι_inj (by rw [hQι, Scheme.Opens.ι_apply, Subtype.coe_mk])
  have hV' : (nuPM i j).hom
      (⟨q.left (IsLocalRing.closedPoint F), hqmem⟩ : (nuPM i j).domain) ∈ D.V := by
    rw [hpt]
    exact hV
  have hmem : (⟨q.left (IsLocalRing.closedPoint F), hqmem⟩ : (nuPM i j).domain)
      ∈ (nuPM i j).hom ⁻¹ᵁ D.V :=
    (Scheme.Hom.mem_preimage (f := (nuPM i j).hom)
      (x := (⟨q.left (IsLocalRing.closedPoint F), hqmem⟩ : (nuPM i j).domain))
      (U := D.V)).mpr hV'
  exact (Scheme.Opens.mem_ι_image_iff (U := (nuPM i j).domain)
    (V := (nuPM i j).hom ⁻¹ᵁ D.V)
    (x := (⟨q.left (IsLocalRing.closedPoint F), hqmem⟩ : (nuPM i j).domain))).mpr hmem

/-! ## The covering of the chart by the `Uν i j` -/

/-- **Every point of `Sym^g` lands in some `Wν i j`**: by COV the class `-picOf i y` is
represented in the `j`-th chart, which says exactly that `ℓ(E i + E j - y) = 1`. -/
theorem exists_landsIn_Wnu (i : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (y : FPt (D.Sym D.g) F) : ∃ j : D.Idx, RPt.LandsIn y (Wnu i j) := by
  obtain ⟨j, w, hwV, hwc⟩ := D.cov (- D.picOf i y)
  refine ⟨j, ?_⟩
  have h0 : LinEquiv C (D.divOf D.g w - bcKF F (D.EDiv j))
      (bcKF F (D.EDiv i) - D.divOf D.g y) :=
    (picOf_eq_neg_iff' i j w y).mp (by rw [Input.picOf_def]; exact hwc)
  have h1 : LinEquiv C (D.divOf D.g w + D.divOf D.g y)
      (bcKF F (D.EDiv i) + bcKF F (D.EDiv j)) :=
    (linEquiv_add_iff_sub (D.divOf D.g w) (bcKF F (D.EDiv i)) (D.divOf D.g y)
      (bcKF F (D.EDiv j))).mp h0
  have hellF : ell C (bcKF F (D.EDiv i) + bcKF F (D.EDiv j) - D.divOf D.g y) = 1 := by
    have h2 : LinEquiv C (D.divOf D.g w)
        (bcKF F (D.EDiv i) + bcKF F (D.EDiv j) - D.divOf D.g y) := by
      have h := (LinEquiv.sub_iff (D.divOf D.g w + D.divOf D.g y)
        (bcKF F (D.EDiv i) + bcKF F (D.EDiv j)) (D.divOf D.g y)).mpr h1
      simpa only [add_sub_cancel_right] using h
    exact (ell_eq_of_linEquiv h2).symm.trans (ell_of_landsIn_V w hwV)
  -- transfer `ℓ = 1` to the residue field of the image point of `y`
  obtain ⟨e, he⟩ := exists_factor_resPt (X := D.Sym D.g) (p := y)
  have hdiv : SpecLin.DivBase.bc e
      (D.divOf D.g (resPt (D.Sym D.g) (y.left (IsLocalRing.closedPoint F))))
      = D.divOf D.g y := by
    rw [← divOf_map' D.g e (resPt (D.Sym D.g) (y.left (IsLocalRing.closedPoint F))), ← he]
  have hE (k : D.Idx) : SpecLin.DivBase.bc e (bcKF (resK y) (D.EDiv k))
      = bcKF F (D.EDiv k) := by
    have hcomp := SpecLin.DivBase.bc_comp (Algebra.ofId K (resK y)) e (D.EDiv k)
    rw [LandsInUAux.comp_ofId_eq e] at hcomp
    exact hcomp.symm
  have hbc : SpecLin.DivBase.bc e (bcKF (resK y) (D.EDiv i) + bcKF (resK y) (D.EDiv j)
      - D.divOf D.g (resPt (D.Sym D.g) (y.left (IsLocalRing.closedPoint F))))
      = bcKF F (D.EDiv i) + bcKF F (D.EDiv j) - D.divOf D.g y := by
    rw [sub_eq_add_neg, SpecLin.DivBase.bc_add, SpecLin.DivBase.bc_add,
      SpecLin.DivBase.bc_neg, hdiv, hE i, hE j]
    abel
  have hdeg : Ddeg C (resK y) (bcKF (resK y) (D.EDiv i) + bcKF (resK y) (D.EDiv j)
      - D.divOf D.g (resPt (D.Sym D.g) (y.left (IsLocalRing.closedPoint F)))) = (D.g : ℤ) := by
    rw [map_sub, map_add]
    rw [show Ddeg C (resK y)
        (D.divOf D.g (resPt (D.Sym D.g) (y.left (IsLocalRing.closedPoint F)))) = (D.g : ℤ)
      from (D.symGeom D.g).divOf_deg _]
    rw [deg_bcKF, D.EDiv_deg, deg_bcKF, D.EDiv_deg]
    ring
  have hellκ : ell C (bcKF (resK y) (D.EDiv i) + bcKF (resK y) (D.EDiv j)
      - D.divOf D.g (resPt (D.Sym D.g) (y.left (IsLocalRing.closedPoint F)))) = 1 :=
    ell_eq_one_of_bc e _ hdeg (by rw [hbc]; exact hellF)
  have hzdom : (y.left (IsLocalRing.closedPoint F)) ∈ (nu i j).domain :=
    nu_mem_domain i j _ hellκ
  -- the value of `ν i j` at `y` is the COV witness `w`, hence lies in `V`
  have hy_dom : RPt.LandsIn y (nu i j).domain := hzdom
  have hval := nu_value i j y hy_dom
  have h3 : LinEquiv C (D.divOf D.g (nuVal i j y hy_dom) + D.divOf D.g y)
      (D.divOf D.g w + D.divOf D.g y) := hval.trans h1.symm
  have h4 : LinEquiv C (D.divOf D.g (nuVal i j y hy_dom)) (D.divOf D.g w) := by
    have h := (LinEquiv.sub_iff (D.divOf D.g (nuVal i j y hy_dom) + D.divOf D.g y)
      (D.divOf D.g w + D.divOf D.g y) (D.divOf D.g y)).mpr h3
    simpa only [add_sub_cancel_right] using h
  have hdiv_eq : D.divOf D.g (nuVal i j y hy_dom) = D.divOf D.g w :=
    linEquiv_eq_of_ell_eq_one ((D.symGeom D.g).divOf_isEffective (nuVal i j y hy_dom))
      (by rw [ell_eq_of_linEquiv h4]; exact ell_of_landsIn_V w hwV)
      ((D.symGeom D.g).divOf_isEffective w) h4
  have hval_eq : nuVal i j y hy_dom = w := (D.symGeom D.g).divOf_injective _ _ hdiv_eq
  obtain ⟨Q, hQ, -⟩ := FPt.factor_of_landsIn (nu i j).domain y hy_dom
  have hQV : (nuPM i j).hom (Q.left (IsLocalRing.closedPoint F)) ∈ D.V := by
    rw [← nuVal_eq_of_factor i j y hy_dom Q hQ, hval_eq]
    exact hwV
  exact landsIn_Wnu_of_nuPM_hom_mem_V i j y Q hQ hQV

/-- **The opens `Uν i j` cover the chart `V`.** -/
theorem exists_mem_Unu (i : D.Idx) (x : (Opens.toOver D.V).left) :
    ∃ j : D.Idx, x ∈ Unu i j := by
  obtain ⟨j, hj⟩ := exists_landsIn_Wnu (D := D) i
    (resPt (Opens.toOver D.V) x ≫ Opens.ιOver D.V)
  refine ⟨j, ?_⟩
  refine (resPt_landsIn_iff (Opens.toOver D.V) x (Unu i j)).mp ?_
  exact (RPt.landsIn_preimage (p := resPt (Opens.toOver D.V) x) (f := Opens.ιOver D.V)
    (V := Wnu i j)).mp hj

/-! ## The pieces of the inverse on the chart `i` -/

/-- The open cover of the chart by the `Uν i j`. -/
abbrev coverUnu (i : D.Idx) : (Opens.toOver D.V).left.OpenCover.{u} :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) D.Idx
    (fun j : D.Idx => (Unu i j : Scheme))
    (fun j => (Unu i j).ι)
    (fun x => by
      obtain ⟨j, hj⟩ := exists_mem_Unu (D := D) i x
      exact ⟨j, ⟨x, hj⟩, rfl⟩)

theorem coverUnu_f (i j : D.Idx) : (coverUnu i).f j = (Unu i j).ι := rfl

/-- The local piece of the inverse on `Uν i j`: the reflection followed by the `j`-th chart
map. -/
def phiPieceOver (i j : D.Idx) : Opens.toOver (Unu i j) ⟶ GSch D := tqnu i j ≫ chartH D j

theorem phiPieceOver_cls (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver (Unu i j)) F) :
    D.cls (q ≫ phiPieceOver i j) = - D.picOf i (q ≫ Unuι i j) := by
  rw [show phiPieceOver i j = tqnu i j ≫ D.chart j from rfl, ← Category.assoc]
  rw [Input.cls_chart D j (q ≫ tqnu i j)]
  exact tqnu_picOf i j q

/-- The overlap of two pieces, as a `K`-scheme. -/
def overlapUnu (i j k : D.Idx) : Sch K :=
  Over.mk (pullback.fst (Unu i j).ι (Unu i k).ι ≫ (Unu i j).ι
    ≫ (Opens.toOver D.V).hom)

def overlapUnuFst (i j k : D.Idx) : overlapUnu i j k ⟶ Opens.toOver (Unu i j) :=
  Over.homMk (pullback.fst (Unu i j).ι (Unu i k).ι) rfl

def overlapUnuSnd (i j k : D.Idx) : overlapUnu i j k ⟶ Opens.toOver (Unu i k) :=
  Over.homMk (pullback.snd (Unu i j).ι (Unu i k).ι) (by
    change pullback.snd (Unu i j).ι (Unu i k).ι
        ≫ ((Unu i k).ι ≫ (Opens.toOver D.V).hom)
      = pullback.fst (Unu i j).ι (Unu i k).ι ≫ (Unu i j).ι ≫ (Opens.toOver D.V).hom
    rw [← Category.assoc, ← Category.assoc, pullback.condition])

theorem overlapUnuFst_ι (i j k : D.Idx) :
    overlapUnuFst i j k ≫ Opens.ιOver (Unu i j)
      = overlapUnuSnd i j k ≫ Opens.ιOver (Unu i k) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, Opens.ιOver_left, Opens.ιOver_left,
    show (overlapUnuFst i j k).left = pullback.fst (Unu i j).ι (Unu i k).ι from rfl,
    show (overlapUnuSnd i j k).left = pullback.snd (Unu i j).ι (Unu i k).ι from rfl]
  exact pullback.condition

instance instIsReducedOverlapUnu (i j k : D.Idx) : IsReduced (overlapUnu i j k).left := by
  haveI hred : IsReduced (Opens.toOver (Unu i j)).left :=
    isReduced_of_isOpenImmersion (Unu i j).ι
  haveI hred' : IsReduced ((Unu i j).ι ⁻¹ᵁ (Unu i k)) := inferInstance
  exact ObjectProperty.prop_of_iso (fun X : Scheme => IsReduced X)
    (pullbackRestrictIsoRestrict (Unu i j).ι (Unu i k)).symm hred'

/-- **The pieces agree on the overlaps.** -/
theorem phiPieceOver_compat (i j k : D.Idx) :
    overlapUnuFst i j k ≫ phiPieceOver i j = overlapUnuSnd i j k ≫ phiPieceOver i k := by
  apply hom_ext_of_resPt (K := K)
  intro y
  refine D.cls_injective (D := D) ?_
  simp only [← Category.assoc]
  rw [phiPieceOver_cls i j, phiPieceOver_cls i k]
  have key : (resPt (overlapUnu i j k) y ≫ overlapUnuFst i j k) ≫ Unuι i j
      = (resPt (overlapUnu i j k) y ≫ overlapUnuSnd i j k) ≫ Unuι i k := by
    have h := congrArg (fun g : overlapUnu i j k ⟶ Opens.toOver D.V =>
      (resPt (overlapUnu i j k) y ≫ g) ≫ Opens.ιOver D.V) (overlapUnuFst_ι i j k)
    simpa only [Unuι_def, Category.assoc] using h
  simp only [neg_inj]
  exact congrArg (fun x => D.picOf i x) key

/-- The pieces of the cover, at the level of schemes. -/
def phiPiece (i j : D.Idx) : (coverUnu i).X j ⟶ (GSch D).left := (phiPieceOver i j).left

theorem phiPiece_compat (i : D.Idx) :
    ∀ j k, pullback.fst ((coverUnu i).f j) ((coverUnu i).f k) ≫ phiPiece i j
      = pullback.snd ((coverUnu i).f j) ((coverUnu i).f k) ≫ phiPiece i k :=
  fun j k => congrArg Over.Hom.left (phiPieceOver_compat i j k)

/-- The inverse on the chart `i`, as a morphism of schemes. -/
abbrev phi_left (i : D.Idx) : (Opens.toOver D.V).left ⟶ (GSch D).left :=
  Scheme.Cover.glueMorphisms (coverUnu i) (phiPiece i) (phiPiece_compat i)

theorem phi_left_ι (i j : D.Idx) : (coverUnu i).f j ≫ phi_left i = phiPiece i j := by
  exact (Scheme.Cover.ι_glueMorphisms (coverUnu i) (phiPiece i) (phiPiece_compat i) j).trans rfl

theorem phi_left_comp (i j : D.Idx) :
    (coverUnu i).f j ≫ (phi_left i ≫ (GSch D).hom)
      = (phiPieceOver i j).left ≫ (GSch D).hom := by
  rw [← Category.assoc, phi_left_ι]
  rfl

/-- The inverse on the chart `i`, as a morphism of `K`-schemes. -/
def phi (i : D.Idx) : Opens.toOver D.V ⟶ GSch D :=
  Over.homMk (phi_left i) (by
    refine Scheme.Cover.hom_ext (coverUnu i) (phi_left i ≫ (GSch D).hom)
      (Opens.toOver D.V).hom (fun j => ?_)
    exact ((phi_left_comp i j).trans (Over.w (phiPieceOver i j))).trans
      (congrArg (fun g : (Unu i j : Scheme) ⟶ (Opens.toOver D.V).left =>
        g ≫ (Opens.toOver D.V).hom) (coverUnu_f i j)).symm)

theorem ιOver_phi (i j : D.Idx) : Opens.ιOver (Unu i j) ≫ phi i = phiPieceOver i j := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Opens.ιOver_left, show (phi i).left = phi_left i from rfl,
    ← coverUnu_f]
  exact phi_left_ι i j

/-- **The class of the inverse on the chart `i`**: `cls (q ≫ phi i) = -picOf i q`. -/
theorem phi_cls (i : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver D.V) F) :
    D.cls (q ≫ phi i) = - D.picOf i (q ≫ Opens.ιOver D.V) := by
  obtain ⟨j, hj⟩ := exists_mem_Unu (D := D) i (q.left (IsLocalRing.closedPoint F))
  obtain ⟨q', hq', -⟩ := FPt.factor_of_landsIn (Unu i j) q hj
  rw [← hq', Category.assoc, ιOver_phi, phiPieceOver_cls i j q']
  congr 1

/-- The transition `t i k` and the reflection commute on the relevant composite. -/
theorem picOf_tcls_form (i k : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver (U i k)) F) :
    D.picOf k ((q ≫ (t i k ≫ Opens.ιOver (U k i))) ≫ Opens.ιOver D.V)
      = D.picOf i ((q ≫ Opens.ιOver (U i k)) ≫ Opens.ιOver D.V) := by
  have h := t_cls (D := D) i k q
  rw [Uι_def, Uι_def] at h
  simpa only [Category.assoc] using h

/-- **The maps `phi i` are compatible with the transitions.** -/
theorem phi_compat (i k : D.Idx) :
    Opens.ιOver (U i k) ≫ phi i = (t i k ≫ Opens.ιOver (U k i)) ≫ phi k := by
  apply hom_ext_of_resPt (K := K)
  intro z
  refine D.cls_injective (D := D) ?_
  show D.cls (resPt (Opens.toOver (U i k)) z ≫ (Opens.ιOver (U i k) ≫ phi i))
      = D.cls (resPt (Opens.toOver (U i k)) z
          ≫ ((t i k ≫ Opens.ιOver (U k i)) ≫ phi k))
  rw [show resPt (Opens.toOver (U i k)) z ≫ (Opens.ιOver (U i k) ≫ phi i)
      = (resPt (Opens.toOver (U i k)) z ≫ Opens.ιOver (U i k)) ≫ phi i
      from (Category.assoc _ _ _).symm]
  rw [show resPt (Opens.toOver (U i k)) z ≫ ((t i k ≫ Opens.ιOver (U k i)) ≫ phi k)
      = (resPt (Opens.toOver (U i k)) z ≫ (t i k ≫ Opens.ιOver (U k i))) ≫ phi k
      from (Category.assoc _ _ _).symm]
  rw [phi_cls i, phi_cls k]
  simp only [neg_inj]
  exact (picOf_tcls_form i k (resPt (Opens.toOver (U i k)) z)).symm

end

open CategoryTheory in
open AlgebraicGeometry in
open scoped AlgebraicGeometry in
theorem inv_exists {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C] (D : Work.GroupChunk.Input C P0)
    [IsSeparated (Work.GroupChunk.GSch D).hom]
    [GeometricallyReduced (Work.GroupChunk.GSch D).hom] :
    ∃ inv : Work.GroupChunk.GSch D ⟶ Work.GroupChunk.GSch D,
      ∀ {F : Type u} [Field F] [Algebra K F]
        (p : Work.GCBasics.FPt (Work.GroupChunk.GSch D) F),
        Work.GroupChunk.Input.cls D (p ≫ inv) = - Work.GroupChunk.Input.cls D p := by
  classical
  obtain ⟨g, hg, -⟩ := Work.GroupChunk.Desc.desc_exists (D := D)
    (Y := Work.GroupChunk.GSch D) (fun i => phi i) (fun i k => phi_compat i k)
  refine ⟨g, ?_⟩
  intro F hF hAlg p
  obtain ⟨i, q, hq⟩ := Work.GroupChunk.Input.exists_factor D p
  have step1 : Work.GroupChunk.Input.cls D (p ≫ g)
      = Work.GroupChunk.Input.cls D (q ≫ phi i) := by
    rw [← hq, Category.assoc, hg i]
  have step3 : D.picOf i (q ≫ Work.GCBasics.Opens.ιOver D.V)
      = Work.GroupChunk.Input.cls D p := by
    rw [← hq]
    exact (Work.GroupChunk.Input.cls_chart D i q).symm
  exact step1.trans ((phi_cls i q).trans (congrArg Neg.neg step3))

end Work.GroupChunk.GroupLaw
