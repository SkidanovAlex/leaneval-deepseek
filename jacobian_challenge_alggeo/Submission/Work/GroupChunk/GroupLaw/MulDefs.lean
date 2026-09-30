/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — the setup of the multiplication of the group chunk `G D`

This file builds the objects used in the construction of the multiplication
`G D ⊗ G D ⟶ G D` of the group chunk (`Work.GroupChunk.GroupLaw.mul_exists`).

The multiplication is glued from pieces.  A piece is indexed by a triple `(i, j, k)` of chart
centres and lives inside `V ⊗ V ⊆ Sym^g C ⊗ Sym^g C`; it is the locus where the RESID map

`(x, y) ↦ |divOf x + divOf y + E k - E i - E j|`

is defined and takes values in `V`, and it is mapped to `G D` by that value followed by the
`k`-th chart.

Contents:

* `SymSym D = Sym^g C ⊗ Sym^g C`, `VVo D = V ⊗ V`, `eVV D : VVo D ⟶ SymSym D`;
* `Esum D i j = E i + E j` with `mulA D i j` (the constant map at `E i + E j`, degree `g + g`)
  and `mulB D k` (the map `(x,y) ↦ x + y + E k`, degree `g + g + g`);
* `mulσ D i j k`, the RESID map, with VALUE (`mulσ_value`) and DEFINED (`mulσ_mem_domain`);
* `mulW D i j k` (where `mulσ` is defined and takes values in `V`), `mulOnW D i j k` (its
  value, with `mulOnW_value`), `mulPiece D i j k` (the piece map into `G D`) and
  `mulPiece_cls` (the class of the piece map is the sum of the classes of the coordinates);
* `MIdx D = D.Idx × D.Idx × D.Idx`, the piece open `mulZ D a` in `V ⊗ V`, the inclusion
  `mulPieceGG D a` of the piece into `G D ⊗ G D` and the piece map `mulPieceZ D a` into
  `G D`, together with `mulPieceZ_cls`.
-/
import Mathlib
import Submission.Work.GroupChunk.Group
import Submission.Work.GroupChunk.Transitions
import Submission.Work.GroupChunk.Gluing.Data
import Submission.Work.GroupChunk.Defs
import Submission.Work.GroupChunk.AbelJacobi
import Submission.Work.GroupChunk.Gluing.Transitions
import Submission.Work.GroupChunk.landsIn_aux
import Submission.Work.GroupChunk.U_self
import Submission.Work.GroupChunk.sigmaOnW_value
import Submission.Work.GroupChunk.exists_factor_resPt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.GroupChunk.GroupLaw

noncomputable section

open Work.GCBasics
open Work.GroupChunk

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
  [SpecLin.DivBase C]

/-! ## General helpers -/

/-- The tensor product of two open immersions is an open immersion. -/
theorem isOpenImmersion_tensorHom {S : Scheme} {X₁ X₂ Y₁ Y₂ : Over S} (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) [IsOpenImmersion f.left] [IsOpenImmersion g.left] :
    IsOpenImmersion (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  infer_instance

/-- The range of `ιOver U ≫ f` is contained in `W` as soon as `U ≤ f ⁻¹ᵁ W`. -/
theorem range_ιOver_comp_subset {X Y : Sch K} (f : X ⟶ Y) (U : X.left.Opens)
    (W : Y.left.Opens) (h : U ≤ f.left ⁻¹ᵁ W) :
    Set.range (Opens.ιOver U ≫ f).left ⊆ (W : Set Y.left) := by
  rintro _ ⟨z, rfl⟩
  have h2 : (Opens.ιOver U ≫ f).left z = f.left (U.ι z) := by
    rw [Over.comp_left, Opens.ιOver_left, Scheme.Hom.comp_apply]
  rw [h2]
  exact h z.2

/-- Base change of divisors is additive, in the form used by `bcKF`. -/
theorem bcKF_add {F : Type u} [Field F] [Algebra K F] (A B : Dv C K) :
    bcKF (C := C) F (A + B) = bcKF (C := C) F A + bcKF (C := C) F B := by
  simp only [bcKF, SpecLin.DivBase.bc_add]

/-! ## The product `Sym^g C ⊗ Sym^g C` and the chart `V ⊗ V` -/

/-- The product `Sym^g C ⊗ Sym^g C`. -/
abbrev SymSym (D : Input C P0) : Sch K := D.Sym D.g ⊗ D.Sym D.g

/-- The product `V ⊗ V` of two copies of the chart. -/
abbrev VVo (D : Input C P0) : Sch K := Opens.toOver D.V ⊗ Opens.toOver D.V

/-- The open immersion `V ⊗ V ⟶ Sym^g C ⊗ Sym^g C`. -/
abbrev eVV (D : Input C P0) : VVo D ⟶ SymSym D :=
  Opens.ιOver D.V ⊗ₘ Opens.ιOver D.V

theorem eVV_fst (D : Input C P0) :
    eVV D ≫ fst (D.Sym D.g) (D.Sym D.g)
      = fst (Opens.toOver D.V) (Opens.toOver D.V) ≫ Opens.ιOver D.V := by
  simp only [eVV, CartesianMonoidalCategory.tensorHom_fst]

theorem eVV_snd (D : Input C P0) :
    eVV D ≫ snd (D.Sym D.g) (D.Sym D.g)
      = snd (Opens.toOver D.V) (Opens.toOver D.V) ≫ Opens.ιOver D.V := by
  simp only [eVV, CartesianMonoidalCategory.tensorHom_snd]

instance instIsOpenImmersion_eVV (D : Input C P0) : IsOpenImmersion (eVV D).left :=
  isOpenImmersion_tensorHom (Opens.ιOver D.V) (Opens.ιOver D.V)

instance instIsOpenImmersion_chartH (D : Input C P0) (i : D.Idx) :
    IsOpenImmersion (chartH D i).left := isOpenImmersion_ι_glue D i

/-- `Sym^g C ⊗ Sym^g C` is integral. -/
theorem isIntegral_SymSym (D : Input C P0) : IsIntegral (SymSym D).left := by
  haveI : IsLocallyNoetherian (D.Sym D.g).left :=
    LocallyOfFiniteType.isLocallyNoetherian (D.Sym D.g).hom
  rw [SymSym, Over.tensorObj_left]
  infer_instance

instance instIsReduced_SymSym (D : Input C P0) : IsReduced (SymSym D).left := by
  haveI : IsIntegral (SymSym D).left := isIntegral_SymSym D
  infer_instance

instance instIsReduced_VVo (D : Input C P0) : IsReduced (VVo D).left :=
  isReduced_of_isOpenImmersion (eVV D).left

/-! ## The divisors `E i + E j` and the maps `mulA`, `mulB` -/

/-- The divisor `E i + E j` of the two chart centres. -/
abbrev Esum (D : Input C P0) (i j : D.Idx) : Dv C K := D.EDiv i + D.EDiv j

theorem Esum_isEffective (D : Input C P0) (i j : D.Idx) : (Esum D i j).IsEffective :=
  (D.EDiv_isEffective i).add (D.EDiv_isEffective j)

theorem Esum_deg (D : Input C P0) (i j : D.Idx) :
    Ddeg C K (Esum D i j) = (D.g + D.g : ℕ) := by
  rw [Esum, map_add, D.EDiv_deg i, D.EDiv_deg j, Nat.cast_add]

/-- The constant map at `E i + E j`. -/
abbrev mulA (D : Input C P0) (i j : D.Idx) : SymSym D ⟶ D.Sym (D.g + D.g) :=
  D.constMap (D.g + D.g) (Esum D i j) (Esum_isEffective D i j) (Esum_deg D i j) (SymSym D)

/-- The map `(x, y) ↦ x + y + E k`. -/
abbrev mulB (D : Input C P0) (k : D.Idx) : SymSym D ⟶ D.Sym ((D.g + D.g) + D.g) :=
  liftEquiv (D.addMap D.g D.g, constE k (SymSym D)) ≫ D.addMap (D.g + D.g) D.g

theorem divOf_mulA (D : Input C P0) (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (SymSym D) F) :
    (D.symGeom (D.g + D.g)).divOf (p ≫ mulA D i j)
      = bcKF (C := C) F (D.EDiv i) + bcKF (C := C) F (D.EDiv j) := by
  have h := D.constMap_divOf (D.g + D.g) (Esum D i j) (Esum_isEffective D i j)
    (Esum_deg D i j) (SymSym D) p
  simpa only [Esum, bcKF_add] using h

theorem divOf_mulB (D : Input C P0) (k : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (SymSym D) F) :
    (D.symGeom ((D.g + D.g) + D.g)).divOf (p ≫ mulB D k)
      = (D.symGeom D.g).divOf (p ≫ fst (D.Sym D.g) (D.Sym D.g))
        + (D.symGeom D.g).divOf (p ≫ snd (D.Sym D.g) (D.Sym D.g))
        + bcKF (C := C) F (D.EDiv k) := by
  have h2 : (D.symGeom (D.g + D.g)).divOf (p ≫ D.addMap D.g D.g)
      = (D.symGeom D.g).divOf (p ≫ fst (D.Sym D.g) (D.Sym D.g))
        + (D.symGeom D.g).divOf (p ≫ snd (D.Sym D.g) (D.Sym D.g)) := by
    have h' := D.addMap_divOf D.g D.g (fst (D.Sym D.g) (D.Sym D.g))
      (snd (D.Sym D.g) (D.Sym D.g)) p
    rw [← h']
    congr 1
    simp only [CartesianMonoidalCategory.liftEquiv_apply, CartesianMonoidalCategory.lift_fst_snd,
      Category.comp_id]
  have h := D.addMap_divOf (D.g + D.g) D.g (D.addMap D.g D.g) (constE k (SymSym D)) p
  rw [mulB]
  rw [← Category.assoc, h, h2, constE_divOf]

/-! ## The RESID map `mulσ` -/

/-- The RESID existence statement of the multiplication (the type is isolated so that the
witness stays opaque for the kernel). -/
theorem exists_mulσ (D : Input C P0) (i j k : D.Idx) :
    ∃ σ : (SymSym D).left ⤏ (D.Sym D.g).left,
      Resid C D.symGeom (inferInstance : IsReduced (SymSym D).left)
        (by haveI := D.isProper_Sym D.g; exact inferInstance) (mulA D i j) (mulB D k) σ := by
  haveI : IsIntegral (SymSym D).left := isIntegral_SymSym D
  haveI hloft : LocallyOfFiniteType (SymSym D).hom := by
    rw [SymSym, Over.tensorObj_hom]
    infer_instance
  haveI hln : IsLocallyNoetherian (SymSym D).left :=
    LocallyOfFiniteType.isLocallyNoetherian (SymSym D).hom
  exact @D.resid_exists (SymSym D) (inferInstance : IsIntegral (SymSym D).left) hln
    D.normal_SymSym (D.g + D.g) D.g (mulA D i j) (mulB D k) le_rfl

/-- The RESID map of the multiplication. -/
def mulσ (D : Input C P0) (i j k : D.Idx) : (SymSym D).left ⤏ (D.Sym D.g).left :=
  Classical.choose (exists_mulσ D i j k)

theorem mulσ_spec (D : Input C P0) (i j k : D.Idx) :
    Resid C D.symGeom (inferInstance : IsReduced (SymSym D).left)
      (by haveI := D.isProper_Sym D.g; exact inferInstance) (mulA D i j) (mulB D k)
      (mulσ D i j k) :=
  Classical.choose_spec (exists_mulσ D i j k)

theorem mulσ_isOver (D : Input C P0) (i j k : D.Idx) :
    (mulσ D i j k).IsOver (Spec (CommRingCat.of K)) :=
  (mulσ_spec D i j k).isOver

/-- The value of `mulσ i j k` at a field point of its domain. -/
def mulσVal (D : Input C P0) (i j k : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (SymSym D) F) (hp : RPt.LandsIn p (mulσ D i j k).domain) : FPt (D.Sym D.g) F :=
  value (instIsReduced_SymSym D)
    (by haveI := D.isProper_Sym D.g; exact inferInstance) (mulσ D i j k)
    (mulσ_isOver D i j k) p hp

/-- **VALUE** of `mulσ i j k`. -/
theorem mulσ_value (D : Input C P0) (i j k : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (SymSym D) F) (hp : RPt.LandsIn p (mulσ D i j k).domain) :
    LinEquiv C (D.divOf D.g (mulσVal D i j k p hp) + (bcKF (C := C) F (D.EDiv i)
        + bcKF (C := C) F (D.EDiv j)))
      ((D.divOf D.g (p ≫ fst (D.Sym D.g) (D.Sym D.g))
        + D.divOf D.g (p ≫ snd (D.Sym D.g) (D.Sym D.g))) + bcKF (C := C) F (D.EDiv k)) := by
  have h := (mulσ_spec D i j k).value p hp
  rw [divOf_mulA, divOf_mulB] at h
  simpa only [mulσVal, value] using h

/-- **DEFINED** of `mulσ i j k`. -/
theorem mulσ_mem_domain (D : Input C P0) (i j k : D.Idx) (x : (SymSym D).left)
    (hx : ell C (D.divOf ((D.g + D.g) + D.g) (resPt (SymSym D) x ≫ mulB D k)
      - D.divOf (D.g + D.g) (resPt (SymSym D) x ≫ mulA D i j)) = 1) :
    x ∈ (mulσ D i j k).domain :=
  (mulσ_spec D i j k).mem_domain x hx

theorem mulσVal_apply (D : Input C P0) (i j k : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (SymSym D) F) (h : RPt.LandsIn q (mulσ D i j k).domain) :
    (mulσVal D i j k q h).left (IsLocalRing.closedPoint F)
      = (mulσ D i j k).toPartialMap.hom ((Classical.choose
          (RPt.factor_of_closed_landsIn (mulσ D i j k).domain q h)).left
            (IsLocalRing.closedPoint F)) := by
  simp only [mulσVal, value]
  rfl

/-- The underlying morphism of `mulσVal`. -/
theorem mulσVal_left (D : Input C P0) (i j k : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (SymSym D) F) (hp : RPt.LandsIn p (mulσ D i j k).domain) :
    (mulσVal D i j k p hp).left
      = (Classical.choose (RPt.factor_of_closed_landsIn (mulσ D i j k).domain p hp)).left
        ≫ (mulσ D i j k).toPartialMap.hom := by
  simp only [mulσVal, value, Over.homMk_left]
  rfl

/-! ## The open `mulW` where `mulσ` is defined and lands in `V` -/

/-- The partial map representing `mulσ i j k`. -/
abbrev mulσPM (D : Input C P0) (i j k : D.Idx) :
    (SymSym D).left.PartialMap (D.Sym D.g).left :=
  (mulσ D i j k).toPartialMap

theorem mulσPM_hom_comp (D : Input C P0) (i j k : D.Idx) :
    (mulσPM D i j k).hom ≫ (D.Sym D.g).hom = (mulσPM D i j k).domain.ι ≫ (SymSym D).hom :=
  (Scheme.PartialMap.isOver_toRationalMap_iff_of_isSeparated
    (S := Spec (CommRingCat.of K))).mp
    (by rw [Scheme.RationalMap.toRationalMap_toPartialMap]; exact mulσ_isOver D i j k) |>.1

/-- The open of `Sym^g C ⊗ Sym^g C` where `mulσ i j k` is defined and takes values in `V`. -/
def mulW (D : Input C P0) (i j k : D.Idx) : (SymSym D).left.Opens :=
  (mulσPM D i j k).domain.ι ''ᵁ ((mulσPM D i j k).hom ⁻¹ᵁ D.V)

theorem mulW_le_domain (D : Input C P0) (i j k : D.Idx) :
    mulW D i j k ≤ (mulσPM D i j k).domain :=
  Scheme.Opens.ι_image_le _ _

/-- A point of `mulW i j k` has its `mulσ`-value in `V`. -/
theorem mem_V_of_mem_mulW (D : Input C P0) (i j k : D.Idx) (z : (mulW D i j k)) :
    (mulσPM D i j k).hom (⟨(z : (SymSym D).left), mulW_le_domain D i j k z.2⟩
      : (mulσPM D i j k).domain) ∈ D.V :=
  (Scheme.Opens.mem_ι_image_iff (U := (mulσPM D i j k).domain)
    (V := (mulσPM D i j k).hom ⁻¹ᵁ D.V)
    (x := (⟨(z : (SymSym D).left), mulW_le_domain D i j k z.2⟩
      : (mulσPM D i j k).domain))).mp z.2

/-- Membership in `mulW i j k` from the value: a point in the domain of `mulσ i j k` whose
value lies in `V` is in `mulW i j k`. -/
theorem mulW_mem_of_val_mem_V (D : Input C P0) (i j k : D.Idx) {F : Type u} [Field F]
    [Algebra K F] (p : FPt (SymSym D) F) (hp : RPt.LandsIn p (mulσ D i j k).domain)
    (hv : RPt.LandsIn (mulσVal D i j k p hp) D.V) : RPt.LandsIn p (mulW D i j k) := by
  have hmem : p.left (IsLocalRing.closedPoint F) ∈ (mulσPM D i j k).domain := hp
  obtain ⟨Q, hQ, -⟩ := FPt.factor_of_landsIn (mulσ D i j k).domain p hp
  have huniq := (Classical.choose_spec
    (RPt.factor_of_closed_landsIn (mulσ D i j k).domain p hp)).2
  have hQ' : Q = Classical.choose (RPt.factor_of_closed_landsIn (mulσ D i j k).domain p hp) :=
    huniq Q hQ
  have hι : Function.Injective (mulσPM D i j k).domain.ι := fun a b h => Subtype.val_injective h
  have hQι : (mulσPM D i j k).domain.ι (Q.left (IsLocalRing.closedPoint F))
      = p.left (IsLocalRing.closedPoint F) := by
    have h := congrArg Over.Hom.left hQ
    rw [Over.comp_left, Opens.ιOver_left] at h
    exact congrArg (fun g : (specOf K F).left ⟶ (SymSym D).left =>
      g (IsLocalRing.closedPoint F)) h
  have hpt : Q.left (IsLocalRing.closedPoint F)
      = (⟨p.left (IsLocalRing.closedPoint F), hmem⟩ : (mulσPM D i j k).domain) :=
    hι (by rw [hQι]; rfl)
  have hV : (mulσPM D i j k).hom (Q.left (IsLocalRing.closedPoint F)) ∈ D.V := by
    have h1 : (mulσPM D i j k).hom ((Classical.choose
        (RPt.factor_of_closed_landsIn (mulσ D i j k).domain p hp)).left
          (IsLocalRing.closedPoint F)) ∈ D.V := by
      rw [← mulσVal_apply D i j k p hp]
      exact hv
    rw [show (Classical.choose (RPt.factor_of_closed_landsIn (mulσ D i j k).domain p hp))
        = Q from hQ'.symm] at h1
    exact h1
  have hmemV : (⟨p.left (IsLocalRing.closedPoint F), hmem⟩ : (mulσPM D i j k).domain)
      ∈ ((mulσPM D i j k).hom ⁻¹ᵁ D.V) := by
    rw [← hpt]; exact hV
  exact (Scheme.Opens.mem_ι_image_iff (U := (mulσPM D i j k).domain)
    (V := (mulσPM D i j k).hom ⁻¹ᵁ D.V)
    (x := (⟨p.left (IsLocalRing.closedPoint F), hmem⟩ : (mulσPM D i j k).domain))).mpr hmemV

/-! ## The value map on `mulW` and the piece map -/

theorem exists_mulWtoDom (D : Input C P0) (i j k : D.Idx) :
    ∃! g : Opens.toOver (mulW D i j k) ⟶ Opens.toOver (mulσ D i j k).domain,
      g ≫ Opens.ιOver (mulσ D i j k).domain = Opens.ιOver (mulW D i j k) :=
  exists_factor_of_range_subset (mulσ D i j k).domain (Opens.ιOver (mulW D i j k))
    (by rw [Opens.range_ιOver]; exact mulW_le_domain D i j k)

/-- The inclusion `mulW i j k ⊆ dom (mulσ i j k)`. -/
def mulWtoDom (D : Input C P0) (i j k : D.Idx) :
    Opens.toOver (mulW D i j k) ⟶ Opens.toOver (mulσ D i j k).domain :=
  Classical.choose (exists_mulWtoDom D i j k)

theorem mulWtoDom_ιOver (D : Input C P0) (i j k : D.Idx) :
    mulWtoDom D i j k ≫ Opens.ιOver (mulσ D i j k).domain = Opens.ιOver (mulW D i j k) :=
  (Classical.choose_spec (exists_mulWtoDom D i j k)).1

/-- The partial map `mulσ i j k` on its domain, as a morphism of `K`-schemes. -/
def mulσOver (D : Input C P0) (i j k : D.Idx) :
    Opens.toOver (mulσ D i j k).domain ⟶ D.Sym D.g :=
  Over.homMk (mulσPM D i j k).hom (mulσPM_hom_comp D i j k)

/-- The value map on `mulW i j k`. -/
def mulOnW (D : Input C P0) (i j k : D.Idx) : Opens.toOver (mulW D i j k) ⟶ D.Sym D.g :=
  mulWtoDom D i j k ≫ mulσOver D i j k

/-- The value map `mulOnW i j k` computes the value of the rational map `mulσ i j k`. -/
theorem mulOnW_value (D : Input C P0) (i j k : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver (mulW D i j k)) F)
    (hq : RPt.LandsIn (q ≫ Opens.ιOver (mulW D i j k)) (mulσ D i j k).domain) :
    q ≫ mulOnW D i j k = mulσVal D i j k (q ≫ Opens.ιOver (mulW D i j k)) hq := by
  have hfac : (q ≫ mulWtoDom D i j k) ≫ Opens.ιOver (mulσ D i j k).domain
      = q ≫ Opens.ιOver (mulW D i j k) := by rw [Category.assoc, mulWtoDom_ιOver]
  have huniq : q ≫ mulWtoDom D i j k
      = Classical.choose (RPt.factor_of_closed_landsIn (mulσ D i j k).domain
          (q ≫ Opens.ιOver (mulW D i j k)) hq) :=
    (Classical.choose_spec (RPt.factor_of_closed_landsIn (mulσ D i j k).domain
      (q ≫ Opens.ιOver (mulW D i j k)) hq)).2 (q ≫ mulWtoDom D i j k) hfac
  have h2 : mulσVal D i j k (q ≫ Opens.ιOver (mulW D i j k)) hq
      = (q ≫ mulWtoDom D i j k) ≫ mulσOver D i j k := by
    apply Over.OverMorphism.ext
    rw [mulσVal_left, ← congrArg Over.Hom.left huniq]
    rfl
  rw [h2, mulOnW, Category.assoc]

theorem range_mulOnW_le_V (D : Input C P0) (i j k : D.Idx) :
    Set.range (mulOnW D i j k).left ⊆ (D.V : Set _) := by
  rintro _ ⟨z, rfl⟩
  have h1 : (mulOnW D i j k).left z = (mulσPM D i j k).hom ((mulWtoDom D i j k).left z) := rfl
  rw [h1]
  have h4 : (mulσ D i j k).domain.ι ((mulWtoDom D i j k).left z)
      = (mulW D i j k).ι z := by
    have h5 := congrArg
      (fun (k' : (Opens.toOver (mulW D i j k)).left ⟶ (SymSym D).left) => k' z)
      (congrArg Over.Hom.left (mulWtoDom_ιOver D i j k))
    simpa only [Over.comp_left, Opens.ιOver_left, Scheme.Hom.comp_apply,
      Scheme.Opens.ι_apply] using h5
  have h2 : (mulWtoDom D i j k).left z
      = (⟨(mulW D i j k).ι z, mulW_le_domain D i j k z.2⟩ : (mulσPM D i j k).domain) := by
    apply Subtype.val_injective
    change (mulσ D i j k).domain.ι ((mulWtoDom D i j k).left z)
      = (mulσ D i j k).domain.ι (⟨(mulW D i j k).ι z, mulW_le_domain D i j k z.2⟩
          : (mulσPM D i j k).domain)
    rw [h4]
    rfl
  rw [h2]
  exact mem_V_of_mem_mulW D i j k z

theorem exists_mulWtoV (D : Input C P0) (i j k : D.Idx) :
    ∃! g : Opens.toOver (mulW D i j k) ⟶ Opens.toOver D.V,
      g ≫ Opens.ιOver D.V = mulOnW D i j k :=
  exists_factor_of_range_subset D.V (mulOnW D i j k) (range_mulOnW_le_V D i j k)

/-- The value map `mulOnW i j k`, factored through the chart `V`. -/
def mulWtoV (D : Input C P0) (i j k : D.Idx) :
    Opens.toOver (mulW D i j k) ⟶ Opens.toOver D.V :=
  Classical.choose (exists_mulWtoV D i j k)

theorem mulWtoV_ιOver (D : Input C P0) (i j k : D.Idx) :
    mulWtoV D i j k ≫ Opens.ιOver D.V = mulOnW D i j k :=
  (Classical.choose_spec (exists_mulWtoV D i j k)).1

/-- **The piece map**: the value of `mulσ i j k` on `mulW i j k` followed by the `k`-th
chart. -/
def mulPiece (D : Input C P0) (i j k : D.Idx) : Opens.toOver (mulW D i j k) ⟶ GSch D :=
  mulWtoV D i j k ≫ chartH D k

set_option maxHeartbeats 1000000 in
/-- The class of `mulσVal` is the sum of the classes of the two coordinates. -/
theorem picOf_mulσVal (D : Input C P0) (i j k : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (SymSym D) F) (hp : RPt.LandsIn p (mulσ D i j k).domain) :
    D.picOf k (mulσVal D i j k p hp)
      = D.picOf i (p ≫ fst (D.Sym D.g) (D.Sym D.g))
        + D.picOf j (p ≫ snd (D.Sym D.g) (D.Sym D.g)) := by
  have hval := mulσ_value D i j k p hp
  rw [← Input.EF_divOf (D := D) i, ← Input.EF_divOf (D := D) j,
    ← Input.EF_divOf (D := D) k] at hval
  have hd1 := ddeg_sub_divOf D.symGeom D.g (p ≫ fst (D.Sym D.g) (D.Sym D.g)) (D.EF i)
  have hd2 := ddeg_sub_divOf D.symGeom D.g (p ≫ snd (D.Sym D.g) (D.Sym D.g)) (D.EF j)
  have hd3 : Ddeg C F ((D.divOf D.g (p ≫ fst (D.Sym D.g) (D.Sym D.g))
      - D.divOf D.g (D.EF i))
      + (D.divOf D.g (p ≫ snd (D.Sym D.g) (D.Sym D.g)) - D.divOf D.g (D.EF j))) = 0 := by
    rw [map_add, hd1, hd2, add_zero]
  have hsum : D.picOf i (p ≫ fst (D.Sym D.g) (D.Sym D.g))
        + D.picOf j (p ≫ snd (D.Sym D.g) (D.Sym D.g))
      = Pic0.mk ((D.divOf D.g (p ≫ fst (D.Sym D.g) (D.Sym D.g))
          - D.divOf D.g (D.EF i))
        + (D.divOf D.g (p ≫ snd (D.Sym D.g) (D.Sym D.g)) - D.divOf D.g (D.EF j))) hd3 := by
    rw [Input.picOf_def, Input.picOf_def]
    exact (Pic0.mk_add hd1 hd2 hd3).symm
  rw [hsum, Input.picOf_def]
  refine (Pic0.mk_eq_iff _ _).mpr ?_
  rw [show (D.divOf D.g (p ≫ fst (D.Sym D.g) (D.Sym D.g))
        - D.divOf D.g (D.EF i))
      + (D.divOf D.g (p ≫ snd (D.Sym D.g) (D.Sym D.g)) - D.divOf D.g (D.EF j))
      = (D.divOf D.g (p ≫ fst (D.Sym D.g) (D.Sym D.g))
          + D.divOf D.g (p ≫ snd (D.Sym D.g) (D.Sym D.g)))
        - (D.divOf D.g (D.EF i) + D.divOf D.g (D.EF j)) from by abel]
  exact (linEquiv_add_iff_sub (D.divOf D.g (mulσVal D i j k p hp))
    (D.divOf D.g (p ≫ fst (D.Sym D.g) (D.Sym D.g))
      + D.divOf D.g (p ≫ snd (D.Sym D.g) (D.Sym D.g)))
    (D.divOf D.g (D.EF i) + D.divOf D.g (D.EF j))
    (D.divOf D.g (D.EF k))).mpr hval

/-- The class of the piece map is the sum of the classes of the two coordinates. -/
theorem mulPiece_cls (D : Input C P0) (i j k : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver (mulW D i j k)) F) :
    D.cls (q ≫ mulPiece D i j k)
      = D.picOf i ((q ≫ Opens.ιOver (mulW D i j k)) ≫ fst (D.Sym D.g) (D.Sym D.g))
        + D.picOf j ((q ≫ Opens.ιOver (mulW D i j k)) ≫ snd (D.Sym D.g) (D.Sym D.g)) := by
  have hq : (q ≫ mulWtoV D i j k) ≫ Opens.ιOver D.V = q ≫ mulOnW D i j k := by
    rw [Category.assoc, mulWtoV_ιOver]
  have hdom : RPt.LandsIn (q ≫ Opens.ιOver (mulW D i j k)) (mulσ D i j k).domain :=
    mulW_le_domain D i j k (landsIn_ιOver_self (mulW D i j k) q)
  have hval := mulOnW_value D i j k q hdom
  have hcls := Input.cls_chart D k (q ≫ mulWtoV D i j k)
  rw [show q ≫ mulPiece D i j k = (q ≫ mulWtoV D i j k) ≫ chartH D k from rfl, hcls, hq, hval]
  exact picOf_mulσVal D i j k (q ≫ Opens.ιOver (mulW D i j k)) hdom

/-! ## The pieces of the multiplication -/

/-- The index type of the pieces: a triple `(i, j, k)` of chart centres. -/
abbrev MIdx (D : Input C P0) : Type u := D.Idx × D.Idx × D.Idx

/-- The piece open in `V ⊗ V`: the locus where `mulσ i j k` is defined with value in `V`. -/
def mulZ (D : Input C P0) (a : MIdx D) : (VVo D).left.Opens :=
  (eVV D).left ⁻¹ᵁ (mulW D a.1 a.2.1 a.2.2)

/-- The inclusion `mulZ a ⟶ mulW i j k`. -/
def mulZtoW (D : Input C P0) (a : MIdx D) :
    Opens.toOver (mulZ D a) ⟶ Opens.toOver (mulW D a.1 a.2.1 a.2.2) :=
  Classical.choose (exists_factor_of_range_subset (mulW D a.1 a.2.1 a.2.2)
    (Opens.ιOver (mulZ D a) ≫ eVV D)
    (range_ιOver_comp_subset (eVV D) (mulZ D a) (mulW D a.1 a.2.1 a.2.2) le_rfl))

theorem mulZtoW_ιOver (D : Input C P0) (a : MIdx D) :
    mulZtoW D a ≫ Opens.ιOver (mulW D a.1 a.2.1 a.2.2) = Opens.ιOver (mulZ D a) ≫ eVV D :=
  (Classical.choose_spec (exists_factor_of_range_subset (mulW D a.1 a.2.1 a.2.2)
    (Opens.ιOver (mulZ D a) ≫ eVV D)
    (range_ιOver_comp_subset (eVV D) (mulZ D a) (mulW D a.1 a.2.1 a.2.2) le_rfl))).1

/-- The piece map into `G D`. -/
def mulPieceZ (D : Input C P0) (a : MIdx D) : Opens.toOver (mulZ D a) ⟶ GSch D :=
  mulZtoW D a ≫ mulPiece D a.1 a.2.1 a.2.2

/-- The piece, as an open subscheme of `G D ⊗ G D`. -/
def mulPieceGG (D : Input C P0) (a : MIdx D) : Opens.toOver (mulZ D a) ⟶ GSch D ⊗ GSch D :=
  Opens.ιOver (mulZ D a) ≫ (chartH D a.1 ⊗ₘ chartH D a.2.1)

instance instIsOpenImmersion_mulPieceGG (D : Input C P0) (a : MIdx D) :
    IsOpenImmersion (mulPieceGG D a).left := by
  rw [mulPieceGG, Over.comp_left]
  haveI : IsOpenImmersion (chartH D a.1 ⊗ₘ chartH D a.2.1).left :=
    isOpenImmersion_tensorHom (chartH D a.1) (chartH D a.2.1)
  exact IsOpenImmersion.comp _ _

theorem mulPieceGG_fst (D : Input C P0) (a : MIdx D) :
    mulPieceGG D a ≫ fst (GSch D) (GSch D)
      = (Opens.ιOver (mulZ D a) ≫ fst (Opens.toOver D.V) (Opens.toOver D.V)) ≫ chartH D a.1 := by
  rw [mulPieceGG, Category.assoc, CartesianMonoidalCategory.tensorHom_fst, Category.assoc]

theorem mulPieceGG_snd (D : Input C P0) (a : MIdx D) :
    mulPieceGG D a ≫ snd (GSch D) (GSch D)
      = (Opens.ιOver (mulZ D a) ≫ snd (Opens.toOver D.V) (Opens.toOver D.V)) ≫ chartH D a.2.1 := by
  rw [mulPieceGG, Category.assoc, CartesianMonoidalCategory.tensorHom_snd, Category.assoc]

instance instIsReduced_mulZ (D : Input C P0) (a : MIdx D) :
    IsReduced (Opens.toOver (mulZ D a)).left :=
  isReduced_of_isOpenImmersion (mulZ D a).ι

set_option maxHeartbeats 800000 in
/-- The class of the piece map is the sum of the classes of the two coordinates of the point
of `G D ⊗ G D`. -/
theorem mulPieceZ_cls (D : Input C P0) (a : MIdx D) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver (mulZ D a)) F) :
    D.cls (q ≫ mulPieceZ D a)
      = D.cls (q ≫ mulPieceGG D a ≫ fst (GSch D) (GSch D))
        + D.cls (q ≫ mulPieceGG D a ≫ snd (GSch D) (GSch D)) := by
  have h1 : q ≫ mulPieceZ D a = (q ≫ mulZtoW D a) ≫ mulPiece D a.1 a.2.1 a.2.2 := by
    rw [mulPieceZ, Category.assoc]
  rw [h1, mulPiece_cls D a.1 a.2.1 a.2.2 (q ≫ mulZtoW D a)]
  congr 1
  · rw [show q ≫ mulPieceGG D a ≫ fst (GSch D) (GSch D)
        = ((q ≫ Opens.ιOver (mulZ D a))
            ≫ fst (Opens.toOver D.V) (Opens.toOver D.V)) ≫ chartH D a.1 from by
      simp only [mulPieceGG, Category.assoc, CartesianMonoidalCategory.tensorHom_fst]]
    rw [Input.cls_chart]
    congr 1
    simp only [mulZtoW_ιOver, eVV_fst, Category.assoc]
  · rw [show q ≫ mulPieceGG D a ≫ snd (GSch D) (GSch D)
        = ((q ≫ Opens.ιOver (mulZ D a))
            ≫ snd (Opens.toOver D.V) (Opens.toOver D.V)) ≫ chartH D a.2.1 from by
      simp only [mulPieceGG, Category.assoc, CartesianMonoidalCategory.tensorHom_snd]]
    rw [Input.cls_chart]
    congr 1
    simp only [mulZtoW_ιOver, eVV_snd, Category.assoc]

/-- `G D ⊗ G D`, the source of the multiplication. -/
abbrev GMul (D : Input C P0) : Sch K := GSch D ⊗ GSch D

/-- **The pieces cover `G D ⊗ G D`**: every field point of `G D ⊗ G D` factors through one of
the piece inclusions `mulPieceGG D a`. -/
def MulCovers (D : Input C P0) : Prop :=
  ∀ {F : Type u} [Field F] [Algebra K F] (u : FPt (GMul D) F),
    ∃ a : MIdx D, ∃ v : FPt (Opens.toOver (mulZ D a)) F, v ≫ mulPieceGG D a = u

/-- The group chunk `G D` is separated over `Spec K`. -/
def GSep (D : Input C P0) : Prop := IsSeparated (GSch D).hom

/-- **The compatibility of the pieces on the overlaps**, i.e. the descent condition for
gluing the piece maps into a morphism `G D ⊗ G D ⟶ G D`. -/
def MulCompat (D : Input C P0) : Prop :=
  ∀ a b : MIdx D,
    pullback.fst (mulPieceGG D a).left (mulPieceGG D b).left ≫ (mulPieceZ D a).left
      = pullback.snd (mulPieceGG D a).left (mulPieceGG D b).left ≫ (mulPieceZ D b).left

end

end Work.GroupChunk.GroupLaw
