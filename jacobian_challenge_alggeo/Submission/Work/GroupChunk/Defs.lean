/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — the transitions `σᵢⱼ` and their domains

For a chart datum `D : Input C P0` (see `Submission/Work/GroupChunk/Interface.lean`) this file
constructs

* `constE i`, the constant map at the centre `E i` of the `i`-th chart;
* `addE j`, the morphism `p ↦ p + E j`;
* `σ i j`, the transition rational map `x ↦ |divOf x - E i + E j|`, obtained from the RESID
  engine `D.resid_exists`;
* the VALUE and DEFINED properties of `σ i j`, restated in terms of the divisors `E i`, `E j`;
* `W i j`, the open of `Sym^g C` where `σ i j` is defined and takes values in the chart `V`;
* `U i j = V ∩ W i j`, the transition domain inside the chart, and `tHom i j`, the value of the
  transition on `U i j`.
-/
import Submission.Work.GroupChunk.Interface

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.GroupChunk

noncomputable section

open Work.GCBasics

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
  [SpecLin.DivBase C]

section

variable [D : Input C P0]

/-! ## Constants and addition -/

/-- The constant map at the centre `E i` of the `i`-th chart (area SY's `Sym.ofDiv`). -/
def constE (i : D.Idx) (X : Sch K) : X ⟶ (D.symGeom D.g).S :=
  D.constMap D.g (D.EDiv i) (D.EDiv_isEffective i) (D.EDiv_deg i) X

/-- The divisor of a point of the constant map at `E i`. -/
theorem constE_divOf (i : D.Idx) (X : Sch K) {F : Type u} [Field F] [Algebra K F]
    (p : FPt X F) :
    (D.symGeom D.g).divOf (p ≫ constE i X) = bcKF F (D.EDiv i) :=
  D.constMap_divOf D.g (D.EDiv i) (D.EDiv_isEffective i) (D.EDiv_deg i) X p

/-- The morphism `p ↦ p + E j` from `Sym^g C` to `Sym^{2g} C`. -/
def addE (j : D.Idx) : D.Sym D.g ⟶ D.Sym (D.g + D.g) :=
  CartesianMonoidalCategory.liftEquiv (𝟙 (D.Sym D.g), constE j (D.Sym D.g)) ≫ D.addMap D.g D.g

/-- The divisor of `p + E j`. -/
theorem divOf_addE (j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (D.Sym D.g) F) :
    (D.symGeom (D.g + D.g)).divOf (p ≫ addE j)
      = (D.symGeom D.g).divOf p + bcKF F (D.EDiv j) := by
  rw [addE, ← Category.assoc, D.addMap_divOf]
  rw [Category.comp_id, constE_divOf]

/-! ## The transition rational maps -/

/-- The transition rational map `σ_ij : Sym^g C ⤏ Sym^g C`, sending a point `x` to the
effective representative of `divOf x - E i + E j`.  This is the RESID engine
`D.resid_exists` applied to `a := constE i` and `b := addE j`. -/
def σ (i j : D.Idx) : (D.Sym D.g).left ⤏ (D.Sym D.g).left :=
  Classical.choose
    (@D.resid_exists (D.Sym D.g) (inferInstance : IsIntegral (D.Sym D.g).left)
      (LocallyOfFiniteType.isLocallyNoetherian (D.Sym D.g).hom) D.normal_Sym D.g D.g (constE i (D.Sym D.g)) (addE j) le_rfl)

/-- The RESID specification of `σ i j`. -/
theorem σ_spec (i j : D.Idx) :
    Resid C D.symGeom (inferInstance : IsReduced (D.Sym D.g).left)
      (by haveI := D.isProper_Sym D.g; exact inferInstance) (constE i (D.Sym D.g)) (addE j)
      (σ i j) :=
  Classical.choose_spec
    (@D.resid_exists (D.Sym D.g) (inferInstance : IsIntegral (D.Sym D.g).left)
      (LocallyOfFiniteType.isLocallyNoetherian (D.Sym D.g).hom) D.normal_Sym D.g D.g (constE i (D.Sym D.g)) (addE j) le_rfl)

/-- `σ i j` is a morphism over `K`. -/
theorem σ_isOver (i j : D.Idx) : (σ i j).IsOver (Spec (CommRingCat.of K)) :=
  (σ_spec i j).isOver

/-- The partial map underlying `σ i j` is a morphism over `K`. -/
theorem σ_toPartialMap_isOver (i j : D.Idx) :
    ((σ i j).toPartialMap).IsOver (Spec (CommRingCat.of K)) := by
  have h1 : ((σ i j).toPartialMap).toRationalMap.IsOver (Spec (CommRingCat.of K)) := by
    rw [Scheme.RationalMap.toRationalMap_toPartialMap]
    exact σ_isOver i j
  exact (Scheme.PartialMap.isOver_toRationalMap_iff_of_isSeparated
    (S := Spec (CommRingCat.of K))).mp h1

/-- The value of `σ i j` at a point of its domain: the canonical `K`-point it induces. -/
abbrev σVal (i j : D.Idx) {F : Type u} [Field F] [Algebra K F] (p : FPt (D.Sym D.g) F)
    (hp : RPt.LandsIn p (σ i j).domain) : FPt (D.Sym D.g) F :=
  value (inferInstance : IsReduced (D.Sym D.g).left)
    (by haveI := D.isProper_Sym D.g; exact inferInstance) (σ i j) (σ_isOver i j) p hp

/-- **VALUE** of the transition: at every point of the domain of `σ i j`,
`divOf (σ i j(x)) + E i ~ divOf x + E j`. -/
theorem σ_value (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (D.Sym D.g) F) (hp : RPt.LandsIn p (σ i j).domain) :
    LinEquiv C ((D.symGeom D.g).divOf (σVal i j p hp) + bcKF F (D.EDiv i))
      ((D.symGeom D.g).divOf p + bcKF F (D.EDiv j)) := by
  have h := (σ_spec i j).value p hp
  rw [divOf_addE j, constE_divOf i (D.Sym D.g)] at h
  exact h

/-- **DEFINED** of the transition: if `ℓ(divOf x + E j - E i) = 1` then `σ i j` is defined
at `x`. -/
theorem σ_mem_domain (i j : D.Idx) (x : (D.Sym D.g).left)
    (hx : ell C ((D.symGeom D.g).divOf (resPt (D.Sym D.g) x)
      + bcKF (resField (D.Sym D.g) x) (D.EDiv j)
      - bcKF (resField (D.Sym D.g) x) (D.EDiv i)) = 1) :
    x ∈ (σ i j).domain := by
  refine (σ_spec i j).mem_domain x ?_
  rw [divOf_addE j, constE_divOf i (D.Sym D.g)]
  exact hx

/-! ## The transition domains -/

/-- The partial map representing `σ i j` (this is `(σ i j).toPartialMap`, kept as a named
abbreviation so that the domain of definition is a single syntactic object). -/
abbrev σPM (i j : D.Idx) : (D.Sym D.g).left.PartialMap (D.Sym D.g).left :=
  (σ i j).toPartialMap

/-- The structure identity for the partial map of `σ i j`. -/
theorem σPM_hom_comp (i j : D.Idx) :
    (σPM i j).hom ≫ (D.Sym D.g).hom = (σPM i j).domain.ι ≫ (D.Sym D.g).hom :=
  (σ_toPartialMap_isOver i j).1

/-- The open `W i j ⊆ Sym^g C` of points of the domain of `σ i j` whose value lies in the
chart `V`. -/
def W (i j : D.Idx) : (D.Sym D.g).left.Opens :=
  (σPM i j).domain.ι ''ᵁ ((σPM i j).hom ⁻¹ᵁ D.V)

/-- `W i j` is contained in the domain of `σ i j`. -/
theorem W_le_domain (i j : D.Idx) : W i j ≤ (σPM i j).domain :=
  Scheme.Opens.ι_image_le _ _

/-- The transition domain `U i j ⊆ V`: `V ∩ dom σ_ij ∩ σ_ij⁻¹V`, as an open subscheme of the
chart. -/
def U (i j : D.Idx) : (Opens.toOver D.V).left.Opens := D.V.ι ⁻¹ᵁ W i j

/-- The composite inclusion `U i j ⊆ Sym^g C`. -/
def Uι (i j : D.Idx) : Opens.toOver (U i j) ⟶ D.Sym D.g :=
  Opens.ιOver (U i j) ≫ Opens.ιOver D.V

/-- The inclusion of `U i j` into `Sym^g C` lands in `W i j`. -/
theorem range_Uι_le_W (i j : D.Idx) :
    Set.range (Uι i j).left ⊆ (W i j : Set (D.Sym D.g).left) := by
  rintro _ ⟨y, rfl⟩
  exact y.2

/-- The value of `σ i j` on `W i j`, as a morphism of `K`-schemes. -/
def σOnW (i j : D.Idx) : Opens.toOver (W i j) ⟶ D.Sym D.g :=
  Over.homMk (Scheme.homOfLE (D.Sym D.g).left (U := W i j) (W_le_domain i j)
      ≫ (σPM i j).hom) (by
    change (Scheme.homOfLE (D.Sym D.g).left (U := W i j) (W_le_domain i j)
        ≫ (σPM i j).hom) ≫ (D.Sym D.g).hom = (W i j).ι ≫ (D.Sym D.g).hom
    rw [Category.assoc, σPM_hom_comp, ← Category.assoc, Scheme.homOfLE_ι])

/-- The identification of `U i j` with the corresponding open of `W i j`. -/
def UToW (i j : D.Idx) : Opens.toOver (U i j) ⟶ Opens.toOver (W i j) :=
  Over.homMk (IsOpenImmersion.lift (W i j).ι (Uι i j).left
    (by rw [Scheme.Opens.range_ι]; exact range_Uι_le_W i j)) (by
    change IsOpenImmersion.lift (W i j).ι (Uι i j).left _ ≫ (W i j).ι ≫ (D.Sym D.g).hom
      = (Uι i j).left ≫ (D.Sym D.g).hom
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Over.Hom.w])

/-- The value of `σ i j` on `U i j`: a morphism `U i j ⟶ Sym^g C`. -/
def tHom (i j : D.Idx) : Opens.toOver (U i j) ⟶ D.Sym D.g :=
  UToW i j ≫ σOnW i j

end

end

end Work.GroupChunk
