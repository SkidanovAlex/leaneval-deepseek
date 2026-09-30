/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — the Abel–Jacobi chart maps

The Abel–Jacobi morphism `AJSym : Sym^g C ⟶ G D` is glued from the chart maps
`ρ i : x ↦ |divOf x - g·P0 + E i|`, exactly as the transitions `σ i j` are glued from
`x ↦ |divOf x - E i + E j|`.  This file constructs `g·P0`, the constant map at it, the chart
maps `ρ i` and their VALUE/DEFINED properties, in complete analogy with `Defs.lean`.
-/
import Submission.Work.GroupChunk.Defs

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

/-! ## The base divisor `g · P0` -/

namespace Input

/-- The divisor `g • [P0]` of the Abel–Jacobi base point. -/
def P0g (D : Input C P0) : Dv C K := D.g • D.P0Div

/-- `g • [P0]` is effective. -/
theorem P0g_isEffective (D : Input C P0) : D.P0g.IsEffective := by
  intro Q
  rw [P0g, Finsupp.nsmul_apply]
  exact mul_nonneg (Nat.cast_nonneg D.g) (D.P0Div_isEffective Q)

/-- The degree of `g • [P0]` is `g`. -/
theorem P0g_deg (D : Input C P0) : Ddeg C K D.P0g = (D.g : ℤ) := by
  have h : Ddeg C K (D.g • D.P0Div) = D.g • Ddeg C K D.P0Div := map_nsmul _ _ _
  rw [P0g, h, D.P0Div_deg, nsmul_eq_mul, mul_one]

end Input

/-- The constant map at `g • [P0]`. -/
def constPg (X : Sch K) : X ⟶ (D.symGeom D.g).S :=
  D.constMap D.g D.P0g (Input.P0g_isEffective D) (Input.P0g_deg D) X

/-- The divisor of a point of the constant map at `g • [P0]`. -/
theorem constPg_divOf (X : Sch K) {F : Type u} [Field F] [Algebra K F] (p : FPt X F) :
    (D.symGeom D.g).divOf (p ≫ constPg X) = bcKF F D.P0g :=
  D.constMap_divOf D.g D.P0g (Input.P0g_isEffective D) (Input.P0g_deg D) X p

/-! ## The Abel–Jacobi chart maps -/

/-- The Abel–Jacobi chart map `ρ i : x ↦ |divOf x - g•P0 + E i|`. -/
def ρ (i : D.Idx) : (D.Sym D.g).left ⤏ (D.Sym D.g).left :=
  Classical.choose
    (@D.resid_exists (D.Sym D.g) (inferInstance : IsIntegral (D.Sym D.g).left)
      (LocallyOfFiniteType.isLocallyNoetherian (D.Sym D.g).hom) D.normal_Sym D.g D.g (constPg (D.Sym D.g)) (addE i) le_rfl)

/-- The RESID specification of `ρ i`. -/
theorem ρ_spec (i : D.Idx) :
    Resid C D.symGeom (inferInstance : IsReduced (D.Sym D.g).left)
      (by haveI := D.isProper_Sym D.g; exact inferInstance) (constPg (D.Sym D.g)) (addE i)
      (ρ i) :=
  Classical.choose_spec
    (@D.resid_exists (D.Sym D.g) (inferInstance : IsIntegral (D.Sym D.g).left)
      (LocallyOfFiniteType.isLocallyNoetherian (D.Sym D.g).hom) D.normal_Sym D.g D.g (constPg (D.Sym D.g)) (addE i) le_rfl)

/-- `ρ i` is a morphism over `K`. -/
theorem ρ_isOver (i : D.Idx) : (ρ i).IsOver (Spec (CommRingCat.of K)) :=
  (ρ_spec i).isOver

/-- The partial map representing `ρ i`. -/
abbrev ρPM (i : D.Idx) : (D.Sym D.g).left.PartialMap (D.Sym D.g).left :=
  (ρ i).toPartialMap

/-- The value of `ρ i` at a point of its domain. -/
abbrev ρVal (i : D.Idx) {F : Type u} [Field F] [Algebra K F] (p : FPt (D.Sym D.g) F)
    (hp : RPt.LandsIn p (ρ i).domain) : FPt (D.Sym D.g) F :=
  value (inferInstance : IsReduced (D.Sym D.g).left)
    (by haveI := D.isProper_Sym D.g; exact inferInstance) (ρ i) (ρ_isOver i) p hp

/-- **VALUE** of the Abel–Jacobi chart map. -/
theorem ρ_value (i : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (D.Sym D.g) F) (hp : RPt.LandsIn p (ρ i).domain) :
    LinEquiv C ((D.symGeom D.g).divOf (ρVal i p hp) + bcKF F D.P0g)
      ((D.symGeom D.g).divOf p + bcKF F (D.EDiv i)) := by
  have h := (ρ_spec i).value p hp
  rw [divOf_addE i, constPg_divOf] at h
  exact h

/-- The structure identity for the partial map of `ρ i`. -/
theorem ρPM_hom_comp (i : D.Idx) :
    (ρPM i).hom ≫ (D.Sym D.g).hom = (ρPM i).domain.ι ≫ (D.Sym D.g).hom := by
  have h1 : ((ρ i).toPartialMap).toRationalMap.IsOver (Spec (CommRingCat.of K)) := by
    rw [Scheme.RationalMap.toRationalMap_toPartialMap]
    exact ρ_isOver i
  exact ((Scheme.PartialMap.isOver_toRationalMap_iff_of_isSeparated
    (S := Spec (CommRingCat.of K))).mp h1).1

/-- **DEFINED** of the Abel–Jacobi chart map. -/
theorem ρ_mem_domain (i : D.Idx) (x : (D.Sym D.g).left)
    (hx : ell C ((D.symGeom D.g).divOf (resPt (D.Sym D.g) x)
      + bcKF (resField (D.Sym D.g) x) (D.EDiv i)
      - bcKF (resField (D.Sym D.g) x) D.P0g) = 1) :
    x ∈ (ρ i).domain := by
  refine (ρ_spec i).mem_domain x ?_
  rw [divOf_addE i, constPg_divOf]
  exact hx

/-- Base change of a `K`-divisor to `F` preserves the degree. -/
theorem deg_bcKF (F : Type u) [Field F] [Algebra K F] (E : Dv C K) :
    Ddeg C F (bcKF F E) = Ddeg C K E :=
  SpecLin.DivBase.deg_bc (Algebra.ofId K F) E

namespace Input

/-- The class of a point of `Sym^g C` modulo `g • [P0]`: the Abel–Jacobi class map. -/
def picAJ (D : Input C P0) {F : Type u} [Field F] [Algebra K F] (p : FPt (D.Sym D.g) F) :
    Pic0 C F :=
  Pic0.mk (D.divOf D.g p - bcKF F D.P0g)
    (by
      rw [map_sub,
        show Ddeg C F (D.divOf D.g p) = (D.g : ℤ) from (D.symGeom D.g).divOf_deg p,
        show Ddeg C F (bcKF F D.P0g) = (D.g : ℤ) from by
          rw [deg_bcKF, Input.P0g_deg], sub_self])

end Input

/-! ## The Abel–Jacobi domains -/

/-- The open `Wρ i ⊆ Sym^g C` of points of the domain of `ρ i` whose value lies in the chart
`V`. -/
def Wρ (i : D.Idx) : (D.Sym D.g).left.Opens :=
  (ρPM i).domain.ι ''ᵁ ((ρPM i).hom ⁻¹ᵁ D.V)

/-- `Wρ i` is contained in the domain of `ρ i`. -/
theorem Wρ_le_domain (i : D.Idx) : Wρ i ≤ (ρPM i).domain :=
  Scheme.Opens.ι_image_le _ _

/-- The value of `ρ i` on `Wρ i`, as a morphism of `K`-schemes. -/
def ρOnW (i : D.Idx) : Opens.toOver (Wρ i) ⟶ D.Sym D.g :=
  Over.homMk (Scheme.homOfLE (D.Sym D.g).left (U := Wρ i) (Wρ_le_domain i)
      ≫ (ρPM i).hom) (by
    change (Scheme.homOfLE (D.Sym D.g).left (U := Wρ i) (Wρ_le_domain i)
        ≫ (ρPM i).hom) ≫ (D.Sym D.g).hom = (Wρ i).ι ≫ (D.Sym D.g).hom
    rw [Category.assoc, ρPM_hom_comp, ← Category.assoc, Scheme.homOfLE_ι])

/-- The transition domain of `ρ i` inside the chart `V`, together with the target open
`Uρ i = V ∩ Wρ i`. -/
def Uρ (i : D.Idx) : (Opens.toOver D.V).left.Opens := D.V.ι ⁻¹ᵁ Wρ i

/-- The composite inclusion `Uρ i ⊆ Sym^g C`. -/
def Uρι (i : D.Idx) : Opens.toOver (Uρ i) ⟶ D.Sym D.g :=
  Opens.ιOver (Uρ i) ≫ Opens.ιOver D.V

/-- The inclusion of `Uρ i` into `Sym^g C` lands in `Wρ i`. -/
theorem range_Uρι_le_Wρ (i : D.Idx) :
    Set.range (Uρι i).left ⊆ (Wρ i : Set (D.Sym D.g).left) := by
  rintro _ ⟨y, rfl⟩
  exact y.2

/-- The identification of `Uρ i` with the corresponding open of `Wρ i`. -/
def UρToW (i : D.Idx) : Opens.toOver (Uρ i) ⟶ Opens.toOver (Wρ i) :=
  Over.homMk (IsOpenImmersion.lift (Wρ i).ι (Uρι i).left
    (by rw [Scheme.Opens.range_ι]; exact range_Uρι_le_Wρ i)) (by
    change IsOpenImmersion.lift (Wρ i).ι (Uρι i).left _ ≫ (Wρ i).ι ≫ (D.Sym D.g).hom
      = (Uρι i).left ≫ (D.Sym D.g).hom
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Over.Hom.w])

/-- The value of `ρ i` on `Uρ i`: a morphism `Uρ i ⟶ Sym^g C`. -/
def ρHom (i : D.Idx) : Opens.toOver (Uρ i) ⟶ D.Sym D.g :=
  UρToW i ≫ ρOnW i

end

end

end Work.GroupChunk
