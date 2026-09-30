/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# (D1) The generic-fibre order dictionary of an affine chart

This file starts the "chart dictionary" needed by the proof of
`Work.SpecLin.Core.coreDivCore` (specialisation of linear equivalence over a valuation ring):

* `rgMap_fac`: an `R`-point of `C` whose image lies in an affine open `W` factors through
  `Spec Γ(C,W)` via the `K`-algebra map `Work.SpecLin.Core.rgMap`;
* `genPtMap_fac`: the generic fibre `s^F` of such a point factors through the base-changed
  chart `W_F`, via the generic fibre of `rgMap`;
* `ptToPoint_genPt_mem_chart`: hence the point of `C_F` attached to `s^F` lies in the chart
  `W_F`;
* `ring_ord_eq_zero_iff`: in any ring, `Ring.ord R x = 0 ↔ IsUnit x`;
* `ord_germ_eq_zero_of_notMem`: **(D1)** for an integral locally Noetherian scheme `X`, a
  nonempty affine open `U`, a point `z ∈ U` of coheight one and a section `a ∈ Γ(X,U)` which
  does not vanish at `z`, the order of vanishing of `a` at `z` is `0`.

The remaining half of (D1) — the comparison of `Scheme.ord` with `Ring.ordFrac` of the ring of
the chart localised at the prime of `z` (equivalently, membership in the powers of that prime) —
is the content of `Work.SpecLin.Core.ord_germ_eq_iff_mem_pow` (requested separately).  See
`NOTES_coreDivCore.md` for the full proof plan of `coreDivCore`.
-/
import Mathlib
import Submission.Work.SpecLin.Conventions
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SpecLin.Core.linEquiv_of_sections
import Submission.Work.SpecLin.Alt.chartDictionary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SpecLin.Core

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}

/-- The `R`-point `s` of `C`, whose image lies in the affine open `W`, factors through the
chart: `Spec.map (rgMapHom R W hW s hs) ≫ hW.fromSpec = s.left`. -/
theorem rgMap_fac (R : Type u) [CommRing R] [Algebra K R] (W : C.left.Opens)
    (hW : IsAffineOpen W) (s : Work.SpecLin.CurvePt C R)
    (hs : Set.range (s.left.base) ⊆ (W : Set C.left)) :
    Spec.map (CommRingCat.ofHom (rgMapHom R W hW s hs)) ≫ hW.fromSpec = s.left := by
  rw [show Spec.map (CommRingCat.ofHom (rgMapHom R W hW s hs)) =
      IsOpenImmersion.lift hW.fromSpec s.left
        (by rw [IsAffineOpen.range_fromSpec]; exact hs) from Spec.map_preimage _]
  exact IsOpenImmersion.lift_fac _ _ _

/-- The generic fibre `s^F` of the `R`-point `s` factors through the base-changed chart `W_F`,
via the generic fibre `Γ(C,W) →ₐ[K] F` of `rgMap`. -/
theorem genPtMap_fac (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : IsAffineOpen W) (s : Work.SpecLin.CurvePt C R)
    (hs : Set.range (s.left.base) ⊆ (W : Set C.left)) :
    (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) s).left
      = (Work.SpecLin.specOfMap (K := K)
          ((IsScalarTower.toAlgHom K R (FractionRing R)).comp (rgMap R W hW s hs))).left
        ≫ hW.fromSpec := by
  show Spec.map (CommRingCat.ofHom (IsScalarTower.toAlgHom K R (FractionRing R)).toRingHom)
      ≫ s.left
    = Spec.map (CommRingCat.ofHom
        (((IsScalarTower.toAlgHom K R (FractionRing R)).comp (rgMap R W hW s hs)).toRingHom))
      ≫ hW.fromSpec
  rw [← rgMap_fac R W hW s hs, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- The generic-fibre point of a section lies in the affine chart `W_F` of `C_F`. -/
theorem ptToPoint_genPt_mem_chart (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (hW : IsAffineOpen W) (s : Work.SpecLin.CurvePt C R)
    (hs : Set.range (s.left.base) ⊆ (W : Set C.left)) :
    Work.SpecLin.ptToPoint
        (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) s)
      ∈ C.bcOpens (FractionRing R) W :=
  Work.SpecLin.Alt.ptToPoint_mem_of_factors W hW _ _
    (genPtMap_fac R W hW s hs)

/-- In any ring, an element has order of vanishing `0` exactly when it is a unit. -/
theorem ring_ord_eq_zero_iff {R : Type u} [CommRing R] (x : R) :
    Ring.ord R x = 0 ↔ IsUnit x := by
  rw [Ring.ord, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff,
    Ideal.span_singleton_eq_top]

/-- **(D1) The vanishing criterion for the order of vanishing on an affine chart.**

Let `X` be an integral locally Noetherian scheme, `U ⊆ X` a nonempty affine open, `z ∈ U` a
point of coheight one and `a ∈ Γ(X,U)` a section which does not vanish at `z` (i.e. `a` is not
in the prime of `z` inside the chart ring).  Then `a` has order of vanishing `0` at `z`. -/
theorem ord_germ_eq_zero_of_notMem {X : AlgebraicGeometry.Scheme} [IsIntegral X]
    [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (z : X) (hz : z ∈ U) (hz1 : Order.coheight z = 1) (a : Γ(X, U))
    (ha : a ∉ (hU.primeIdealOf ⟨z, hz⟩).asIdeal) :
    X.ord (X.germToFunctionField U a) z = 0 := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, hz⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hz⟩).asIdeal :=
    hU.isLocalization_stalk ⟨z, hz⟩
  have hunit : IsUnit (X.presheaf.germ U z hz a) := by
    rw [show X.presheaf.germ U z hz a = algebraMap Γ(X, U) (X.presheaf.stalk z) a from rfl]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk z)
      (hU.primeIdealOf ⟨z, hz⟩).asIdeal a).mpr (by simpa [Ideal.mem_primeCompl_iff] using ha)
  have ha0 : a ≠ 0 := fun h => ha (h ▸ (hU.primeIdealOf ⟨z, hz⟩).asIdeal.zero_mem)
  have hf : X.germToFunctionField U a ≠ 0 := by
    intro h
    exact ha0 (Scheme.germToFunctionField_injective X U (by simpa using h))
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz1.le
  have h1 : (X.ordHom z hz1) (X.germToFunctionField U a) = 1 := by
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hz a]
    exact Ring.ordFrac_of_isUnit (R := X.presheaf.stalk z) (K := X.functionField) hunit
  rw [Scheme.ord_eq_iff hz1 hf, h1]
  simp

end Work.SpecLin.Core
