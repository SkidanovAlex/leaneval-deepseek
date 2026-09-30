/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Order of vanishing along the base change of a curve

For a curve `C` over `k`, a field extension `F/k` and a place `Q'` of the base change
`C_F = C ×_k Spec F` whose image `Q` in `C` is a closed point, the order of vanishing of a
rational function `f ∈ K(C)` at `Q`, read in `K(C_F)` along the canonical injection
`K(C) ⟶ K(C_F)`, is multiplied by the ramification index `e(Q'/Q)`:

`ord_{Q'}(f) = e(Q'/Q) · ord_Q(f)`.

## Implementation notes

Everything is a computation with the order of vanishing `Ring.ordFrac` of the discrete
valuation rings `𝒪_{C,Q}` and `𝒪_{C_F,Q'}` (Mathlib's `Scheme.ord` is `Ring.ordFrac` of the
local ring, `Scheme.ord_eq_unzero_ordHom`).

* `ordAt_eq_log_ordFrac` rewrites `Scheme.ord` as the logarithm of `Ring.ordFrac`, which is
  additive: the whole computation happens in `ℤ`.
* `ordFrac_log_comp` (pure ring theory) is the numerical heart: if a field homomorphism
  `φ : K → L` of fraction fields of discrete valuation rings comes from a ring homomorphism
  `ψ : A → B` of the valuation rings and `u` is a uniformizer of `A`, then
  `log (ordFrac_B (φ f)) = log (ordFrac_B (φ u)) · log (ordFrac_A f)`.  Indeed
  `f = u^n · a` with `a` a unit of `A`, `n = log (ordFrac_A f)`, so `φ f = φ(u)^n · ψ(a)`
  and `ψ(a)` is a unit of `B`.
* `functionFieldMap_stalkMap` identifies the map on function fields with the local map of
  stalks `𝒪_{C,Q} ⟶ 𝒪_{C_F,Q'}` (a germ computation, using that every element of a stalk is a
  germ, `TopCat.Presheaf.exists_mem_germ_eq_of_isBasis`).
-/
import Mathlib
import Submission.Work.CurveBasics.BaseChangeDivisor

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe v

namespace Work.CurveBasics

/-- **The numerical core of the ramification formula for a base change.**

Let `A` and `B` be discrete valuation rings with fraction fields `K` and `L` and let
`φ : K →+* L` be an injective field homomorphism which is induced by a ring homomorphism
`ψ : A →+* B` of the valuation rings (i.e. `φ (algebraMap A K a) = algebraMap B L (ψ a)`).
If `u ∈ K` is a uniformizer of `A` (in the sense that `ordFrac A u = WithZero.exp 1`), then for
every `f ∈ K`

`log (ordFrac B (φ f)) = log (ordFrac B (φ u)) · log (ordFrac A f)`,

which says precisely that `φ` multiplies orders of vanishing by the ramification index
`log (ordFrac B (φ u))`. -/
theorem ordFrac_log_comp
    {A K B L : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing B] [IsDomain B] [IsNoetherianRing B] [Ring.KrullDimLE 1 B]
    [IsDiscreteValuationRing B]
    [Field L] [Algebra B L] [IsFractionRing B L]
    (φ : K →+* L) (hinj : Function.Injective φ) (ψ : A →+* B)
    (hcomm : ∀ a : A, φ (algebraMap A K a) = algebraMap B L (ψ a))
    {u : K} (hu : Ring.ordFrac A u = WithZero.exp 1) (f : K) :
    (Ring.ordFrac B (φ f)).log = (Ring.ordFrac B (φ u)).log * (Ring.ordFrac A f).log := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hfx : Ring.ordFrac A f ≠ 0 := fun h0 => hf (MonoidWithZeroHom.map_eq_zero_iff.mp h0)
  have huz : u ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hu
    exact WithZero.exp_ne_zero hu.symm
  have hφu : φ u ≠ 0 := fun h0 => huz (hinj (by rw [h0, map_zero]))
  -- `m` is the order of vanishing of `f`
  set m : ℤ := (Ring.ordFrac A f).log with hm
  have hm_eq : Ring.ordFrac A f = WithZero.exp m := (WithZero.exp_log hfx).symm.trans (by rw [hm])
  -- `u ^ m` has the same order of vanishing as `f`, so `f` is `u ^ m` up to a unit of `A`
  have hzu : Ring.ordFrac A (u ^ m) = Ring.ordFrac A f := by
    rw [map_zpow₀, hu, ← WithZero.exp_zsmul m (1 : ℤ), smul_eq_mul, mul_one, hm_eq]
  obtain ⟨w, hw⟩ := Ring.associated_of_ordFrac_eq (u ^ m) f hzu
  have hf_eq : f = algebraMap A K (w : A) * u ^ m := by
    rw [← hw, Units.smul_def, Algebra.smul_def]
  -- `φ` of a unit of `A` is a unit of `B`
  have hφ_eq : φ f = algebraMap B L (ψ (w : A)) * (φ u) ^ m := by
    rw [hf_eq, map_mul, map_zpow₀, hcomm (w : A)]
  have hψw : Ring.ordFrac B (algebraMap B L (ψ (w : A))) = 1 :=
    Ring.ordFrac_of_isUnit (w.isUnit.map ψ)
  have hpu : Ring.ordFrac B (φ u) ≠ 0 :=
    fun h0 => hφu (MonoidWithZeroHom.map_eq_zero_iff.mp h0)
  calc (Ring.ordFrac B (φ f)).log
      = (Ring.ordFrac B (algebraMap B L (ψ (w : A)) * (φ u) ^ m)).log := by rw [hφ_eq]
    _ = (Ring.ordFrac B (algebraMap B L (ψ (w : A))) * (Ring.ordFrac B (φ u)) ^ m).log := by
          rw [map_mul, map_zpow₀]
    _ = (Ring.ordFrac B (φ u)).log * (Ring.ordFrac A f).log := by
          rw [hψw, WithZero.log_mul one_ne_zero (zpow_ne_zero m hpu), WithZero.log_one, zero_add,
            WithZero.log_zpow, smul_eq_mul, ← hm]
          ring

namespace Curve

variable {k : Type v} [Field k] {C : Curve k}

/-- The order of vanishing of a rational function at a place is the logarithm of the order of
vanishing function `Ring.ordFrac` of the local ring at that place. -/
theorem ordAt_eq_log_ordFrac (Q : C.Place) (f : C.functionField) :
    C.ordAt f Q = (Ring.ordFrac (C.left.presheaf.stalk Q.point) (K := ↑C.functionField) f).log := by
  by_cases hf : f = 0
  · subst hf; simp [Curve.ordAt]
  · rw [Curve.ordAt, Scheme.ord_eq_unzero_ordHom Q.eq_coheight_one hf,
      WithZero.toAdd_unzero_eq_log]
    congr 1

/-- **The projection `C_F ⟶ C` is compatible with the maps of local rings.**

For a place `Q'` of the base change `C_F` with image `Q` in `C`, the induced map on function
fields intertwines `𝒪_{C,Q} ⟶ K(C)` with `𝒪_{C_F,Q'} ⟶ K(C_F)` along the stalk map of the
projection:

`φ (algebraMap 𝒪_{C,Q} K(C) a) = algebraMap 𝒪_{C_F,Q'} K(C_F) (stalkMap a)`. -/
theorem functionFieldMap_stalkMap (F : Type v) [Field F] [Algebra k F] (y : C.baseChangeLeft F)
    (a : C.left.presheaf.stalk ((C.baseChangeFst F) y)) :
    (C.functionFieldMap F).hom
        (algebraMap (C.left.presheaf.stalk ((C.baseChangeFst F) y)) (↑C.functionField) a) =
      algebraMap ((C.baseChangeLeft F).presheaf.stalk y) (↑(C.baseChangeLeft F).functionField)
        (((C.baseChangeFst F).stalkMap y).hom a) := by
  let Φ : (↑C.functionField) →+* (↑(C.baseChangeLeft F).functionField) := (C.functionFieldMap F).hom
  change Φ (algebraMap (C.left.presheaf.stalk ((C.baseChangeFst F) y)) (↑C.functionField) a) =
      algebraMap ((C.baseChangeLeft F).presheaf.stalk y) (↑(C.baseChangeLeft F).functionField)
        (((C.baseChangeFst F).stalkMap y).hom a)
  -- every element of a stalk is the germ of a section on an affine open neighbourhood
  obtain ⟨U, hxU, hUaff, r, hr⟩ :=
    TopCat.Presheaf.exists_mem_germ_eq_of_isBasis C.left.isBasis_affineOpens C.left.presheaf _ a
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  haveI hbc : Nonempty (C.bcOpens F U) := C.bcOpens_nonempty F U
  -- the two sides, evaluated on the germ of `r`
  have hA : algebraMap (C.left.presheaf.stalk ((C.baseChangeFst F) y)) (↑C.functionField)
      (C.left.presheaf.germ U ((C.baseChangeFst F) y) hxU r) = C.germToFunctionField U r :=
    Scheme.algebraMap_germ_eq_germToFunctionField (X := C.left) hxU r
  have hΦ : Φ (C.germToFunctionField U r) =
      Scheme.germToFunctionField (X := C.baseChangeLeft F) (U := C.bcOpens F U) (h := hbc)
        ((C.baseChangeFst F).app U r) := by
    rw [show Φ = (C.functionFieldMap F).hom from rfl, Curve.functionFieldMap]
    erw [ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
      Scheme.Hom.germ_stalkMap_apply]
    rfl
  have hψ : ((C.baseChangeFst F).stalkMap y).hom
      (C.left.presheaf.germ U ((C.baseChangeFst F) y) hxU r) =
      (C.baseChangeLeft F).presheaf.germ (C.bcOpens F U) y hxU
        ((C.baseChangeFst F).app U r) :=
    Scheme.Hom.germ_stalkMap_apply (C.baseChangeFst F) U y hxU r
  have hβ : algebraMap ((C.baseChangeLeft F).presheaf.stalk y) (↑(C.baseChangeLeft F).functionField)
      ((C.baseChangeLeft F).presheaf.germ (C.bcOpens F U) y hxU ((C.baseChangeFst F).app U r)) =
      Scheme.germToFunctionField (X := C.baseChangeLeft F) (U := C.bcOpens F U) (h := hbc)
        ((C.baseChangeFst F).app U r) :=
    @Scheme.algebraMap_germ_eq_germToFunctionField (C.baseChangeLeft F) _ (C.bcOpens F U) hbc y hxU
      ((C.baseChangeFst F).app U r)
  rw [← hr, hA, hψ]
  exact hΦ.trans hβ.symm

end Curve

end Work.CurveBasics

namespace Work.CurveBasics.BaseChange

universe u in
open Work.CurveBasics in
theorem ordAt_fieldMap {k : Type u} [Field k] {C : Curve k} (F : Type u) [Field F]
    [Algebra k F] (Q' : (C.baseChange F).Place)
    (h : IsClosed ({(C.baseChangeFst F) Q'.point} : Set C.left)) {f : C.functionField}
    (hf : f ≠ 0) :
    (C.baseChange F).ordAt ((C.functionFieldMap F).hom f) Q' =
      C.ramIdx F Q' * C.ordAt f (C.under F Q' h) := by
  classical
  -- the local rings of `C` at `Q` and of `C_F` at `Q'` are discrete valuation rings
  haveI hDVR : IsDiscreteValuationRing (C.left.presheaf.stalk ((C.baseChangeFst F) Q'.point)) :=
    (C.under F Q' h).instIsDiscreteValuationRing
  haveI hDVR' : IsDiscreteValuationRing ((C.baseChange F).left.presheaf.stalk Q'.point) :=
    Q'.instIsDiscreteValuationRing
  -- a uniformizer vanishes to order one
  have hu' : Ring.ordFrac (C.left.presheaf.stalk (C.under F Q' h).point) (K := ↑C.functionField)
      (C.under F Q' h).uniformizer = WithZero.exp 1 := by
    have h1 : Scheme.ord (C.under F Q' h).uniformizer (C.under F Q' h).point = 1 :=
      Work.CurveBasics.Place.ord_uniformizer (C.under F Q' h)
    have hne : (C.under F Q' h).uniformizer ≠ 0 := by
      intro h0; rw [h0] at h1; simp at h1
    have h2 := (Scheme.ord_eq_iff (C.under F Q' h).eq_coheight_one hne).mp h1
    simpa [Scheme.ordHom, WithZero.exp] using h2
  have hu : Ring.ordFrac (C.left.presheaf.stalk ((C.baseChangeFst F) Q'.point))
      (K := ↑C.functionField) (C.under F Q' h).uniformizer = WithZero.exp 1 := hu'
  -- the map on function fields comes from the map of local rings
  have hcomm : ∀ a : C.left.presheaf.stalk ((C.baseChangeFst F) Q'.point),
      (C.functionFieldMap F).hom
          (algebraMap (C.left.presheaf.stalk ((C.baseChangeFst F) Q'.point)) (↑C.functionField) a) =
        algebraMap ((C.baseChange F).left.presheaf.stalk Q'.point)
          (↑(C.baseChange F).functionField)
          (((C.baseChangeFst F).stalkMap Q'.point).hom a) :=
    fun a => Curve.functionFieldMap_stalkMap F Q'.point a
  have hcore := ordFrac_log_comp
    (A := C.left.presheaf.stalk ((C.baseChangeFst F) Q'.point)) (K := ↑C.functionField)
    (B := (C.baseChange F).left.presheaf.stalk Q'.point) (L := ↑(C.baseChange F).functionField)
    ((C.functionFieldMap F).hom) (C.functionFieldMap_injective F)
    (((C.baseChangeFst F).stalkMap Q'.point).hom) hcomm (u := (C.under F Q' h).uniformizer) hu f
  have hram : C.ramIdx F Q' = (Ring.ordFrac ((C.baseChange F).left.presheaf.stalk Q'.point)
      (K := ↑(C.baseChange F).functionField)
      ((C.functionFieldMap F).hom (C.under F Q' h).uniformizer)).log := by
    rw [Curve.ramIdx, dite_eq_left h, Curve.ordAt_eq_log_ordFrac (C := C.baseChange F) Q']
  rw [Curve.ordAt_eq_log_ordFrac (C := C.baseChange F) Q' ((C.functionFieldMap F).hom f), hram,
    Curve.ordAt_eq_log_ordFrac (C := C) (C.under F Q' h) f]
  exact hcore

end Work.CurveBasics.BaseChange
