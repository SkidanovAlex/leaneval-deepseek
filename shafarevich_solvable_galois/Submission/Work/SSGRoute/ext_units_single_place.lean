import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.brauer_single_place
import Submission.Work.SSGRoute.extHRestrict_comp_mk0
import Submission.Work.SSGRoute.E0bClean.eBridge_natural
import Submission.Work.SSGRoute.hbn_ext_units
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-!
# The Hasse principle for the relative Brauer group, single place, `Ext` form

`Work.SSGRoute.ext_units_single_place` is the `Ext`-vocabulary form of the
Hasse–Brauer–Noether principle at a *single place* `w₀`: a class
`a ∈ H²(Gal(L/k), Lˣ) = extH (unitsK k L) 2 = Br(L/k)` whose localisation vanishes at every
place `w` of `L` that is not a `Gal(L/k)`-conjugate of `w₀` is zero.

The proof transports the group-cohomology statement `brauer_single_place` (proved from
`NK.GlobalCFTdeep.hbnUnits`, the Hasse–Brauer–Noether theorem) across the E0b comparison
`E0bGroupCoeff.eBridge : Hⁿ(G, A) ≃+ extH A n`, using

* `E0bClean.eBridge_natural` — naturality of `eBridge` under a change of group followed by a
  coefficient map (here `Γ_w ↪ Gal(L/k)` and `Lˣ → L_wˣ`);
* `extHRestrict_comp_mk0` — rewriting the `Ext`-localisation as `extHMap` (i.e. as
  `(extHRestrict · a) ∘ mk₀ (unitsToLocalUnits)`);
* `hbnAux_locUnits_eq_map` — NK's `locUnits` is a single `groupCohomology.map`.
-/

theorem ext_units_single_place (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (a : extH (unitsK k L) 2) (w₀ : NK.GlobalCFT.Place L)
    (h : ∀ w : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • w₀ ≠ w) →
      (extHRestrict (decompK (k := k) (K := L) w) a).comp
        (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k L w)) (add_zero 2) = 0) :
    a = 0 := by
  classical
  -- Transport along the E0b comparison `eBridge : H²(Gal(L/k), Lˣ) ≃+ extH (unitsK k L) 2`.
  let e := E0bGroupCoeff.eBridge 2 (L ≃ₐ[k] L) (unitsK k L)
  let x : groupCohomology (unitsK k L) 2 := e.symm a
  have hax : e x = a := e.apply_symm_apply a
  -- It suffices to show `x = 0`, by `brauer_single_place`.
  have hx0 : x = 0 := by
    refine brauer_single_place k L x w₀ (fun w hw => ?_)
    -- NK's `locUnits` at `w` is the single group change `Γ_w ↪ Gal(L/k)` with coefficient `Lˣ → L_wˣ`.
    have hmap : NK.HassePrinciple.locUnits k L w =
        groupCohomology.map (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
          (NK.HassePrinciple.unitsToLocalUnits k L w) 2 :=
      hbnAux_locUnits_eq_map (k := k) (L := L) w
    rw [hmap]
    -- Naturality of `eBridge` for this group change.
    have hnat := E0bClean.eBridge_natural
      (G := L ≃ₐ[k] L) (H := MulAction.stabilizer (L ≃ₐ[k] L) w)
      (A := unitsK k L) (B := NK.HassePrinciple.localUnitsRep k L w)
      (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
      (NK.HassePrinciple.unitsToLocalUnits k L w) 2 x
    -- Reduce to a statement about `eBridge`, which is injective.
    suffices E0bGroupCoeff.eBridge 2 (MulAction.stabilizer (L ≃ₐ[k] L) w)
        (NK.HassePrinciple.localUnitsRep k L w)
        ((groupCohomology.map (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
          (NK.HassePrinciple.unitsToLocalUnits k L w) 2).hom x) = 0 by
      exact (E0bGroupCoeff.eBridge 2 (MulAction.stabilizer (L ≃ₐ[k] L) w)
        (NK.HassePrinciple.localUnitsRep k L w)).injective (by rw [this, map_zero])
    rw [hnat, hax, ← extHRestrict_comp_mk0
      (MulAction.stabilizer (L ≃ₐ[k] L) w) a (NK.HassePrinciple.unitsToLocalUnits k L w)]
    exact h w hw
  calc a = e x := hax.symm
    _ = 0 := by rw [hx0, map_zero]

end Work.SSGRoute
