/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Kummer map commutes with the localisation at a place

Umbrella development: `Submission/Work/NUV2/LC/RouteB/`.

For a Galois extension `L/F` of number fields, a prime `p`, a place `w` of `L` with decomposition
group `Γ_w = MulAction.stabilizer (L ≃ₐ[F] L) w`, we prove

> if `a ∈ H²(Gal(L/F), μ_p(L))` restricts to `0` in `H²(Γ_w, μ_p(L))` (i.e. `a` is locally
  trivial at `w`), then the localisation at `w` of the Kummer image of `a` in
  `H²(Gal(L/F), Lˣ) = Br(L/F)` is zero,

i.e. `kummerMap_locUnits`.

This is the *local triviality* half of the Kummer dictionary used in Route B: it says that the
obvious square commutes, namely that the localisation `locUnits` of `H²(Γ, Lˣ)` is a natural
transformation of functors applied to the coefficient map `μ_p(L) ↪ Lˣ`, so that the localisation
of the Kummer map factors through the restriction to the decomposition group.

The proof is the naturality of `groupCohomology.resNatTrans` with respect to the coefficient
morphism `kummerIncl p F L : μ_p(L) ⟶ Lˣ`, evaluated at the class `a`.
-/

import Mathlib
import Submission.NK.NUV2.LC.LocalLevelSystem
import Submission.NK.HassePrinciple.LocalUnits

open CategoryTheory

namespace NK.NUV2.LC.RouteB

set_option maxHeartbeats 800000 in
/-- **The Kummer map followed by the localisation at `w` vanishes on classes already locally
trivial at `w`.**  Purely formal: `locUnits` is `res` followed by the coefficient map
`Lˣ → L_wˣ`, and `kummerMap` is the coefficient map `μ_p(L) → Lˣ` in second cohomology; the two
commute by the naturality of `resNatTrans` in the coefficient representation. -/
theorem kummerMap_locUnits {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (p : ℕ) (w : NK.GlobalCFT.Place L) (a : groupCohomology (NK.HassePrinciple.muRep p F L) 2)
    (h : ((groupCohomology.resNatTrans NK.HassePrinciple.CoeffInt
        (G := MulAction.stabilizer (L ≃ₐ[F] L) w) (H := L ≃ₐ[F] L)
        (MulAction.stabilizer (L ≃ₐ[F] L) w).subtype 2).app
          (NK.HassePrinciple.muRep p F L)).hom a = 0) :
    (NK.HassePrinciple.locUnits F L w).hom ((NK.HassePrinciple.kummerMap p F L).hom a) = 0 := by
  -- Naturality of the restriction `resNatTrans` in the coefficient representation.
  have hnat := NatTrans.naturality (groupCohomology.resNatTrans NK.HassePrinciple.CoeffInt
        (G := MulAction.stabilizer (L ≃ₐ[F] L) w) (H := L ≃ₐ[F] L)
        (MulAction.stabilizer (L ≃ₐ[F] L) w).subtype 2)
      (NK.HassePrinciple.kummerIncl p F L)
  -- Restated with the component maps `map _ _ 2` made explicit.
  have hnat' : groupCohomology.map (MonoidHom.id (L ≃ₐ[F] L))
          (NK.HassePrinciple.kummerIncl p F L) 2 ≫
        groupCohomology.map (MulAction.stabilizer (L ≃ₐ[F] L) w).subtype
          (𝟙 (Rep.res (MulAction.stabilizer (L ≃ₐ[F] L) w).subtype
            (NK.HassePrinciple.unitsRep F L))) 2
      = groupCohomology.map (MulAction.stabilizer (L ≃ₐ[F] L) w).subtype
          (𝟙 (Rep.res (MulAction.stabilizer (L ≃ₐ[F] L) w).subtype
            (NK.HassePrinciple.muRep p F L))) 2 ≫
        groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[F] L) w))
          ((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[F] L) w).subtype).map
            (NK.HassePrinciple.kummerIncl p F L)) 2 := hnat
  have h1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hnat') a
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  have h' : (ModuleCat.Hom.hom (groupCohomology.map (MulAction.stabilizer (L ≃ₐ[F] L) w).subtype
          (𝟙 (Rep.res (MulAction.stabilizer (L ≃ₐ[F] L) w).subtype
            (NK.HassePrinciple.muRep p F L))) 2)) a = 0 := h
  -- `locUnits` is the restriction followed by the coefficient map `Lˣ → L_wˣ`.
  change (ModuleCat.Hom.hom (groupCohomology.map (MulAction.stabilizer (L ≃ₐ[F] L) w).subtype
          (𝟙 (Rep.res (MulAction.stabilizer (L ≃ₐ[F] L) w).subtype
            (NK.HassePrinciple.unitsRep F L))) 2 ≫
        groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[F] L) w))
          (NK.HassePrinciple.unitsToLocalUnits F L w) 2))
      ((ModuleCat.Hom.hom (groupCohomology.map (MonoidHom.id (L ≃ₐ[F] L))
          (NK.HassePrinciple.kummerIncl p F L) 2)) a) = 0
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, h1]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, h']
  simp

end NK.NUV2.LC.RouteB
