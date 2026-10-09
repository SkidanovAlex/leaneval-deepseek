import Mathlib
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.HassePrinciple.IdelesLevel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Compatibility of the localisation of the units with the localisation of the idèles

This module proves `NK.HassePrinciple.locUnits_compatible`, the compatibility of the relative
Hasse–Brauer–Noether localisation `H²(Gal(L/K), Lˣ) → ∏_w H²(Γ_w, L_wˣ)` with the idèle
localisation `H²(Gal(L/K), 𝕀_L) → ∏_w H²(Γ_w, L_wˣ)` along the principal idèles `Lˣ ↪ 𝕀_L`.

The mathematical content is two facts:

* the `w`-component of the principal idèle of `x : Lˣ` is the image of `x` in `L_wˣ`, which is
  the statement that the coefficient morphisms fit into a commutative triangle
  `Rep.res _ ideleIncl ≫ ideleToLocalUnits = unitsToLocalUnits`
  (`NK.HassePrinciple.res_ideleIncl_comp_ideleToLocalUnits`);
* the naturality of `groupCohomology.resNatTrans` in the coefficient representation, which says
  that restriction to the decomposition group `Γ_w` commutes with the coefficient map
  (`NK.HassePrinciple.locUnits_eq_unitsToIdeleH2_comp`).

Assembling these two gives the compatibility of the localisations
(`NK.HassePrinciple.locUnits_compatible`).
-/

open CategoryTheory Representation
open NK.GlobalCFT

namespace NK.HassePrinciple

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## The coefficient triangle -/

/-- **The `w`-component of the principal idèle of `x : Lˣ` is the image of `x` in `L_wˣ`.**

Equivalently: the composite of the principal idèles `Lˣ ↪ 𝕀_L` with the `w`-component
`𝕀_L → L_wˣ` is the natural embedding `Lˣ ↪ L_wˣ`, i.e.

`Rep.res _ ideleIncl ≫ ideleToLocalUnits = unitsToLocalUnits`. -/
theorem res_ideleIncl_comp_ideleToLocalUnits (w : Place L) :
    (Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype).map (ideleIncl K L) ≫
        ideleToLocalUnits K L w = unitsToLocalUnits K L w := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rw [Rep.hom_comp]
  simp only [Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply]
  show Additive.ofMul (ideleComponentHom w (Idele.principalIdele L (Additive.toMul x)))
     = Additive.ofMul (unitsToLocalUnitsHom w (Additive.toMul x))
  rfl

/-! ## The compatibility of the two localisations -/

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The `w`-component of the localisation of `H²(Γ, Lˣ)` is the `w`-component of the idèle
localisation composed with the map induced by the principal idèles.**

This is the naturality of `groupCohomology.resNatTrans` combined with
`NK.HassePrinciple.res_ideleIncl_comp_ideleToLocalUnits`.  The option
`backward.isDefEq.respectTransparency false` is needed because the types of
`groupCohomology.resNatTrans`'s components are stated through the composite functor
`Rep.resFunctor f ⋙ groupCohomology.functor k G n`, which is only definitionally equal (and not
at the transparency level used by rewriting) to `groupCohomology (Rep.res f X) n`. -/
theorem locUnits_eq_unitsToIdeleH2_comp (w : Place L) :
    locUnits K L w = unitsToIdeleH2 K L ≫ ideleLoc K L w := by
  have hcomp := res_ideleIncl_comp_ideleToLocalUnits (K := K) (L := L) w
  -- `map (id Γ_w) ∘ (coefficient triangle)` for the previously localised modules
  have hmap : groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
        ((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype).map (ideleIncl K L)) 2 ≫
      groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
        (ideleToLocalUnits K L w) 2 =
      (groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
        (unitsToLocalUnits K L w) 2 :
        groupCohomology (Rep.res (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype (unitsRep K L)) 2 ⟶
          groupCohomology (localUnitsRep K L w) 2) := by
    rw [← groupCohomology.map_id_comp
      ((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype).map (ideleIncl K L))
      (ideleToLocalUnits K L w) 2, hcomp]
  -- the naturality square of the restriction, in the form used by the definitions
  have hnat : groupCohomology.map (MonoidHom.id (L ≃ₐ[K] L)) (ideleIncl K L) 2 ≫
        groupCohomology.map (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
          (𝟙 (Rep.res (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype (ideleRep K L))) 2 =
      groupCohomology.map (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
          (𝟙 (Rep.res (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype (unitsRep K L))) 2 ≫
        groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
          ((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype).map (ideleIncl K L)) 2 := by
    have h := (groupCohomology.resNatTrans CoeffInt (G := MulAction.stabilizer (L ≃ₐ[K] L) w)
      (H := L ≃ₐ[K] L) (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype 2).naturality (ideleIncl K L)
    simpa only [groupCohomology.resNatTrans_app, groupCohomology.functor_map, Functor.comp_map,
      Functor.comp_obj, groupCohomology.functor_obj, Rep.resMap] using h
  rw [locUnits, ideleLoc, unitsToIdeleH2]
  simp only [groupCohomology.resNatTrans_app]
  rw [← hmap, ← Category.assoc, ← hnat, Category.assoc]

/-- **The compatibility of the localisation of the units with the localisation of the idèles**
(`NK.HassePrinciple.LocUnitsCompatible K L`, defined in
`Submission/Work/HassePrinciple/LocalUnits.lean`): for every place `w : Place L` and every class
`a : H²(Gal(L/K), Lˣ)`, the `w`-component `NK.HassePrinciple.locUnits K L w a` of the relative
Hasse–Brauer–Noether localisation of `a` equals the `w`-component
`NK.HassePrinciple.ideleLoc K L w (NK.HassePrinciple.unitsToIdeleH2 K L a)` of the idèle
localisation of the image of `a` along the principal idèles `Lˣ ↪ 𝕀_L`.

Proof: naturality of `groupCohomology.resNatTrans` (restriction commutes with the coefficient map
`ideleIncl`), together with the fact that the `w`-component of the principal idèle of `x : Lˣ` is
the image of `x` in `L_wˣ` (`LocalUnits.ideleToLocalUnits` composed with `ideleIncl` is
`unitsToLocalUnits`), i.e. `Rep.res _ ideleIncl ≫ ideleToLocalUnits = unitsToLocalUnits`. -/
theorem locUnits_compatible {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    NK.HassePrinciple.LocUnitsCompatible K L := by
  intro w a
  rw [locUnits_eq_unitsToIdeleH2_comp (K := K) (L := L) w]
  rfl

end NK.HassePrinciple
