import Mathlib
import Submission.NK.NUV2.LC.RouteB.muLift

/-!
# The Kummer morphism commutes with the `μ_p` / units transports to a level

Companion of `NK.NUV2.LC.RouteB.unitsLift` (`Submission/Work/NUV2/LC/RouteB/level_kills_aux.lean`)
and of `NK.NUV2.LC.RouteB.muLift` (`Submission/Work/NUV2/LC/RouteB/muLift.lean`).

Both `unitsLift` and `muLift` are transports along the *same* level-group dictionary
`levelGroupEquiv V L : LevelGroup V L ≃* Gal(↥L / ↥(levelBase V L))`, with the *identity* linear
equivalence on the coefficient modules (`Lˣ` respectively `μ_p(L)`).  The Kummer morphisms
`kummerLevel p V L : MuLevelH2 p V L ⟶ UnitsLevelH2 V L` and
`kummerMap p F L : H²(Gal(L/F), μ_p(L)) ⟶ H²(Gal(L/F), Lˣ)` are the maps induced on `H²` by the
coefficient inclusion `μ_p(L) ↪ Lˣ`.  This file proves that the obvious square commutes, i.e. that
the transports are natural with respect to the Kummer morphisms:

`unitsLift V L ((kummerLevel p V L) a) = (kummerMap p ↥(levelBase V L) ↥L) (muLift p V L a)`.

The formal proof is a bookkeeping computation with `groupCohomology.map`/`groupCohomology.mapIso`:
unfold the four maps (`unitsLift_apply`, `muLift_apply`, `mapIso_hom`), combine the two function
applications into a single composite (`hcomp`), merge the two `map`s of each side into a single one
(`groupCohomology.map_comp`), and observe that the two resulting representation morphisms
`(resFunctor e.symm).map (muToUnits p V L) ≫ 𝟙` and `(resFunctor (id _)).map 𝟙 ≫ kummerIncl p ↥F ↥L`
have the same underlying linear map (the inclusion `μ_p(L) ↪ Lˣ`), so that
`groupCohomology.map_congr` applies.
-/

namespace NK.NUV2.LC.RouteB

open CategoryTheory

-- The terms produced by `unitsLift_apply` / `muLift_apply` mention the `LinearEquiv.refl` of the
-- coefficient modules with instance arguments coming from the (definitionally equal) representation
-- structures; comparing them with the goal needs transparent `isDefEq`.
set_option backward.isDefEq.respectTransparency false

section Base

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The computation rule for `unitsLift`, exactly as for `muLift_apply`: the transport is the map on
`H²` induced by `groupCohomology.mapIso` along the level-group dictionary and the identity on the
coefficients. -/
theorem unitsLift_apply (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (a : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L) :
    unitsLift (K := K) (K' := K') V L a =
      (groupCohomology.mapIso
        (A := NK.HassePrinciple.unitsRep (↥(levelBase (K := K) V L)) (↥L))
        (B := NK.HassePrinciple.unitsLevelRep V L)
        (levelGroupEquiv (K := K) (K' := K') V L)
        (LinearEquiv.refl NK.HassePrinciple.CoeffInt (Additive (↥L)ˣ))
        (fun g => by
          induction g using QuotientGroup.induction_on with
          | H v => simp only [NK.HassePrinciple.levelGroupRestrictHom_mk]; rfl) 2).hom a := rfl

end Base

/-- **The Kummer morphism commutes with the transports**: the level comparison of a `μ_p` level class
followed by the units transport equals the Kummer map (for the base field `↥(levelBase V L)`) of the
`μ_p` transport of the class. -/
theorem unitsLift_kummerLevel {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (a : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L) :
    NK.NUV2.LC.RouteB.unitsLift (K := K) (K' := K') V L
        ((NK.HassePrinciple.kummerLevel p V L).hom a) =
      (NK.HassePrinciple.kummerMap p (↥(NK.NUV2.LC.RouteB.levelBase (K := K) V L)) (↥L)).hom
        (NK.NUV2.LC.RouteB.muLift (K := K) (K' := K') p V L a) := by
  -- Combining two successive applications of `H²`-maps into a single application of the composite.
  have hcomp : ∀ {X Y Z : ModuleCat NK.HassePrinciple.CoeffInt} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X),
      ConcreteCategory.hom g (ConcreteCategory.hom f x) = ConcreteCategory.hom (f ≫ g) x :=
    fun f g x => rfl
  -- Unfold the four maps.
  rw [unitsLift_apply, NK.NUV2.LC.RouteB.muLift_apply]
  rw [groupCohomology.mapIso_hom, groupCohomology.mapIso_hom]
  simp only [NK.HassePrinciple.kummerLevel, NK.HassePrinciple.kummerMap]
  -- Turn both sides into the application of a single composite of two `H²`-maps.
  rw [hcomp, hcomp]
  -- Merge the two `map`s on each side into a single `map` (`groupCohomology.map_comp`).
  conv_lhs => rw [← groupCohomology.map_comp]
  conv_rhs => rw [← groupCohomology.map_comp]
  -- The two remaining representation morphisms have the same underlying linear map (the inclusion
  -- `μ_p(L) ↪ Lˣ`), and the two group homomorphisms `(id).comp e.symm` and `e.symm.comp (id)`
  -- are both `e.symm`, so `groupCohomology.map_congr` finishes.
  refine congrArg (fun (z : (NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L) ⟶
      (groupCohomology (NK.HassePrinciple.unitsRep (↥(NK.NUV2.LC.RouteB.levelBase (K := K) V L))
        (↥L)) 2)) => ConcreteCategory.hom z a) ?_
  exact groupCohomology.map_congr (by rw [MonoidHom.id_comp, MonoidHom.comp_id]) (by rfl) 2

end NK.NUV2.LC.RouteB
