import Mathlib
import Submission.NK.NUV2.LC.RouteB.level_kills_aux
import Submission.NK.HassePrinciple.KummerLevel
import Submission.NK.HassePrinciple.LocalUnits

/-!
# The `μ_p` transport to the number-field cohomology of a level

Companion of `NK.NUV2.LC.RouteB.unitsLift` (`Submission/Work/NUV2/LC/RouteB/level_kills_aux.lean`)
for the cyclotomic coefficients: for a level `L` of `K'/K` and a subgroup `V`, the level group
`LevelGroup V L` is the Galois group of the number-field extension `↥L/↥(levelBase V L)`
(`levelGroupEquiv`), so the `μ_p` level cohomology transports to the field cohomology
`H²(Gal(↥L/↥(levelBase V L)), μ_p(↥L))` in which the Kummer and localisation layers of the
`HassePrinciple` chapter (`kummerMap`, `locUnits`) are stated.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

universe u

namespace NK.NUV2.LC.RouteB

open CategoryTheory

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The `μ_p` transport**: between the `μ_p` level cohomology of `LevelGroup V L` and the
number-field cohomology `H²(Gal(↥L/↥(levelBase V L)), μ_p(↥L))`.  Built with
`groupCohomology.mapIso` along `levelGroupEquiv` and the identity on the coefficients, exactly as
`unitsLift`. -/
noncomputable def muLift (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L ≃+
      (groupCohomology (NK.HassePrinciple.muRep p (↥(levelBase (K := K) V L)) (↥L)) 2) := by
  refine ((groupCohomology.mapIso
    (A := NK.HassePrinciple.muRep p (↥(levelBase (K := K) V L)) (↥L))
    (B := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p V L)
    (levelGroupEquiv (K := K) (K' := K') V L)
    (LinearEquiv.refl NK.HassePrinciple.CoeffInt
      (Additive ↥(rootsOfUnity p ↥L))) ?_ 2).toLinearEquiv).toAddEquiv
  intro g
  induction g using QuotientGroup.induction_on with
  | H v => simp only [NK.HassePrinciple.levelGroupRestrictHom_mk]; rfl

/-- The computation rule for `muLift`. -/
theorem muLift_apply (p : ℕ) (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (a : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L) :
    muLift (K := K) (K' := K') p V L a =
      (groupCohomology.mapIso
        (A := NK.HassePrinciple.muRep p (↥(levelBase (K := K) V L)) (↥L))
        (B := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p V L)
        (levelGroupEquiv (K := K) (K' := K') V L)
        (LinearEquiv.refl NK.HassePrinciple.CoeffInt
          (Additive ↥(rootsOfUnity p ↥L)))
        (fun g => by
          induction g using QuotientGroup.induction_on with
          | H v => simp only [NK.HassePrinciple.levelGroupRestrictHom_mk]; rfl) 2).hom a := rfl

end NK.NUV2.LC.RouteB
