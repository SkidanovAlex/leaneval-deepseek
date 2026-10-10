import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Galois.GaloisClosure
import Submission.Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top
import Submission.NK.BrauerHasse.Profinite
import Submission.NeukirchUchida.Local.PlaceFromValuation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.HassePrinciple

universe u

set_option maxHeartbeats 1600000

/-- **The finite levels of the profinite cohomology are finite groups.**

For a subgroup `U ≤ Gal(K'/K)` and a finite Galois intermediate field `L`, the level group
`NK.BrauerHasse.LevelGroup U L = U/(U ⊓ Gal(K'/L))` is finite: the restriction map
`AlgEquiv.restrictNormalHom L : Gal(K'/K) →* Gal(L/K)` has kernel `L.fixingSubgroup`, so it induces
an *injection* `U/(U ⊓ Gal(K'/L)) →* Gal(L/K)` into the (finite) Galois group of the finite
extension `L/K`, and finiteness follows by `Finite.of_injective` (or by `Finite.of_injective'` /
`QuotientGroup.lift`).

This is the finiteness instance needed to apply the prime-to-`p` index restriction lemma
`NK.HassePrinciple.H2_map_injective_of_coprime_index` to the level groups (see
`Submission/Work/HassePrinciple/Inert.lean`).  Please also *register the result as an instance*
(`instance finite_levelGroup ...`) so that typeclass search can discharge the
`[Finite (NK.BrauerHasse.LevelGroup U L)]` binder appearing there. -/
theorem finite_levelGroup {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    Finite (NK.BrauerHasse.LevelGroup U L) := by
  -- The restriction map to the finite Galois group of the finite level `L`.
  let g : ↥U →* Gal(L/K) := (AlgEquiv.restrictNormalHom L).comp U.subtype
  -- Its kernel is exactly the normal subgroup that is quotiented out in `LevelGroup U L`.
  have hker : L.fixingSubgroup.subgroupOf U = MonoidHom.ker g := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact FiniteGaloisIntermediateField.mem_fixingSubgroup_iff _ _
  -- `Gal(L/K)` is finite because `L/K` is finite and Galois (found by typeclass search).
  change Finite (↥U ⧸ L.fixingSubgroup.subgroupOf U)
  rw [hker]
  -- The canonical map `U ⧸ ker g →* Gal(L/K)` is injective.
  exact Finite.of_injective (QuotientGroup.kerLift g) (QuotientGroup.kerLift_injective g)

/-- The finiteness statement registered for typeclass search, so that the
`[Finite (NK.BrauerHasse.LevelGroup U L)]` binder can be discharged automatically. -/
instance finite_levelGroup' {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    Finite (NK.BrauerHasse.LevelGroup U L) :=
  finite_levelGroup U L

end NK.HassePrinciple
