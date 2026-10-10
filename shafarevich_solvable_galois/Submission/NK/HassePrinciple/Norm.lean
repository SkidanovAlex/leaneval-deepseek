import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.GlobalCFT.ClassFormation.globalCFT_fieldAxiom_self
import Submission.NK.GlobalCFT.H0Computation
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_compactSpace_normOneClassGroup
import Submission.NK.GlobalCFT.IdeleClassGroupExact
import Submission.NK.GlobalCFT.Ideles.globalCFT_principalIdele_injective
import Submission.NK.GlobalCFT.Ideles.globalCFT_principalSubgroup_isClosed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false

universe u

namespace NK.HassePrinciple

open NK.GlobalCFT

/-- **The Hasse norm theorem for cyclic extensions of number fields**, in its two classical forms:

* `index_eq` — the reciprocity isomorphism for a cyclic extension `L/K` in index form,
  `[C_K : N_{L/K} C_L] = [L : K]`;
* `hasse_norm` — the Hasse norm theorem: an element of `Kˣ` whose principal idèle is a norm from
  the idèles of `L` (equivalently: which is a local norm at every place) is the norm of an element
  of `Lˣ`, i.e. `Kˣ ∩ N_{L/K} 𝕀_L = N_{L/K} Lˣ`. -/
structure HasseNormTheorem : Prop where
  /-- **The reciprocity isomorphism for cyclic extensions, in index form.** -/
  index_eq : ∀ {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
      IsCyclic (L ≃ₐ[K] L) →
        (Idele.normClassSubgroup K L).index = Module.finrank K L
  /-- **The Hasse norm theorem.** -/
  hasse_norm : ∀ {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
      IsCyclic (L ≃ₐ[K] L) → ∀ a : Kˣ,
        Idele.principalIdele K a ∈ Idele.normImage K L →
          ∃ b : Lˣ, Idele.principalIdele K a =
            Idele.normIdeleFun K L (Idele.principalIdele L b)


/-- **The Hasse norm theorem implies the field axiom for cyclic extensions.**  The norm index
formula of `HasseNormTheorem` together with the positivity of `[L : K]` gives the field axiom
`NK.GlobalCFT.FieldAxiom K L` of the on-disk class formation for every cyclic extension `L/K`:
the norm subgroup has finite index and its index is `[L : K]`. -/
theorem fieldAxiom_of_hasseNormTheorem (h : HasseNormTheorem.{u}) {K L : Type u} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (hcyc : IsCyclic (L ≃ₐ[K] L)) :
    FieldAxiom K L where
  finiteIndex := by
    rw [Subgroup.finiteIndex_iff, h.index_eq hcyc]
    exact (Module.finrank_pos).ne'
  index_eq := h.index_eq hcyc

end NK.HassePrinciple
