import Mathlib
import Submission.Work.SSGRoute.PT.shapiro_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The fibre of `t ↦ t⁻¹ • C` in a coset space is open

For a topological group `G`, an *open* subgroup `U ≤ G` and two left cosets `C C' : G ⧸ U`,
the set of `t : G` with `t⁻¹ • C = C'` is open.

Concretely, writing `C = aU` and `C' = bU`, the condition `t⁻¹ • aU = bU` is equivalent to
`a⁻¹ * t * b ∈ U`, i.e. the fibre is the left translate by `a` of the conjugate open subgroup
`b U b⁻¹`.  Formally we use that the preimage of the open set `U` under the homeomorphism
`t ↦ a⁻¹ * t * b` is open.

This is the topological input used in the Poitou–Tate / Shafarevich route (the cosets of an
open subgroup form a discrete `G`-set).
-/

namespace Work.SSGRoute.PT

theorem isOpen_setOf_inv_smul_eq {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G)) (C C' : G ⧸ U) :
    IsOpen {t : G | t⁻¹ • C = C'} := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective C
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective C'
  have hset : {t : G | t⁻¹ • QuotientGroup.mk a = (QuotientGroup.mk b : G ⧸ U)}
      = {t : G | a⁻¹ * t * b ∈ U} := by
    ext t
    simp only [Set.mem_ofPred_eq, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
    rw [show (t⁻¹ * a)⁻¹ * b = a⁻¹ * t * b by group]
  rw [hset]
  exact hU.preimage (by continuity)

end Work.SSGRoute.PT
