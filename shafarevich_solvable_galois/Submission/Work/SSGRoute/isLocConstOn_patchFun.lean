import Mathlib
import Submission.Work.SSGRoute.grunwald_distinct_defs
import Submission.Work.SSGRoute.exists_open_subgroup_stabilizer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local constancy transfers from `Gal(ℚ̄/↥K)` to `G_ℚ` along `patchFun`

`Work.SSGRoute.patchFun K z` extends a function `z` on `Gal(ℚ̄/↥K)` to `G_ℚ` by `0` outside
`K.fixingSubgroup`.  This module shows that if `z` is locally constant on the whole of
`Gal(ℚ̄/↥K)` (the Krull topology), then its extension is locally constant on `K.fixingSubgroup`.

An open subgroup `U ≤ Gal(ℚ̄/↥K)` contains `E.fixingSubgroup` for some finite `E/↥K`, and
`Work.SSGRoute.exists_open_subgroup_stabilizer` then provides an open subgroup of `G_ℚ` whose
elements in `K.fixingSubgroup` have their image in `Gal(ℚ̄/↥K)` inside `E.fixingSubgroup`, hence
inside `U`.
-/

open scoped Pointwise

namespace Work.SSGRoute

open SSGRoute

/-- Local constancy on `⊤ ≤ Gal(ℚ̄/↥K)` transports to `K.fixingSubgroup ≤ G_ℚ` along `patchFun`. -/
theorem isLocConstOn_patchFun (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    {M : Type} [Zero M] (z : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → M)
    (hz : SSGRoute.IsLocConstOn (⊤ : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) z) :
    SSGRoute.IsLocConstOn K.fixingSubgroup (patchFun K z) := by
  classical
  obtain ⟨U, hUo, hU⟩ := hz
  obtain ⟨E, hEfin, hEU⟩ :=
    (krullTopology_mem_nhds_one_iff ↥K SSGRoute.QBar (U : Set _)).mp
      (hUo.mem_nhds U.one_mem)
  haveI : FiniteDimensional ↥K E := hEfin
  obtain ⟨U', hU'o, hU'⟩ := exists_open_subgroup_stabilizer K E
  refine ⟨U', hU'o, ?_⟩
  intro g hg u hu huH
  obtain ⟨huK, huE⟩ := hU' u hu
  have hgu : g * u ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hg huK
  rw [patchFun_of_mem K z (g * u) hgu, patchFun_of_mem K z g hg]
  rw [show ((IntermediateField.fixingSubgroupEquiv K) ⟨g * u, hgu⟩) =
      ((IntermediateField.fixingSubgroupEquiv K) ⟨g, hg⟩) *
        ((IntermediateField.fixingSubgroupEquiv K) ⟨u, huK⟩) from by rw [← map_mul]; rfl]
  exact hU _ trivial _ (hEU huE) trivial

end Work.SSGRoute
