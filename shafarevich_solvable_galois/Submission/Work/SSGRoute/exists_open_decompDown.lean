import Mathlib
import Submission.Work.SSGRoute.grunwald_distinct_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Open subgroups of `D_A ≤ G_ℚ` are open subgroups of `D_A ≤ Gal(ℚ̄/↥K)` for a split place `A`

For a finite place `A` of `ℚ̄` which is *split* in `K` (`SSGRoute.IsSplitIn ℚ K A`, i.e.
`D_A ≤ G_K`), the decomposition group of `A` inside `G_ℚ` and inside `Gal(ℚ̄/↥K)` have the same
elements (as functions), so an open subgroup of one is an open subgroup of the other.  This module
proves the direction needed in the base change `ℚ → ↥K` of the Grünwald theorem:
`Work.SSGRoute.decompDownHom` carries an open subgroup of `D_A ≤ G_ℚ` to an open subgroup of
`D_A ≤ Gal(ℚ̄/↥K)` (with the convention that the subgroup upstairs is the largest one whose image is
contained in the given one).

The proof unpacks the subspace topology: an open subgroup `U ≤ ↥(D_A)` is, near `1`, the trace of
an open subset `V` of `G_ℚ`, and `V` contains `E.fixingSubgroup` for some finite `E/ℚ`
(`krullTopology_mem_nhds_one_iff`).  The elements of `D_A ≤ Gal(ℚ̄/↥K)` whose underlying function
fixes `E` then form an open subgroup, and their images under `decompDownHom` lie in `V`, hence
in `U`.
-/

open scoped Pointwise Topology

namespace Work.SSGRoute

open SSGRoute

/-- Openness of a subgroup of `D_A ≤ G_ℚ` transports to the decomposition group of `A` over `↥K`,
for a place `A` split in `K`. -/
theorem exists_open_decompDown (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (A : ValuationSubring SSGRoute.QBar)
    (hsplit : SSGRoute.decomp ℚ A ≤ K.fixingSubgroup)
    (U : Subgroup ↥(SSGRoute.decomp ℚ A)) (hU : IsOpen (U : Set ↥(SSGRoute.decomp ℚ A))) :
    ∃ U' : Subgroup ↥(SSGRoute.decomp ↥K A),
      IsOpen (U' : Set ↥(SSGRoute.decomp ↥K A)) ∧
      ∀ x ∈ U', decompDownHom K A hsplit x ∈ U := by
  classical
  -- unpack the subspace topology of `D_A ≤ G_ℚ`
  have hmem : (U : Set ↥(SSGRoute.decomp ℚ A)) ∈ 𝓝 (1 : ↥(SSGRoute.decomp ℚ A)) :=
    hU.mem_nhds U.one_mem
  rw [nhds_subtype] at hmem
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hmem
  -- a finite subextension of `ℚ` whose fixing subgroup lies in `V`
  obtain ⟨E, hEfin, hEV⟩ := (krullTopology_mem_nhds_one_iff ℚ SSGRoute.QBar V).mp hV
  -- the corresponding open subgroup upstairs: elements fixing `E` and `K`
  haveI : FiniteDimensional ↥K (overK K (E ⊔ K) le_sup_right) :=
    finiteDimensional_overK_of_finite K (E ⊔ K) le_sup_right
  have hWopen : IsOpen ((Subgroup.comap ((SSGRoute.decomp ↥K A).subtype)
      (overK K (E ⊔ K) le_sup_right).fixingSubgroup) : Set ↥(SSGRoute.decomp ↥K A)) := by
    rw [Subgroup.coe_comap]
    exact IsOpen.preimage continuous_subtype_val
      (IntermediateField.fixingSubgroup_isOpen (overK K (E ⊔ K) le_sup_right))
  have hWle : Subgroup.comap ((SSGRoute.decomp ↥K A).subtype)
      (overK K (E ⊔ K) le_sup_right).fixingSubgroup
      ≤ U.comap (decompDownHom K A hsplit) := by
    intro x hx
    rw [Subgroup.mem_comap] at hx ⊢
    refine hVU ?_
    have hfix : ((decompDownHom K A hsplit x : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ)
        ∈ E.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      show ⇑(((decompDownHom K A hsplit x : ↥(SSGRoute.decomp ℚ A))) : SSGRoute.GalQ) y = y
      rw [coe_decompDownHom]
      rw [IntermediateField.mem_fixingSubgroup_iff] at hx
      exact hx y ((le_sup_left : E ≤ (E ⊔ K : IntermediateField ℚ SSGRoute.QBar)) hy)
    exact hEV hfix
  exact ⟨U.comap (decompDownHom K A hsplit), Subgroup.isOpen_mono hWle hWopen,
    fun x hx => (Subgroup.mem_comap.mp hx)⟩

end Work.SSGRoute
