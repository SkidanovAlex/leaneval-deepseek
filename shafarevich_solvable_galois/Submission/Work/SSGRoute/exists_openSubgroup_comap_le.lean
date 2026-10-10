import Mathlib.FieldTheory.KrullTopology
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Open subgroups of a subgroup of `Gal(L/K)` extend to open subgroups of `Gal(L/K)`

Let `G = Gal(L/K)` with the Krull topology.  If `H ≤ G` is an arbitrary subgroup (with the
subspace topology) and `N ≤ H` is open, then there is an open subgroup `U ≤ G` such that
`U ∩ H ≤ N`.

The proof is a direct application of the description of the neighbourhood filter of the identity
in the Krull topology: neighbourhoods of `1` are exactly the sets containing `Gal(L/E)` for some
finite (intermediate) extension `E/K`, and each `Gal(L/E)` is an *open subgroup* of `G`.
-/

open scoped Topology

namespace Work.SSGRoute

theorem exists_openSubgroup_comap_le {K L : Type*} [Field K] [Field L] [Algebra K L]
    (H : Subgroup Gal(L/K)) (N : Subgroup ↥H) (hN : IsOpen (N : Set ↥H)) :
    ∃ U : Subgroup Gal(L/K), IsOpen (U : Set Gal(L/K)) ∧
      U.comap (Subgroup.subtype H) ≤ N := by
  -- Unfold openness of `N` in the subspace topology on `H`: `N = H ∩ V` for some `V` open in `G`.
  obtain ⟨V, hVopen, hV⟩ := isOpen_induced_iff.mp hN
  -- `1 ∈ N`, hence `1 ∈ V`.
  have h1V : (1 : Gal(L/K)) ∈ V := by
    have : (1 : ↥H) ∈ (N : Set ↥H) := N.one_mem
    rw [← hV] at this
    exact this
  -- So `V` is a neighbourhood of `1`, and the Krull topology gives a finite subextension `E/K`
  -- whose fixing subgroup `Gal(L/E)` is contained in `V`.
  have hVnhds : V ∈ 𝓝 (1 : Gal(L/K)) := hVopen.mem_nhds h1V
  obtain ⟨E, hEfin, hEsub⟩ := (krullTopology_mem_nhds_one_iff K L V).mp hVnhds
  have hEfin_inst : FiniteDimensional K E := hEfin
  -- `Gal(L/E)` is an open subgroup of `G`, and it is the `U` we are after.
  refine ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen, ?_⟩
  intro x hx
  rw [Subgroup.mem_comap] at hx
  have hxV : (x : Gal(L/K)) ∈ V := hEsub hx
  have : x ∈ Subtype.val ⁻¹' V := hxV
  rwa [hV] at this

end Work.SSGRoute
