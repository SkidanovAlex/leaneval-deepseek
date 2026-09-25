import Mathlib
import Submission.NK.GlobalCFT.Idele
import Submission.NK.GlobalCFT.Ideles.globalCFT_principalIdele_isDiscrete

/-!
# The principal idèles form a closed subgroup of the idèle group

For a number field `K` the diagonal image `Kˣ → 𝕀 K` of the principal idèles is a *closed*
subgroup of the idèle group `𝕀 K`.

The input from the local/arithmetic side is the theorem
`NK.GlobalCFT.Ideles.globalCFT_principalIdele_isDiscrete`: the range of the diagonal embedding
is a discrete subset of `𝕀 K`.  Evaluated at the trivial principal idèle this produces an open
neighbourhood `V` of `1 = (1)ᵥ` in `𝕀 K` with `V ∩ Kˣ = {1}`; a *finite* intersection suffices
for the argument below.

The topological step is the general group-theoretic lemma
`isClosed_subgroup_of_exists_open_finite_inter`: if a subgroup `H` of a topological group has an
open neighbourhood of `1` meeting `H` in finitely many points, then `H` is closed.  (This is the
standard argument showing that *discrete* subgroups of locally compact groups are closed, but in
the form needed here it requires neither local compactness nor actual discreteness.)  Applying it
to `H = Kˣ ⊆ 𝕀 K` gives the result.

## Main results

* `NK.GlobalCFT.Ideles.isClosed_subgroup_of_exists_open_finite_inter`
* `NK.GlobalCFT.Ideles.globalCFT_principalSubgroup_isClosed`
-/

set_option autoImplicit false

open scoped NumberField RestrictedProduct Pointwise Topology

open Filter NK.GlobalCFT

noncomputable section

namespace NK.GlobalCFT.Ideles

/-- **A subgroup of a topological group which has an open neighbourhood of `1` meeting it in
finitely many points is closed.**

Indeed, let `V` be such a neighbourhood, replaced by the symmetric neighbourhood `V ∩ V⁻¹`
without loss of generality.  If `x` lies in the closure of `H`, the neighbourhood `x * V` of `x`
meets `H`, say in `y = x * v` with `v ∈ V`; then `y⁻¹ * x = v⁻¹` lies in `V ∩ closure H`, and
since `V` is open this is contained in `closure (V ∩ H) = V ∩ H ⊆ H` (here `V ∩ H` is finite,
hence closed).  Finally `x = y * (y⁻¹ * x) ∈ H`. -/
theorem isClosed_subgroup_of_exists_open_finite_inter {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] {H : Subgroup G}
    (h : ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ (V ∩ (H : Set G)).Finite) :
    IsClosed (H : Set G) := by
  obtain ⟨V, hVopen, hV1, hVfin⟩ := h
  -- it is harmless to replace `V` by the symmetric neighbourhood `V ∩ V⁻¹`
  set W : Set G := V ∩ V⁻¹ with hWdef
  have hWopen : IsOpen W := hVopen.inter hVopen.inv
  have hW1 : (1 : G) ∈ W := ⟨hV1, by simpa using hV1⟩
  have hWinv : W⁻¹ = W := by
    rw [hWdef, Set.inter_inv]
    simp [Set.inter_comm]
  have hWfin : (W ∩ (H : Set G)).Finite :=
    hVfin.subset (Set.inter_subset_inter_left _ Set.inter_subset_left)
  have hWclosed : IsClosed (W ∩ (H : Set G)) := hWfin.isClosed
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm (fun x hx => ?_) subset_closure
  -- `x * W` is an open neighbourhood of `x`, so it meets `H`
  have hxW : ({x} : Set G) * W ∈ 𝓝 x := by
    refine (IsOpen.mul_left hWopen).mem_nhds ?_
    simpa using Set.mul_mem_mul (Set.mem_singleton x) hW1
  obtain ⟨y, hy⟩ := Set.nonempty_def.mp ((mem_closure_iff_nhds.mp hx) ({x} * W) hxW)
  obtain ⟨hyxW, hyH⟩ := hy
  obtain ⟨a, ha, b, hbW, hab⟩ := Set.mem_mul.mp hyxW
  rw [Set.mem_singleton_iff] at ha
  -- so `y = x * b` with `b ∈ W`, and `y⁻¹ * x = b⁻¹ ∈ W`
  have hxb : x * b = y := by
    rw [← ha]
    exact hab
  have hbWinv : b⁻¹ ∈ W := by
    rw [← hWinv]
    exact Set.inv_mem_inv.mpr hbW
  have hxy : y⁻¹ * x = b⁻¹ := by
    rw [← hxb]
    group
  have hT : y⁻¹ * x ∈ W ∩ closure (H : Set G) := by
    refine ⟨?_, ?_⟩
    · rw [hxy]
      exact hbWinv
    · have hyT : y ∈ H.topologicalClosure := Subgroup.le_topologicalClosure H hyH
      have hyiT : y⁻¹ ∈ H.topologicalClosure := H.topologicalClosure.inv_mem hyT
      have hxT : x ∈ H.topologicalClosure := hx
      exact H.topologicalClosure.mul_mem hyiT hxT
  -- `W` being open, `W ∩ closure H ⊆ closure (W ∩ H) = W ∩ H ⊆ H`
  have hmem : y⁻¹ * x ∈ W ∩ (H : Set G) := by
    have hcl : y⁻¹ * x ∈ closure (W ∩ (H : Set G)) := hWopen.inter_closure hT
    rwa [hWclosed.closure_eq] at hcl
  rw [show x = y * (y⁻¹ * x) from by group]
  exact H.mul_mem hyH hmem.2

/-- **The principal idèles form a closed subgroup of the idèle group** (Neukirch, *Algebraic
Number Theory*, Chapter II): the diagonal image of `Kˣ` in `𝕀 K` is closed.

The proof uses the discreteness of the diagonal image, which provides an open neighbourhood `V`
of `1` in `𝕀 K` with `V ∩ Kˣ = {1}`. -/
theorem globalCFT_principalSubgroup_isClosed {K : Type*} [Field K] [NumberField K] :
    IsClosed ((NK.GlobalCFT.Idele.principalSubgroup K : Subgroup (NK.GlobalCFT.Idele K)) :
      Set (NK.GlobalCFT.Idele K)) := by
  have hd : IsDiscrete (Set.range (NK.GlobalCFT.Idele.principalIdele K)) :=
    NK.GlobalCFT.Ideles.globalCFT_principalIdele_isDiscrete (K := K)
  rw [isDiscrete_iff_forall_mem_exists_isOpen] at hd
  obtain ⟨V, hVopen, hVeq⟩ := hd 1 ⟨1, map_one (NK.GlobalCFT.Idele.principalIdele K)⟩
  have hV1 : (1 : NK.GlobalCFT.Idele K) ∈ V := by
    have hmem : (1 : NK.GlobalCFT.Idele K) ∈
        V ∩ Set.range (NK.GlobalCFT.Idele.principalIdele K) := by
      rw [hVeq]
      exact Set.mem_singleton 1
    exact hmem.1
  refine isClosed_subgroup_of_exists_open_finite_inter ⟨V, hVopen, hV1, ?_⟩
  have hcoe : ((NK.GlobalCFT.Idele.principalSubgroup K : Subgroup (NK.GlobalCFT.Idele K)) :
      Set (NK.GlobalCFT.Idele K)) = Set.range (NK.GlobalCFT.Idele.principalIdele K) :=
    MonoidHom.coe_range (NK.GlobalCFT.Idele.principalIdele K)
  exact (Set.finite_singleton (1 : NK.GlobalCFT.Idele K)).subset (le_of_eq (by rw [hcoe, hVeq]))

end NK.GlobalCFT.Ideles
