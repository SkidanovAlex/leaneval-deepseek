import Mathlib

namespace Work.WilE2

theorem range_eq_top_of_linearIndependent_comp
    {K : Type*} [Field K]
    {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (L : M →ₗ[K] N) {ι : Type*} [Fintype ι] (ψ : ι → Module.Dual K N)
    (h : LinearIndependent K (fun i => (ψ i).comp L))
    (hcard : Fintype.card ι = Module.finrank K N) :
    LinearMap.range L = ⊤ ∧
      Module.finrank K (LinearMap.ker L) = Module.finrank K M - Fintype.card ι := by
  classical
  -- The pullbacks `ψ i ∘ L` are the images of the `ψ i` under `L.dualMap`, and they are
  -- linearly independent.  This forces `range L.dualMap` to have the dimension of `Dual K N`,
  -- hence (by the duality `finrank (range L.dualMap) = finrank (range L)`) forces `L` to be
  -- surjective.
  have hh : LinearIndependent K (fun i => L.dualMap (ψ i)) := h
  have hle : Submodule.span K (Set.range (fun i => L.dualMap (ψ i))) ≤
      LinearMap.range L.dualMap :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i =>
      LinearMap.mem_range_self L.dualMap (ψ i))
  have hcard' : Module.finrank K (LinearMap.range L.dualMap) = Fintype.card ι := by
    refine le_antisymm ?_ ?_
    · have h3 := LinearMap.finrank_range_le L.dualMap
      rwa [Subspace.dual_finrank_eq, ← hcard] at h3
    · rw [← finrank_span_eq_card hh]
      exact Submodule.finrank_mono hle
  have htop : LinearMap.range L = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [← LinearMap.finrank_range_dualMap_eq_finrank_range L, hcard', hcard]
  refine ⟨htop, ?_⟩
  -- Rank-nullity, using that `range L` is everything and `finrank K N = card ι`.
  have hrn := LinearMap.finrank_range_add_finrank_ker L
  rw [htop, finrank_top] at hrn
  omega

end Work.WilE2
