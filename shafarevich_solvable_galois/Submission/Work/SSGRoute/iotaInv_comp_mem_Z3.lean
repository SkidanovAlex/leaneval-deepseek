import Mathlib
import Submission.Work.SSGRoute.kummerBase_euler_connectingH3_descent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **Transporting a `3`-cocycle supported in `ker π` back through `ι⁻¹`** (the degree-`3`
analogue of `Work.SSGRoute.iotaInv_comp_mem_Z2`): if `c` is a continuous `3`-cocycle of `N`
taking all its values in `ker π = range ι`, then `p ↦ ι⁻¹ (c p)` is a continuous `3`-cocycle
of `M`.

Both structural identities transfer along the inclusion `ι`: the cocycle identity because `ι`
is additive and equivariant (so it intertwines `d³` with the `G`-action, and `ι ∘ ι⁻¹ = id`
on `range ι`), and local constancy because it is preserved by post-composition with an
arbitrary function. -/
theorem iotaInv_comp_mem_Z3 {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) {c : G × G × G → N}
    (hc : c ∈ Work.SSGRoute.Z3 (M := N) G) (hker : ∀ p : G × G × G, c p ∈ S.pi.ker) :
    (fun p : G × G × G => S.iotaInv (c p)) ∈ Work.SSGRoute.Z3 (M := M) G := by
  rw [Work.SSGRoute.mem_Z3_iff]
  refine ⟨?_, ?_⟩
  · ext p
    obtain ⟨g, h, k, l⟩ := p
    apply S.iota_injective
    simp only [Pi.zero_apply, map_zero]
    rw [Work.SSGRoute.d3_apply]
    rw [map_add, map_sub, map_add, map_sub, S.iota_equivariant,
      S.iota_iotaInv (S.mem_range_of_mem_ker (hker (h, k, l))),
      S.iota_iotaInv (S.mem_range_of_mem_ker (hker (g * h, k, l))),
      S.iota_iotaInv (S.mem_range_of_mem_ker (hker (g, h * k, l))),
      S.iota_iotaInv (S.mem_range_of_mem_ker (hker (g, h, k * l))),
      S.iota_iotaInv (S.mem_range_of_mem_ker (hker (g, h, k)))]
    simpa only [Work.SSGRoute.d3_apply, Pi.zero_apply] using
      congr_fun ((Work.SSGRoute.mem_Z3_iff (M := N) (G := G)).mp hc).1 (g, h, k, l)
  · exact Work.AbsoluteKummer.IsLocallyConstant.map S.iotaInv
      ((Work.SSGRoute.mem_Z3_iff (M := N) (G := G)).mp hc).2

end Work.SSGRoute
