import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.SSGRoute.kummerBase_euler_connectingH3_descent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `c - d²(liftCochain2 k)` is a `3`-cocycle with values in `ker π`

Let `0 → M →^{ι} N →^{π} P → 0` be a short exact sequence of discrete `G`-modules.  Suppose
`c : G × G × G → N` is a continuous `3`-cocycle and `k : G × G → P` a continuous `2`-cochain whose
`d²` is `π ∘ c`:

  `d²k = π ∘ c`.

Then the difference `c - d²(liftCochain2 k)` (where `liftCochain2 k` is any set-theoretic lift of
`k` along `π`) is again a continuous `3`-cocycle, now with values in `ker π = range ι`.  Concretely
`π` kills it because `π ∘ d²(liftCochain2 k) = d²(π ∘ liftCochain2 k) = d²k = π ∘ c`, and it is a
cocycle because both `c` and `d²` of a `2`-cochain are (`d³ ∘ d² = 0`, i.e. `d3_d2`).

This is the cocycle-level form of the statement that the `3`-coboundary `d²(liftCochain2 k)`
differs from `c` by a cocycle lying in the image of the coefficient map `ι`; it feeds the
comparison of the connecting map with the lift chosen for `H³`.
-/

namespace Work.SSGRoute

theorem sub_d2_liftCochain2_mem_Z3_and_ker {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) {c : G × G × G → N}
    (hc : c ∈ Work.SSGRoute.Z3 (M := N) G) {k : G × G → P}
    (hklc : Work.AbsoluteKummer.IsLocallyConstant k)
    (hk : (Work.GroupCohomology.d2 G P) k = fun p : G × G × G => S.pi (c p)) :
    (fun p : G × G × G => c p - (Work.GroupCohomology.d2 G N) (S.liftCochain2 k) p)
        ∈ Work.SSGRoute.Z3 (M := N) G ∧
      (∀ p : G × G × G,
        c p - (Work.GroupCohomology.d2 G N) (S.liftCochain2 k) p ∈ S.pi.ker) := by
  obtain ⟨hcd3, hclc⟩ := (Work.SSGRoute.mem_Z3_iff (G := G) (M := N)).mp hc
  have hlift : Work.AbsoluteKummer.IsLocallyConstant (S.liftCochain2 k) :=
    S.isLocallyConstant_liftCochain2 hklc
  have hd2 : Work.AbsoluteKummer.IsLocallyConstant
      (Work.GroupCohomology.d2 G N (S.liftCochain2 k)) :=
    Work.SSGRoute.isLocallyConstant_d2 S.isDiscreteN hlift
  -- `π` commutes with `d²`, and `π ∘ liftCochain2 k = k`
  have hpi : ∀ p : G × G × G,
      S.pi (Work.GroupCohomology.d2 G N (S.liftCochain2 k) p)
        = Work.GroupCohomology.d2 G P k p := by
    intro p
    have h1 : Work.GroupCohomology.d2 G P (fun q => S.pi (S.liftCochain2 k q))
        = fun q => S.pi (Work.GroupCohomology.d2 G N (S.liftCochain2 k) q) :=
      Work.SSGRoute.d2_comp S.pi S.pi_equivariant (S.liftCochain2 k)
    have h2 : (fun q : G × G => S.pi (S.liftCochain2 k q)) = k :=
      funext fun q => S.pi_liftCochain2 k q
    rw [← congrFun h1 p, h2]
  refine ⟨?_, ?_⟩
  · rw [Work.SSGRoute.mem_Z3_iff]
    refine ⟨?_, hclc.sub hd2⟩
    -- `d³` is additive and kills both `c` and `d²` of a `2`-cochain
    change Work.SSGRoute.d3 (c - Work.GroupCohomology.d2 G N (S.liftCochain2 k)) = 0
    rw [map_sub, hcd3, Work.SSGRoute.d3_d2 (G := G) (A := N) (S.liftCochain2 k), sub_zero]
  · intro p
    rw [AddMonoidHom.mem_ker, map_sub, hpi p, congrFun hk p, sub_self]

end Work.SSGRoute
