import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.AbsoluteKummer.SES.Connecting
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.SES

/-- Exactness at `H⁰(G, P)`: the kernel of the connecting map `δ : H⁰(G,P) → H¹(G,M)` is contained
in the image of the map `H⁰(G,N) → H⁰(G,P)` induced by `π`.

Given `p ∈ H⁰(G,P)` with `δ p = 0`, the cocycle `g ↦ ι⁻¹(g • n - n)` attached to a lift `n` of `p`
is a coboundary: `g • m - m = ι⁻¹(g • n - n)` for some `m ∈ M`.  Then `n - ι m` is a `G`-invariant
lift of `p`, i.e. `p` is the image of an element of `H⁰(G,N)`. -/
theorem ker_le_range_mapH0 {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P] (S : Work.AbsoluteKummer.ShortExactSeq G M N P) : S.delta.ker ≤ (Work.GroupCohomology.mapH0 G S.pi S.pi_equivariant).range := by
  intro p hp
  rw [AddMonoidHom.mem_ker, S.delta_apply, Work.AbsoluteKummer.H1π_eq_zero_iff] at hp
  obtain ⟨m, hm⟩ := (Work.AbsoluteKummer.mem_B1_iff _).mp hp
  let n : N := S.liftOf p
  have hn : (S.pi n) ∈ Work.AbsoluteKummer.H0 G P := S.liftOf_invariant p
  have key : ∀ g : G, g • n - n = S.iota (g • m - m) := by
    intro g
    have h2 : g • m - m = S.iotaInv (g • n - n) := by
      have h3 := congrFun hm g
      rw [Work.GroupCohomology.d0_apply, S.cocycleOf_apply] at h3
      exact h3
    rw [h2]
    exact (S.iota_iotaInv (S.mem_range_of_mem_ker (S.mem_ker_smul_sub n hn g))).symm
  have hinv : ∀ g : G, g • (n - S.iota m) = n - S.iota m := by
    intro g
    have h := key g
    rw [map_sub] at h
    rw [smul_sub, ← S.iota_equivariant g m]
    have h2 : S.iota (g • m) = g • n - n + S.iota m := by rw [h]; abel
    rw [h2]
    abel
  refine AddMonoidHom.mem_range.mpr ⟨⟨n - S.iota m, hinv⟩, ?_⟩
  apply Subtype.ext
  show S.pi (n - S.iota m) = (p : P)
  rw [map_sub, S.pi_iota, sub_zero]
  exact S.pi_liftOf p

end Work.AbsoluteKummer.SES
