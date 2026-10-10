import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.AbsoluteKummer.SES.Connecting
import Submission.Work.AbsoluteKummer.SES.range_mapH1_eq_ker_mapH1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.SES

open Work.AbsoluteKummer

/-- **Exactness at `H¹(G,M)`**: the kernel of the map `H¹(G,M) → H¹(G,N)` induced by `ι` is
contained in the image of the connecting map `δ : H⁰(G,P) → H¹(G,M)`.

Given a continuous cocycle `f : G → M` whose image `ι ∘ f` is a coboundary, say
`ι (f g) = g • n - n` for some `n : N`, the element `π n` is fixed by `G` and the lift `n` of
`π n` differs from the chosen lift `S.liftOf (π n)` by `ι a`, `a ∈ M`.  Hence
`ι⁻¹ (g • liftOf (π n) - liftOf (π n)) = f g + (g • a - a)`, so `δ (π n) = [f]`. -/
theorem ker_mapH1_le_range_delta {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P] (S : Work.AbsoluteKummer.ShortExactSeq G M N P) : (Work.AbsoluteKummer.mapH1 S.iota S.iota_equivariant).ker ≤ S.delta.range := by
  intro x hx
  rw [AddMonoidHom.mem_ker] at hx
  revert hx
  induction x using H1_induction_on with
  | h f =>
    intro hx
    rw [Work.AbsoluteKummer.mapH1_H1π, Work.AbsoluteKummer.H1π_eq_zero_iff,
      Work.AbsoluteKummer.mem_B1_iff] at hx
    obtain ⟨n, hn⟩ := hx
    have hnval : ∀ g : G, g • n - n = S.iota ((f : G → M) g) := by
      intro g
      have h := congrFun hn g
      rw [Work.GroupCohomology.d0_apply, Work.AbsoluteKummer.mapZ1_apply] at h
      exact h
    have hpinv : S.pi n ∈ Work.AbsoluteKummer.H0 G P := by
      intro g
      have h := congrArg S.pi (hnval g)
      rw [map_sub, S.pi_equivariant g n, S.pi_iota, sub_eq_zero] at h
      exact h
    let p : Work.AbsoluteKummer.H0 G P := ⟨S.pi n, hpinv⟩
    have hpval : (p : P) = S.pi n := rfl
    have hmem : S.liftOf p - n ∈ S.pi.ker := by
      rw [AddMonoidHom.mem_ker, map_sub, S.pi_liftOf p, hpval, sub_self]
    have hmem' : S.liftOf p - n ∈ S.iota.range := by
      rw [S.range_iota_eq_ker_pi]
      exact hmem
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hmem'
    have hkey : ∀ g : G, (S.cocycleOf (S.liftOf p) (S.liftOf_invariant p) : G → M) g
        = (f : G → M) g + (g • a - a) := by
      intro g
      apply S.iota_injective
      rw [S.iota_cocycleOf, map_add, map_sub, S.iota_equivariant g a, ha, ← hnval g, smul_sub]
      abel
    refine AddMonoidHom.mem_range.mpr ⟨p, ?_⟩
    rw [S.delta_apply, Work.AbsoluteKummer.H1π_eq_iff]
    refine (Work.AbsoluteKummer.mem_B1_iff _).mpr ⟨a, ?_⟩
    funext g
    rw [Work.GroupCohomology.d0_apply, AddSubgroup.coe_sub, Pi.sub_apply, hkey g]
    abel

end Work.AbsoluteKummer.SES
