import Mathlib.Analysis.Normed.Group.Uniform
import Submission.Work.Tate.Delta0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

/-- The connecting cocycle `δ₀(c)` of a fixed point `c ∈ C^G` is a coboundary whenever `c` lies
in the image of the norm `N : C → C^G`.

Indeed, if `c = N c₀`, then `N (sec c₀) = ∑_γ γ • sec c₀` is a `G`-fixed lift of `c` (it is
invariant under the action by reindexing the sum).  Writing the difference of the two lifts
`sec c - N (sec c₀)` as `f a`, the element `a` satisfies
`f (γ • a - a) = γ • sec c - sec c` for all `γ`, so injectivity of `f` identifies `γ • a - a`
with `δ₀(c)(γ)`. -/
theorem delta0Cocycle_eq_coboundary_of_eq_norm {G : Type*} {A B C : Type*} [Group G]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A]
    [DistribMulAction G B] [DistribMulAction G C] [Fintype G] (S : Work.Tate.SES G A B C)
    (c : Work.Tate.fixedSubgroup G C) (c₀ : C) (hc : c = Work.Tate.normToFixed G C c₀) :
    ∃ a : A, ∀ γ : G, S.delta0Cocycle c γ = γ • a - a := by
  classical
  have hc' : (c : C) = norm G C c₀ := congrArg Subtype.val hc
  -- `sec c - N (sec c₀)` lies in the kernel of `g`, since both terms lift `c`.
  have hmem : S.sec (c : C) - norm G B (S.sec c₀) ∈ S.g.ker := by
    rw [AddMonoidHom.mem_ker, map_sub, ← norm_map S.g S.g_equiv (S.sec c₀), S.sec_spec,
      S.sec_spec, hc', sub_self]
  obtain ⟨a, ha⟩ := S.exists_of_g_eq_zero (AddMonoidHom.mem_ker.mp hmem)
  refine ⟨a, fun γ => ?_⟩
  apply S.f_injective
  rw [S.f_delta0Cocycle, map_sub, S.f_equiv, ha]
  have hN : γ • norm G B (S.sec c₀) = norm G B (S.sec c₀) := norm_mem_fixed (S.sec c₀) γ
  simp only [smul_sub, hN]
  abel

end Work.Tate
