import Mathlib
import Submission.Work.AbsoluteKummer.SES
import Submission.Work.GroupCohomology.ShortExact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.SES

/-- A short exact sequence of discrete `G`-modules is exact at `H⁰(G, N)`: the image of the
induced map `H⁰(G, M) → H⁰(G, N)` is the kernel of the induced map `H⁰(G, N) → H⁰(G, P)`. -/
theorem range_mapH0_eq_ker_mapH0 {G : Type*} [TopologicalSpace G] [Group G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P] (S : Work.AbsoluteKummer.ShortExactSeq G M N P) : (Work.GroupCohomology.mapH0 G S.iota S.iota_equivariant).range = (Work.GroupCohomology.mapH0 G S.pi S.pi_equivariant).ker := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hx
    rw [AddMonoidHom.mem_ker, ← ha]
    apply Subtype.ext
    simp [Work.GroupCohomology.mapH0, S.pi_iota]
  · intro hx
    rw [AddMonoidHom.mem_ker] at hx
    have hxN : S.pi (x : N) = 0 := by
      have h := congrArg Subtype.val hx
      simpa [Work.GroupCohomology.mapH0] using h
    have hm : (x : N) ∈ S.pi.ker := hxN
    rw [← S.range_iota_eq_ker_pi] at hm
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hm
    refine AddMonoidHom.mem_range.mpr ⟨⟨a, ?_⟩, ?_⟩
    · intro g
      apply S.iota_injective
      rw [S.iota_equivariant g a, ha]
      exact x.2 g
    · exact Subtype.ext ha

end Work.AbsoluteKummer.SES
