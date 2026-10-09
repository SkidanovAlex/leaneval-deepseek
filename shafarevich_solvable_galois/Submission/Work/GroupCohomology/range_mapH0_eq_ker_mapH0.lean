import Mathlib
import Submission.Work.GroupCohomology.ShortExact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- A short exact sequence of `G`-modules is exact at `H⁰(G, B)`: the image of the induced
map `H⁰(G, A) → H⁰(G, B)` is the kernel of the induced map `H⁰(G, B) → H⁰(G, C)`.

This is the `H⁰` part of the long exact cohomology sequence. -/
theorem range_mapH0_eq_ker_mapH0 {G : Type*} {A B C : Type*} [Group G] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] (S : Work.GroupCohomology.ShortExactSeq G A B C) :
    (Work.GroupCohomology.mapH0 G S.iota S.iota_equivariant).range =
      (Work.GroupCohomology.mapH0 G S.pi S.pi_equivariant).ker := by
  ext x
  constructor
  · -- `x = iota a` for `a ∈ A^G`, so `pi x = pi (iota a) = 0`.
    intro hx
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hx
    rw [AddMonoidHom.mem_ker, ← ha]
    apply Subtype.ext
    simp [mapH0, S.pi_iota]
  · -- `pi x = 0`, so `x = iota a`; equivariance and injectivity give `a ∈ A^G`.
    intro hx
    rw [AddMonoidHom.mem_ker] at hx
    have hxB : S.pi (x : B) = 0 := by
      have h := congrArg Subtype.val hx
      simpa [mapH0] using h
    have hm : (x : B) ∈ S.pi.ker := hxB
    rw [← S.range_iota_eq_ker_pi] at hm
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hm
    refine AddMonoidHom.mem_range.mpr ⟨⟨a, ?_⟩, ?_⟩
    · intro g
      apply S.iota_injective
      rw [S.iota_equivariant g a, ha]
      exact x.2 g
    · exact Subtype.ext ha

end Work.GroupCohomology
