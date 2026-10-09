import Mathlib
import Submission.Work.AbsoluteKummer.All
import Submission.Work.AbsoluteKummer.SES.deltaH2_exact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open scoped Classical Topology

/-- **`H²` only depends on the coefficient module up to equivariant additive isomorphism.**

An isomorphism of `G`-modules `Φ : M ≃+ N` (additive, commuting with the `G`-action) induces an
additive isomorphism `H²(G,M) ≃+ H²(G,N)` on continuous second cohomology.  Indeed `Φ` and its
inverse are equivariant additive maps, so they induce `mapH2` maps in the two directions, and the
composites are the identity because on cocycle representatives they are `Φ.symm ∘ Φ = id` and
`Φ ∘ Φ.symm = id`. -/
theorem h2_equiv_of_equiv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {M N : Type} [AddCommGroup M] [AddCommGroup N] [DistribMulAction G M] [DistribMulAction G N]
    (Φ : M ≃+ N) (h : ∀ (g : G) (m : M), Φ (g • m) = g • Φ m) :
    Nonempty (Work.AbsoluteKummer.H2 G M ≃+ Work.AbsoluteKummer.H2 G N) := by
  let Φ' : M →+ N := Φ.toAddMonoidHom
  have hΦ : Work.GroupCohomology.IsEquivariant G Φ' := fun g m => h g m
  let Ψ : N →+ M := Φ.symm.toAddMonoidHom
  have hΨ : Work.GroupCohomology.IsEquivariant G Ψ := by
    intro g n
    apply Φ.injective
    calc Φ (Ψ (g • n)) = g • n := by simp [Ψ]
      _ = g • Φ (Ψ n) := by simp [Ψ]
      _ = Φ (g • Ψ n) := (h g (Ψ n)).symm
  -- on cocycle representatives, the two composites are the identity
  have hz : ∀ c : Work.AbsoluteKummer.Z2 G M,
      Work.AbsoluteKummer.mapZ2 Ψ hΨ (Work.AbsoluteKummer.mapZ2 Φ' hΦ c) = c := by
    intro c
    ext p
    simp [Work.AbsoluteKummer.mapZ2_apply, Ψ, Φ']
  have hz' : ∀ d : Work.AbsoluteKummer.Z2 G N,
      Work.AbsoluteKummer.mapZ2 Φ' hΦ (Work.AbsoluteKummer.mapZ2 Ψ hΨ d) = d := by
    intro d
    ext p
    simp [Work.AbsoluteKummer.mapZ2_apply, Ψ, Φ']
  have hleft : ∀ x : Work.AbsoluteKummer.H2 G M,
      Work.AbsoluteKummer.mapH2 Ψ hΨ (Work.AbsoluteKummer.mapH2 Φ' hΦ x) = x := by
    intro x
    obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
      ((Work.AbsoluteKummer.B2 G M).comap (Work.AbsoluteKummer.Z2 G M).subtype) x
    rw [← hc]
    show Work.AbsoluteKummer.mapH2 Ψ hΨ (Work.AbsoluteKummer.mapH2 Φ' hΦ
      (Work.AbsoluteKummer.H2π G M c)) = Work.AbsoluteKummer.H2π G M c
    rw [Work.AbsoluteKummer.mapH2_H2π, Work.AbsoluteKummer.mapH2_H2π, hz c]
  have hright : ∀ y : Work.AbsoluteKummer.H2 G N,
      Work.AbsoluteKummer.mapH2 Φ' hΦ (Work.AbsoluteKummer.mapH2 Ψ hΨ y) = y := by
    intro y
    obtain ⟨d, hd⟩ := QuotientAddGroup.mk'_surjective
      ((Work.AbsoluteKummer.B2 G N).comap (Work.AbsoluteKummer.Z2 G N).subtype) y
    rw [← hd]
    show Work.AbsoluteKummer.mapH2 Φ' hΦ (Work.AbsoluteKummer.mapH2 Ψ hΨ
      (Work.AbsoluteKummer.H2π G N d)) = Work.AbsoluteKummer.H2π G N d
    rw [Work.AbsoluteKummer.mapH2_H2π, Work.AbsoluteKummer.mapH2_H2π, hz' d]
  exact ⟨{ toFun := Work.AbsoluteKummer.mapH2 Φ' hΦ
           invFun := Work.AbsoluteKummer.mapH2 Ψ hΨ
           left_inv := hleft
           right_inv := hright
           map_add' := fun a b => (Work.AbsoluteKummer.mapH2 Φ' hΦ).map_add a b }⟩

end Work.SSGRoute.PT
