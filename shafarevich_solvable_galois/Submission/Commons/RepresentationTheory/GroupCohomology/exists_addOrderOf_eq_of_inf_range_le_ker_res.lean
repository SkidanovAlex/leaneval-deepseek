import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.Commons.RepresentationTheory.GroupCohomology.H2_inflation_restriction_exact_of_subsingleton_H1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RepresentationTheory.GroupCohomology

/-- **The abstract twist.**  Let `M, N ◁ G` be normal subgroups of a group `G`, `A` a
`ℤ`-representation of `G`, and suppose that `H¹` of `A` vanishes for both `M` and `N`, and that
the image of the inflation along `M` is contained in the kernel of the restriction along `N`
(so that the inflation along `M` factors through the inflation along `N`).  Then any element of
`H²(G ⧸ M, A^M)` of order `n` produces an element of `H²(G ⧸ N, A^N)` of order `n`, provided the
latter group has exponent dividing `n`. -/
theorem exists_addOrderOf_eq_of_inf_range_le_ker_res
    {G : Type} [Group G] (M N : Subgroup G) [M.Normal] [N.Normal] (A : Rep ℤ G)
    (h1M : Subsingleton (groupCohomology (Rep.res M.subtype A) 1))
    (h1N : Subsingleton (groupCohomology (Rep.res N.subtype A) 1))
    (hle : LinearMap.range ((groupCohomology.infNatTrans ℤ M 2).app A).hom ≤
      LinearMap.ker ((groupCohomology.resNatTrans ℤ (G := N) (H := G) N.subtype 2).app A).hom)
    (n : ℕ) (hkill : ∀ y : groupCohomology (A.quotientToInvariants N) 2, addOrderOf y ∣ n)
    (x : groupCohomology (A.quotientToInvariants M) 2) (hx : addOrderOf x = n) :
    ∃ y : groupCohomology (A.quotientToInvariants N) 2, addOrderOf y = n := by
  set f : groupCohomology (A.quotientToInvariants M) 2 →ₗ[ℤ] groupCohomology A 2 :=
    ((groupCohomology.infNatTrans ℤ M 2).app A).hom with hf
  set g : groupCohomology (A.quotientToInvariants N) 2 →ₗ[ℤ] groupCohomology A 2 :=
    ((groupCohomology.infNatTrans ℤ N 2).app A).hom with hg
  set r : groupCohomology A 2 →ₗ[ℤ] groupCohomology (Rep.res N.subtype A) 2 :=
    ((groupCohomology.resNatTrans ℤ (G := N) (H := G) N.subtype 2).app A).hom with hr
  have hginj : Function.Injective g :=
    H2_inflation_injective_of_subsingleton_H1 N A h1N
  have hfinj : Function.Injective f :=
    H2_inflation_injective_of_subsingleton_H1 M A h1M
  have hex : LinearMap.range g = LinearMap.ker r :=
    H2_inflation_restriction_exact_of_subsingleton_H1 N A h1N
  have hpre : ∀ z : groupCohomology (A.quotientToInvariants M) 2, ∃ y, g y = f z := by
    intro z
    have h : f z ∈ LinearMap.range g := by
      rw [hex]
      exact hle (LinearMap.mem_range_self f z)
    exact LinearMap.mem_range.mp h
  obtain ⟨y, hy⟩ := hpre x
  refine ⟨y, ?_⟩
  calc addOrderOf y = addOrderOf (g y) :=
        (addOrderOf_injective g.toAddMonoidHom hginj y).symm
    _ = addOrderOf (f x) := by rw [hy]
    _ = addOrderOf x := addOrderOf_injective f.toAddMonoidHom hfinj x
    _ = n := hx

end Commons.RepresentationTheory.GroupCohomology
