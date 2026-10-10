import Mathlib.Algebra.Order.Ring.Star
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.Commons.RepresentationTheory.GroupCohomology.range_infNatTrans_eq_ker_resNatTrans_of_subsingleton
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RepresentationTheory.GroupCohomology

/-- **Cardinality comparison of `H²` for two normal subgroups linked by a vanishing composite.**

Let `M, N ◁ G`, `A` a `ℤ`-linear `G`-representation.  Assume `H¹(M, A) = H¹(N, A) = 0`, so that
the inflation–restriction sequences in degree two are exact at `H²(G, A)`, and that the composite
`H²(G ⧸ M, A^M) --inf--> H²(G, A) --res--> H²(N, A)` vanishes.  Then the range of `inf_M` is
contained in the range of `inf_N`; since both inflation maps are injective, this embeds
`H²(G ⧸ M, A^M)` into `H²(G ⧸ N, A^N)`, giving the cardinality inequality (with `Nat.card`, which
is `0` on infinite types, the inequality holds unconditionally). -/
theorem natCard_quotientToInvariants_le_of_twist
    {G : Type} [Group G] (M N : Subgroup G) [M.Normal] [N.Normal] (A : Rep.{0,0,0} ℤ G)
    [Fintype N] [Finite (groupCohomology (A.quotientToInvariants N) 2)]
    (h1N : Subsingleton (groupCohomology (Rep.res N.subtype A) 1))
    (h1M : Subsingleton (groupCohomology (Rep.res M.subtype A) 1))
    (hzero : CategoryTheory.CategoryStruct.comp ((groupCohomology.infNatTrans ℤ M 2).app A)
        ((groupCohomology.resNatTrans ℤ (G := N) (H := G) N.subtype 2).app A) = 0) :
    Nat.card (groupCohomology (A.quotientToInvariants M) 2) ≤
      Nat.card (groupCohomology (A.quotientToInvariants N) 2) := by
  classical
  set gM : groupCohomology (A.quotientToInvariants M) 2 →ₗ[ℤ] groupCohomology A 2 :=
    ((groupCohomology.infNatTrans ℤ M 2).app A).hom with hgM
  set gN : groupCohomology (A.quotientToInvariants N) 2 →ₗ[ℤ] groupCohomology A 2 :=
    ((groupCohomology.infNatTrans ℤ N 2).app A).hom with hgN
  set fN : groupCohomology A 2 →ₗ[ℤ] groupCohomology (Rep.res N.subtype A) 2 :=
    ((groupCohomology.resNatTrans ℤ (G := N) (H := G) N.subtype 2).app A).hom with hfN
  have hinjM : Function.Injective gM :=
    H2_inflation_injective_of_subsingleton_H1 M A h1M
  have hinjN : Function.Injective gN :=
    H2_inflation_injective_of_subsingleton_H1 N A h1N
  have hexN : gN.range = fN.ker :=
    range_infNatTrans_eq_ker_resNatTrans_of_subsingleton N A (by norm_num) (fun j hj hjlt => by
      interval_cases j
      exact h1N)
  have hcomp : fN.comp gM = 0 := by
    have h2 := congrArg ModuleCat.Hom.hom hzero
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
    rw [hfN, hgM]
    exact h2
  have hle : gM.range ≤ gN.range := by
    have h1 : gM.range ≤ fN.ker := LinearMap.range_le_ker_iff.mpr hcomp
    rw [← hexN] at h1
    exact h1
  set φ : groupCohomology (A.quotientToInvariants M) 2 →
      groupCohomology (A.quotientToInvariants N) 2 :=
    fun x => Classical.choose (LinearMap.mem_range.mp (hle (LinearMap.mem_range_self gM x)))
  have hφspec : ∀ x, gN (φ x) = gM x := fun x =>
    Classical.choose_spec (LinearMap.mem_range.mp (hle (LinearMap.mem_range_self gM x)))
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply hinjM
    rw [← hφspec x, ← hφspec y, hxy]
  exact Nat.card_le_card_of_injective φ hφinj

end Commons.RepresentationTheory.GroupCohomology
