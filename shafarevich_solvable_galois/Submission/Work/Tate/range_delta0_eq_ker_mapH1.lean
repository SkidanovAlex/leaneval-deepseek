import Mathlib.Tactic.Abel
import Mathlib.Data.Fintype.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.Tate.Delta0Map
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

/-- **Exactness at `H¹(G, A)`.**  For a short exact sequence of `G`-modules
`0 → A --f--> B --g--> C → 0` with `G` finite, the range of the connecting map
`δ₀ : Ĥ⁰(G, C) → H¹(G, A)` is exactly the kernel of the map
`mapH1 f : H¹(G, A) → H¹(G, B)`.

* `range δ₀ ⊆ ker mapH1(f)`: on the class of a fixed point `c ∈ C^G` the connecting map is
  represented by the cocycle `γ ↦ f⁻¹(γ • sec c - sec c)`, whose image under `f` is the
  coboundary `d⁰(sec c)`, hence is trivial in `H¹(G, B)`.

* `ker mapH1(f) ⊆ range δ₀`: if a cocycle `a : Z¹(G, A)` has `f ∘ a` a coboundary, say
  `f (a γ) = γ • b - b` for some `b : B`, then `c := g b` is fixed and `b` is a lift of `c`;
  comparing it with the canonical lift `sec c` exhibits `δ₀(c) - [a]` as the coboundary of a
  suitable element of `A`. -/
theorem range_delta0_eq_ker_mapH1 {G : Type*} {A B C : Type*} [Group G] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] [Fintype G] (S : Work.Tate.SES G A B C) :
    S.delta0.range = (Work.GroupCohomology.mapH1 G S.f S.f_equiv).ker := by
  apply le_antisymm
  · -- `range δ₀ ⊆ ker mapH1(f)`
    intro y hy
    obtain ⟨z, rfl⟩ := AddMonoidHom.mem_range.mp hy
    rw [AddMonoidHom.mem_ker]
    induction z using H0_induction_on with
    | h c =>
      rw [S.delta0_H0π]
      rw [Work.GroupCohomology.mapH1_H1π G S.f S.f_equiv]
      apply (Work.GroupCohomology.H1pi_eq_zero_iff _).mpr
      refine AddMonoidHom.mem_range.mpr ⟨S.sec (c : C), ?_⟩
      funext γ
      rw [Work.GroupCohomology.d0_apply, Work.GroupCohomology.mapZ1_coe G S.f S.f_equiv,
        Work.GroupCohomology.mapCochain1_apply]
      exact (S.f_delta0Cocycle c γ).symm
  · -- `ker mapH1(f) ⊆ range δ₀`
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    rw [AddMonoidHom.mem_range]
    revert hx
    refine Work.GroupCohomology.H1_induction_on
      (C := fun z => (Work.GroupCohomology.mapH1 G S.f S.f_equiv) z = 0 →
        z ∈ S.delta0.range) x ?_
    intro a ha
    rw [Work.GroupCohomology.mapH1_H1π G S.f S.f_equiv] at ha
    rw [Work.GroupCohomology.H1pi_eq_zero_iff] at ha
    rw [Work.GroupCohomology.mem_B1_iff] at ha
    obtain ⟨b, hb⟩ := ha
    -- `f ∘ a` is the coboundary of `b`: `γ • b - b = f (a γ)`
    have hb' : ∀ γ : G, γ • b - b = S.f ((a : G → A) γ) := by
      intro γ
      have h := congrFun hb γ
      rw [Work.GroupCohomology.mapZ1_coe G S.f S.f_equiv,
        Work.GroupCohomology.mapCochain1_apply, Work.GroupCohomology.d0_apply] at h
      exact h
    have h₁ : ∀ γ : G, S.g (γ • b - b) = 0 := by
      intro γ
      rw [hb' γ, S.g_comp_f]
    -- `c := g b` is `G`-fixed
    have hc : S.g b ∈ fixedSubgroup G C := by
      rw [mem_fixedSubgroup]
      intro γ
      rw [← S.g_equiv γ b]
      have h1 : S.g (γ • b - b) = 0 := h₁ γ
      calc S.g (γ • b) = S.g ((γ • b - b) + b) := by rw [sub_add_cancel]
        _ = S.g (γ • b - b) + S.g b := map_add S.g _ _
        _ = S.g b := by rw [h1, zero_add]
    -- `b` and the canonical lift `sec (g b)` differ by `f a₀`
    have hker : S.g (b - S.sec (S.g b)) = 0 := by
      rw [map_sub, S.sec_spec, sub_self]
    obtain ⟨a₀, ha₀⟩ := S.exists_of_g_eq_zero hker
    refine ⟨H0π G C ⟨S.g b, hc⟩, ?_⟩
    rw [S.delta0_H0π]
    apply (Work.GroupCohomology.H1pi_eq_iff _ _).mpr
    rw [Work.GroupCohomology.mem_B1_iff]
    refine ⟨-a₀, ?_⟩
    funext γ
    rw [Work.GroupCohomology.d0_apply]
    rw [AddSubgroup.coe_sub, Pi.sub_apply]
    -- compare the cocycles attached to `b` and to `sec (g b)`
    have hsub := delta0CocycleOf_sub_eq (b' := S.sec (S.g b)) S h₁
      (S.sec_sub_self_mem_ker ⟨S.g b, hc⟩) ha₀.symm γ
    have hDb : S.delta0CocycleOf b h₁ γ = (a : G → A) γ := by
      apply S.f_injective
      rw [S.f_delta0CocycleOf b h₁ γ, hb' γ]
    change γ • -a₀ - -a₀ = S.delta0CocycleOf (S.sec (S.g b))
      (S.sec_sub_self_mem_ker ⟨S.g b, hc⟩) γ - (a : G → A) γ
    have hDsec : S.delta0CocycleOf (S.sec (S.g b)) (S.sec_sub_self_mem_ker ⟨S.g b, hc⟩) γ
        = (a : G → A) γ - (γ • a₀ - a₀) := by
      have h2 : (a : G → A) γ
          - S.delta0CocycleOf (S.sec (S.g b)) (S.sec_sub_self_mem_ker ⟨S.g b, hc⟩) γ
          = γ • a₀ - a₀ := by
        rw [hDb] at hsub
        exact hsub
      rw [← h2]
      abel
    rw [hDsec, smul_neg]
    abel

end Work.Tate
