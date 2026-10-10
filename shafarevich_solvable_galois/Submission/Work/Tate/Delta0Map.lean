import Mathlib.Data.Fintype.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.GroupCohomology.H1pi_eq_iff
import Submission.Work.GroupCohomology.H1pi_eq_zero_iff
import Submission.Work.Tate.delta0CocycleOf_add
import Submission.Work.Tate.delta0CocycleOf_mem_Z1
import Submission.Work.Tate.delta0CocycleOf_sub_eq
import Submission.Work.Tate.delta0Cocycle_eq_coboundary_of_eq_norm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w x

namespace Work.Tate

variable {G : Type u} {A : Type v} {B : Type w} {C : Type x} [Group G] [AddCommGroup A]
  [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
  [DistribMulAction G C] [Fintype G]

/-- The cocycle attached to a fixed point is a `1`-cocycle of `A`. -/
theorem SES.delta0Cocycle_mem_Z1 (S : SES G A B C) (c : fixedSubgroup G C) :
    S.delta0Cocycle c ∈ GroupCohomology.Z1 G A :=
  delta0CocycleOf_mem_Z1 S (S.sec (c : C)) (S.sec_sub_self_mem_ker c)

/-- The map `A^G → H¹(G,A)` underlying `δ₀`. -/
noncomputable def SES.delta0Fun (S : SES G A B C) :
    fixedSubgroup G C →+ GroupCohomology.H1 G A where
  toFun c := GroupCohomology.H1π G A ⟨S.delta0Cocycle c, S.delta0Cocycle_mem_Z1 c⟩
  map_zero' := by
    obtain ⟨a, ha⟩ := delta0Cocycle_eq_coboundary_of_eq_norm S 0 0 (by rw [map_zero])
    rw [GroupCohomology.H1pi_eq_zero_iff, GroupCohomology.mem_B1_iff]
    exact ⟨a, by funext γ; exact (ha γ).symm⟩
  map_add' c₁ c₂ := by
    rw [← map_add]
    refine (GroupCohomology.H1pi_eq_iff _ _).mpr ?_
    rw [GroupCohomology.mem_B1_iff]
    have hker : S.g (S.sec ((c₁ + c₂ : fixedSubgroup G C) : C) -
        (S.sec (c₁ : C) + S.sec (c₂ : C))) = 0 := by
      rw [map_sub, map_add, S.sec_spec, S.sec_spec, S.sec_spec]
      show ((c₁ : C) + (c₂ : C)) - ((c₁ : C) + (c₂ : C)) = 0
      rw [sub_self]
    obtain ⟨a₀, ha₀⟩ := S.exists_of_g_eq_zero hker
    have hb' : ∀ γ : G, S.g (γ • (S.sec (c₁ : C) + S.sec (c₂ : C)) -
        (S.sec (c₁ : C) + S.sec (c₂ : C))) = 0 := by
      intro γ
      rw [map_sub, S.g_equiv, map_add, S.sec_spec, S.sec_spec, smul_add, (c₁.2 γ), (c₂.2 γ)]
      show ((c₁ : C) + (c₂ : C)) - ((c₁ : C) + (c₂ : C)) = 0
      rw [sub_self]
    refine ⟨a₀, ?_⟩
    funext γ
    rw [show ((⟨S.delta0Cocycle (c₁ + c₂), S.delta0Cocycle_mem_Z1 (c₁ + c₂)⟩ -
        (⟨S.delta0Cocycle c₁, S.delta0Cocycle_mem_Z1 c₁⟩ +
          ⟨S.delta0Cocycle c₂, S.delta0Cocycle_mem_Z1 c₂⟩) : GroupCohomology.Z1 G A) : G → A) γ
        = S.delta0Cocycle (c₁ + c₂) γ
          - (S.delta0Cocycle c₁ γ + S.delta0Cocycle c₂ γ) from rfl]
    rw [show S.delta0Cocycle (c₁ + c₂) γ
        = S.delta0CocycleOf (S.sec ((c₁ + c₂ : fixedSubgroup G C) : C))
            (S.sec_sub_self_mem_ker (c₁ + c₂)) γ from rfl]
    rw [show S.delta0Cocycle c₁ γ = S.delta0CocycleOf (S.sec (c₁ : C))
        (S.sec_sub_self_mem_ker c₁) γ from rfl]
    rw [show S.delta0Cocycle c₂ γ = S.delta0CocycleOf (S.sec (c₂ : C))
        (S.sec_sub_self_mem_ker c₂) γ from rfl]
    rw [← delta0CocycleOf_add S (S.sec_sub_self_mem_ker c₁) (S.sec_sub_self_mem_ker c₂) hb' γ]
    rw [delta0CocycleOf_sub_eq S (S.sec_sub_self_mem_ker (c₁ + c₂)) hb' ha₀.symm γ]
    rw [GroupCohomology.d0_apply]

/-- The connecting map `δ₀ : Ĥ⁰(G, C) →+ H¹(G, A)` of a short exact sequence of `G`-modules. -/
noncomputable def SES.delta0 (S : SES G A B C) : H0 G C →+ GroupCohomology.H1 G A :=
  QuotientAddGroup.lift (normToFixed G C).range S.delta0Fun (by
    intro x hx
    rw [AddMonoidHom.mem_ker]
    obtain ⟨c₀, rfl⟩ := hx
    obtain ⟨a, ha⟩ := delta0Cocycle_eq_coboundary_of_eq_norm S (normToFixed G C c₀) c₀ rfl
    show GroupCohomology.H1π G A ⟨S.delta0Cocycle (normToFixed G C c₀),
      S.delta0Cocycle_mem_Z1 (normToFixed G C c₀)⟩ = 0
    rw [GroupCohomology.H1pi_eq_zero_iff, GroupCohomology.mem_B1_iff]
    exact ⟨a, by funext γ; exact (ha γ).symm⟩)

@[simp] theorem SES.delta0_H0π (S : SES G A B C) (c : fixedSubgroup G C) :
    S.delta0 (H0π G C c) = GroupCohomology.H1π G A
      ⟨S.delta0Cocycle c, S.delta0Cocycle_mem_Z1 c⟩ := rfl

end Work.Tate
