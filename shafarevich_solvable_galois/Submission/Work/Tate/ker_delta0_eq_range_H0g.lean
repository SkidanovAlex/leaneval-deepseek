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

/-- Exactness of the Tate sequence at `Ĥ⁰(G, C)`: the kernel of the connecting map
`δ₀ : Ĥ⁰(G, C) → H¹(G, A)` is the image of the map `Ĥ⁰(G, B) → Ĥ⁰(G, C)` induced by `g`.

Both inclusions are computations with the explicit description `δ₀ (H0π c) = [γ ↦ f⁻¹(γ • b - b)]`
of the connecting map on a fixed point `c` with lift `b`:

* if `x = H0g (H0π b)` with `b ∈ B^G`, the element `sec (g b) - b` lies in `ker g = im f` and is
  fixed, so the cocycle `γ ↦ f⁻¹(γ • sec (g b) - sec (g b))` is the coboundary of the
  corresponding preimage and `δ₀ x = 0`;
* if `δ₀ (H0π c) = 0`, say `γ • a - a = f⁻¹(γ • sec c - sec c)`, then `sec c - f a` is a fixed
  lift of `c`, so `H0π c` is in the image of `H0g`. -/
theorem ker_delta0_eq_range_H0g {G : Type*} {A B C : Type*} [Group G] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] [Fintype G] (S : Work.Tate.SES G A B C) :
    S.delta0.ker = S.H0g.range := by
  apply le_antisymm
  · -- `ker δ₀ ⊆ range H0g`
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    rw [AddMonoidHom.mem_range]
    revert hx
    refine H0_induction_on (C := fun z => S.delta0 z = 0 → z ∈ S.H0g.range) x ?_
    intro c hc
    rw [SES.delta0_H0π, GroupCohomology.H1pi_eq_zero_iff,
      GroupCohomology.mem_B1_iff] at hc
    obtain ⟨a, ha⟩ := hc
    -- the cocycle attached to `c` is the coboundary of `a`
    have hca : ∀ γ : G, γ • a - a = S.delta0Cocycle c γ := by
      intro γ
      have h := congrFun ha γ
      rw [GroupCohomology.d0_apply] at h
      exact h
    -- the lift `sec c - f a` of `c` is fixed
    have hb : S.sec (c : C) - S.f a ∈ fixedSubgroup G B := by
      rw [mem_fixedSubgroup]
      intro γ
      have key : γ • S.sec (c : C) - S.sec (c : C) = γ • S.f a - S.f a := by
        rw [← S.f_delta0Cocycle c γ, ← hca γ, map_sub, S.f_equiv]
      have h1 : (γ • S.sec (c : C) - γ • S.f a) - (S.sec (c : C) - S.f a)
          = (γ • S.sec (c : C) - S.sec (c : C)) - (γ • S.f a - S.f a) := by abel
      rw [key, sub_self] at h1
      rw [smul_sub]
      exact sub_eq_zero.mp h1
    refine AddMonoidHom.mem_range.mpr ⟨H0π G B ⟨S.sec (c : C) - S.f a, hb⟩, ?_⟩
    rw [H0g_H0π]
    congr 1
    exact Subtype.ext (by rw [mapFixed_apply, map_sub, S.sec_spec, S.g_comp_f, sub_zero])
  · -- `range H0g ⊆ ker δ₀`
    intro x hx
    rw [AddMonoidHom.mem_range] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [AddMonoidHom.mem_ker]
    refine H0_induction_on (C := fun z => S.delta0 (S.H0g z) = 0) y ?_
    intro b
    rw [H0g_H0π, SES.delta0_H0π, GroupCohomology.H1pi_eq_zero_iff,
      GroupCohomology.mem_B1_iff]
    set c : fixedSubgroup G C := mapFixed G B C S.g S.g_equiv b with hcdef
    have hcval : (c : C) = S.g (b : B) := by rw [hcdef, mapFixed_apply]
    -- `sec c - b ∈ ker g`
    have hker : S.g (S.sec (c : C) - (b : B)) = 0 := by
      rw [map_sub, S.sec_spec, hcval, sub_self]
    obtain ⟨a, ha⟩ := S.exists_of_g_eq_zero hker
    refine ⟨a, ?_⟩
    funext γ
    rw [GroupCohomology.d0_apply]
    show γ • a - a = S.delta0Cocycle c γ
    apply S.f_injective
    rw [map_sub, S.f_equiv, S.f_delta0Cocycle]
    have hbγ : γ • (b : B) = (b : B) := b.2 γ
    calc γ • S.f a - S.f a
        = γ • (S.sec (c : C) - (b : B)) - (S.sec (c : C) - (b : B)) := by rw [ha]
      _ = γ • S.sec (c : C) - S.sec (c : C) := by rw [smul_sub, hbγ]; abel

end Work.Tate
