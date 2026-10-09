import Mathlib
import Submission.Work.Tate.SES
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

/-- Exactness at `Ĥ⁰(G, B)` for a short exact sequence of `G`-modules: the kernel of the map
`Ĥ⁰(G, B) → Ĥ⁰(G, C)` induced by `g` is the image of the map `Ĥ⁰(G, A) → Ĥ⁰(G, B)` induced
by `f`. -/
theorem ker_H0g_eq_range_H0f {G : Type*} {A : Type*} {B : Type*} {C : Type*} [Group G]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A]
    [DistribMulAction G B] [DistribMulAction G C] [Fintype G] (S : Work.Tate.SES G A B C) :
    S.H0g.ker = S.H0f.range := by
  -- The composite `H0g ∘ H0f` is zero.
  have hgf : ∀ y, S.H0g (S.H0f y) = 0 := fun y =>
    H0_induction_on (C := fun z => S.H0g (S.H0f z) = 0) y (fun a => by
      rw [H0f_H0π, H0g_H0π]
      apply (H0π_eq_zero_iff _).mpr
      refine AddMonoidHom.mem_range.mpr ⟨0, Subtype.ext ?_⟩
      simp [S.g_comp_f])
  ext x
  constructor
  · -- `ker H0g ⊆ range H0f`
    intro hx
    rw [AddMonoidHom.mem_ker] at hx
    revert hx
    refine H0_induction_on (C := fun z => S.H0g z = 0 → z ∈ S.H0f.range) x (fun b hb => ?_)
    rw [H0g_H0π, H0π_eq_zero_iff] at hb
    obtain ⟨c, hc⟩ := AddMonoidHom.mem_range.mp hb
    have hcb : norm G C c = S.g b := congrArg Subtype.val hc
    have hge : S.g (norm G B (S.sec c) - b) = 0 := by
      rw [map_sub, ← norm_map S.g S.g_equiv (S.sec c), S.sec_spec c, hcb, sub_self]
    obtain ⟨a, ha⟩ := S.exists_of_g_eq_zero hge
    have hfix : (S.f a) ∈ fixedSubgroup G B := by
      rw [ha]
      exact sub_mem (norm_mem_fixed (S.sec c)) b.2
    rw [mem_fixedSubgroup] at hfix
    have haf : a ∈ fixedSubgroup G A := by
      rw [mem_fixedSubgroup]
      intro γ
      apply S.f_injective
      rw [S.f_equiv γ a]
      exact hfix γ
    refine AddMonoidHom.mem_range.mpr ⟨H0π G A ⟨-a, neg_mem haf⟩, ?_⟩
    rw [H0f_H0π]
    apply (H0π_eq_iff _ _).mpr
    refine AddMonoidHom.mem_range.mpr ⟨-S.sec c, Subtype.ext ?_⟩
    simp only [normToFixed_apply, mapFixed_apply, AddSubgroup.coe_sub]
    have hL : norm G B (-S.sec c) = -(norm G B (S.sec c)) := map_neg (norm G B) (S.sec c)
    have hR : S.f (-a) = -(S.f a) := map_neg S.f a
    rw [hL, hR, ha]
    abel
  · -- `range H0f ⊆ ker H0g`
    intro hx
    rw [AddMonoidHom.mem_ker]
    obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.mp hx
    exact hgf y

end Work.Tate
