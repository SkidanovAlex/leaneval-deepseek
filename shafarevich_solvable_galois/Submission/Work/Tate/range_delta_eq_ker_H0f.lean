import Mathlib.Analysis.Normed.Group.Uniform
import Submission.Work.Tate.Delta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

theorem range_delta_eq_ker_H0f {G : Type*} {A : Type*} {B : Type*} {C : Type*} [Group G]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A]
    [DistribMulAction G B] [DistribMulAction G C] [Fintype G] (S : Work.Tate.SES G A B C) :
    S.delta.range = S.H0f.ker := by
  apply le_antisymm
  · -- `range δ ⊆ ker H0f`: the composite `H0f ∘ δ` is zero.
    intro y hy
    rw [AddMonoidHom.mem_range] at hy
    obtain ⟨z, rfl⟩ := hy
    rw [AddMonoidHom.mem_ker]
    refine Hm1_induction_on (C := fun z => S.H0f (S.delta z) = 0) z ?_
    intro c
    rw [S.delta_Hm1π, deltaLiftFun_apply, H0f_H0π]
    apply (H0π_eq_zero_iff _).mpr
    exact AddMonoidHom.mem_range.mpr
      ⟨S.sec (c : C), Subtype.ext (by rw [normToFixed_apply, mapFixed_apply, S.f_preimage])⟩
  · -- `ker H0f ⊆ range δ`.
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    rw [AddMonoidHom.mem_range]
    revert hx
    refine H0_induction_on (C := fun z => S.H0f z = 0 → z ∈ S.delta.range) x ?_
    intro a ha
    rw [H0f_H0π, H0π_eq_zero_iff] at ha
    -- `f a = N_B b` for some `b : B`
    obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.mp ha
    have hbval : norm G B b = S.f a := by
      have := congrArg Subtype.val hb
      simpa only [normToFixed_apply, mapFixed_apply] using this
    -- then `g b ∈ ker N_C`, since `N_C (g b) = g (N_B b) = g (f a) = 0`
    have hc : S.g b ∈ (norm G C).ker := by
      rw [AddMonoidHom.mem_ker, norm_map S.g S.g_equiv b, hbval, S.g_comp_f]
    -- `b - sec (g b) ∈ ker g = range f`, say `= f a₀`
    have hker : S.g (b - S.sec (S.g b)) = 0 := by
      rw [map_sub, S.sec_spec]; abel
    obtain ⟨a₀, ha₀⟩ := S.exists_of_g_eq_zero hker
    -- hence `preimage (g b) = a - N_A a₀`
    have hpre : S.preimage ⟨S.g b, hc⟩ = (a : A) - norm G A a₀ := by
      apply S.f_injective
      rw [S.f_preimage, map_sub, ← norm_map S.f S.f_equiv a₀, ha₀, map_sub, hbval]
      change norm G B (S.sec (S.g b)) = S.f ↑a - (S.f ↑a - norm G B (S.sec (S.g b)))
      abel
    refine ⟨Hm1π G C ⟨S.g b, hc⟩, ?_⟩
    rw [S.delta_Hm1π, deltaLiftFun_apply, H0π_eq_iff]
    -- `preimage (g b) - a = -N_A a₀` is a norm
    refine AddMonoidHom.mem_range.mpr ⟨-a₀, Subtype.ext ?_⟩
    show norm G A (-a₀) = S.preimage ⟨S.g b, hc⟩ - (a : A)
    rw [map_neg, hpre]
    abel

end Work.Tate
