import Mathlib.Analysis.Normed.Group.Uniform
import Submission.Work.Tate.Delta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

/-- Exactness of the six-term Tate sequence at `Ĥ⁻¹(G, C)`: a class in `Ĥ⁻¹(G, C)` dies under
the connecting map `δ` if and only if it comes from `Ĥ⁻¹(G, B)`.

Both inclusions are computations with the explicit description of `δ` on representatives:

* if `δ (c) = 0` for a class `c ∈ Ĥ⁻¹(G, C)` represented by `c₀ ∈ ker N_C`, then the canonical
  preimage `preimage c₀ = N_A a` is a norm, so the element `sec c₀ - f a` lies in `ker N_B` and
  maps to `c₀` under `g`; hence the class of `c` is in the image of `Ĥ⁻¹(G, B) → Ĥ⁻¹(G, C)`;
* if a class in `Ĥ⁻¹(G, C)` is the image of a class represented by `b ∈ ker N_B`, its canonical
  lift is `g b`, whose norm is `g (N_B b) = 0`; thus the preimage of `g b` differs from `0` by a
  norm, and `δ` kills the class. -/
theorem ker_delta_eq_range_Hm1g {G : Type*} {A : Type*} {B : Type*} {C : Type*} [Group G]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A]
    [DistribMulAction G B] [DistribMulAction G C] [Fintype G] (S : Work.Tate.SES G A B C) :
    S.delta.ker = S.Hm1g.range := by
  refine le_antisymm ?_ ?_
  · -- `ker delta ⊆ range Hm1g`
    intro y hy
    rw [AddMonoidHom.mem_ker] at hy
    revert hy
    refine Hm1_induction_on (C := fun z => S.delta z = 0 → z ∈ S.Hm1g.range) y ?_
    intro c hc
    rw [SES.delta_Hm1π, deltaLiftFun_apply, H0π_eq_zero_iff] at hc
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hc
    have ha' : norm G A a = S.preimage c := congrArg Subtype.val ha
    refine AddMonoidHom.mem_range.mpr ⟨Hm1π G B ⟨S.sec (c : C) - S.f a, ?_⟩, ?_⟩
    · rw [AddMonoidHom.mem_ker, map_sub, norm_map S.f S.f_equiv a, ha', S.f_preimage,
        sub_self]
    · rw [Hm1g_Hm1π]
      congr 1
      apply Subtype.ext
      rw [mapKer_apply, map_sub, S.sec_spec, S.g_comp_f, sub_zero]
  · -- `range Hm1g ⊆ ker delta`
    intro y hy
    obtain ⟨x, hx⟩ := hy
    rw [← hx, AddMonoidHom.mem_ker]
    refine Hm1_induction_on (C := fun z => S.delta (S.Hm1g z) = 0) x ?_
    intro b
    rw [Hm1g_Hm1π, SES.delta_Hm1π, deltaLiftFun_apply, H0π_eq_zero_iff]
    set c : (norm G C).ker := mapKer G B C S.g S.g_equiv b with hc
    have hcval : (c : C) = S.g (b : B) := by rw [hc]; rfl
    have hker : S.g (S.sec (c : C) - (b : B)) = 0 := by
      rw [map_sub, S.sec_spec, hcval, sub_self]
    obtain ⟨a, ha⟩ := S.exists_of_g_eq_zero hker
    refine AddMonoidHom.mem_range.mpr ⟨a, Subtype.ext ?_⟩
    show norm G A a = S.preimage c
    apply S.f_injective
    rw [S.f_preimage, ← norm_map S.f S.f_equiv a]
    have h1 : S.sec (c : C) = (b : B) + S.f a := by rw [ha]; abel
    rw [h1, map_add, b.2, zero_add]

end Work.Tate
