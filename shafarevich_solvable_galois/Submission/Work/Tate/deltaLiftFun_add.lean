import Mathlib
import Submission.Work.Tate.SES
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

/-- The connecting map `Ĥ⁻¹(G, C) → Ĥ⁰(G, A)`, computed on representatives of `ker N_C` via a
set-theoretic section of `g`, is additive: the class of `preimage (c₁ + c₂)` equals the sum of
the classes of `preimage c₁` and `preimage c₂`.

The point is that `sec (c₁ + c₂) - sec c₁ - sec c₂` lies in `ker g = range f`, hence is `f a` for
some `a : A`; applying the norm gives `N_B (sec (c₁ + c₂)) - N_B (sec c₁) - N_B (sec c₂) =
f (N_A a)`, so by injectivity of `f` the difference `preimage (c₁ + c₂) - preimage c₁ -
preimage c₂` is exactly the norm `N_A a`, i.e. a coboundary in `Ĥ⁰(G, A) = A^G / N(A)`. -/
theorem deltaLiftFun_add {G : Type*} {A : Type*} {B : Type*} {C : Type*} [Group G]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A]
    [DistribMulAction G B] [DistribMulAction G C] [Fintype G] (S : Work.Tate.SES G A B C)
    (c₁ c₂ : (Work.Tate.norm G C).ker) :
    S.deltaLiftFun (c₁ + c₂) = S.deltaLiftFun c₁ + S.deltaLiftFun c₂ := by
  simp only [deltaLiftFun_apply]
  rw [← map_add, H0π_eq_iff]
  -- the element `b = sec (c₁+c₂) - sec c₁ - sec c₂` lies in `ker g`
  set b : B := S.sec ((c₁ + c₂ : (norm G C).ker) : C) - S.sec (c₁ : C) - S.sec (c₂ : C)
    with hb_def
  have hb : S.g b = 0 := by
    rw [hb_def, map_sub, map_sub, S.sec_spec, S.sec_spec, S.sec_spec, AddSubgroup.coe_add]
    abel
  obtain ⟨a, ha⟩ := S.exists_of_g_eq_zero hb
  -- `norm G B b = S.f (norm G A a)`
  have hfa : S.f (norm G A a) = norm G B b := by
    rw [← norm_map S.f S.f_equiv a, ha]
  refine ⟨a, Subtype.ext ?_⟩
  show norm G A a = _
  apply S.f_injective
  rw [AddSubgroup.coe_sub, AddSubgroup.coe_add]
  rw [hfa, hb_def, map_sub, map_sub, map_sub, map_add,
    S.f_preimage, S.f_preimage, S.f_preimage]
  abel

end Work.Tate
