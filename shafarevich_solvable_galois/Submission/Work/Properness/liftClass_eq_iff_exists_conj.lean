import Mathlib
import Submission.Work.Properness.Defs
import Submission.Work.Properness.cocycleOfLiftFun_mem_Z1
import Submission.Work.Properness.conjLift_mulFun
import Submission.Work.Properness.mulFun_cocycleOfLiftFun
import Submission.Work.Properness.cocycleOfLiftFun_eq_of_forall_mulFun
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit true
universe u v w

namespace Work.Properness

theorem liftClass_eq_iff_exists_conj {u v w : Universe} {S : Work.Properness.Setup.{u, v, w}} (ψ₀ ψ ψ' : S.Lift) : (Work.GroupCohomology.H1π S.H (Additive S.A) ⟨S.cocycleOfLiftFun ψ₀ ψ, Work.Properness.cocycleOfLiftFun_mem_Z1 (u := u) (v := v) (w := w) (S := S) ψ₀ ψ⟩ = Work.GroupCohomology.H1π S.H (Additive S.A) ⟨S.cocycleOfLiftFun ψ₀ ψ', Work.Properness.cocycleOfLiftFun_mem_Z1 (u := u) (v := v) (w := w) (S := S) ψ₀ ψ'⟩) ↔ ∃ a : S.A, ∀ h : S.H, (ψ' : S.H → S.E) h = (a : S.E) * (ψ : S.H → S.E) h * (a : S.E)⁻¹ := by
  set x : Work.GroupCohomology.Z1 S.H (Additive S.A) :=
    ⟨S.cocycleOfLiftFun ψ₀ ψ, Work.Properness.cocycleOfLiftFun_mem_Z1 (u := u) (v := v) (w := w) (S := S) ψ₀ ψ⟩ with hx
  set y : Work.GroupCohomology.Z1 S.H (Additive S.A) :=
    ⟨S.cocycleOfLiftFun ψ₀ ψ', Work.Properness.cocycleOfLiftFun_mem_Z1 (u := u) (v := v) (w := w) (S := S) ψ₀ ψ'⟩ with hy
  constructor
  · intro hcls
    obtain ⟨z, hzN, hxz⟩ := (QuotientAddGroup.mk'_eq_mk' _).mp hcls
    rw [AddSubgroup.mem_comap] at hzN
    rw [Work.GroupCohomology.mem_B1_iff] at hzN
    obtain ⟨b, hb⟩ := hzN
    refine ⟨(Additive.toMul b)⁻¹, fun h => ?_⟩
    have hα : -(Additive.ofMul ((Additive.toMul b)⁻¹)) = b := by
      rw [ofMul_inv, ofMul_toMul, neg_neg]
    have hzy : x + S.d0Z1 (-(Additive.ofMul ((Additive.toMul b)⁻¹))) = y := by
      apply Subtype.ext
      funext g
      rw [hα]
      rw [AddSubgroup.coe_add, Pi.add_apply]
      have hb' : (S.d0Z1 b).1 = z.1 := hb
      rw [hb']
      have h2 : (x + z).1 g = y.1 g := by rw [hxz]
      simpa [AddSubgroup.coe_add] using h2
    have key := conjLift_mulFun (u := u) (v := v) (w := w) ((Additive.toMul b)⁻¹) x ψ₀ h
    rw [mulFun_cocycleOfLiftFun (u := u) (v := v) (w := w) ψ₀ ψ h] at key
    rw [show S.mulFun (x + S.d0Z1 (-(Additive.ofMul ((Additive.toMul b)⁻¹)))).1 ψ₀.1 h
        = S.mulFun y.1 ψ₀.1 h from by rw [hzy]] at key
    rw [mulFun_cocycleOfLiftFun (u := u) (v := v) (w := w) ψ₀ ψ' h] at key
    exact key.symm
  · rintro ⟨a, ha⟩
    have hfun : ∀ h : S.H, (ψ' : S.H → S.E) h
        = S.mulFun (x + S.d0Z1 (-(Additive.ofMul a))).1 ψ₀.1 h := by
      intro h
      rw [ha h, ← mulFun_cocycleOfLiftFun (u := u) (v := v) (w := w) ψ₀ ψ h]
      exact conjLift_mulFun (u := u) (v := v) (w := w) a x ψ₀ h
    have hxy : x + S.d0Z1 (-(Additive.ofMul a)) = y := by
      apply Subtype.ext
      funext h
      exact (cocycleOfLiftFun_eq_of_forall_mulFun (u := u) (v := v) (w := w) ψ₀ ψ'
        (x + S.d0Z1 (-(Additive.ofMul a))) hfun h).symm
    rw [← hxy]
    refine (QuotientAddGroup.mk'_eq_mk' _).mpr ⟨_, ?_, rfl⟩
    rw [AddSubgroup.mem_comap]
    exact ⟨-(Additive.ofMul a), rfl⟩

end Work.Properness
