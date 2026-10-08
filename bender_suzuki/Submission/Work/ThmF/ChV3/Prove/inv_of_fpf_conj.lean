import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

theorem inv_of_fpf_conj {G : Type*} [Group G] {T : Subgroup G} {s : G}
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hsT : s ∈ Subgroup.normalizer (T : Set G))
    (hs2 : s * s = 1)
    (hfpf : ∀ x ∈ T, s * x * s⁻¹ = x → x = 1) :
    ∀ x ∈ T, s * x * s⁻¹ = x⁻¹ := by
  intro x hx
  -- Conjugation by s on T is an abelian group action whose only fixed point is 1.
  -- We show that the product of the image of x under this action with x is fixed.
  set a := s * x * s⁻¹ with ha
  have haT : a ∈ T := ((Subgroup.mem_normalizer_iff.mp hsT) x).mp hx
  have hmem : a * x ∈ T := T.mul_mem haT hx
  -- conjugation by the involution s is an involution itself
  have hconj : s * (s * x * s⁻¹) * s⁻¹ = x := by
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    calc s * (s * x * s⁻¹) * s⁻¹
        = s * (s * x * s) * s := by rw [hsinv]
      _ = (s * s) * x * (s * s) := by group
      _ = x := by rw [hs2]; simp
  -- a * x is a fixed point of conjugation by s
  have hfix : s * (a * x) * s⁻¹ = a * x := by
    have h1 : s * (a * x) * s⁻¹ = (s * a * s⁻¹) * (s * x * s⁻¹) := by group
    have h2 : s * a * s⁻¹ = x := by rw [ha]; exact hconj
    have h3 : s * x * s⁻¹ = a := ha.symm
    rw [h1, h2, h3]
    exact hcomm x hx a haT
  have hone : a * x = 1 := hfpf (a * x) hmem hfix
  rw [ha]
  exact eq_inv_of_mul_eq_one_left hone

end Work.ThmF.ChV3.Prove
