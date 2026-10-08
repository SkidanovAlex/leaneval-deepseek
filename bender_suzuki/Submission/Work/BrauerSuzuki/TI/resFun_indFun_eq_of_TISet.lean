import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.Induction.Defs
import Submission.Work.Induction.indFun_TI_apply
import Submission.Work.CharCore.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.TI

/-- For a TI set `S` with normalizer `H` (Dade 5.10) and a class function `φ` on `H` with
support contained in `S`, the induced function `Ind_H^G φ` agrees with `φ` at every
`h ∈ H` with `h ∈ S`: `Ind_H^G φ (h) = φ h`.

Indeed, in the defining sum `Ind_H^G φ (h) = |H|⁻¹ ∑_{x : x h x⁻¹ ∈ H} φ (x h x⁻¹)`, an
element `x ∉ H` can only contribute when `x h x⁻¹ ∈ H`, and then `x h x⁻¹ ∈ S` would force
(by TI) `x ∈ H`; hence for `x ∉ H` the value `φ (x h x⁻¹)` vanishes.  The elements `x ∈ H`
contribute `φ h` each (class function), whence the sum is `|H| · φ h`. -/
theorem resFun_indFun_eq_of_TISet {G : Type*} [Group G] [Fintype G] {S : Set G} {H : Subgroup G}
    (hTI : Work.BrauerSuzuki.IsTISet S H) {φ : H → ℂ} (hφ : Work.CharCore.IsClassFun φ)
    (hsup : Work.BrauerSuzuki.SupportLeSub φ S) {h : H} (hh : (h : G) ∈ S) :
    Work.Induction.indFun H φ (h : G) = φ h := by
  classical
  -- An element `x ∉ H` conjugates no `h ∈ S` back into `S` (TI property).
  have hnotMem : ∀ x : G, x ∉ H → x * (h : G) * x⁻¹ ∉ S := by
    intro x hx hconj
    have hxinv : x⁻¹ ∉ H := fun hxin => hx (by simpa using H.inv_mem hxin)
    exact (hTI.conj_disjoint hxinv hconj hh) (by group)
  -- Each summand of the induction formula is `φ h` for `x ∈ H` and `0` for `x ∉ H`.
  have hstep : ∀ x : G,
      (if hx : x * (h : G) * x⁻¹ ∈ H then φ ⟨x * (h : G) * x⁻¹, hx⟩ else 0)
        = (if hx : x ∈ H then φ h else 0) := by
    intro x
    by_cases hx : x ∈ H
    · have hxH : x * (h : G) * x⁻¹ ∈ H := H.mul_mem (H.mul_mem hx h.2) (H.inv_mem hx)
      rw [dite_eq_left hxH, dite_eq_left hx]
      have hkey : (⟨x * (h : G) * x⁻¹, hxH⟩ : H) = ⟨x, hx⟩ * h * ⟨x, hx⟩⁻¹ := by
        ext
        simp [Subgroup.coe_mul]
      rw [hkey]
      exact hφ h ⟨x, hx⟩
    · rw [dite_eq_right hx]
      by_cases hxH : x * (h : G) * x⁻¹ ∈ H
      · rw [dite_eq_left hxH]
        exact hsup ⟨x * (h : G) * x⁻¹, hxH⟩ (hnotMem x hx)
      · rw [dite_eq_right hxH]
  rw [Work.Induction.indFun_apply_def, Finset.sum_congr rfl (fun x _ => hstep x)]
  -- The sum is the constant sum over `H`.
  have hsum : (∑ x : G, (if hx : x ∈ H then φ h else 0)) = (Nat.card H : ℂ) * φ h := by
    have h₁ : (∑ x : G, (if hx : x ∈ H then φ h else 0))
        = ∑ x : G, dite (x ∈ H) (fun _ => φ h) (fun _ => 0) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hx : x ∈ H <;> simp [hx]
    rw [h₁, Work.Induction.sum_dite_mem_subgroup H (fun _ => φ h)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  rw [hsum]
  have hne0 : (Nat.card H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  rw [← mul_assoc, inv_mul_cancel₀ hne0, one_mul]

end Work.BrauerSuzuki.TI
