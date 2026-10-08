import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Induction.Basic`: elementary API for `indFun`

Linearity of `Work.Induction.indFun` in its argument (so that induction is a ℂ-linear map on
the space of complex functions on a subgroup), together with the basic rewrite lemmas.
-/

noncomputable section

open Classical
open scoped Pointwise

namespace Work.Induction

variable {G : Type*} [Group G] [Fintype G]

theorem indFun_zero (H : Subgroup G) : indFun H (0 : H → ℂ) = 0 := by
  ext g
  simp only [indFun, Pi.zero_apply, mul_eq_zero]
  right
  apply Finset.sum_eq_zero
  intro x _
  by_cases hp : x * g * x⁻¹ ∈ H <;> simp [hp]

theorem indFun_add (H : Subgroup G) (φ ψ : H → ℂ) :
    indFun H (φ + ψ) = indFun H φ + indFun H ψ := by
  ext g
  simp only [indFun, Pi.add_apply, ← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hp : x * g * x⁻¹ ∈ H <;> simp [hp]

theorem indFun_neg (H : Subgroup G) (φ : H → ℂ) : indFun H (-φ) = -indFun H φ := by
  ext g
  simp only [indFun, Pi.neg_apply]
  rw [← mul_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun x _ => by by_cases hp : x * g * x⁻¹ ∈ H <;> simp [hp]

theorem indFun_sub (H : Subgroup G) (φ ψ : H → ℂ) :
    indFun H (φ - ψ) = indFun H φ - indFun H ψ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, indFun_add, indFun_neg]

theorem indFun_smul (H : Subgroup G) (c : ℂ) (φ : H → ℂ) :
    indFun H (c • φ) = c • indFun H φ := by
  ext g
  simp only [indFun, Pi.smul_apply, smul_eq_mul]
  have key : ∀ x : G, (if hx : x * g * x⁻¹ ∈ H then c * φ ⟨x * g * x⁻¹, hx⟩ else 0)
      = c * (if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0) := by
    intro x
    by_cases hp : x * g * x⁻¹ ∈ H <;> simp [hp]
  simp only [key, ← Finset.mul_sum]
  ring

theorem indFun_sum {ι : Type*} (H : Subgroup G) (s : Finset ι) (F : ι → H → ℂ) :
    indFun H (∑ i ∈ s, F i) = ∑ i ∈ s, indFun H (F i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, indFun_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, indFun_add, ih]

@[simp] theorem indFun_const_smul_apply (H : Subgroup G) (c : ℂ) (φ : H → ℂ) (g : G) :
    indFun H (c • φ) g = c * indFun H φ g := by
  rw [indFun_smul]
  rfl

theorem indFun_congr (H : Subgroup G) {φ ψ : H → ℂ} (h : φ = ψ) : indFun H φ = indFun H ψ := by
  rw [h]

theorem indFun_congr_apply (H : Subgroup G) {φ ψ : H → ℂ} (h : ∀ x : H, φ x = ψ x) :
    indFun H φ = indFun H ψ := by
  ext g
  simp only [indFun]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hp : x * g * x⁻¹ ∈ H <;> simp [hp, h]

/-- The support of `indFun H φ` is contained in the conjugates of `H`: if no conjugate of `g`
lies in `H` then `indFun H φ g = 0`. -/
theorem indFun_apply_eq_zero_of_not_conj (H : Subgroup G) (φ : H → ℂ) (g : G)
    (h : ∀ x : G, x * g * x⁻¹ ∉ H) : indFun H φ g = 0 := by
  simp only [indFun]
  rw [mul_eq_zero]
  right
  apply Finset.sum_eq_zero
  intro x _
  by_cases hp : x * g * x⁻¹ ∈ H
  · exact absurd hp (h x)
  · simp [hp]

end Work.Induction
