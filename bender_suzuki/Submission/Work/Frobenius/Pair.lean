import Mathlib
import Submission.Work.Frobenius.Char

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Bilinearity of the trace pairing `charPair`

`Work.Frobenius.charPair` is linear in each variable (no complex conjugation appears).
This module records the API used by the Frobenius-group character arguments, together
with the subgroup version `charPairOn` which is written as a sum over the ambient group
so that no `Fintype` instance for the subgroup is needed in statements.
-/

@[expose] public section

noncomputable section

open Classical

namespace Work.Frobenius

variable {G : Type*} [Group G] [Fintype G]

section Linear

@[simp]
theorem charPair_zero_left (g : G → ℂ) : charPair (0 : G → ℂ) g = 0 := by
  simp [charPair]

@[simp]
theorem charPair_zero_right (f : G → ℂ) : charPair f (0 : G → ℂ) = 0 := by
  simp [charPair]

theorem charPair_add_left (f₁ f₂ g : G → ℂ) :
    charPair (f₁ + f₂) g = charPair f₁ g + charPair f₂ g := by
  simp only [charPair_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem charPair_add_right (f g₁ g₂ : G → ℂ) :
    charPair f (g₁ + g₂) = charPair f g₁ + charPair f g₂ := by
  simp only [charPair_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, mul_add]

theorem charPair_smul_left (c : ℂ) (f g : G → ℂ) :
    charPair (c • f) g = c * charPair f g := by
  simp only [charPair_apply, Pi.smul_apply, smul_eq_mul]
  have h : (∑ x : G, (c * f x) * g x⁻¹) = c * ∑ x : G, f x * g x⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [h]
  ring

theorem charPair_smul_right (c : ℂ) (f g : G → ℂ) :
    charPair f (c • g) = c * charPair f g := by
  simp only [charPair_apply, Pi.smul_apply, smul_eq_mul]
  have h : (∑ x : G, f x * (c * g x⁻¹)) = c * ∑ x : G, f x * g x⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [h]
  ring

@[simp]
theorem charPair_neg_left (f g : G → ℂ) : charPair (-f) g = -charPair f g := by
  rw [show (-f : G → ℂ) = (-1 : ℂ) • f by simp, charPair_smul_left]
  ring

@[simp]
theorem charPair_neg_right (f g : G → ℂ) : charPair f (-g) = -charPair f g := by
  rw [show (-g : G → ℂ) = (-1 : ℂ) • g by simp, charPair_smul_right]
  ring

theorem charPair_sub_left (f₁ f₂ g : G → ℂ) :
    charPair (f₁ - f₂) g = charPair f₁ g - charPair f₂ g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, charPair_add_left, charPair_neg_left]

theorem charPair_sub_right (f g₁ g₂ : G → ℂ) :
    charPair f (g₁ - g₂) = charPair f g₁ - charPair f g₂ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, charPair_add_right, charPair_neg_right]

theorem charPair_sum_left {ι : Type*} (s : Finset ι) (F : ι → G → ℂ) (g : G → ℂ) :
    charPair (∑ i ∈ s, F i) g = ∑ i ∈ s, charPair (F i) g := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, charPair_add_left, ih]

theorem charPair_sum_right {ι : Type*} (s : Finset ι) (F : ι → G → ℂ) (f : G → ℂ) :
    charPair f (∑ i ∈ s, F i) = ∑ i ∈ s, charPair f (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, charPair_add_right, ih]

theorem charPair_sum_smul_left {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → G → ℂ)
    (g : G → ℂ) : charPair (∑ i ∈ s, c i • F i) g = ∑ i ∈ s, c i * charPair (F i) g := by
  rw [charPair_sum_left]
  exact Finset.sum_congr rfl fun i _ => charPair_smul_left _ _ _

theorem charPair_sum_smul_right {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → G → ℂ)
    (f : G → ℂ) : charPair f (∑ i ∈ s, c i • F i) = ∑ i ∈ s, c i * charPair f (F i) := by
  rw [charPair_sum_right]
  exact Finset.sum_congr rfl fun i _ => charPair_smul_right _ _ _

/-- Expansion of the pairing of two differences of scalar multiples. -/
theorem charPair_sub_smul_sub_smul (f₁ f₂ g₁ g₂ : G → ℂ) (c d : ℂ) :
    charPair (f₁ - c • g₁) (f₂ - d • g₂)
      = charPair f₁ f₂ - d * charPair f₁ g₂ - c * charPair g₁ f₂
        + c * d * charPair g₁ g₂ := by
  rw [charPair_sub_left, charPair_sub_right, charPair_sub_right, charPair_smul_right,
    charPair_smul_left, charPair_smul_right, charPair_smul_left]
  ring

/-- Expansion of the pairing of two sums of scalar multiples. -/
theorem charPair_add_smul_add_smul (f₁ f₂ g₁ g₂ : G → ℂ) (c d : ℂ) :
    charPair (f₁ + c • g₁) (f₂ + d • g₂)
      = charPair f₁ f₂ + d * charPair f₁ g₂ + c * charPair g₁ f₂
        + c * d * charPair g₁ g₂ := by
  rw [charPair_add_left, charPair_add_right, charPair_add_right, charPair_smul_right,
    charPair_smul_left, charPair_smul_right, charPair_smul_left]
  ring

/-- The trace pairing is symmetric. -/
theorem charPair_comm (f g : G → ℂ) : charPair f g = charPair g f := by
  simp only [charPair_apply]
  congr 1
  have h : (∑ x : G, g x * f x⁻¹) = ∑ x : G, f x * g x⁻¹ := by
    rw [← Equiv.sum_comp (Equiv.inv G) (fun x : G => g x * f x⁻¹)]
    simp [mul_comm]
  rw [h]

end Linear

end Work.Frobenius
