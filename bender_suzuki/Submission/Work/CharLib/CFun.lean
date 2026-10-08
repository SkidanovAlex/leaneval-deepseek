import Submission.Work.CharLib.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Basic API for `cfInner` and `IsClassFun`

Bilinearity of `cfInner` (linear in the first variable, conjugate linear in the second),
conjugate symmetry, and closure properties of class functions.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Classical Finset

namespace Work.CharLib

variable {G : Type} [Group G] [Fintype G]

section Inner

@[simp] theorem cfInner_apply (f g : G → ℂ) :
    cfInner f g = (Fintype.card G : ℂ)⁻¹ * ∑ x, f x * starRingEnd ℂ (g x) := rfl

@[simp] theorem cfInner_zero_left (g : G → ℂ) : cfInner (0 : G → ℂ) g = 0 := by
  simp [cfInner]

@[simp] theorem cfInner_zero_right (f : G → ℂ) : cfInner f (0 : G → ℂ) = 0 := by
  simp [cfInner]

theorem cfInner_add_left (f₁ f₂ g : G → ℂ) :
    cfInner (f₁ + f₂) g = cfInner f₁ g + cfInner f₂ g := by
  simp only [cfInner]
  simp_rw [Pi.add_apply, add_mul]
  rw [Finset.sum_add_distrib, mul_add]

theorem cfInner_add_right (f g₁ g₂ : G → ℂ) :
    cfInner f (g₁ + g₂) = cfInner f g₁ + cfInner f g₂ := by
  simp only [cfInner]
  simp_rw [Pi.add_apply, map_add, mul_add]
  rw [Finset.sum_add_distrib, mul_add]

theorem cfInner_smul_left (c : ℂ) (f g : G → ℂ) :
    cfInner (c • f) g = c * cfInner f g := by
  simp only [cfInner, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  conv_rhs => rw [← mul_assoc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem cfInner_smul_right (c : ℂ) (f g : G → ℂ) :
    cfInner f (c • g) = starRingEnd ℂ c * cfInner f g := by
  have key : ∀ x : G,
      f x * starRingEnd ℂ ((c • g) x) = starRingEnd ℂ c * (f x * starRingEnd ℂ (g x)) := by
    intro x; simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
  simp only [cfInner, key]
  rw [Finset.mul_sum]
  conv_rhs => rw [← mul_assoc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

@[simp] theorem cfInner_neg_left (f g : G → ℂ) : cfInner (-f) g = -cfInner f g := by
  simp only [cfInner, Pi.neg_apply, neg_mul]
  rw [Finset.sum_neg_distrib, mul_neg]

@[simp] theorem cfInner_neg_right (f g : G → ℂ) : cfInner f (-g) = -cfInner f g := by
  simp only [cfInner, Pi.neg_apply, map_neg, mul_neg]
  rw [Finset.sum_neg_distrib, mul_neg]

theorem cfInner_sub_left (f₁ f₂ g : G → ℂ) :
    cfInner (f₁ - f₂) g = cfInner f₁ g - cfInner f₂ g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, cfInner_add_left, cfInner_neg_left]

theorem cfInner_sub_right (f g₁ g₂ : G → ℂ) :
    cfInner f (g₁ - g₂) = cfInner f g₁ - cfInner f g₂ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, cfInner_add_right, cfInner_neg_right]

/-- `cfInner` is conjugate symmetric. -/
theorem cfInner_conj_symm (f g : G → ℂ) : cfInner f g = starRingEnd ℂ (cfInner g f) := by
  have key : ∀ x : G,
      starRingEnd ℂ (g x * starRingEnd ℂ (f x)) = f x * starRingEnd ℂ (g x) := by
    intro x
    rw [map_mul, starRingEnd_self_apply, mul_comm]
  rw [cfInner_apply, cfInner_apply, map_mul, map_inv₀, map_natCast, map_sum]
  simp only [key]

theorem cfInner_sum_left {ι : Type*} (s : Finset ι) (F : ι → G → ℂ) (g : G → ℂ) :
    cfInner (∑ i ∈ s, F i) g = ∑ i ∈ s, cfInner (F i) g := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cfInner_add_left, ih]

theorem cfInner_sum_right {ι : Type*} (s : Finset ι) (F : ι → G → ℂ) (f : G → ℂ) :
    cfInner f (∑ i ∈ s, F i) = ∑ i ∈ s, cfInner f (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cfInner_add_right, ih]

theorem cfInner_sum_smul_left {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → G → ℂ)
    (g : G → ℂ) :
    cfInner (∑ i ∈ s, c i • F i) g = ∑ i ∈ s, c i * cfInner (F i) g := by
  classical
  rw [cfInner_sum_left]
  exact Finset.sum_congr rfl fun i _ => cfInner_smul_left _ _ _

theorem cfInner_sum_smul_right {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → G → ℂ)
    (f : G → ℂ) :
    cfInner f (∑ i ∈ s, c i • F i) = ∑ i ∈ s, starRingEnd ℂ (c i) * cfInner f (F i) := by
  classical
  rw [cfInner_sum_right]
  exact Finset.sum_congr rfl fun i _ => cfInner_smul_right _ _ _

end Inner

section ClassFun

variable {f f₁ f₂ : G → ℂ}

theorem isClassFun_iff {f : G → ℂ} :
    IsClassFun f ↔ ∀ g h : G, f (h * g * h⁻¹) = f g := Iff.rfl

@[simp] theorem isClassFun_zero : IsClassFun (0 : G → ℂ) := fun _ _ => rfl

@[simp] theorem isClassFun_const (c : ℂ) : IsClassFun (fun _ : G => c) := fun _ _ => rfl

theorem IsClassFun.add (hf₁ : IsClassFun f₁) (hf₂ : IsClassFun f₂) : IsClassFun (f₁ + f₂) :=
  fun g h => by simp only [Pi.add_apply, hf₁ g h, hf₂ g h]

theorem IsClassFun.neg (hf : IsClassFun f) : IsClassFun (-f) :=
  fun g h => by simp only [Pi.neg_apply, hf g h]

theorem IsClassFun.sub (hf₁ : IsClassFun f₁) (hf₂ : IsClassFun f₂) : IsClassFun (f₁ - f₂) :=
  fun g h => by simp only [Pi.sub_apply, hf₁ g h, hf₂ g h]

theorem IsClassFun.mul (hf₁ : IsClassFun f₁) (hf₂ : IsClassFun f₂) : IsClassFun (f₁ * f₂) :=
  fun g h => by simp only [Pi.mul_apply, hf₁ g h, hf₂ g h]

theorem IsClassFun.smul (c : ℂ) (hf : IsClassFun f) : IsClassFun (c • f) :=
  fun g h => by simp only [Pi.smul_apply, hf g h]

theorem IsClassFun.sum {ι : Type*} (s : Finset ι) (F : ι → G → ℂ)
    (h : ∀ i ∈ s, IsClassFun (F i)) : IsClassFun (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The conjugate of a class function is a class function. -/
theorem IsClassFun.conj (hf : IsClassFun f) :
    IsClassFun (fun g => starRingEnd ℂ (f g)) :=
  fun g h => by simp only [hf g h]

/-- Characters of finite dimensional complex representations are class functions. -/
theorem isClassFun_char (V : FDRep ℂ G) : IsClassFun V.character :=
  fun g h => FDRep.char_conj V g h

end ClassFun

end Work.CharLib
