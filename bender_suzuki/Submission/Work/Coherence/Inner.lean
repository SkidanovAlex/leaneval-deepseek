import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The character inner product on complex valued functions on a finite group

`Work.CharLib.cfInner` (in `Submission/Work/CharLib/`) is declared for `G : Type` only, i.e. it
is monomorphic in the universe of `G`.  The coherence area needs the inner product at an
arbitrary universe, so we restate the same formula here at `G : Type u` and record the
compatibility lemma `Work.Coherence.charLib_cfInner`.

Everything else in `Submission/Work/Coherence/` uses *this* `cfInner`.
-/

noncomputable section

open Classical

namespace Work.Coherence

universe u

variable {G : Type u}

/-- The normalised inner product of two complex valued functions on a finite group,
`(1/|G|) ∑_x f x * conj (g x)`, linear in the first argument and conjugate linear in the
second.  Identical to `Work.CharLib.cfInner`, but universe polymorphic. -/
def cfInner [Fintype G] (f g : G → ℂ) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ x, f x * starRingEnd ℂ (g x)

@[simp] theorem cfInner_apply [Fintype G] (f g : G → ℂ) :
    cfInner f g = (Fintype.card G : ℂ)⁻¹ * ∑ x, f x * starRingEnd ℂ (g x) := rfl

@[simp] theorem cfInner_zero_left [Fintype G] (g : G → ℂ) : cfInner (0 : G → ℂ) g = 0 := by
  simp [cfInner]

@[simp] theorem cfInner_zero_right [Fintype G] (f : G → ℂ) : cfInner f (0 : G → ℂ) = 0 := by
  simp [cfInner]

theorem cfInner_add_left [Fintype G] (f₁ f₂ g : G → ℂ) :
    cfInner (f₁ + f₂) g = cfInner f₁ g + cfInner f₂ g := by
  simp only [cfInner]
  simp_rw [Pi.add_apply, add_mul]
  rw [Finset.sum_add_distrib, mul_add]

theorem cfInner_add_right [Fintype G] (f g₁ g₂ : G → ℂ) :
    cfInner f (g₁ + g₂) = cfInner f g₁ + cfInner f g₂ := by
  simp only [cfInner]
  simp_rw [Pi.add_apply, map_add, mul_add]
  rw [Finset.sum_add_distrib, mul_add]

theorem cfInner_smul_left [Fintype G] (c : ℂ) (f g : G → ℂ) :
    cfInner (c • f) g = c * cfInner f g := by
  simp only [cfInner, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  conv_rhs => rw [← mul_assoc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem cfInner_smul_right [Fintype G] (c : ℂ) (f g : G → ℂ) :
    cfInner f (c • g) = starRingEnd ℂ c * cfInner f g := by
  have key : ∀ x : G,
      f x * starRingEnd ℂ ((c • g) x) = starRingEnd ℂ c * (f x * starRingEnd ℂ (g x)) := by
    intro x; simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
  simp only [cfInner, key]
  rw [Finset.mul_sum]
  conv_rhs => rw [← mul_assoc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

@[simp] theorem cfInner_neg_left [Fintype G] (f g : G → ℂ) : cfInner (-f) g = -cfInner f g := by
  simp only [cfInner, Pi.neg_apply, neg_mul]
  rw [Finset.sum_neg_distrib, mul_neg]

@[simp] theorem cfInner_neg_right [Fintype G] (f g : G → ℂ) : cfInner f (-g) = -cfInner f g := by
  simp only [cfInner, Pi.neg_apply, map_neg, mul_neg]
  rw [Finset.sum_neg_distrib, mul_neg]

theorem cfInner_sub_left [Fintype G] (f₁ f₂ g : G → ℂ) :
    cfInner (f₁ - f₂) g = cfInner f₁ g - cfInner f₂ g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, cfInner_add_left, cfInner_neg_left]

theorem cfInner_sub_right [Fintype G] (f g₁ g₂ : G → ℂ) :
    cfInner f (g₁ - g₂) = cfInner f g₁ - cfInner f g₂ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, cfInner_add_right, cfInner_neg_right]

/-- `cfInner` is conjugate symmetric. -/
theorem cfInner_conj_symm [Fintype G] (f g : G → ℂ) :
    cfInner f g = starRingEnd ℂ (cfInner g f) := by
  have key : ∀ x : G,
      starRingEnd ℂ (g x * starRingEnd ℂ (f x)) = f x * starRingEnd ℂ (g x) := by
    intro x
    rw [map_mul, starRingEnd_self_apply, mul_comm]
  rw [cfInner_apply, cfInner_apply, map_mul, map_inv₀, map_natCast, map_sum]
  simp only [key]

theorem cfInner_sum_left [Fintype G] {ι : Type*} (s : Finset ι) (F : ι → G → ℂ) (g : G → ℂ) :
    cfInner (∑ i ∈ s, F i) g = ∑ i ∈ s, cfInner (F i) g := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cfInner_add_left, ih]

theorem cfInner_sum_right [Fintype G] {ι : Type*} (s : Finset ι) (F : ι → G → ℂ)
    (f : G → ℂ) :
    cfInner f (∑ i ∈ s, F i) = ∑ i ∈ s, cfInner f (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cfInner_add_right, ih]

theorem cfInner_zsmul_left [Fintype G] (n : ℤ) (f g : G → ℂ) :
    cfInner (n • f) g = (n : ℂ) * cfInner f g := by
  rw [← Int.cast_smul_eq_zsmul ℂ n f, cfInner_smul_left]

theorem cfInner_zsmul_right [Fintype G] (n : ℤ) (f g : G → ℂ) :
    cfInner f (n • g) = (n : ℂ) * cfInner f g := by
  rw [← Int.cast_smul_eq_zsmul ℂ n g, cfInner_smul_right, map_intCast]

/-- Expansion of `cfInner` of two finite linear combinations. -/
theorem cfInner_sum_smul [Fintype G] {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (u : ι → G → ℂ) (b : ι → ℂ) (v : ι → G → ℂ) :
    cfInner (∑ x ∈ s, a x • u x) (∑ y ∈ s, b y • v y) =
      ∑ x ∈ s, ∑ y ∈ s, a x * starRingEnd ℂ (b y) * cfInner (u x) (v y) := by
  rw [cfInner_sum_left]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [cfInner_smul_left, cfInner_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [cfInner_smul_right]
  ring

/-- `f` is a class function on `G` (universe polymorphic version of
`Work.CharLib.IsClassFun`). -/
def IsClassFun [Group G] (f : G → ℂ) : Prop := ∀ g h : G, f (h * g * h⁻¹) = f g

@[simp] theorem isClassFun_zero [Group G] : IsClassFun (0 : G → ℂ) := fun _ _ => rfl

@[simp] theorem isClassFun_const [Group G] (c : ℂ) : IsClassFun (fun _ : G => c) :=
  fun _ _ => rfl

theorem IsClassFun.add [Group G] {f₁ f₂ : G → ℂ} (hf₁ : IsClassFun f₁) (hf₂ : IsClassFun f₂) :
    IsClassFun (f₁ + f₂) := fun g h => by simp only [Pi.add_apply, hf₁ g h, hf₂ g h]

theorem IsClassFun.neg [Group G] {f : G → ℂ} (hf : IsClassFun f) : IsClassFun (-f) :=
  fun g h => by simp only [Pi.neg_apply, hf g h]

theorem IsClassFun.sub [Group G] {f₁ f₂ : G → ℂ} (hf₁ : IsClassFun f₁) (hf₂ : IsClassFun f₂) :
    IsClassFun (f₁ - f₂) := hf₁.add hf₂.neg

theorem IsClassFun.smul [Group G] (c : ℂ) {f : G → ℂ} (hf : IsClassFun f) :
    IsClassFun (c • f) := fun g h => by simp only [Pi.smul_apply, hf g h]

theorem IsClassFun.sum [Group G] {ι : Type*} (s : Finset ι) (F : ι → G → ℂ)
    (h : ∀ i ∈ s, IsClassFun (F i)) : IsClassFun (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The conjugate of a class function is a class function. -/
theorem IsClassFun.conj [Group G] {f : G → ℂ} (hf : IsClassFun f) :
    IsClassFun (fun g => starRingEnd ℂ (f g)) := fun g h => by simp only [hf g h]

end Work.Coherence
