import Mathlib
import Submission.Work.Frobenius.Char

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The class-function API used by area A8

`Work.Frobenius.IsClassFun` is conjugation invariance.  This module records the closure
properties needed by the Frobenius-group argument.
-/

@[expose] public section

noncomputable section

open Classical

namespace Work.Frobenius

variable {G : Type*} [Group G]

theorem isClassFun_iff {f : G → ℂ} : IsClassFun f ↔ ∀ g h : G, f (h * g * h⁻¹) = f g := Iff.rfl

@[simp] theorem isClassFun_zero : IsClassFun (0 : G → ℂ) := fun _ _ => rfl

@[simp] theorem isClassFun_one : IsClassFun (1 : G → ℂ) := fun _ _ => rfl

@[simp] theorem isClassFun_const (c : ℂ) : IsClassFun (fun _ : G => c) := fun _ _ => rfl

theorem IsClassFun.add {f g : G → ℂ} (hf : IsClassFun f) (hg : IsClassFun g) :
    IsClassFun (f + g) := fun g' h => by simp only [Pi.add_apply, hf g' h, hg g' h]

theorem IsClassFun.neg {f : G → ℂ} (hf : IsClassFun f) : IsClassFun (-f) :=
  fun g h => by simp only [Pi.neg_apply, hf g h]

theorem IsClassFun.sub {f g : G → ℂ} (hf : IsClassFun f) (hg : IsClassFun g) :
    IsClassFun (f - g) := fun g' h => by simp only [Pi.sub_apply, hf g' h, hg g' h]

theorem IsClassFun.smul (c : ℂ) {f : G → ℂ} (hf : IsClassFun f) : IsClassFun (c • f) :=
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

/-- The character of a representation is a class function. -/
theorem IrrRep.isClassFun (d : IrrRep G) : IsClassFun d.ρ.character :=
  fun g h => Representation.char_conj d.ρ g h

end Work.Frobenius
