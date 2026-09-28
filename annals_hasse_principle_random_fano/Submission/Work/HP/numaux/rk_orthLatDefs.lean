import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.numaux.Defs

/-!
# Rational spreading of integral lattices

This file collects the small definitions that the rank formula for the orthogonal
lattice `Work.HP.numaux.rk_orthLat` needs.

The idea: an integral lattice `Λ ⊆ ℤ^ι` gives a rational subspace `spread Λ ⊆ ℚ^ι`
(the `ℚ`-span of the rational points of `Λ`).  Two facts are used:

* `finrank ℤ Λ = finrank ℚ (spread Λ)`  (spreading out is rank preserving);
* `spread (orthLat Λ) = stdB.orthogonal (spread Λ)` where `stdB` is the standard
  bilinear form `⟨x,y⟩ = ∑ᵢ xᵢ yᵢ` on `ℚ^ι`.

Then the rank formula follows from Mathlib's `LinearMap.BilinForm.finrank_orthogonal`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace Work.HP.numaux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The canonical `ℤ`-linear map `ℤ^ι → ℚ^ι`, coordinatewise inclusion. -/
def castL : (ι → ℤ) →ₗ[ℤ] (ι → ℚ) where
  toFun v := fun i => (v i : ℚ)
  map_add' a b := by ext i; simp
  map_smul' c a := by ext i; simp

@[simp] lemma castL_apply (v : ι → ℤ) (i : ι) : castL v i = (v i : ℚ) := rfl

lemma castL_injective : Function.Injective (castL (ι := ι)) := by
  intro a b h
  funext i
  have h' : ((a i : ℤ) : ℚ) = ((b i : ℤ) : ℚ) := congrFun h i
  exact_mod_cast h'

/-- The `ℚ`-subspace of `ℚ^ι` spanned by the rational points of an integral lattice `L`. -/
def spread (L : Submodule ℤ (ι → ℤ)) : Submodule ℚ (ι → ℚ) :=
  Submodule.span ℚ ((L.map (castL (ι := ι)) : Submodule ℤ (ι → ℚ)) : Set (ι → ℚ))

lemma spread_eq_span_image (L : Submodule ℤ (ι → ℤ)) :
    spread L = Submodule.span ℚ ((castL (ι := ι)) '' (L : Set (ι → ℤ))) := by
  unfold spread
  congr 1

/-- The standard bilinear form `⟨x,y⟩ = ∑ᵢ xᵢ yᵢ` on `ℚ^ι`. -/
def stdB : LinearMap.BilinForm ℚ (ι → ℚ) :=
  LinearMap.mk₂ ℚ (fun x y => ∑ i, x i * y i)
    (fun x y z => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring)
    (fun x y z => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring)

lemma stdB_apply (x y : ι → ℚ) : stdB x y = ∑ i, x i * y i := rfl

lemma stdB_comm (x y : ι → ℚ) : stdB x y = stdB y x := by
  simp only [stdB_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end Work.HP.numaux
