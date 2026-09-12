import Mathlib.NumberTheory.NumberField.House
import Submission.Conjugates

/-!
# Dictionary: conjugates of `α` in `K` versus roots of the minimal polynomial

For `α` in a number field `K`, the values `σ α` for `σ : K →+* ℂ` are
exactly the complex roots of the minimal polynomial of `α` over `ℚ`.
This is `NumberField.Embeddings.range_eval_eq_rootSet_minpoly`.
-/

noncomputable section

open scoped Complex Polynomial
open Polynomial

namespace Submission.Dictionary

open Submission.Conjugates

variable {K : Type*} [Field K] [NumberField K]

/-- The set of conjugates equals the range of the evaluation map at `α`. -/
theorem conjugateValues_eq_range (α : K) :
    (conjugateValues α : Set ℂ) = Set.range (fun σ : K →+* ℂ => σ α) := by
  classical
  ext z
  constructor
  · intro hz
    have hz' : z ∈ conjugateValues α := by simpa using hz
    rcases Finset.mem_image.mp hz' with ⟨σ, hσ, rfl⟩
    exact ⟨σ, rfl⟩
  · intro hz
    rcases hz with ⟨σ, rfl⟩
    simp [conjugateValues]

/-- The conjugates of `α` (values of all complex embeddings) are exactly the
complex roots of the minimal polynomial of `α` over `ℚ`. -/
theorem conjugateValues_eq_rootSet (α : K) :
    (conjugateValues α : Set ℂ) = (minpoly ℚ α).rootSet ℂ := by
  rw [conjugateValues_eq_range α]
  exact NumberField.Embeddings.range_eval_eq_rootSet_minpoly K ℂ α

/-- The conjugates of `α` are closed under complex conjugation. -/
theorem conjugateValues_conj_closed (α : K) :
    (conjugateValues α).image (fun z : ℂ => star z) = conjugateValues α := by
  classical
  ext z
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨w, hw, hzw⟩
    rcases Finset.mem_image.mp hw with ⟨σ, hσ, rfl⟩
    exact Finset.mem_image.mpr ⟨(starRingEnd ℂ).comp σ, Finset.mem_univ _, by
      simp [RingHom.comp_apply, ← hzw]⟩
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨σ, hσ, rfl⟩
    refine Finset.mem_image.mpr ⟨star (σ α), ?mem, by simp⟩
    exact Finset.mem_image.mpr ⟨(starRingEnd ℂ).comp σ, Finset.mem_univ _,
      by simp [RingHom.comp_apply]⟩

/-- `0` is not a conjugate of a nonzero `α`. -/
theorem zero_not_mem_conjugateValues {α : K} (hα0 : α ≠ 0) :
    (0 : ℂ) ∉ conjugateValues α := by
  intro hz
  rcases Finset.mem_image.mp hz with ⟨σ, hσ, hσ0⟩
  exact hα0 (σ.injective (by simpa using hσ0))

/-- Every conjugate of `α` is a root of the minimal polynomial of `α`. -/
theorem conjugate_mem_rootSet_minpoly (α : K) (σ : K →+* ℂ) :
    σ α ∈ (minpoly ℚ α).rootSet ℂ := by
  rw [← conjugateValues_eq_rootSet α]
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨σ, Finset.mem_univ σ, rfl⟩)

end Submission.Dictionary

end
