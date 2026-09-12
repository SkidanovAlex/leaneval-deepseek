import Mathlib.NumberTheory.NumberField.House

/-!
# Conjugates, house, and phases: dictionary lemmas

Given a number field `K` and `α : K`, the complex values `σ α` for
`σ : K →+* ℂ` are the conjugates of `α`.  We record basic facts about
`NumberField.house α` (the maximal modulus of these conjugates) and
about the *phases* `(σ α).arg`.
-/

noncomputable section

open scoped Complex Polynomial

namespace Submission.Conjugates

variable {K : Type*} [Field K] [NumberField K]

/-- The set of distinct conjugates of `α`, i.e. the values `σ α` for all
complex embeddings `σ`. -/
def conjugateValues (α : K) : Finset ℂ :=
  Finset.univ.image fun σ : K →+* ℂ ↦ σ α

/-- The set of distinct principal arguments of the conjugates of `α`. -/
def argSet (α : K) : Finset ℝ := (conjugateValues α).image fun z : ℂ => z.arg

/-- The cardinality appearing in Dimitrov's bound equals the number of
distinct phases of the conjugates. -/
theorem argSet_card (α : K) :
    (Finset.univ.image fun σ : K →+* ℂ ↦ (σ α).arg).card = (argSet α).card := by
  classical
  unfold argSet conjugateValues
  rw [Finset.image_image]
  rfl

/-- The house of `α` is the maximum modulus of its conjugates. -/
theorem house_eq_sup_conj (α : K) :
    NumberField.house α = ((conjugateValues α).sup (fun z : ℂ => ‖z‖₊) : NNReal) := by
  classical
  rw [NumberField.house_eq_sup']
  rw [Finset.sup'_eq_sup]
  congr 1
  unfold conjugateValues
  rw [Finset.sup_image]
  rfl

/-- `house` is at least the modulus of every conjugate. -/
theorem norm_conj_le_house (α : K) (σ : K →+* ℂ) : ‖σ α‖ ≤ NumberField.house α := by
  have hz : σ α ∈ conjugateValues α := by
    unfold conjugateValues
    exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ σ, rfl⟩
  have h := Finset.le_sup (f := fun z : ℂ => ‖z‖₊) hz
  rw [house_eq_sup_conj]
  exact NNReal.coe_le_coe.mpr h

/-- A conjugate attaining the maximal modulus exists. -/
theorem exists_conj_house (α : K) :
    ∃ σ : K →+* ℂ, NumberField.house α = ‖σ α‖ := by
  classical
  have hne : (conjugateValues α).Nonempty := by
    unfold conjugateValues
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  rcases Finset.exists_mem_eq_sup (s := conjugateValues α) (f := fun z : ℂ => ‖z‖₊) hne with ⟨z, hz, hzsup⟩
  rcases Finset.mem_image.mp hz with ⟨σ, hσ, rfl⟩
  refine ⟨σ, ?_⟩
  rw [house_eq_sup_conj, hzsup]
  rfl

/-- Nonzero algebraic integers have house at least 1. -/
theorem one_le_house_of_isIntegral_ne_zero {α : K} (hα : IsIntegral ℤ α) (hα0 : α ≠ 0) :
    1 ≤ NumberField.house α :=
  NumberField.one_le_house_of_isIntegral hα hα0

end Submission.Conjugates

end
