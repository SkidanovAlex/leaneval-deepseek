import Mathlib
import Submission.Work.EKLContract.Interfaces

/-!
# Auxiliary definitions for the class of a leafwise measure

`Work.EKLProd.PropEq ρ σ` says that the measures `ρ, σ` (on a measurable space) differ by a
nonzero *finite* scalar.  This is the relation which appears in the conclusion of
`Work.EKLProd.nuT_class_of_mem_shape`: `νT (y • x) = c • ((νT x).map (· * g⁻¹))` with
`c ≠ 0`, `c ≠ ⊤`.

The file also records the elementary calculus of `PropEq`, and the effect of the right-translation
push-forward `ρ ↦ ρ.map (· * h)`.
-/

open MeasureTheory
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLProd

/-- Two measures are *proportional* (in the strict sense of the frozen interface: nonzero finite
scalar) if one is a nonzero finite multiple of the other. -/
def PropEq {α : Type*} [MeasurableSpace α] (ρ σ : Measure α) : Prop :=
  ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ σ = c • ρ

namespace PropEq

variable {α : Type*} [MeasurableSpace α] {ρ σ τ : Measure α}

protected theorem refl (ρ : Measure α) : PropEq ρ ρ :=
  ⟨1, one_ne_zero, ENNReal.one_ne_top, (one_smul _ _).symm⟩

theorem symm (h : PropEq ρ σ) : PropEq σ ρ := by
  obtain ⟨c, hc0, hct, rfl⟩ := h
  refine ⟨c⁻¹, ENNReal.inv_ne_zero.mpr hct, ENNReal.inv_ne_top.mpr hc0, ?_⟩
  rw [smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]

theorem trans (h₁ : PropEq ρ σ) (h₂ : PropEq σ τ) : PropEq ρ τ := by
  obtain ⟨c, hc0, hct, rfl⟩ := h₁
  obtain ⟨d, hd0, hdt, rfl⟩ := h₂
  refine ⟨d * c, mul_ne_zero hd0 hc0, ENNReal.mul_ne_top hdt hct, ?_⟩
  rw [smul_smul]

theorem map {β : Type*} [MeasurableSpace β] (h : PropEq ρ σ) (f : α → β) (hf : AEMeasurable f ρ) :
    PropEq (ρ.map f) (σ.map f) := by
  obtain ⟨c, hc0, hct, rfl⟩ := h
  exact ⟨c, hc0, hct, Measure.map_smul _ hf⟩

end PropEq

/-- `PropEq` as an existential over `ℝ≥0∞`, unfolded for rewriting. -/
theorem propEq_iff {α : Type*} [MeasurableSpace α] (ρ σ : Measure α) :
    PropEq ρ σ ↔ ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ σ = c • ρ := Iff.rfl

end Work.EKLProd
