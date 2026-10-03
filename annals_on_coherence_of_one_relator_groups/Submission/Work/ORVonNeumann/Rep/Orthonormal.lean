/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The orthonormal family `δ_g` of `ℓ²(G)`

`deltaG g` (`Submission.Work.ORVonNeumann.Rep.delta1_separating`) is the indicator function of
the singleton `{g}` in `ℓ²(G) = L²(G, #)`.  Since the counting measure gives each point measure
`1`, the family `g ↦ δ_g` is orthonormal:

`⟪δ_g, δ_h⟫ = if g = h then 1 else 0`,  `‖δ_g‖ = 1`.

This is the family in which the trace `τ a = ⟪δ₁, a δ₁⟫` is computed and whose closed span is
all of `ℓ²(G)` (`Submission.Work.ORVonNeumann.Rep.DenseSpan`).

## Main results

* `Work.ORVonNeumann.Rep.norm_deltaG` — `‖δ_g‖ = 1`;
* `Work.ORVonNeumann.Rep.inner_deltaG_self`, `Work.ORVonNeumann.Rep.inner_deltaG_of_ne` —
  the two cases of orthonormality (no decidability hypothesis);
* `Work.ORVonNeumann.Rep.inner_deltaG_deltaG` — `⟪δ_g, δ_h⟫ = if g = h then 1 else 0`;
* `Work.ORVonNeumann.Rep.orthonormal_deltaG` — the family is orthonormal;
* `Work.ORVonNeumann.Rep.rightRegOp_deltaG` — the right regular representation permutes the
  family: `ρ_k δ_g = δ_{g k⁻¹}`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep
import Submission.Work.ORVonNeumann.Rep.delta1_separating

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORVonNeumann.Rep

open MeasureTheory

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- `δ_g` has norm one: it is the indicator of a set of measure one. -/
theorem norm_deltaG (g : G) : ‖deltaG g‖ = 1 := by
  rw [deltaG, MeasureTheory.norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [MeasureTheory.Measure.real, MeasureTheory.Measure.count_singleton,
    ENNReal.toReal_one, norm_one, one_mul, Real.one_rpow]

/-- The measure of `{g} ∩ {h}` when `g = h`: it is `1`. -/
theorem real_count_inter_singleton_self (g : G) :
    (Measure.count : Measure G).real ({g} ∩ {g}) = 1 := by
  simp [MeasureTheory.Measure.real]

/-- The measure of `{g} ∩ {h}` when `g ≠ h`: it is `0`. -/
theorem real_count_inter_singleton_of_ne {g h : G} (hgh : g ≠ h) :
    (Measure.count : Measure G).real ({g} ∩ {h}) = 0 := by
  have hemp : ({g} : Set G) ∩ {h} = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
      not_and]
    exact fun hx hy => hgh (hx.symm.trans hy)
  rw [hemp]
  simp [MeasureTheory.Measure.real]

/-- The inner product of two basis vectors, in terms of the measure of the intersection. -/
private theorem inner_deltaG_eq (g h : G) :
    inner ℂ (deltaG g) (deltaG h)
      = (Measure.count : Measure G).real ({g} ∩ {h}) • inner ℂ (1 : ℂ) (1 : ℂ) := by
  have hμ : ∀ x : G, (Measure.count : Measure G) ({x} : Set G) ≠ ⊤ := by
    intro x
    rw [Measure.count_singleton]
    exact ENNReal.one_ne_top
  rw [deltaG, deltaG]
  exact MeasureTheory.L2.inner_indicatorConstLp_indicatorConstLp (s := {g}) (t := {h})
    (MeasurableSet.singleton g) (MeasurableSet.singleton h) (hμ g) (hμ h) 1 1

/-- `⟪δ_g, δ_g⟫ = 1`. -/
theorem inner_deltaG_self (g : G) : inner ℂ (deltaG g) (deltaG g) = 1 := by
  rw [inner_deltaG_eq, real_count_inter_singleton_self]
  simp

/-- `⟪δ_g, δ_h⟫ = 0` for `g ≠ h`. -/
theorem inner_deltaG_of_ne {g h : G} (hgh : g ≠ h) : inner ℂ (deltaG g) (deltaG h) = 0 := by
  rw [inner_deltaG_eq, real_count_inter_singleton_of_ne hgh]
  simp

/-- The family `δ_g` is orthonormal: `⟪δ_g, δ_h⟫ = if g = h then 1 else 0`. -/
theorem inner_deltaG_deltaG [DecidableEq G] (g h : G) :
    inner ℂ (deltaG g) (deltaG h) = if g = h then (1 : ℂ) else 0 := by
  by_cases hgh : g = h
  · rw [if_pos hgh, hgh]
    exact inner_deltaG_self h
  · rw [if_neg hgh]
    exact inner_deltaG_of_ne hgh

/-- The family `g ↦ δ_g` is orthonormal in `ℓ²(G)`. -/
theorem orthonormal_deltaG : Orthonormal ℂ (deltaG (G := G)) :=
  ⟨fun g => norm_deltaG g, fun _ _ hgh => inner_deltaG_of_ne hgh⟩

/-- The right regular representation permutes the orthonormal family: `ρ_k δ_g = δ_{g k⁻¹}`. -/
theorem rightRegOp_deltaG (k g : G) : rightRegOp k (deltaG g) = deltaG (g * k⁻¹) := by
  have h : rightRegOp (k * g⁻¹) (delta1 G) = deltaG (g * k⁻¹) := by
    simpa only [mul_inv_rev, inv_inv] using rightRegOp_inv_delta1 (G := G) ((k * g⁻¹)⁻¹)
  calc rightRegOp k (deltaG g)
      = rightRegOp k (rightRegOp g⁻¹ (delta1 G)) := by rw [rightRegOp_inv_delta1]
    _ = rightRegOp (k * g⁻¹) (delta1 G) := rightRegOp_mul_apply k g⁻¹ (delta1 G)
    _ = deltaG (g * k⁻¹) := h

end Work.ORVonNeumann.Rep
