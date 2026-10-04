import Mathlib
import Submission.Work.Diff.C.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

theorem osc_lower {α c β : ℝ} (hα0 : 0 < α) (hαπ : α < Real.pi) (hc : 0 < c)
    (hc3 : 3 * c ≤ 1)
    (hkey : 3 * c ≤ 1 - Real.cos α) (hβ : -Real.cos α ≤ β) (hβ1 : β ≤ 1)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ Real.pi - α) :
    (∀ σ ∈ Set.Icc (0 : ℝ) s, -1 + 3 * c ≤ Real.cos σ) ∧
    (∀ σ ∈ Set.Icc (0 : ℝ) s, -1 + 3 * c ≤ β * Real.sin σ) := by
  -- basic range facts
  have hpi_alpha_nonneg : 0 ≤ Real.pi - α := by linarith
  -- cos bound: on [0, s] ⊆ [0, π-α] ⊆ [0, π], cos is decreasing, cos(π-α) = -cos α
  have hcos_lower : ∀ σ ∈ Set.Icc (0 : ℝ) s, -Real.cos α ≤ Real.cos σ := by
    intro σ hσ
    have hσ0 : 0 ≤ σ := hσ.1
    have hσs : σ ≤ Real.pi - α := le_trans hσ.2 hs
    have hle : Real.pi - α ≤ Real.pi := by linarith
    have h := Real.cos_le_cos_of_nonneg_of_le_pi hσ0 hle hσs
    rwa [Real.cos_pi_sub] at h
  -- key inequality: -1 + 3c ≤ -cos α
  have hcα : -1 + 3 * c ≤ -Real.cos α := by linarith
  refine ⟨?_, ?_⟩
  · intro σ hσ
    linarith [hcos_lower σ hσ, hcα]
  · intro σ hσ
    have hσ0 : 0 ≤ σ := hσ.1
    have hσs : σ ≤ Real.pi - α := le_trans hσ.2 hs
    have hsin0 : 0 ≤ Real.sin σ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hσ0 (by linarith [hσs, hα0])
    have hsin1 : Real.sin σ ≤ 1 := Real.sin_le_one σ
    rcases le_or_gt (0:ℝ) β with hβ0 | hβ0
    · -- β ≥ 0: β sin σ ≥ 0 ≥ -1 + 3c
      have : 0 ≤ β * Real.sin σ := mul_nonneg hβ0 hsin0
      linarith
    · -- β < 0: β sin σ ≥ β ≥ -cos α ≥ -1 + 3c
      have hbs : β ≤ β * Real.sin σ := by
        have := mul_le_mul_of_nonpos_left hsin1 (le_of_lt hβ0)
        simpa using this
      linarith [hbs, hβ, hcα]
end Work.Diff.C
