import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.H2.T1Q.Basic
import Submission.Work.FTS.H2.OscSqLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2.T1Q

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The slicewise `L^∞`-`L²` estimate on the open angular interval.**  For `1 < γ ≤ 2` and
`u : ℝ → ℝ` of class `C¹` on the open interval `(0,π/2)`, with `u²` and
`(u')² sin(2θ)^{2-γ}` integrable (over `Iθ = [0,π/2]`), and for every `θ ∈ (0,π/2)`:

`u(θ)² ≤ (4/π)·∫_{Iθ} u² + (200/(γ-1))·∫_{Iθ} (u')² sin(2θ)^{2-γ}`.

This is `Work.FTS.H2.slice_sup_sq_le` (in `Submission/Work/FTS/H2/SupThetaInt.lean`) with the
regularity weakened from `ContDiffOn ℝ 1 u (Ioo (-1) (π/2+1))` (a neighbourhood of the *closed*
interval) to `ContDiffOn ℝ 1 u (Ioo 0 (π/2))` (the open interval), and with the conclusion
claimed only at the interior points `θ ∈ (0,π/2)`.  Route: `MeasureTheory.exists_le_setAverage`
on the set `Set.Ioo 0 (π/2)` (nonempty, finite measure) produces a point `θ₀ ∈ (0,π/2)` with
`u(θ₀)² ≤ (2/π)∫_{Ioo} u² = (2/π)∫_{Iθ} u²`; combine `u(θ)² ≤ 2u(θ₀)² + 2(u(θ)-u(θ₀))²` with
the oscillation bound `Work.FTS.H2.OscSqLe` applied on `uIcc θ θ₀ ⊆ (0,π/2)`. -/
theorem SliceSupOpen : ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 →
    ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn
      (fun θ => (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      Work.Spaces.Iθ →
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (u θ) ^ 2 ≤ (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
        + (200 / (Work.Spaces.gam α - 1)) * ∫ θ in Work.Spaces.Iθ,
            (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
  intro α u hα hα1 hdiff hu2 hint
  -- Step 1: a point `θ₀ ∈ (0,π/2)` where `u²` is below its mean, via `exists_le_setAverage`.
  have hs : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hintIoo : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu2.mono_set hs
  have hvol : volume (Set.Ioo (0 : ℝ) (Real.pi / 2)) ≠ 0 := by
    rw [Real.volume_Ioo]
    simp only [sub_zero]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have htop : volume (Set.Ioo (0 : ℝ) (Real.pi / 2)) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  obtain ⟨θ₀, hθ₀, hle⟩ := MeasureTheory.exists_le_setAverage hvol htop hintIoo
  have havg : ⨍ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (u x) ^ 2
      = (2 / Real.pi) * ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (u x) ^ 2 := by
    rw [MeasureTheory.setAverage_eq, MeasureTheory.measureReal_def, Real.volume_Ioo]
    simp only [sub_zero, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ Real.pi / 2),
      smul_eq_mul]
    congr 1
    field_simp
  rw [havg] at hle
  have hmono : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (u x) ^ 2)
      ≤ ∫ x in Work.Spaces.Iθ, (u x) ^ 2 := by
    refine MeasureTheory.setIntegral_mono_set hu2 ?_ ?_
    · exact Filter.Eventually.of_forall fun x => by positivity
    · exact Filter.Eventually.of_forall fun x hx => hs hx
  have hθ₀le : (u θ₀) ^ 2 ≤ (2 / Real.pi) * ∫ x in Work.Spaces.Iθ, (u x) ^ 2 := by
    calc (u θ₀) ^ 2 ≤ (2 / Real.pi) * ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (u x) ^ 2 := hle
      _ ≤ (2 / Real.pi) * ∫ x in Work.Spaces.Iθ, (u x) ^ 2 := by
          apply mul_le_mul_of_nonneg_left hmono
          positivity
  intro θ hθ
  -- Step 2: the oscillation bound `OscSqLe` for `h = u` between `θ` and `θ₀`.
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hθ₀Iθ : θ₀ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ₀.1, le_of_lt hθ₀.2⟩
  have hsub : Set.uIcc θ θ₀ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [Set.uIcc]
    intro x hx
    refine ⟨lt_of_lt_of_le (lt_min hθ.1 hθ₀.1) hx.1,
      lt_of_le_of_lt hx.2 (max_lt hθ.2 hθ₀.2)⟩
  have hder : ∀ x ∈ Set.uIcc θ θ₀, HasDerivAt u (deriv u x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hsub hx
    have hd : DifferentiableAt ℝ u x :=
      (hdiff.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hx')
    exact hd.hasDerivAt
  have hcont : ContinuousOn (deriv u) (Set.uIcc θ θ₀) :=
    (hdiff.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hsub
  have hosc := Work.FTS.H2.OscSqLe α hα hα1 u hθIθ hθ₀Iθ hder hcont hint
  -- Step 3: `u θ = (u θ - u θ₀) + u θ₀` and the elementary square bound `add_sq_le`.
  have hsq : (u θ) ^ 2 ≤ 2 * (u θ - u θ₀) ^ 2 + 2 * (u θ₀) ^ 2 := by
    have h : ((u θ - u θ₀) + u θ₀) ^ 2 ≤ 2 * ((u θ - u θ₀) ^ 2 + (u θ₀) ^ 2) := add_sq_le
    have e : u θ = (u θ - u θ₀) + u θ₀ := by ring
    rw [e]
    linarith
  calc (u θ) ^ 2
      ≤ 2 * (u θ - u θ₀) ^ 2 + 2 * (u θ₀) ^ 2 := hsq
    _ ≤ 2 * ((100 / (Work.Spaces.gam α - 1)) *
          ∫ σ in Work.Spaces.Iθ,
            (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
        + 2 * ((2 / Real.pi) * ∫ σ in Work.Spaces.Iθ, (u σ) ^ 2) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hosc (by norm_num)
        · exact mul_le_mul_of_nonneg_left hθ₀le (by norm_num)
    _ = (4 / Real.pi) * (∫ σ in Work.Spaces.Iθ, (u σ) ^ 2)
        + (200 / (Work.Spaces.gam α - 1)) * ∫ σ in Work.Spaces.Iθ,
            (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := by
        ring

end Work.H2.T1Q
