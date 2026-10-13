/-
# `hBounds`: the quantitative input to the angular gap-Wirtinger estimate

For `h` of class `C²` on `[0, π/2]` vanishing at both endpoints, there is a constant `C > 0`
with

* `|h θ| ≤ C · sin (2θ)` on `[0, π/2]`, and
* `|h' θ| ≤ C` on `(0, π/2)`.

The proof has two halves.

* *Derivative bound.* `hh : ContDiffOn ℝ 2 h (Icc 0 (π/2))` gives that `derivWithin h I`
  is continuous on the compact interval `I = Icc 0 (π/2)`
  (`ContDiffOn.continuousOn_derivWithin`), hence bounded there by some `C₀`
  (`IsCompact.exists_bound_of_continuousOn`).  At an interior point `θ`, `deriv h θ` agrees
  with `derivWithin h I θ` (`derivWithin_of_mem_nhds`), so `|deriv h θ| ≤ C₀`.

* *Value bound.* The mean value inequality on the convex set `I`
  (`Convex.norm_image_sub_le_of_norm_fderivWithin_le`) applied to the pairs
  `(0, θ)` and `(π/2, θ)` gives `|h θ| ≤ C₀ · θ` and `|h θ| ≤ C₀ · (π/2 - θ)`;
  hence `|h θ| ≤ C₀ · min θ (π/2 - θ)`.  Finally `min θ (π/2 - θ) ≤ (π/4) sin (2θ)` on
  `I` (Jordan's inequality in the two halves), so `|h θ| ≤ C₀ sin (2θ)` since `sin (2θ) ≥ 0`
  and `π/4 ≤ 1`.

Taking `C = max C₀ 1` finishes.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.AngGap.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngGap

/-- On `[0, π/2]` we have `min θ (π/2 - θ) ≤ (π/4) * sin (2θ)`.

This is Jordan's inequality on the two halves of the interval: on the left half
`sin (2θ) ≥ (2/π)(2θ)`, on the right half `sin (2θ) = sin (2(π/2 - θ)) ≥ (2/π)(2(π/2 - θ))`. -/
theorem min_le_quarter_pi_mul_sin_two {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (π / 2)) :
    min θ (π / 2 - θ) ≤ π / 4 * Real.sin (2 * θ) := by
  rcases le_or_gt θ (π / 4) with hl | hr
  · have hmin : min θ (π / 2 - θ) = θ := by
      apply min_eq_left
      linarith [Real.pi_pos]
    rw [hmin]
    have hj := Real.mul_le_sin (x := 2 * θ) (by linarith [hθ.1]) (by linarith)
    calc θ = π / 4 * (2 / π * (2 * θ)) := by field_simp; ring
      _ ≤ π / 4 * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hj (by positivity)
  · have hmin : min θ (π / 2 - θ) = π / 2 - θ := by
      apply min_eq_right
      linarith [Real.pi_pos]
    rw [hmin]
    have hj := Real.mul_le_sin (x := 2 * (π / 2 - θ)) (by linarith [hθ.2]) (by linarith)
    have hsin : Real.sin (2 * (π / 2 - θ)) = Real.sin (2 * θ) := by
      rw [show 2 * (π / 2 - θ) = π - 2 * θ by ring, Real.sin_pi_sub]
    rw [hsin] at hj
    calc π / 2 - θ = π / 4 * (2 / π * (2 * (π / 2 - θ))) := by field_simp; ring
      _ ≤ π / 4 * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hj (by positivity)

theorem hBounds (h : ℝ → ℝ) (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2))) (h0 : h 0 = 0)
    (h1 : h (π / 2) = 0) :
    ∃ C : ℝ, 0 < C ∧ (∀ θ ∈ Set.Icc 0 (π / 2), |h θ| ≤ C * Real.sin (2 * θ))
      ∧ (∀ θ ∈ Set.Ioo 0 (π / 2), |deriv h θ| ≤ C) := by
  have hpi : 0 < π / 2 := by positivity
  have hIu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (π / 2)) := uniqueDiffOn_Icc hpi
  have hcderiv : ContinuousOn (derivWithin h (Set.Icc (0 : ℝ) (π / 2))) (Set.Icc (0 : ℝ) (π / 2)) :=
    hh.continuousOn_derivWithin hIu (by norm_num)
  -- a uniform bound `C₀` for the derivative
  obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn hcderiv
  have hC0nn : 0 ≤ C0 := by
    have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨le_rfl, hpi.le⟩
    have h := hC0 0 hmem
    rw [Real.norm_eq_abs] at h
    exact le_trans (abs_nonneg _) h
  have hderiv_eq : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 2),
      deriv h x = derivWithin h (Set.Icc (0 : ℝ) (π / 2)) x :=
    fun x hx => (derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)).symm
  have hbound : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 2), |deriv h x| ≤ C0 := by
    intro x hx
    rw [hderiv_eq x hx]
    simpa [Real.norm_eq_abs] using hC0 x ⟨hx.1.le, hx.2.le⟩
  -- the mean value inequality on the convex interval
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) (π / 2)) := convex_Icc _ _
  have hdiff : DifferentiableOn ℝ h (Set.Icc (0 : ℝ) (π / 2)) := hh.differentiableOn (by norm_num)
  have hnorm : ∀ c : ℝ, ‖ContinuousLinearMap.toSpanSingleton ℝ c‖ = |c| := by
    intro c
    have h := (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).norm_map c
    simpa [Real.norm_eq_abs] using h
  have hfdb : ∀ x ∈ Set.Icc (0 : ℝ) (π / 2),
      ‖fderivWithin ℝ h (Set.Icc (0 : ℝ) (π / 2)) x‖ ≤ C0 := by
    intro x hx
    rw [← toSpanSingleton_derivWithin, hnorm]
    simpa [Real.norm_eq_abs] using hC0 x hx
  have hmvt : ∀ x ∈ Set.Icc (0 : ℝ) (π / 2), ∀ y ∈ Set.Icc (0 : ℝ) (π / 2),
      ‖h y - h x‖ ≤ C0 * ‖y - x‖ :=
    fun x hx y hy => Convex.norm_image_sub_le_of_norm_fderivWithin_le hdiff hfdb hconv hx hy
  have hmain : ∀ θ ∈ Set.Icc (0 : ℝ) (π / 2), |h θ| ≤ C0 * min θ (π / 2 - θ) := by
    intro θ hθ
    have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨le_rfl, hpi.le⟩
    have hpimem : (π / 2) ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨hpi.le, le_rfl⟩
    have hl := hmvt 0 h0mem θ hθ
    have hr := hmvt (π / 2) hpimem θ hθ
    have hl' : |h θ| ≤ C0 * θ := by
      simpa [Real.norm_eq_abs, h0, abs_of_nonneg hθ.1] using hl
    have hr' : |h θ| ≤ C0 * (π / 2 - θ) := by
      have h2 : |θ - π / 2| = π / 2 - θ := by
        rw [abs_of_nonpos (by linarith [hθ.2])]; ring
      simpa [Real.norm_eq_abs, h1, h2] using hr
    rw [mul_min_of_nonneg θ (π / 2 - θ) hC0nn]
    exact le_min hl' hr'
  have hθb : ∀ θ ∈ Set.Icc (0 : ℝ) (π / 2), |h θ| ≤ C0 * Real.sin (2 * θ) := by
    intro θ hθ
    have hsin : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])
    calc |h θ| ≤ C0 * min θ (π / 2 - θ) := hmain θ hθ
      _ ≤ C0 * (π / 4 * Real.sin (2 * θ)) :=
          mul_le_mul_of_nonneg_left (min_le_quarter_pi_mul_sin_two hθ) hC0nn
      _ ≤ C0 * Real.sin (2 * θ) := by
          apply mul_le_mul_of_nonneg_left _ hC0nn
          exact mul_le_of_le_one_left hsin (by linarith [Real.pi_lt_four])
  refine ⟨max C0 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_, ?_⟩
  · intro θ hθ
    have hsin : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])
    calc |h θ| ≤ C0 * Real.sin (2 * θ) := hθb θ hθ
      _ ≤ max C0 1 * Real.sin (2 * θ) := mul_le_mul_of_nonneg_right (le_max_left _ _) hsin
  · intro θ hθ
    exact le_trans (hbound θ hθ) (le_max_left _ _)

end Work.FTS.EllipticEst.AngGap
