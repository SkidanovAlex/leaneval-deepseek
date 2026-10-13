/-
Copyright: work module for the Elgindi finite-time singularity project.

# A priori bounds for a `C²` slice vanishing at both ends of `Iθ`

`Work.FTS.EllipticEst.AngSecond.slice_a_priori_bounds`: a function `f` of class `C²` on the
closed angular interval `Iθ = [0, π/2]` (only *within* the interval!) with `f 0 = f (π/2) = 0`
admits a single constant `C ≥ 0` bounding `|f'|` and `|f''|` on the interior and both endpoint
slopes of `f` on `Iθ`:

* `|f' θ| ≤ C` and `|f'' θ| ≤ C` for `θ ∈ (0, π/2)`;
* `|f θ| ≤ C · θ` and `|f θ| ≤ C · (π/2 - θ)` for `θ ∈ Iθ`.

The point of the statement is that `f` is *not* assumed smooth on a neighbourhood of `Iθ`
(contrast `Work.FTS.EllipticEst.abs_le_mul_of_abs_deriv_le`, which needs `SliceSmooth`): only
the *one-sided* derivatives at `0` and `π/2` are controlled.  The proof therefore works with
`derivWithin f Iθ`, which is the honest derivative on the closed interval, and bridges back to
the plain `deriv` on the *open* interval, where `Iθ ∈ 𝓝 θ`.

Route (all constants are the sup norms of the within-derivatives on the compact `Iθ`):

1. `ContDiffOn ℝ 2 f Iθ` gives `ContDiffOn ℝ 1 (derivWithin f Iθ) Iθ`
   (`ContDiffOn.derivWithin`, using `UniqueDiffOn ℝ Iθ`), hence the continuity on `Iθ` of both
   `derivWithin f Iθ` and `derivWithin (derivWithin f Iθ) Iθ`
   (`ContDiffOn.continuousOn_derivWithin`).  Both are bounded on the compact `Iθ`
   (`IsCompact.exists_bound_of_continuousOn`); let `C` be the maximum of the two bounds and `0`.
2. For `θ` in the open interval, `Iθ ∈ 𝓝 θ`, so `derivWithin f Iθ θ = deriv f θ`
   (`derivWithin_of_mem_nhds`).  For the second derivative one first replaces `deriv f` by the
   eventually equal `derivWithin f Iθ` (`Filter.EventuallyEq.deriv_eq`, the two agree on the
   open interval) and then applies `derivWithin_of_mem_nhds` once more.
3. Both endpoint bounds are the mean value theorem on the convex set `Iθ` for the within
   derivative (`Convex.norm_image_sub_le_of_norm_derivWithin_le`), applied on the segments
   `[0, θ]` (using `f 0 = 0`) and `[θ, π/2]` (using `f (π/2) = 0`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.AngSecond.SliceIBPDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `Work.Spaces.Iθ = [0, π/2]` has unique derivatives, being a nondegenerate closed interval. -/
private lemma uniqueDiffOn_Iθ : UniqueDiffOn ℝ Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]
  exact uniqueDiffOn_Icc (by positivity : (0 : ℝ) < Real.pi / 2)

/-- A `C²` function on the closed interval `Iθ` has within-derivatives of order `1` and `2`
which are continuous on `Iθ`.  (`derivWithin f Iθ` is the honest derivative of `f` on the
closed interval: in particular it is the one-sided derivative at the two endpoints.) -/
private lemma contDiffOn_two_continuousOn_derivWithin {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f Work.Spaces.Iθ) :
    ContinuousOn (derivWithin f Work.Spaces.Iθ) Work.Spaces.Iθ ∧
      ContinuousOn (derivWithin (derivWithin f Work.Spaces.Iθ) Work.Spaces.Iθ)
        Work.Spaces.Iθ := by
  have h1 : ContinuousOn (derivWithin f Work.Spaces.Iθ) Work.Spaces.Iθ :=
    hf.continuousOn_derivWithin uniqueDiffOn_Iθ (by norm_num)
  have h2 : ContDiffOn ℝ 1 (derivWithin f Work.Spaces.Iθ) Work.Spaces.Iθ :=
    hf.derivWithin uniqueDiffOn_Iθ (by norm_num)
  exact ⟨h1, h2.continuousOn_derivWithin uniqueDiffOn_Iθ (by norm_num)⟩

/-- `Iθ` is a neighbourhood of each of its interior points. -/
private lemma Iθ_mem_nhds {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.Iθ ∈ 𝓝 θ := by
  rw [Work.Spaces.Iθ]
  exact Icc_mem_nhds hθ.1 hθ.2

theorem slice_a_priori_bounds (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f Work.Spaces.Iθ)
    (h0 : f 0 = 0) (h1 : f (Real.pi / 2) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv f θ| ≤ C)
      ∧ (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (deriv f) θ| ≤ C)
      ∧ (∀ θ ∈ Work.Spaces.Iθ, |f θ| ≤ C * θ)
      ∧ (∀ θ ∈ Work.Spaces.Iθ, |f θ| ≤ C * (Real.pi / 2 - θ)) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  -- Step 1: the two within-derivatives are continuous on the compact `Iθ`, hence bounded
  -- on it; take `C` the maximum of the two bounds and `0`.
  obtain ⟨hcont1, hcont2⟩ := contDiffOn_two_continuousOn_derivWithin hf
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont1
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont2
  have hC1le : ∀ x ∈ Work.Spaces.Iθ, ‖derivWithin f Work.Spaces.Iθ x‖ ≤ max (max C1 C2) 0 :=
    fun x hx => le_trans (hC1 x hx) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hC2le : ∀ x ∈ Work.Spaces.Iθ,
      ‖derivWithin (derivWithin f Work.Spaces.Iθ) Work.Spaces.Iθ x‖ ≤ max (max C1 C2) 0 :=
    fun x hx => le_trans (hC2 x hx) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hdiff : DifferentiableOn ℝ f Work.Spaces.Iθ := hf.differentiableOn (by norm_num)
  have hconv : Convex ℝ Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact convex_Icc 0 (Real.pi / 2)
  have h0Iθ : (0 : ℝ) ∈ Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact ⟨le_rfl, hpi.le⟩
  have h1Iθ : Real.pi / 2 ∈ Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact ⟨hpi.le, le_rfl⟩
  refine ⟨max (max C1 C2) 0, le_max_right _ _, ?_, ?_, ?_, ?_⟩
  -- Step 2a: the first derivative on the open interval.
  · intro θ hθ
    have hmem := Iθ_mem_nhds hθ
    rw [← derivWithin_of_mem_nhds hmem]
    exact hC1le θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- Step 2b: the second derivative on the open interval: `deriv f` and `derivWithin f Iθ`
  -- agree on the open interval, which is a neighbourhood of `θ`.
  · intro θ hθ
    have hcongr : (fun x => deriv f x) =ᶠ[𝓝 θ] (fun x => derivWithin f Work.Spaces.Iθ x) := by
      filter_upwards [IsOpen.mem_nhds isOpen_Ioo hθ] with x hx
      exact (derivWithin_of_mem_nhds (Iθ_mem_nhds hx)).symm
    rw [hcongr.deriv_eq, ← derivWithin_of_mem_nhds (Iθ_mem_nhds hθ)]
    exact hC2le θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- Step 3a: `|f θ| ≤ C θ`, by the mean value theorem on the segment `[0, θ]`.
  · intro θ hθ
    have h := Convex.norm_image_sub_le_of_norm_derivWithin_le (f := f) (s := Work.Spaces.Iθ)
      (x := 0) (y := θ) (C := max (max C1 C2) 0) hdiff hC1le hconv h0Iθ hθ
    simp only [h0, sub_zero, Real.norm_eq_abs, abs_of_nonneg hθ.1] at h
    exact h
  -- Step 3b: `|f θ| ≤ C (π/2 - θ)`, by the mean value theorem on the segment `[θ, π/2]`.
  · intro θ hθ
    have h := Convex.norm_image_sub_le_of_norm_derivWithin_le (f := f) (s := Work.Spaces.Iθ)
      (x := θ) (y := Real.pi / 2) (C := max (max C1 C2) 0) hdiff hC1le hconv hθ h1Iθ
    simp only [h1, zero_sub, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (sub_nonneg.mpr hθ.2)] at h
    exact h

end Work.FTS.EllipticEst.AngSecond
