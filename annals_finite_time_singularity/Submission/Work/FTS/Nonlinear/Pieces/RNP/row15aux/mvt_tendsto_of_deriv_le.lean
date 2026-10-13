import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

theorem mvt_tendsto_of_deriv_le {f : ℝ → ℝ} {L C θ₀ : ℝ}
    (hC : 0 ≤ C) (hθ₀ : 0 < θ₀)
    (hdiff : DifferentiableOn ℝ f (Set.Ioo (0 : ℝ) θ₀))
    (htend : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L))
    (hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) θ₀, |deriv f θ| ≤ C) :
    (∀ θ ∈ Set.Ioo (0 : ℝ) θ₀, |f θ - L| ≤ C * θ) ∧
    (∀ θ₁ ∈ Set.Ioo (0 : ℝ) θ₀, ∀ ε ∈ Set.Ioo (0 : ℝ) θ₁,
      |f θ₁ - f ε| ≤ C * (θ₁ - ε)) := by
  -- Mean value inequality on the open interval `(0, θ₀)` for the second conjunct.
  have hsecond : ∀ θ₁ ∈ Set.Ioo (0 : ℝ) θ₀, ∀ ε ∈ Set.Ioo (0 : ℝ) θ₁,
      |f θ₁ - f ε| ≤ C * (θ₁ - ε) := by
    intro θ₁ hθ₁ ε hε
    have hε' : ε ∈ Set.Ioo (0 : ℝ) θ₀ := ⟨hε.1, lt_trans hε.2 hθ₁.2⟩
    have hdiff' : ∀ x ∈ Set.Ioo (0 : ℝ) θ₀, DifferentiableAt ℝ f x :=
      fun x hx => hdiff.differentiableAt (isOpen_Ioo.mem_nhds hx)
    have hbound : ∀ x ∈ Set.Ioo (0 : ℝ) θ₀, ‖deriv f x‖ ≤ C := by
      intro x hx
      rw [Real.norm_eq_abs]
      exact hderiv x hx
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff' hbound (convex_Ioo 0 θ₀) hε' hθ₁
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hε.2)] at h
    exact h
  refine ⟨?_, hsecond⟩
  intro θ hθ
  have hθpos : 0 < θ := hθ.1
  -- Pass to the limit `ε → 0⁺` in the second conjunct.
  have h1 : Filter.Tendsto (fun ε => |f θ - f ε|) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds |f θ - L|) := by
    have hs : Filter.Tendsto (fun ε : ℝ => f θ - f ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (f θ - L)) :=
      tendsto_const_nhds.sub htend
    exact hs.abs
  have h2 : Filter.Tendsto (fun ε : ℝ => C * (θ - ε)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (C * θ)) := by
    have hid : Filter.Tendsto (fun ε : ℝ => ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (0 : ℝ)) :=
      (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
    have hs : Filter.Tendsto (fun ε : ℝ => θ - ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (θ - 0)) :=
      tendsto_const_nhds.sub hid
    simpa using hs.const_mul C
  have hev : ∀ᶠ ε in (nhdsWithin (0 : ℝ) (Set.Ioi 0)), |f θ - f ε| ≤ C * (θ - ε) := by
    have hsmall : ∀ᶠ ε in (nhdsWithin (0 : ℝ) (Set.Ioi 0)), ε < θ :=
      (eventually_lt_nhds hθpos).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hlt
    exact hsecond θ hθ ε ⟨hε, hlt⟩
  exact le_of_tendsto_of_tendsto h1 h2 hev

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
