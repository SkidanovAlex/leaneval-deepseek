import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists
import Submission.Work.FTS.EllipticEst.H2W.SliceEtaFacts
import Submission.Work.FTS.EllipticEst.H2W.integrableOn_sq_mul_sEta_of_bdd
import Submission.Work.FTS.EllipticEst.SgamBound.integrableOn_abs_of_sq_mul_sEta
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open MeasureTheory Set Filter

/-- **FTC bound anchored at an interior point.**  If `g` is `C¹` on the open interval
`(0, π/2)` and `|g'|` is integrable on `Iθ = [0, π/2]`, then for every interior `θ` the
increment of `g` from an interior point `c` is bounded by the full mass of `|g'|`:

`|g θ - g c| ≤ ∫_{Iθ} |g'|`.

This is `Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv` applied to `x ↦ g x - g c`
(which vanishes at `c`), using `deriv_sub_const`. -/
private lemma abs_sub_const_le_integral_abs_deriv {g : ℝ → ℝ} {c : ℝ}
    (hg : ContDiffOn ℝ 1 g (Set.Ioo 0 (Real.pi / 2)))
    (hc : c ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hint : MeasureTheory.IntegrableOn (fun s : ℝ => |deriv g s|) Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |g θ - g c| ≤ ∫ s in Work.Spaces.Iθ, |deriv g s| := by
  have hcd : ContDiffOn ℝ 1 (fun x : ℝ => g x - g c) (Set.Ioo 0 (Real.pi / 2)) :=
    hg.sub contDiffOn_const
  have hz : (fun x : ℝ => g x - g c) c = 0 := by simp
  have heq : (fun s : ℝ => |deriv (fun x : ℝ => g x - g c) s|) = fun s : ℝ => |deriv g s| := by
    funext s
    rw [deriv_sub_const]
  have hint' : MeasureTheory.IntegrableOn
      (fun s : ℝ => |deriv (fun x : ℝ => g x - g c) s|) Work.Spaces.Iθ := by
    rw [heq]; exact hint
  intro θ hθ
  have h := Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
    (f := fun x : ℝ => g x - g c) hcd hc hz hint' θ hθ
  rw [heq] at h
  exact h

theorem slice_deriv_of_sq_deriv_deriv {f : ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n f (Set.Ioo 0 (Real.pi / 2)))
    (hI : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv f t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  have hpi4 : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  -- ## Smoothness of `f'` and `f''` on the open interval `(0, π/2)`
  have hd1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
    (hf 2).deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hd1c : ContinuousOn (deriv f) (Set.Ioo 0 (Real.pi / 2)) := hd1.continuousOn
  have hd2c : ContinuousOn (fun θ : ℝ => deriv (fun t : ℝ => deriv f t) θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    hd1.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  -- ## The second derivative is in `L¹` (against the trivial weight)
  have habs : MeasureTheory.IntegrableOn
      (fun s : ℝ => |deriv (fun t : ℝ => deriv f t) s|) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.SgamBound.integrableOn_abs_of_sq_mul_sEta hd2c hI
  -- ## Fundamental theorem of calculus, anchored at the interior point `π/4`
  have hftc : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv f θ - deriv f (Real.pi / 4)|
        ≤ ∫ s in Work.Spaces.Iθ, |deriv (fun t : ℝ => deriv f t) s| :=
    abs_sub_const_le_integral_abs_deriv hd1 hpi4 habs
  -- ## Hence `f'` is bounded on the open interval by `M = |f' (π/4)| + ∫_{Iθ} |f''|`
  have hbdd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv f θ| ≤ |deriv f (Real.pi / 4)|
        + ∫ s in Work.Spaces.Iθ, |deriv (fun t : ℝ => deriv f t) s| := by
    intro θ hθ
    have htri : |deriv f θ| ≤ |deriv f (Real.pi / 4)|
        + |deriv f θ - deriv f (Real.pi / 4)| := by
      have hid : deriv f θ = deriv f (Real.pi / 4)
          + (deriv f θ - deriv f (Real.pi / 4)) := by ring
      calc |deriv f θ|
          = |deriv f (Real.pi / 4) + (deriv f θ - deriv f (Real.pi / 4))| := congrArg abs hid
        _ ≤ |deriv f (Real.pi / 4)| + |deriv f θ - deriv f (Real.pi / 4)| :=
            abs_add_le (deriv f (Real.pi / 4)) (deriv f θ - deriv f (Real.pi / 4))
    linarith [hftc θ hθ]
  have hM0 : 0 ≤ |deriv f (Real.pi / 4)|
      + ∫ s in Work.Spaces.Iθ, |deriv (fun t : ℝ => deriv f t) s| := by
    have h1 : (0 : ℝ) ≤ ∫ s in Work.Spaces.Iθ, |deriv (fun t : ℝ => deriv f t) s| :=
      MeasureTheory.integral_nonneg fun s => abs_nonneg _
    linarith [abs_nonneg (deriv f (Real.pi / 4))]
  -- ## A bounded, continuous slice has finite weighted square integral
  exact integrableOn_sq_mul_sEta_of_bdd hd1c ⟨_, hM0, hbdd⟩

end Work.FTS.EllipticEst.H2W
