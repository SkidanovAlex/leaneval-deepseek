import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open MeasureTheory Set Filter
open scoped Real Topology

/-- `Iθ = [0, π/2]` and the open interval `(0, π/2)` carry the same restricted Lebesgue
measure: they differ by the null set `{0, π/2}`. -/
private lemma restrict_Iθ_eq_Ioo' :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  rw [Work.Spaces.Iθ]
  exact Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm

/-- **Integrability of a square from an a.e. bound.**  If `u` is a.e. strongly measurable on the
open interval `(0, π/2)` and `|u|` is bounded there by the constant `C`, then `u²` is integrable
on `Iθ = [0, π/2]` (which has finite measure). -/
private lemma integrableOn_sq_of_bdd {u : ℝ → ℝ} {C : ℝ}
    (haesm : AEStronglyMeasurable u (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
    (hbdd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |u θ| ≤ C) :
    IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ := by
  rw [MeasureTheory.IntegrableOn, restrict_Iθ_eq_Ioo']
  refine Integrable.of_bound (haesm.pow 2) (C ^ 2) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 : |u θ| ^ 2 ≤ C ^ 2 := by
    have h0 := abs_nonneg (u θ)
    nlinarith [hbdd θ hθ]
  rwa [sq_abs] at h1

/-- `|sin θ · cos²θ| ≤ 1` for every real `θ`. -/
private lemma abs_sinCos2_le_one (θ : ℝ) : |Work.Elliptic.sinCos2 θ| ≤ 1 := by
  rw [Work.Elliptic.sinCos2, abs_mul]
  have h1 : |Real.sin θ| ≤ 1 := by
    rw [abs_le]
    exact ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have h2 : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact Real.cos_sq_le_one θ
  calc |Real.sin θ| * |Real.cos θ ^ 2| ≤ 1 * 1 :=
        mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

/-- **Boundedness and slice integrability from the `σ`-weighted `L²`-bound on `f''`.**

From `ContDiffOn ℝ 2 f (0,π/2)` and `∫_{Iθ} (f'')² σ < ∞` (`σ = sEta = sin(2θ)^{-η}`) we obtain:
`f` and `f'` are bounded on the open interval, `(f')²`, `f²` and `f · sinCos2` are integrable on
`Iθ = [0, π/2]`, and `f''` is integrable on the open interval.

The mechanism is that `σ ≥ 1` on `(0, π/2)` (since `0 < sin 2θ ≤ 1` there), so the hypothesis
forces `f'' ∈ L²(0, π/2) ⊂ L¹(0, π/2)`; the fundamental theorem of calculus from the interior
point `π/4` then bounds `f'` (and, once more, `f`) by `|f'(π/4)| + ∫|f''|` and
`|f(π/4)| + (π/2)·sup|f'|`. -/
theorem HonestBddOfSecondSq {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv f t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv f θ| ≤ M) ∧
    (∃ B : ℝ, 0 ≤ B ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ B) ∧
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ : ℝ => deriv (fun t : ℝ => deriv f t) θ)
      (Set.Ioo 0 (Real.pi / 2)) ∧
    MeasureTheory.IntegrableOn (fun θ : ℝ => f θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  -- Boundedness of `f` and `f'` on the open interval, with a common constant.
  obtain ⟨C, hC0, hC⟩ := slice_bdd_of_sq_mul_sEta hf hint
  have hf1 : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) := hf.of_le (by norm_num)
  have hcontf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)) := hf1.continuousOn
  have hcontψ : ContinuousOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h : Continuous (fun θ : ℝ => Work.Elliptic.sinCos2 θ) := by
      simp only [Work.Elliptic.sinCos2]; fun_prop
    exact h.continuousOn
  -- `(f')² ∈ L¹(Iθ)`
  have h3 : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2) Work.Spaces.Iθ :=
    integrableOn_sq_of_bdd (measurable_deriv f).aestronglyMeasurable
      (fun θ hθ => (hC θ hθ).2)
  -- `f² ∈ L¹(Iθ)`
  have h4 : MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2) Work.Spaces.Iθ :=
    integrableOn_sq_of_bdd (hcontf.aestronglyMeasurable measurableSet_Ioo)
      (fun θ hθ => (hC θ hθ).1)
  -- `f'' ∈ L¹((0, π/2))`
  have h5 : MeasureTheory.IntegrableOn (fun θ : ℝ => deriv (fun t : ℝ => deriv f t) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hsq := Work.FTS.EllipticEst.sliceLim_integrableOn_sq_of_integrableOn_mul_sEta f hint
    have habs := Work.FTS.EllipticEst.sliceLim_integrableOn_abs_of_integrableOn_sq f hsq
    refine MeasureTheory.Integrable.mono' habs
      (measurable_deriv (fun t : ℝ => deriv f t)).aestronglyMeasurable ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs]
  -- `f · sinCos2 ∈ L¹(Iθ)`
  have h6 : MeasureTheory.IntegrableOn (fun θ : ℝ => f θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
    rw [MeasureTheory.IntegrableOn, restrict_Iθ_eq_Ioo']
    refine MeasureTheory.Integrable.of_bound
      ((hcontf.mul hcontψ).aestronglyMeasurable measurableSet_Ioo) (max C 0) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [Real.norm_eq_abs, abs_mul]
    calc |f θ| * |Work.Elliptic.sinCos2 θ| ≤ C * 1 :=
          mul_le_mul (hC θ hθ).1 (abs_sinCos2_le_one θ) (abs_nonneg _) hC0
      _ = C := by ring
      _ ≤ max C 0 := le_max_left _ _
  exact ⟨⟨C, hC0, fun θ hθ => (hC θ hθ).2⟩, ⟨C, hC0, fun θ hθ => (hC θ hθ).1⟩, h3, h4, h5, h6⟩

end Work.FTS.EllipticEst.Honest
