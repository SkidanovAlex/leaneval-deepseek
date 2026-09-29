import Mathlib
import Submission.Work.Holonomy3.defs

namespace Work.Holonomy3

open MeasureTheory
open scoped BigOperators
open Submission.CDTPlan

/-- Continuity on the square `[0,1]²` of `(s,t) ↦ max (f s) (g t)`. -/
lemma continuousOn_max_prod {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hg : ContinuousOn g (Set.Icc 0 1)) :
    ContinuousOn (fun p : ℝ × ℝ => max (f p.1) (g p.2)) (Set.Icc 0 1 ×ˢ Set.Icc 0 1) := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => f p.1) (Set.Icc 0 1 ×ˢ Set.Icc 0 1) :=
    hf.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have h2 : ContinuousOn (fun p : ℝ × ℝ => g p.2) (Set.Icc 0 1 ×ˢ Set.Icc 0 1) :=
    hg.comp continuous_snd.continuousOn (fun p hp => hp.2)
  exact h1.sup h2

/-- **The elementary domination.** For continuous `f, g` on `[0,1]`,
`∫₀¹∫₀¹ f(s) ≤ ∫₀¹∫₀¹ max(f(s), g(t))`, since `max(f(s),g(t)) ≥ f(s)` pointwise.
Proved through the product measure (`[0,1]²` is a compact finite-measure square, so both
integrands are integrable and `∫∫ = ∫` on the product). -/
lemma intervalIntegral_double_le_max {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hg : ContinuousOn g (Set.Icc 0 1)) :
    ∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, f s ≤
      ∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, max (f s) (g t) := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    rw [MeasureTheory.isFiniteMeasure_restrict, Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hsub : Set.Ioc (0:ℝ) 1 ×ˢ Set.Ioc (0:ℝ) 1 ⊆ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 :=
    Set.prod_mono (fun x hx => ⟨le_of_lt hx.1, hx.2⟩) (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  have hF : IntegrableOn (fun p : ℝ × ℝ => f p.1)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) volume :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      (hf.comp continuous_fst.continuousOn (fun p hp => hp.1))
  have hM : IntegrableOn (fun p : ℝ × ℝ => max (f p.1) (g p.2))
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) volume :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      (continuousOn_max_prod hf hg)
  have hFi : Integrable (fun p : ℝ × ℝ => f p.1)
      ((volume.restrict (Set.Ioc (0:ℝ) 1)).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact IntegrableOn.mono_set hF hsub
  have hMi : Integrable (fun p : ℝ × ℝ => max (f p.1) (g p.2))
      ((volume.restrict (Set.Ioc (0:ℝ) 1)).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact IntegrableOn.mono_set hM hsub
  have hFubF := MeasureTheory.integral_prod (fun p : ℝ × ℝ => f p.1) hFi
  have hFubM := MeasureTheory.integral_prod (fun p : ℝ × ℝ => max (f p.1) (g p.2)) hMi
  have hmono :
      ∫ p, f p.1 ∂((volume.restrict (Set.Ioc (0:ℝ) 1)).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) ≤
      ∫ p, max (f p.1) (g p.2)
        ∂((volume.restrict (Set.Ioc (0:ℝ) 1)).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) :=
    MeasureTheory.integral_mono hFi hMi (fun p => le_max_left _ _)
  simp only [intervalIntegral.integral_of_le h01]
  rw [← hFubF, ← hFubM]
  exact hmono

/-- The single integral `∫₀¹ f` is dominated by the double integral `∫₀¹∫₀¹ max (f s) (g t)`. -/
lemma integral_le_double_max {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hg : ContinuousOn g (Set.Icc 0 1)) :
    ∫ s in (0:ℝ)..1, f s ≤
      ∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, max (f s) (g t) := by
  have h1 : ∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, f s = ∫ s in (0:ℝ)..1, f s := by
    apply intervalIntegral.integral_congr
    intro s _
    simp [intervalIntegral.integral_const]
  rw [← h1]
  exact intervalIntegral_double_le_max hf hg

/-- **The rearrangement integral dominates the weighted mean.** For each pair of blocks,
`∫∫ max(f s, g t) ≥ ∫∫ f s`, so for nonnegative weights `rearrInt ≥ Σ_k w_k·(Σ_k' w_k')·∫₀¹ log|φ_k|`.
This is the elementary lower bound behind the `m = 1` case of the fine holonomy bound. -/
theorem rearrInt_ge_mean {l : ℕ} (w : Fin (l + 1) → ℝ) (φ : Fin (l + 1) → ℂ → ℂ)
    (hw : ∀ k, 0 ≤ w k)
    (hcont : ∀ k, ContinuousOn (Submission.CDTPlan.circleLog (φ k)) (Set.Icc 0 1)) :
    ∑ k, w k * (∑ k', w k') * (∫ t in (0 : ℝ)..1, Submission.CDTPlan.circleLog (φ k) t) ≤
      Submission.CDTPlan.rearrInt w φ := by
  -- Termwise domination: `w k * w k' * ∫ f_k ≤ w k * w k' * ∫∫ max (f_k, f_k')`.
  have hterm : ∀ k k' : Fin (l + 1),
      w k * w k' * (∫ t in (0:ℝ)..1, circleLog (φ k) t) ≤
        w k * w k' * (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
          max (circleLog (φ k) s) (circleLog (φ k') t)) := by
    intro k k'
    exact mul_le_mul_of_nonneg_left (integral_le_double_max (hcont k) (hcont k'))
      (mul_nonneg (hw k) (hw k'))
  -- Rewrite the weighted mean as the double sum.
  have hsum :
      (∑ k : Fin (l + 1), w k * (∑ k', w k') * (∫ t in (0:ℝ)..1, circleLog (φ k) t)) =
        ∑ k : Fin (l + 1), ∑ k' : Fin (l + 1),
          w k * w k' * (∫ t in (0:ℝ)..1, circleLog (φ k) t) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    calc w k * (∑ k', w k') * (∫ t in (0:ℝ)..1, circleLog (φ k) t)
        = (w k * (∫ t in (0:ℝ)..1, circleLog (φ k) t)) * ∑ k', w k' := by ring
      _ = ∑ k', (w k * (∫ t in (0:ℝ)..1, circleLog (φ k) t)) * w k' := by
            rw [Finset.mul_sum]
      _ = ∑ k', w k * w k' * (∫ t in (0:ℝ)..1, circleLog (φ k) t) :=
            Finset.sum_congr rfl (fun k' _ => by ring)
  rw [Submission.CDTPlan.rearrInt, hsum]
  exact Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun k' _ => hterm k k'))

end Work.Holonomy3
