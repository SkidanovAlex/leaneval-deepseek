import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

/-- The kernel `Jker ρ ε` is nonnegative, because `ρ` is. -/
theorem Jker_slice_nonneg {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    (ε : ℝ) (p : ℝ × ℝ) : 0 ≤ Work.FTS.StrongEps.Jker ρ ε p := by
  rw [Work.FTS.StrongEps.Jker]
  exact mul_nonneg (sq_nonneg _) (hρ.nonneg _)

/-- **The `p₁`-slices of the rescaled kernel have uniformly bounded integrals.**

`Jker ρ ε` is supported in the closed ball of radius `ε`, so for every fixed `p₂ = q` the slice
`p₁ ↦ Jker ρ ε (p₁, q)` is continuous and vanishes off `[-ε, ε]`; continuity on the compact box
`[-ε, ε] × [-ε, ε]` supplies a bound `M` on the box, and off the box the slice vanishes in each
variable.  Hence every slice integral is at most `M · 2ε`. -/
theorem exists_bound_integral_Jker_slice {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q : ℝ, ∫ p₁ : ℝ, Work.FTS.StrongEps.Jker ρ ε (p₁, q) ≤ B := by
  have hcont : Continuous (Work.FTS.StrongEps.Jker ρ ε) :=
    Work.FTS.StrongEps.Jker_continuous hρ ε
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hcont.continuousOn :
      ContinuousOn (Work.FTS.StrongEps.Jker ρ ε)
        (Set.Icc (-ε) ε ×ˢ Set.Icc (-ε) ε))
  have hM0 : 0 ≤ M :=
    le_trans (norm_nonneg _)
      (hM (0, 0) ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩)
  have hsmall : ∀ x : ℝ, x ∉ Set.Icc (-ε) ε → ε < |x| := by
    intro x hx
    by_contra hc
    push Not at hc
    exact hx ⟨by linarith [neg_abs_le x, hc], by linarith [le_abs_self x, hc]⟩
  -- the slice vanishes in each variable off `[-ε, ε]`
  have hzero_snd : ∀ (x y : ℝ), y ∉ Set.Icc (-ε) ε → Work.FTS.StrongEps.Jker ρ ε (x, y) = 0 := by
    intro x y hy
    refine Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε ?_
    intro hmem
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    have h1 : |y| ≤ ε := by
      have := norm_snd_le ((x, y) : ℝ × ℝ)
      rw [Real.norm_eq_abs] at this
      exact le_trans this hmem
    exact absurd h1 (not_le.2 (hsmall y hy))
  have hzero_fst : ∀ (x y : ℝ), x ∉ Set.Icc (-ε) ε → Work.FTS.StrongEps.Jker ρ ε (x, y) = 0 := by
    intro x y hx
    refine Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε ?_
    intro hmem
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    have h1 : |x| ≤ ε := by
      have := norm_fst_le ((x, y) : ℝ × ℝ)
      rw [Real.norm_eq_abs] at this
      exact le_trans this hmem
    exact absurd h1 (not_le.2 (hsmall x hx))
  refine ⟨M * (2 * ε), mul_nonneg hM0 (by linarith), fun q => ?_⟩
  have hrestrict : (∫ p₁ : ℝ, Work.FTS.StrongEps.Jker ρ ε (p₁, q))
      = ∫ p₁ in Set.Icc (-ε) ε, Work.FTS.StrongEps.Jker ρ ε (p₁, q) :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun p₁ : ℝ => Work.FTS.StrongEps.Jker ρ ε (p₁, q))
      (s := Set.Icc (-ε) ε) (fun x hx => hzero_fst x q hx)).symm
  rw [hrestrict]
  calc ∫ x in Set.Icc (-ε) ε, Work.FTS.StrongEps.Jker ρ ε (x, q)
      ≤ ∫ _ in Set.Icc (-ε) ε, M := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x => Jker_slice_nonneg hρ ε (x, q))
          (MeasureTheory.integrableOn_const (C := M) ?_) ?_
        · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx
          by_cases hq : q ∈ Set.Icc (-ε) ε
          · have h := hM (x, q) ⟨hx, hq⟩
            exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using h)
          · rw [hzero_snd x q hq]
            exact hM0
    _ = M * (2 * ε) := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.Measure.real_def,
          Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
        ring

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
