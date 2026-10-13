import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.RingTheory.TotallySplit
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.StepFacts

/-- A continuous function supported in the closed unit ball of `ℝ × ℝ`, multiplied by
`exp (c * (|t.1| + |t.2|))`, is integrable: it is continuous and compactly supported. -/
private lemma integrable_sigma_exp (σ : ℝ × ℝ → ℝ) (hσc : Continuous σ)
    (hσsupp : ∀ p : ℝ × ℝ, σ p ≠ 0 → p.1 ^ 2 + p.2 ^ 2 ≤ 1) (c : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ × ℝ => σ t * Real.exp (c * (|t.1| + |t.2|))) := by
  have hexp : Continuous fun t : ℝ × ℝ => Real.exp (c * (|t.1| + |t.2|)) := by fun_prop
  have hsupp : Function.support (fun t : ℝ × ℝ => σ t * Real.exp (c * (|t.1| + |t.2|)))
      ⊆ Metric.closedBall (0 : ℝ × ℝ) 1 := by
    intro t ht
    rw [Function.mem_support] at ht
    have hσne : σ t ≠ 0 := fun h => ht (by rw [h, zero_mul])
    have h := hσsupp t hσne
    have h1 : |t.1| ≤ 1 := by
      have h2 : t.1 ^ 2 ≤ (1 : ℝ) ^ 2 := by nlinarith [h, sq_nonneg t.2]
      rwa [sq_le_sq, abs_one] at h2
    have h2 : |t.2| ≤ 1 := by
      have h3 : t.2 ^ 2 ≤ (1 : ℝ) ^ 2 := by nlinarith [h, sq_nonneg t.1]
      rwa [sq_le_sq, abs_one] at h3
    rw [Metric.mem_closedBall, dist_zero_right]
    exact max_le h1 h2
  exact (hσc.mul hexp).integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℝ × ℝ) 1) isClosed_closure
      (closure_minimal hsupp Metric.isClosed_closedBall))

set_option maxHeartbeats 800000 in
-- context: namespace Work.FTS.StrongEps.StepFacts. `Jker σ ε p = ε⁻¹^2 * σ (ε⁻¹ • p)` is the `ε`-rescaled kernel; `σ` is an arbitrary nonnegative continuous function supported in the closed unit ball. The conclusion is a conjunction.
theorem Jker_moment_le (σ : ℝ × ℝ → ℝ) (hσ0 : ∀ p : ℝ × ℝ, 0 ≤ σ p)
    (hσc : Continuous σ)
    (hσsupp : ∀ p : ℝ × ℝ, σ p ≠ 0 → p.1 ^ 2 + p.2 ^ 2 ≤ 1)
    {ε γ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hγ : 0 ≤ γ) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.Jker σ ε p * Real.exp (γ * (|p.1| + |p.2|)))
    ∧ (∫ p : ℝ × ℝ,
        Work.FTS.StrongEps.Jker σ ε p * Real.exp (γ * (|p.1| + |p.2|)))
      ≤ ∫ t : ℝ × ℝ, σ t * Real.exp (γ * (|t.1| + |t.2|)) := by
  -- the right-hand sides with the two exponents are integrable
  have hG : MeasureTheory.Integrable
      (fun t : ℝ × ℝ => σ t * Real.exp (γ * (|t.1| + |t.2|))) :=
    integrable_sigma_exp σ hσc hσsupp γ
  have hG' : MeasureTheory.Integrable
      (fun t : ℝ × ℝ => σ t * Real.exp (γ * ε * (|t.1| + |t.2|))) :=
    integrable_sigma_exp σ hσc hσsupp (γ * ε)
  -- `ε * (ε⁻¹ * a + ε⁻¹ * b) = a + b`, the cancellation behind the change of variables
  have harg : ∀ a b : ℝ, γ * ε * (ε⁻¹ * a + ε⁻¹ * b) = γ * (a + b) := by
    intro a b
    have hne : ε ≠ 0 := hε.ne'
    field_simp
  -- unfolding the kernel, keeping the exponential as it is
  have hpt : ∀ p : ℝ × ℝ,
      Work.FTS.StrongEps.Jker σ ε p * Real.exp (γ * (|p.1| + |p.2|))
        = ε⁻¹ ^ 2 * (σ (ε⁻¹ • p) * Real.exp (γ * (|p.1| + |p.2|))) := by
    intro p
    simp only [Work.FTS.StrongEps.Jker]
    ring
  -- the same integrand with the variable scaled by `ε⁻¹`
  have hpoint : ∀ p : ℝ × ℝ, σ (ε⁻¹ • p) * Real.exp (γ * (|p.1| + |p.2|))
      = (fun t : ℝ × ℝ => σ t * Real.exp (γ * ε * (|t.1| + |t.2|))) (ε⁻¹ • p) := by
    intro p
    have h : γ * (|p.1| + |p.2|) = γ * ε * (|(ε⁻¹ • p).1| + |(ε⁻¹ • p).2|) := by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr hε.le)]
      exact (harg |p.1| |p.2|).symm
    rw [h]
  -- the change of variables `p ↦ ε⁻¹ p`
  have hcv : (∫ p : ℝ × ℝ, σ (ε⁻¹ • p) * Real.exp (γ * (|p.1| + |p.2|)))
      = ε ^ 2 * ∫ t : ℝ × ℝ, σ t * Real.exp (γ * ε * (|t.1| + |t.2|)) := by
    rw [show (fun p : ℝ × ℝ => σ (ε⁻¹ • p) * Real.exp (γ * (|p.1| + |p.2|)))
        = (fun p : ℝ × ℝ =>
            (fun t : ℝ × ℝ => σ t * Real.exp (γ * ε * (|t.1| + |t.2|))) (ε⁻¹ • p))
        from funext hpoint]
    rw [MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
      (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      (fun t : ℝ × ℝ => σ t * Real.exp (γ * ε * (|t.1| + |t.2|))) hε.le]
    rw [Module.finrank_prod, Module.finrank_self]
    norm_num
  refine ⟨?_, ?_⟩
  · have h1 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (fun t : ℝ × ℝ => σ t * Real.exp (γ * ε * (|t.1| + |t.2|))) (ε⁻¹ • p)) :=
      hG'.comp_smul (inv_ne_zero hε.ne')
    have h2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ε⁻¹ ^ 2 *
        ((fun t : ℝ × ℝ => σ t * Real.exp (γ * ε * (|t.1| + |t.2|))) (ε⁻¹ • p))) :=
      h1.const_mul _
    have h3 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ε⁻¹ ^ 2 *
        (σ (ε⁻¹ • p) * Real.exp (γ * (|p.1| + |p.2|)))) :=
      h2.congr (Filter.Eventually.of_forall fun p => by
        show ε⁻¹ ^ 2 * ((fun t : ℝ × ℝ => σ t * Real.exp (γ * ε * (|t.1| + |t.2|))) (ε⁻¹ • p))
          = ε⁻¹ ^ 2 * (σ (ε⁻¹ • p) * Real.exp (γ * (|p.1| + |p.2|)))
        rw [hpoint p])
    exact h3.congr (Filter.Eventually.of_forall fun p => (hpt p).symm)
  · have hle : ∀ t : ℝ × ℝ, σ t * Real.exp (γ * ε * (|t.1| + |t.2|))
        ≤ σ t * Real.exp (γ * (|t.1| + |t.2|)) := by
      intro t
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hσ0 t)
      have hS : 0 ≤ |t.1| + |t.2| := by positivity
      have h1 : γ * ε ≤ γ := by simpa using mul_le_mul_of_nonneg_left hε1 hγ
      calc γ * ε * (|t.1| + |t.2|) = (γ * ε) * (|t.1| + |t.2|) := by ring
        _ ≤ γ * (|t.1| + |t.2|) := mul_le_mul_of_nonneg_right h1 hS
    calc (∫ p : ℝ × ℝ,
          Work.FTS.StrongEps.Jker σ ε p * Real.exp (γ * (|p.1| + |p.2|)))
        = ∫ p : ℝ × ℝ, ε⁻¹ ^ 2 * (σ (ε⁻¹ • p) * Real.exp (γ * (|p.1| + |p.2|))) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => hpt p)
      _ = ε⁻¹ ^ 2 * ∫ p : ℝ × ℝ, σ (ε⁻¹ • p) * Real.exp (γ * (|p.1| + |p.2|)) :=
          MeasureTheory.integral_const_mul _ _
      _ = ε⁻¹ ^ 2 * (ε ^ 2 * ∫ t : ℝ × ℝ, σ t * Real.exp (γ * ε * (|t.1| + |t.2|))) := by
          rw [hcv]
      _ = ∫ t : ℝ × ℝ, σ t * Real.exp (γ * ε * (|t.1| + |t.2|)) := by
          have h2 : ε⁻¹ ^ 2 * ε ^ 2 = (1 : ℝ) := by
            rw [← mul_pow, inv_mul_cancel₀ hε.ne', one_pow]
          rw [← mul_assoc, h2, one_mul]
      _ ≤ ∫ t : ℝ × ℝ, σ t * Real.exp (γ * (|t.1| + |t.2|)) :=
          MeasureTheory.integral_mono hG' hG (fun t => hle t)

end Work.FTS.StrongEps.StepFacts
