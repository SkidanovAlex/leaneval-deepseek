import Mathlib.MeasureTheory.Integral.Prod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false

/-!
# The one-body pairing identity `pairingP1`

For a finite measure `μ` and measurable functions `f g : α → α → ℝ` bounded by `M` and `N`
respectively, the two iterated integrals

  `∫ a, ∫ b, f a b * (r * ∫ a', g a' b)`
  `∫ a, ∫ b, (r * ∫ a', f a' b) * g a b`

coincide.  Both are equal to `r * ∫ b, (∫ a, f a b) * (∫ a', g a' b)`: the inner integrals
`F b = ∫ a, f a b` and `G b = ∫ a', g a' b` are bounded by `M * μ univ` and `N * μ univ`
(finiteness of `μ`), so all integrands are bounded and measurable on the finite product
measure `μ.prod μ`, and one application of Fubini to each side produces the common middle
term.  The boundedness hypotheses `hfb`, `hgb` are exactly what makes Fubini applicable
without extra integrability assumptions in the statement.
-/

open MeasureTheory Filter

namespace Work.BoseBoxFock

theorem pairingP1 {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    {f g : α → α → ℝ} {M N r : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hfb : ∀ a b, |f a b| ≤ M) (hgb : ∀ a b, |g a b| ≤ N) :
    (∫ a, ∫ b, f a b * (r * ∫ a', g a' b ∂μ) ∂μ ∂μ)
      = ∫ a, ∫ b, (r * ∫ a', f a' b ∂μ) * g a b ∂μ ∂μ := by
  -- the two "marginal" functions are strongly measurable as parametrised integrals
  have hGmeas : StronglyMeasurable (fun b => ∫ a', g a' b ∂μ) :=
    StronglyMeasurable.integral_prod_left' (μ := μ) (f := Function.uncurry g)
      hg.stronglyMeasurable
  have hFmeas : StronglyMeasurable (fun b => ∫ a', f a' b ∂μ) :=
    StronglyMeasurable.integral_prod_left' (μ := μ) (f := Function.uncurry f)
      hf.stronglyMeasurable
  -- and bounded, because `μ` is a finite measure
  have hGbd : ∀ b, |∫ a', g a' b ∂μ| ≤ N * μ.real Set.univ := by
    intro b
    have h : ‖∫ a', g a' b ∂μ‖ ≤ N * μ.real Set.univ :=
      MeasureTheory.norm_integral_le_of_norm_le_const (f := fun a' => g a' b) (C := N)
        (Eventually.of_forall (fun a' => by simpa [Real.norm_eq_abs] using hgb a' b))
    simpa [Real.norm_eq_abs] using h
  have hFbd : ∀ b, |∫ a', f a' b ∂μ| ≤ M * μ.real Set.univ := by
    intro b
    have h : ‖∫ a', f a' b ∂μ‖ ≤ M * μ.real Set.univ :=
      MeasureTheory.norm_integral_le_of_norm_le_const (f := fun a' => f a' b) (C := M)
        (Eventually.of_forall (fun a' => by simpa [Real.norm_eq_abs] using hfb a' b))
    simpa [Real.norm_eq_abs] using h
  -- integrability of the two uncurried integrands on the product measure
  have hInt1 : Integrable (Function.uncurry fun a b => f a b * (∫ a', g a' b ∂μ))
      (μ.prod μ) := by
    have h1 : AEStronglyMeasurable
        (fun p : α × α => f p.1 p.2 * (∫ a', g a' p.2 ∂μ)) (μ.prod μ) :=
      (hf.aestronglyMeasurable).mul (hGmeas.aestronglyMeasurable.comp_snd)
    refine Integrable.of_bound h1 (M * (N * μ.real Set.univ)) ?_
    filter_upwards with p
    have hf1 : ‖f p.1 p.2‖ ≤ M := by simpa [Real.norm_eq_abs] using hfb p.1 p.2
    have hG1 : ‖∫ a', g a' p.2 ∂μ‖ ≤ N * μ.real Set.univ := by
      simpa [Real.norm_eq_abs] using hGbd p.2
    calc ‖f p.1 p.2 * (∫ a', g a' p.2 ∂μ)‖
        = ‖f p.1 p.2‖ * ‖∫ a', g a' p.2 ∂μ‖ := norm_mul _ _
      _ ≤ M * (N * μ.real Set.univ) := mul_le_mul hf1 hG1 (norm_nonneg _) hM
  have hInt2 : Integrable (Function.uncurry fun a b => (∫ a', f a' b ∂μ) * g a b)
      (μ.prod μ) := by
    have h1 : AEStronglyMeasurable
        (fun p : α × α => (∫ a', f a' p.2 ∂μ) * g p.1 p.2) (μ.prod μ) :=
      (hFmeas.aestronglyMeasurable.comp_snd).mul (hg.aestronglyMeasurable)
    refine Integrable.of_bound h1 (M * (N * μ.real Set.univ)) ?_
    filter_upwards with p
    have hg1 : ‖g p.1 p.2‖ ≤ N := by simpa [Real.norm_eq_abs] using hgb p.1 p.2
    have hF1 : ‖∫ a', f a' p.2 ∂μ‖ ≤ M * μ.real Set.univ := by
      simpa [Real.norm_eq_abs] using hFbd p.2
    calc ‖(∫ a', f a' p.2 ∂μ) * g p.1 p.2‖
        = ‖(∫ a', f a' p.2 ∂μ)‖ * ‖g p.1 p.2‖ := norm_mul _ _
      _ ≤ (M * μ.real Set.univ) * N := mul_le_mul hF1 hg1 (norm_nonneg _) (by positivity)
      _ = M * (N * μ.real Set.univ) := by ring
  -- pulling the constant `r` out of the iterated integrals
  have hpt1 : ∀ a, (∫ b, f a b * (r * (∫ a', g a' b ∂μ)) ∂μ)
      = r * ∫ b, f a b * (∫ a', g a' b ∂μ) ∂μ := by
    intro a
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with b
    ring
  have hpt2 : ∀ a, (∫ b, (r * (∫ a', f a' b ∂μ)) * g a b ∂μ)
      = r * ∫ b, (∫ a', f a' b ∂μ) * g a b ∂μ := by
    intro a
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with b
    ring
  -- Fubini, then `∫ a, f a b * G b = F b * G b`
  have key1 : (∫ a, ∫ b, f a b * (∫ a', g a' b ∂μ) ∂μ ∂μ)
      = ∫ b, (∫ a, f a b ∂μ) * (∫ a', g a' b ∂μ) ∂μ := by
    rw [MeasureTheory.integral_integral_swap hInt1]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with b
    exact MeasureTheory.integral_mul_const (∫ a', g a' b ∂μ) (fun a => f a b)
  have key2 : (∫ a, ∫ b, (∫ a', f a' b ∂μ) * g a b ∂μ ∂μ)
      = ∫ b, (∫ a, f a b ∂μ) * (∫ a', g a' b ∂μ) ∂μ := by
    rw [MeasureTheory.integral_integral_swap hInt2]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with b
    exact MeasureTheory.integral_const_mul (∫ a', f a' b ∂μ) (fun a => g a b)
  calc (∫ a, ∫ b, f a b * (r * ∫ a', g a' b ∂μ) ∂μ ∂μ)
      = r * ∫ a, ∫ b, f a b * (∫ a', g a' b ∂μ) ∂μ ∂μ := by
        simp_rw [hpt1]; rw [MeasureTheory.integral_const_mul]
    _ = r * ∫ b, (∫ a, f a b ∂μ) * (∫ a', g a' b ∂μ) ∂μ := by rw [key1]
    _ = r * ∫ a, ∫ b, (∫ a', f a' b ∂μ) * g a b ∂μ ∂μ := by rw [← key2]
    _ = ∫ a, ∫ b, (r * ∫ a', f a' b ∂μ) * g a b ∂μ ∂μ := by
        simp_rw [hpt2]; rw [MeasureTheory.integral_const_mul]

end Work.BoseBoxFock
