import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.EllTwoAsm

theorem HeavyDerivIntegrable (a : ℝ) (ha : -1 < a) (ha0 : a ≤ 0) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ a) (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => deriv f θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) ∧
    (∀ a' b' : ℝ, Set.Ioo a' b' ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => deriv f θ) (Set.Ioo a' b')) := by
  -- `(0, π/2)` is open, so `f ∈ C¹` there gives `deriv f` continuous there, hence measurable.
  set s := Set.Ioo (0 : ℝ) (Real.pi / 2) with hs
  have hcont : ContinuousOn (deriv f) s :=
    hf.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have hsaesm : MeasureTheory.AEStronglyMeasurable (deriv f)
      (MeasureTheory.volume.restrict s) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  -- On `(0, π/2)` we have `0 < sin (2θ) ≤ 1`; with `a ≤ 0` this gives `1 ≤ sin (2θ) ^ a`.
  have hsinpos : ∀ θ ∈ s, 0 < Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hone : ∀ θ ∈ s, (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ a := by
    intro θ hθ
    have h := Real.rpow_le_rpow_of_exponent_ge (hsinpos θ hθ) (Real.sin_le_one _) ha0
    simpa using h
  -- Hence `(deriv f)² ≤ (deriv f)² · sin (2θ) ^ a` pointwise, so `(deriv f)²` is integrable.
  have hsq_int : MeasureTheory.Integrable (fun θ : ℝ => (deriv f θ) ^ 2)
      (MeasureTheory.volume.restrict s) := by
    refine hint.mono' (MeasureTheory.AEStronglyMeasurable.pow hsaesm 2) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have h1 := hone θ hθ
    have hsq : 0 ≤ (deriv f θ) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hsq]
    simpa using mul_le_mul_of_nonneg_left h1 hsq
  -- Since `(0, π/2)` has finite measure, `|deriv f| ≤ (deriv f)² + 1` is integrable.
  have hmaj : MeasureTheory.Integrable (fun θ : ℝ => (deriv f θ) ^ 2 + 1)
      (MeasureTheory.volume.restrict s) :=
    hsq_int.add (MeasureTheory.integrable_const (1 : ℝ))
  have hmain : MeasureTheory.IntegrableOn (fun θ : ℝ => deriv f θ) s := by
    refine hmaj.mono' hsaesm ?_
    filter_upwards with θ
    have h1 : |deriv f θ| ≤ (deriv f θ) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|deriv f θ| - 1 / 2), sq_abs (deriv f θ), abs_nonneg (deriv f θ)]
    simpa only [Real.norm_eq_abs] using h1
  refine ⟨hmain, fun a' b' hab => ?_⟩
  exact hmain.mono_set hab


end Work.FTS.EllipticEst.EllTwoAsm
