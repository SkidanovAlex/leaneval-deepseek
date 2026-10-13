import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.PhiStar.Honesty.sq_integral_sqrt_mul_le
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.PhiStar.Honesty.integrableOn_eFam_cos_sq_sin_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory
open scoped Real

/-- **Weighted Cauchy–Schwarz for the `η`-weighted slice pairing.**

With the weights `A θ = (F z θ)^2 * sin(2θ)^{-η}` and
`B θ = (eFam m θ cos θ)^2 * sin(2θ)^{η}` the Cauchy–Schwarz (Bunyakovsky) inequality applied to
`√A` and `√B` gives

`(∫_Iθ F z θ · eFam m θ · cos θ)^2 ≤ (∫_Iθ (F z θ)^2 sin(2θ)^{-η}) · (∫_Iθ (eFam m θ cos θ)^2 sin(2θ)^{η})`,

because `√A · √B = |F z θ| · |eFam m θ cos θ|` on the interior of `Iθ` (the two weights multiply to
`1` there) and the target integral is dominated by the integral of its absolute value.  The
integrability hypothesis on `A` is used, together with the fact that `B` is integrable on the
compact `Iθ` (the `eFam m` are polynomials composed with `sin`, multiplied by `cos`). -/
theorem sliceMass_moment_le {m : ℕ} {F : ℝ → ℝ → ℝ} {z : ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        * (∫ θ in Work.Spaces.Iθ,
            (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
              * (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) := by
  let A : ℝ → ℝ := fun θ : ℝ => (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
  let B : ℝ → ℝ := fun θ : ℝ =>
    (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
      * (Real.sin (2 * θ)) ^ (Work.Spaces.eta)
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hA : MeasureTheory.IntegrableOn A Work.Spaces.Iθ := hint
  have hB : MeasureTheory.IntegrableOn B Work.Spaces.Iθ :=
    (Work.PhiStar.Honesty.integrableOn_eFam_cos_sq_sin_rpow m).1
  have hAnn : ∀ x ∈ Work.Spaces.Iθ, 0 ≤ A x := by
    intro x hx
    change 0 ≤ (F z x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta))
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.PhiStar.Honesty.sin_two_nonneg_of_mem_Iθ hx) _)
  have hBnn : ∀ x ∈ Work.Spaces.Iθ, 0 ≤ B x := by
    intro x hx
    change 0 ≤ (Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x) ^ 2
      * (Real.sin (2 * x)) ^ (Work.Spaces.eta)
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.PhiStar.Honesty.sin_two_nonneg_of_mem_Iθ hx) _)
  -- Cauchy–Schwarz for the two square roots
  have hcs := Work.PhiStar.Honesty.sq_integral_sqrt_mul_le hIθ hA hB hAnn hBnn
  -- The square-root product equals `|F z ·| * |eFam m · · cos ·|` up to the two endpoints of `Iθ`.
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Work.Spaces.Iθ →
      Real.sqrt (A x) * Real.sqrt (B x)
        = |F z x| * |Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x| := by
    rw [MeasureTheory.ae_iff]
    have hnull : volume ({(0 : ℝ), π / 2} : Set ℝ) = 0 :=
      Set.Finite.measure_zero ((Set.finite_singleton (π / 2)).insert (0 : ℝ)) volume
    refine MeasureTheory.measure_mono_null ?_ hnull
    intro x hx
    rw [Set.mem_setOf_eq, not_imp] at hx
    obtain ⟨hxI, hxne⟩ := hx
    have hmem : (0 : ℝ) ≤ x ∧ x ≤ π / 2 := hxI
    have hbd : ¬ (0 < x ∧ x < π / 2) := fun h =>
      hxne (Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo F m z h)
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases lt_or_eq_of_le hmem.1 with h0 | h0
    · right
      have hge : π / 2 ≤ x := by
        by_contra hlt
        exact hbd ⟨h0, lt_of_not_ge hlt⟩
      exact le_antisymm hmem.2 hge
    · left; exact h0.symm
  have hEq : (∫ x in Work.Spaces.Iθ, Real.sqrt (A x) * Real.sqrt (B x))
      = ∫ x in Work.Spaces.Iθ,
          |F z x| * |Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x| :=
    MeasureTheory.setIntegral_congr_ae hIθ hae
  -- The target integral is dominated by the integral of its absolute value, which in turn is the
  -- integral of `|F| * |eFam·cos|`.
  have h1 : |∫ x in Work.Spaces.Iθ,
        F z x * Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x|
      ≤ ∫ x in Work.Spaces.Iθ,
          |F z x * Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x| := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := (volume : Measure ℝ).restrict Work.Spaces.Iθ)
        (f := fun x : ℝ => F z x * Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x))
  have h2 : (∫ x in Work.Spaces.Iθ,
        |F z x * Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x|)
      = ∫ x in Work.Spaces.Iθ,
          |F z x| * |Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x| :=
    MeasureTheory.setIntegral_congr_fun hIθ (fun x _ => by
      rw [abs_mul, abs_mul, abs_mul]
      ring)
  have h3 : |∫ x in Work.Spaces.Iθ,
        F z x * Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x|
      ≤ ∫ x in Work.Spaces.Iθ,
          |F z x| * |Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x| := by
    rw [← h2]; exact h1
  calc (∫ x in Work.Spaces.Iθ, F z x * Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x) ^ 2
      = |∫ x in Work.Spaces.Iθ,
            F z x * Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ x in Work.Spaces.Iθ,
          |F z x| * |Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h3 2
    _ = (∫ x in Work.Spaces.Iθ, Real.sqrt (A x) * Real.sqrt (B x)) ^ 2 := by rw [hEq]
    _ ≤ (∫ x in Work.Spaces.Iθ, A x) * (∫ x in Work.Spaces.Iθ, B x) := hcs

end Work.FTS.PhiStar.Honesty
