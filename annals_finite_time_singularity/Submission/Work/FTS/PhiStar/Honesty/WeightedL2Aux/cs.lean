/-
# `Work.FTS.PhiStar.Honesty.WeightedL2Aux.cs`

Two elementary measure-theoretic tools used by the weighted-`L²` convergence
`radGreen_tendsto_of_weightedL2`:

* `sq_setIntegral_mul_le` — Cauchy–Schwarz for the set integral of two functions whose squares
  are integrable (no measurability hypothesis on the functions themselves: it goes through the
  "square roots" form `Work.PhiStar.Honesty.sq_integral_sqrt_mul_le` and
  `|∫ f g| ≤ ∫ |f g|`);

* `integral_sub_abs_le` — the *junk-robust* additivity of the Bochner integral:
  if `f - g` is integrable on `s`, then `|∫_s f - ∫_s g| ≤ |∫_s (f - g)|`.  When `f` is
  integrable the two sides are equal; when `f` is not, `g` is not either (since `f = g + (f-g)`),
  so both sides vanish.  This is the form needed to compare `∫ f` and `∫ g` without assuming
  that either is integrable.

* `sqrt_add_le` — `√(a+b) ≤ √a + √b`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.PhiStar.Honesty.sq_integral_sqrt_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.PhiStar.Honesty.WeightedL2Aux

set_option autoImplicit false

/-- **Cauchy–Schwarz for the set integral.**  If `f²` and `g²` are integrable on the measurable
set `s`, then `(∫_s f g)² ≤ (∫_s f²)(∫_s g²)`.  No measurability of `f` or `g` is required. -/
theorem sq_setIntegral_mul_le {s : Set ℝ} (hs : MeasurableSet s) {f g : ℝ → ℝ}
    (hf : IntegrableOn (fun t => (f t) ^ 2) s)
    (hg : IntegrableOn (fun t => (g t) ^ 2) s) :
    (∫ t in s, f t * g t) ^ 2 ≤ (∫ t in s, (f t) ^ 2) * (∫ t in s, (g t) ^ 2) := by
  have hcs := Work.PhiStar.Honesty.sq_integral_sqrt_mul_le hs hf hg
    (fun t _ => sq_nonneg (f t)) (fun t _ => sq_nonneg (g t))
  have h1 : (∫ t in s, Real.sqrt ((f t) ^ 2) * Real.sqrt ((g t) ^ 2))
      = ∫ t in s, |f t| * |g t| :=
    MeasureTheory.setIntegral_congr_fun hs (fun t _ => by
      rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs])
  have h2 : (∫ t in s, |f t| * |g t|) = ∫ t in s, |f t * g t| :=
    MeasureTheory.setIntegral_congr_fun hs (fun t _ => by rw [abs_mul])
  have h3 : |∫ t in s, f t * g t| ≤ ∫ t in s, |f t * g t| :=
    MeasureTheory.abs_integral_le_integral_abs (f := fun t => f t * g t)
  have h4 : (∫ t in s, |f t * g t|) = ∫ t in s, Real.sqrt ((f t) ^ 2) * Real.sqrt ((g t) ^ 2) :=
    (h1.trans h2).symm
  calc (∫ t in s, f t * g t) ^ 2
      = |∫ t in s, f t * g t| ^ 2 := by rw [sq_abs]
    _ ≤ (∫ t in s, |f t * g t|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h3 2
    _ = (∫ t in s, Real.sqrt ((f t) ^ 2) * Real.sqrt ((g t) ^ 2)) ^ 2 := by rw [h4]
    _ ≤ (∫ t in s, (f t) ^ 2) * (∫ t in s, (g t) ^ 2) := hcs

/-- **Junk-robust difference of set integrals.**  If `f - g` is integrable on `s`, then
`|∫_s f - ∫_s g| ≤ |∫_s (f - g)|`. -/
theorem integral_sub_abs_le {s : Set ℝ} {f g : ℝ → ℝ}
    (h : IntegrableOn (fun t => f t - g t) s) :
    |(∫ t in s, f t) - (∫ t in s, g t)| ≤ |∫ t in s, (f t - g t)| := by
  by_cases hf : IntegrableOn f s
  · have hg : IntegrableOn g s :=
      MeasureTheory.Integrable.congr (hf.sub h)
        (Filter.Eventually.of_forall (fun t => by change f t - (f t - g t) = g t; ring))
    rw [MeasureTheory.integral_sub hf hg]
  · have hg : ¬ IntegrableOn g s := by
      intro hg
      refine hf ?_
      have h1 : IntegrableOn (fun t => g t + (f t - g t)) s := hg.add h
      exact MeasureTheory.Integrable.congr h1
        (Filter.Eventually.of_forall (fun t => by ring))
    rw [MeasureTheory.integral_undef hf, MeasureTheory.integral_undef hg]
    simp

/-- `√(a+b) ≤ √a + √b` for `a, b ≥ 0`. -/
theorem sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have h2 := Real.sq_sqrt ha
    have h3 := Real.sq_sqrt hb
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, h2, h3]
  have h4 : Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) :=
    Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b))] at h4

end Work.FTS.PhiStar.Honesty.WeightedL2Aux
