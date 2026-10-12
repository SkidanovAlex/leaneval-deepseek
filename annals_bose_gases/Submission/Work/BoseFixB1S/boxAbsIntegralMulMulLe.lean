import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseFixB1S.BoxPIndFlat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory

set_option linter.style.haveILetI false

/-- Cauchy–Schwarz on the centred box with a bounded weight: for measurable `f`, `g`, bounded on
`abox N ℓ` by `Cf`, `Cg`, and any `w` with `|w| ≤ sw` everywhere,
`|∫_{abox} f g w| ≤ sw √(∫_{abox} f²) √(∫_{abox} g²)`.

No measurability of `w` is assumed; if `f g w` fails to be integrable its Bochner integral is `0`
(`integral_undef`), which is the favourable case, and otherwise `f g w` is a.e. strongly measurable
and the monotonicity of the integral applies.  The Cauchy–Schwarz step is the corpus lemma
`Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt` applied to `|f|`, `|g|` (both in `L²` of
the finite measure `volume ↾ abox N ℓ` by `MemLp.of_bound`). -/
theorem boxAbsIntegralMulMulLe {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {f g w : Submission.BoseGases.X N → ℝ} {Cf Cg sw : ℝ}
    (hfm : Measurable f) (hgm : Measurable g)
    (hfb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |f x| ≤ Cf)
    (hgb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |g x| ≤ Cg)
    (hw : ∀ x, |w x| ≤ sw) :
    |∫ x in Submission.BoseGases.abox N ℓ, f x * g x * w x|
      ≤ sw * Real.sqrt (∫ x in Submission.BoseGases.abox N ℓ, f x ^ 2)
          * Real.sqrt (∫ x in Submission.BoseGases.abox N ℓ, g x ^ 2) := by
  let μ : Measure (Submission.BoseGases.X N) :=
    (volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N ℓ)
  change |∫ x, f x * g x * w x ∂μ|
      ≤ sw * Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ)
  have hfin : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact Submission.BoseGases.abox_lt_top N ℓ hℓ.le
  letI : IsFiniteMeasure μ := hfin
  have hsw : 0 ≤ sw := le_trans (abs_nonneg _) (hw 0)
  have hbf : ∀ᵐ x ∂μ, |f x| ≤ Cf := by
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    exact ae_of_all volume (fun x hx => hfb x hx)
  have hbg : ∀ᵐ x ∂μ, |g x| ≤ Cg := by
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    exact ae_of_all volume (fun x hx => hgb x hx)
  have hmf : MemLp (fun x => |f x|) 2 μ :=
    MemLp.of_bound hfm.aestronglyMeasurable.norm (max Cf 0) (by
      filter_upwards [hbf] with x hx
      rw [Real.norm_eq_abs, abs_abs]
      exact le_trans hx (le_max_left _ _))
  have hmg : MemLp (fun x => |g x|) 2 μ :=
    MemLp.of_bound hgm.aestronglyMeasurable.norm (max Cg 0) (by
      filter_upwards [hbg] with x hx
      rw [Real.norm_eq_abs, abs_abs]
      exact le_trans hx (le_max_left _ _))
  have hcsP : ∫ x, |f x| * |g x| ∂μ ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
    have h := Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt (μ := μ) hmf hmg
    have h1 : (∫ x, |f x| ^ 2 ∂μ) = ∫ x, f x ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [sq_abs]
    have h2 : (∫ x, |g x| ^ 2 ∂μ) = ∫ x, g x ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [sq_abs]
    rw [h1, h2] at h
    have hnn : 0 ≤ ∫ x, |f x| * |g x| ∂μ :=
      integral_nonneg (fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    rwa [abs_of_nonneg hnn] at h
  have hIfg : Integrable (fun x => |f x| * |g x|) μ :=
    Integrable.of_bound (hfm.abs.aestronglyMeasurable.mul hgm.abs.aestronglyMeasurable)
      (max Cf 0 * max Cg 0) (by
        filter_upwards [hbf, hbg] with x hx hy
        rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_abs]
        exact mul_le_mul (le_trans hx (le_max_left _ _)) (le_trans hy (le_max_left _ _))
          (abs_nonneg _) (le_max_right _ _))
  have hIcon : Integrable (fun x => (|f x| * |g x|) * sw) μ := hIfg.mul_const sw
  by_cases hφ : Integrable (fun x => f x * g x * w x) μ
  · have hIφ : Integrable (fun x => |f x * g x * w x|) μ := hφ.norm
    have hmono : ∫ x, |f x * g x * w x| ∂μ ≤ ∫ x, (|f x| * |g x|) * sw ∂μ :=
      integral_mono_ae hIφ hIcon (by
        filter_upwards with x
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hw x) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    calc |∫ x, f x * g x * w x ∂μ|
        ≤ ∫ x, |f x * g x * w x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, (|f x| * |g x|) * sw ∂μ := hmono
      _ = (∫ x, |f x| * |g x| ∂μ) * sw := integral_mul_const sw _
      _ ≤ (Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ)) * sw :=
            mul_le_mul_of_nonneg_right hcsP hsw
      _ = sw * Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by ring
  · rw [integral_undef hφ]
    simp only [abs_zero]
    exact mul_nonneg (mul_nonneg hsw (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end Work.BoseFixB1S
