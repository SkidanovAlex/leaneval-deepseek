import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Elliptic.DivSinBddDefs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.SliceBddBounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-!
## The angular integrability of the first-order terms of `SinQ h`

`SliceBdd_ae_bounds` shows that `deriv (SinQ h)` is bounded on `Iθ = [0,π/2]` by a constant
`C`, almost everywhere.  On `Iθ` the factors `sin(2θ)^p` for `p ≥ 0` are bounded by `1`
(because `0 ≤ sin(2θ) ≤ 1` and `y ↦ y^p` is increasing for `p ≥ 0`), and `cos(2θ)² ≤ 1`.
Hence each of the three integrands below is dominated almost everywhere by the constant
`C ^ 2`, which is integrable on the finite-measure set `Iθ`.

The only non-trivial ingredients are the almost-everywhere bound for `deriv (SinQ h)` and
the (Borel) measurability of `deriv (SinQ h)`, which is the general Mathlib fact
`measurable_deriv`. -/

/-- On `Iθ`, the factor `sin(2θ)^p` with `p ≥ 0` is at most `1` in absolute value. -/
private lemma sin_two_rpow_abs_le_one {p θ : ℝ} (hp : 0 ≤ p) (hθ : θ ∈ Work.Spaces.Iθ) :
    |(Real.sin (2 * θ)) ^ p| ≤ 1 := by
  have hsin0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rw [abs_of_nonneg (Real.rpow_nonneg hsin0 p)]
  exact Real.rpow_le_one hsin0 (Real.sin_le_one _) hp

/-- If `A` is measurable and bounded almost everywhere on `Iθ` by a constant `M ≥ 0`, then
`θ ↦ A θ * sin(2θ)^p` is integrable on `Iθ` for every `p ≥ 0`: the second factor is at most
`1`, so the product is dominated by the integrable constant `M`. -/
private lemma integrableOn_mul_sin_rpow {A : ℝ → ℝ} {p M : ℝ} (hp : 0 ≤ p) (hM : 0 ≤ M)
    (hm : Measurable A) (h : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), |A θ| ≤ M) :
    MeasureTheory.IntegrableOn (fun θ => A θ * (Real.sin (2 * θ)) ^ p)
      Work.Spaces.Iθ volume := by
  have hne : volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hconst : Integrable (fun _ : ℝ => M) (volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.integrableOn_const (C := M) hne
  have hmM : Measurable (fun θ : ℝ => A θ * (Real.sin (2 * θ)) ^ p) :=
    hm.mul ((Real.measurable_sin.comp (measurable_id.const_mul 2)).pow_const p)
  refine hconst.mono' hmM.aestronglyMeasurable ?_
  filter_upwards [h, ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
    with θ hA hθ
  rw [Real.norm_eq_abs, abs_mul]
  calc |A θ| * |(Real.sin (2 * θ)) ^ p| ≤ M * 1 :=
        mul_le_mul hA (sin_two_rpow_abs_le_one hp hθ) (abs_nonneg _) hM
    _ = M := mul_one M

theorem DivSinIntegrable_u1 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (h : ℝ → ℝ)
    (hh : Work.Elliptic.SmoothSlice h) (hb : Work.Elliptic.SliceBdd h) :
    MeasureTheory.IntegrableOn
        (fun θ => (deriv (Work.Elliptic.SinQ h) θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        Work.Spaces.Iθ MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn
        (fun θ => (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          * (deriv (Work.Elliptic.SinQ h) θ) ^ 2)
        Work.Spaces.Iθ MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn
        (fun θ => (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) * (deriv (Work.Elliptic.SinQ h) θ) ^ 2)
        Work.Spaces.Iθ MeasureTheory.volume := by
  obtain ⟨C, hC0, hae⟩ := Work.Elliptic.SliceBdd_ae_bounds h hh hb
  -- The exponents `2 - γ` and `4 - γ` are nonnegative because `1 < γ ≤ 11/10`.
  have hexp2 : 0 ≤ 2 - Work.Spaces.gam α := by
    simp only [Work.Spaces.gam]; linarith
  have hexp4 : 0 ≤ 4 - Work.Spaces.gam α := by
    simp only [Work.Spaces.gam]; linarith
  -- The almost-everywhere bound for `deriv (SinQ h)`.
  have hu : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      |deriv (Work.Elliptic.SinQ h) θ| ≤ C :=
    hae.mono fun θ hθ => hθ.2.2.2.1
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  -- Measurability of the derivative of the quotient.
  have hdm : Measurable (deriv (Work.Elliptic.SinQ h)) := measurable_deriv _
  have hu2m : Measurable (fun θ : ℝ => (deriv (Work.Elliptic.SinQ h) θ) ^ 2) :=
    hdm.pow_const 2
  have hu2a : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      |(deriv (Work.Elliptic.SinQ h) θ) ^ 2| ≤ C ^ 2 := by
    filter_upwards [hu] with θ hθ
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hθ 2
  refine ⟨?_, ?_, ?_⟩
  · -- `(u')² · sin(2θ)^{2-γ}`
    exact integrableOn_mul_sin_rpow hexp2 hC2 hu2m hu2a
  · -- `cos(2θ)² · sin(2θ)^{2-γ} · (u')²`
    have hA : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        |(Real.cos (2 * θ)) ^ 2 * (deriv (Work.Elliptic.SinQ h) θ) ^ 2| ≤ C ^ 2 := by
      filter_upwards [hu] with θ hθ
      rw [abs_mul, abs_pow, abs_pow]
      have hcos : |Real.cos (2 * θ)| ^ 2 ≤ 1 := by
        have := pow_le_pow_left₀ (abs_nonneg (Real.cos (2 * θ))) (Real.abs_cos_le_one (2 * θ)) 2
        simpa using this
      have hu2 : |deriv (Work.Elliptic.SinQ h) θ| ^ 2 ≤ C ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hθ 2
      calc |Real.cos (2 * θ)| ^ 2 * |deriv (Work.Elliptic.SinQ h) θ| ^ 2 ≤ 1 * C ^ 2 :=
            mul_le_mul hcos hu2 (by positivity) (by norm_num)
        _ = C ^ 2 := one_mul _
    have hmA : Measurable
        (fun θ : ℝ => (Real.cos (2 * θ)) ^ 2 * (deriv (Work.Elliptic.SinQ h) θ) ^ 2) :=
      (Real.measurable_cos.comp (measurable_id.const_mul 2)).pow_const 2 |>.mul hu2m
    refine (integrableOn_mul_sin_rpow hexp2 hC2 hmA hA).congr_fun ?_ measurableSet_Icc
    intro θ _
    ring
  · -- `sin(2θ)^{4-γ} · (u')²`
    refine (integrableOn_mul_sin_rpow hexp4 hC2 hu2m hu2a).congr_fun ?_ measurableSet_Icc
    intro θ _
    ring
