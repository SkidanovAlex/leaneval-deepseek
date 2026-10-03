import Mathlib
import Submission.Work.L62.norm_second_order_integrand_le

namespace Work.L62

namespace Work.L62

/-- **Cauchy integral representation of the second-order Taylor remainder** (auxiliary).

If `f` is holomorphic on the closed disc `closedBall c R` of radius `R > 0`, then for every
`u` in the open disc
`2πi (f u - f c - f'(c)(u-c)) = ∮_{|ζ-c|=R} f ζ · (u-c)²/((ζ-u)(ζ-c)²) dζ`:
on the circle `|ζ-c| = R` the algebraic identity
`(u-c)²/((ζ-u)(ζ-c)²) = (ζ-u)⁻¹ - (ζ-c)⁻¹ - (u-c)/(ζ-c)²`
holds (`ζ ≠ c` because `R > 0`, `ζ ≠ u` because `|ζ-u| ≥ R - |u-c| > 0`), and the three
integrated pieces are given by the Cauchy formulas
`DifferentiableOn.circleIntegral_sub_inv_smul` (at `u` and at `c`) and
`DifferentiableOn.deriv_eq_smul_circleIntegral`. -/
theorem cauchy_second_order_representation_aux {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall c R)) :
    ∀ u ∈ Metric.ball c R,
      (2 * (Real.pi : ℂ) * Complex.I) • (f u - f c - deriv f c * (u - c)) =
        ∮ z in C(c, R), (((u - c) ^ 2 / ((z - u) * (z - c) ^ 2) : ℂ) • f z) := by
  intro u hu
  have hc_ball : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  have h1 := DifferentiableOn.circleIntegral_sub_inv_smul hf hu
  have h2 := DifferentiableOn.circleIntegral_sub_inv_smul hf hc_ball
  have h3 := DifferentiableOn.deriv_eq_smul_circleIntegral hR hf
  have hfc : ContinuousOn f (Metric.sphere c R) :=
    hf.continuousOn.mono Metric.sphere_subset_closedBall
  have hzu : ∀ z ∈ Metric.sphere c R, z - u ≠ 0 := by
    intro z hz h
    have hz' : ‖z - c‖ = R := by
      have := Metric.mem_sphere.mp hz
      rwa [dist_eq_norm] at this
    have hu' : ‖u - c‖ < R := by
      have := Metric.mem_ball.mp hu
      rwa [dist_eq_norm] at this
    rw [sub_eq_zero.mp h] at hz'
    linarith
  have hzc : ∀ z ∈ Metric.sphere c R, z - c ≠ 0 := by
    intro z hz h
    have hz' : ‖z - c‖ = R := by
      have := Metric.mem_sphere.mp hz
      rwa [dist_eq_norm] at this
    rw [h, norm_zero] at hz'
    linarith
  have ha : CircleIntegrable (fun z => (z - u)⁻¹ • f z) c R :=
    (((continuousOn_id.sub continuousOn_const).inv₀ hzu).smul hfc).circleIntegrable hR.le
  have hb : CircleIntegrable (fun z => (z - c)⁻¹ • f z) c R :=
    (((continuousOn_id.sub continuousOn_const).inv₀ hzc).smul hfc).circleIntegrable hR.le
  have hcontsq : ContinuousOn (fun z => 1 / (z - c) ^ 2) (Metric.sphere c R) :=
    continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2)
      (fun z hz => pow_ne_zero 2 (hzc z hz))
  have hd : CircleIntegrable (fun z => ((u - c) * (1 / (z - c) ^ 2)) • f z) c R :=
    ((continuousOn_const.mul hcontsq).smul hfc).circleIntegrable hR.le
  have hident : ∀ z ∈ Metric.sphere c R,
      ((u - c) ^ 2 / ((z - u) * (z - c) ^ 2) : ℂ)
        = (z - u)⁻¹ - (z - c)⁻¹ - (u - c) * (1 / (z - c) ^ 2) := by
    intro z hz
    have h1' := hzu z hz
    have h2' := hzc z hz
    field_simp
    ring
  have hd' : (∮ z in C(c, R), ((u - c) * (1 / (z - c) ^ 2)) • f z)
      = (u - c) • ∮ z in C(c, R), (1 / (z - c) ^ 2) • f z := by
    rw [← circleIntegral.integral_smul (u - c) (fun z => (1 / (z - c) ^ 2) • f z) c R]
    exact circleIntegral.integral_congr hR.le
      (fun z _ => mul_smul (u - c) (1 / (z - c) ^ 2) (f z))
  have hsplit : ∀ z : ℂ,
      ((z - u)⁻¹ - (z - c)⁻¹ - (u - c) * (1 / (z - c) ^ 2)) • f z
        = ((z - u)⁻¹ • f z - (z - c)⁻¹ • f z) - ((u - c) * (1 / (z - c) ^ 2)) • f z := by
    intro z
    rw [sub_smul, sub_smul]
  have hcongr1 : (∮ z in C(c, R), (((u - c) ^ 2 / ((z - u) * (z - c) ^ 2) : ℂ) • f z))
      = (∮ z in C(c, R), ((z - u)⁻¹ - (z - c)⁻¹ - (u - c) * (1 / (z - c) ^ 2)) • f z) :=
    circleIntegral.integral_congr hR.le (fun z hz => by rw [hident z hz])
  have hcongr2 : (∮ z in C(c, R), ((z - u)⁻¹ - (z - c)⁻¹ - (u - c) * (1 / (z - c) ^ 2)) • f z)
      = (∮ z in C(c, R), ((z - u)⁻¹ • f z - (z - c)⁻¹ • f z)
            - ((u - c) * (1 / (z - c) ^ 2)) • f z) :=
    circleIntegral.integral_congr hR.le (fun z _ => hsplit z)
  have hlin1 : (∮ z in C(c, R), ((z - u)⁻¹ • f z - (z - c)⁻¹ • f z)
            - ((u - c) * (1 / (z - c) ^ 2)) • f z)
      = (∮ z in C(c, R), ((z - u)⁻¹ • f z - (z - c)⁻¹ • f z))
        - (∮ z in C(c, R), ((u - c) * (1 / (z - c) ^ 2)) • f z) :=
    circleIntegral.integral_sub (ha.sub hb) hd
  have hlin2 : (∮ z in C(c, R), ((z - u)⁻¹ • f z - (z - c)⁻¹ • f z))
      = (∮ z in C(c, R), (z - u)⁻¹ • f z) - (∮ z in C(c, R), (z - c)⁻¹ • f z) :=
    circleIntegral.integral_sub ha hb
  have heval : (∮ z in C(c, R), ((z - u)⁻¹ • f z - (z - c)⁻¹ • f z)
            - ((u - c) * (1 / (z - c) ^ 2)) • f z)
      = (2 * (Real.pi : ℂ) * Complex.I) • (f u - f c - deriv f c * (u - c)) := by
    rw [hlin1, hlin2, hd', h1, h2, h3]
    simp only [smul_eq_mul]
    ring
  exact (hcongr1.trans (hcongr2.trans heval)).symm

/-- **Second-order Taylor remainder with a uniform bound on the boundary circle.**

`f` is holomorphic on the closed disc `closedBall c R` (`0 < R`), `‖f z‖ ≤ M` on the boundary
circle `sphere c R` (`0 ≤ M`).  Then the second-order Taylor remainder at the centre is
`O(‖u-c‖²)` on the disc of radius `R/2` with the explicit constant `2M/R²`.

Route: combine the Cauchy integral formulas `∮ f ζ/(ζ-u) = 2πi f u`,
`∮ f ζ/(ζ-c) = 2πi f c` and `∮ f ζ/(ζ-c)² = 2πi f'(c)`
(`DifferentiableOn.circleIntegral_sub_inv_smul`, `DifferentiableOn.deriv_eq_smul_circleIntegral`,
both in Mathlib/Analysis/Complex/CauchyIntegral.lean), to get
`2πi (f u - f c - f'(c)(u-c)) = ∮_{|ζ-c|=R} f ζ · w²/((ζ-u)(ζ-c)²) dζ`, `w = u - c`, and bound
the integrand by `M ‖w‖²/((R/2)R²)` on the circle (where `|ζ-u| ≥ R - ‖w‖ ≥ R/2`) using
`circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const`
(Mathlib/MeasureTheory/Integral/CircleIntegral.lean). -/
theorem holomorphic_second_order_remainder {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hM0 : 0 ≤ M) (hf : DifferentiableOn ℂ f (Metric.closedBall c R))
    (hM : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ M) :
    ∀ u : ℂ, ‖u - c‖ ≤ R / 2 →
      ‖f u - f c - deriv f c * (u - c)‖ ≤ (2 * M / R ^ 2) * ‖u - c‖ ^ 2 := by
  intro u hu
  -- `u` lies in the open disc
  have hu_ball : u ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_eq_norm]
    linarith
  -- Cauchy integral representation of the second order remainder
  have hrep := cauchy_second_order_representation_aux hR hf u hu_ball
  -- pointwise bound on the integrand
  have hC := _root_.Work.L62.norm_second_order_integrand_le (u := u) hR hM0 hM hu
  -- Cauchy's estimate on the circle
  have hbound := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le hC
  -- the arithmetic identity for the constant
  have harith :
      R * (M * ‖u - c‖ ^ 2 / ((R / 2) * R ^ 2)) = (2 * M / R ^ 2) * ‖u - c‖ ^ 2 := by
    field_simp
  calc ‖f u - f c - deriv f c * (u - c)‖
      = ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
            ((2 * (Real.pi : ℂ) * Complex.I) • (f u - f c - deriv f c * (u - c)))‖ := by
          rw [inv_smul_smul₀ Complex.two_pi_I_ne_zero]
    _ = ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
            ∮ z in C(c, R), (((u - c) ^ 2 / ((z - u) * (z - c) ^ 2) : ℂ) • f z)‖ := by
          rw [hrep]
    _ ≤ R * (M * ‖u - c‖ ^ 2 / ((R / 2) * R ^ 2)) := hbound
    _ = (2 * M / R ^ 2) * ‖u - c‖ ^ 2 := harith

end Work.L62

/-- Alias of `Work.L62.Work.L62.holomorphic_second_order_remainder` under the namespace derived
from the module path, so that the lemma is reachable under either name. -/
theorem holomorphic_second_order_remainder {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hM0 : 0 ≤ M) (hf : DifferentiableOn ℂ f (Metric.closedBall c R))
    (hM : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ M) :
    ∀ u : ℂ, ‖u - c‖ ≤ R / 2 →
      ‖f u - f c - deriv f c * (u - c)‖ ≤ (2 * M / R ^ 2) * ‖u - c‖ ^ 2 :=
  _root_.Work.L62.Work.L62.holomorphic_second_order_remainder hR hM0 hf hM

end Work.L62
