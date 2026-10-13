import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.Have
import Submission.Work.FTS.EllipticEst.TT.SinHardy.Narrow.powHardyOpenAlt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular weighted Hardy inequality on the quarter interval

For `1 < c ≤ 2` and `u` of class `C¹` on `(0, π/4)` whose left trace vanishes, one has

  `∫_{(0,π/4)} sin(2θ)^{-c} u² ≤ 4/(c-1)² ∫_{(0,π/4)} sin(2θ)^{2-c} (u')²`,

as an inequality of Lebesgue integrals in `ℝ≥0∞` (so no integrability hypothesis is needed:
the left-hand side is finite as soon as the right-hand one is).  This is the *sharp* Hardy
constant for the power weight, `4/(1+η)²` with `η = c-2 ∈ (-1,0]`.

## Route

Put `η := c - 2` so that `2 + η = c`, `1 + η = c - 1` and `-η = 2 - c`.

* **Weight comparison with powers.**  Jordan's inequality `sin(2θ) ≥ (4/π)θ` on `(0,π/4)` gives,
  in the two directions needed, `sin(2θ)^{-c} ≤ (π/4)^c θ^{-c}` and `θ^{2-c} ≤ (π/4)^{2-c}
  sin(2θ)^{2-c}` (the second uses that the exponent `2-c` is nonnegative).
* **Power Hardy.**  `powerHardy_open` (the completion-of-squares / Fatou argument of
  `TT.SinHardy.Narrow`) gives `∫_{(0,π/4)} θ^{-c} u² ≤ (4/(c-1)²) ∫_{(0,π/4)} θ^{2-c} (u')²`
  directly as a `∫⁻`-inequality.
* The constants multiply to `(π/4)^c · (4/(c-1)²) · (π/4)^{2-c} = (π/4)² · 4/(c-1)² ≤ 4/(c-1)²`.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

/-- **Jordan's inequality on the quarter interval**: `θ ≤ (π/4) sin(2θ)` for `0 < θ < π/4`. -/
private lemma quarter_le_sin {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    θ ≤ (Real.pi / 4) * Real.sin (2 * θ) := by
  have h2θ0 : (0 : ℝ) ≤ 2 * θ := by linarith [hθ.1]
  have h2θπ : 2 * θ ≤ Real.pi / 2 := by linarith [hθ.2, Real.pi_pos]
  have h := Real.mul_le_sin h2θ0 h2θπ
  have heq : (Real.pi / 4) * (2 / Real.pi * (2 * θ)) = θ := by
    field_simp
    ring
  calc θ = (Real.pi / 4) * (2 / Real.pi * (2 * θ)) := heq.symm
    _ ≤ (Real.pi / 4) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left h (by positivity)

/-- `sin(2θ)^{-c} ≤ (π/4)^c θ^{-c}` on `(0,π/4)` for `c > 0`. -/
private lemma sin_pow_neg_le {c : ℝ} (hc : 0 < c) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    (Real.sin (2 * θ)) ^ (-c) ≤ (Real.pi / 4) ^ c * θ ^ (-c) := by
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hj := quarter_le_sin hθ
  have hdiv : θ / Real.sin (2 * θ) ≤ Real.pi / 4 := by
    rw [div_le_iff₀ hsinpos]; linarith [hj]
  have h1 : (θ / Real.sin (2 * θ)) ^ c ≤ (Real.pi / 4) ^ c :=
    Real.rpow_le_rpow (div_nonneg hθ.1.le hsinpos.le) hdiv hc.le
  have h2 : (θ / Real.sin (2 * θ)) ^ c = θ ^ c * (Real.sin (2 * θ)) ^ (-c) := by
    rw [Real.div_rpow hθ.1.le hsinpos.le, div_eq_mul_inv, ← Real.rpow_neg hsinpos.le]
  have h3 : θ ^ c * (Real.sin (2 * θ)) ^ (-c) ≤ (Real.pi / 4) ^ c := h2 ▸ h1
  have hθc : (0 : ℝ) < θ ^ c := Real.rpow_pos_of_pos hθ.1 c
  have h4 : (Real.sin (2 * θ)) ^ (-c) ≤ (Real.pi / 4) ^ c / θ ^ c := by
    rw [le_div_iff₀ hθc]; linarith [h3]
  have h5 : (Real.pi / 4) ^ c / θ ^ c = (Real.pi / 4) ^ c * θ ^ (-c) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hθ.1.le]
  linarith [h4, h5]

/-- `θ^{2-c} ≤ (π/4)^{2-c} sin(2θ)^{2-c}` on `(0,π/4)` for `c ≤ 2`. -/
private lemma pow_le_sin_pow {c : ℝ} (hc2 : c ≤ 2) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    θ ^ (2 - c) ≤ (Real.pi / 4) ^ (2 - c) * (Real.sin (2 * θ)) ^ (2 - c) := by
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hj := quarter_le_sin hθ
  have h2c : (0 : ℝ) ≤ 2 - c := by linarith
  calc θ ^ (2 - c) ≤ ((Real.pi / 4) * Real.sin (2 * θ)) ^ (2 - c) :=
        Real.rpow_le_rpow hθ.1.le hj h2c
    _ = (Real.pi / 4) ^ (2 - c) * (Real.sin (2 * θ)) ^ (2 - c) :=
        Real.mul_rpow (by positivity) hsinpos.le

theorem sinHardyGamLeft (c : ℝ) (hc1 : 1 < c) (hc2 : c ≤ 2) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Set.Ioo (0 : ℝ) (Real.pi / 4)))
    (h0 : Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal (4 / (c - 1) ^ 2) *
        (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := by
  have h4pos : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hc0 : (0 : ℝ) < c := by linarith
  have hKpos : (0 : ℝ) < 4 / (c - 1) ^ 2 := by positivity
  have hpi_nn : (0 : ℝ) ≤ (Real.pi / 4) ^ c := (Real.rpow_pos_of_pos h4pos c).le
  have hpi_nn2 : (0 : ℝ) ≤ (Real.pi / 4) ^ (2 - c) := (Real.rpow_pos_of_pos h4pos (2 - c)).le
  -- ## Step A: compare `sin(2θ)^{-c}` with the power `θ^{-c}`
  have hA : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal ((Real.pi / 4) ^ c) *
        (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), ENNReal.ofReal (θ ^ (-c) * (u θ) ^ 2)) := by
    rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine MeasureTheory.lintegral_mono_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall fun θ hθ => ?_)
    have hcmp := sin_pow_neg_le hc0 hθ
    rw [← ENNReal.ofReal_mul hpi_nn]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2
        ≤ ((Real.pi / 4) ^ c * θ ^ (-c)) * (u θ) ^ 2 :=
          mul_le_mul_of_nonneg_right hcmp (sq_nonneg _)
      _ = (Real.pi / 4) ^ c * (θ ^ (-c) * (u θ) ^ 2) := by ring
  -- ## Step B: the power-weighted Hardy inequality
  have hB := Work.FTS.EllipticEst.TT.SinHardy.NarrowAlt.powerHardy_open
      (a := Real.pi / 4) (η := c - 2) h4pos (by linarith) (by linarith)
      (hu.continuousOn.aemeasurable measurableSet_Ioo) hu h0
  have hB' : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), ENNReal.ofReal (θ ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal (4 / (c - 1) ^ 2) *
        (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal (θ ^ (2 - c) * (deriv u θ) ^ 2)) := by
    have e1 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal (u θ ^ 2 * θ ^ (-(2 + (c - 2)))))
        = (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), ENNReal.ofReal (θ ^ (-c) * (u θ) ^ 2)) := by
      refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      congr 1
      rw [show -(2 + (c - 2)) = -c by ring]
      ring
    have e2 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal (deriv u θ ^ 2 * θ ^ (-(c - 2))))
        = (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal (θ ^ (2 - c) * (deriv u θ) ^ 2)) := by
      refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      congr 1
      rw [show -(c - 2) = 2 - c by ring]
      ring
    rw [e1, e2] at hB
    rw [show (4 : ℝ) / (1 + (c - 2)) ^ 2 = 4 / (c - 1) ^ 2 by ring] at hB
    exact hB
  -- ## Step C: compare the power `θ^{2-c}` with `sin(2θ)^{2-c}`
  have hC : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), ENNReal.ofReal (θ ^ (2 - c) * (deriv u θ) ^ 2))
      ≤ ENNReal.ofReal ((Real.pi / 4) ^ (2 - c)) *
        (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := by
    rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine MeasureTheory.lintegral_mono_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall fun θ hθ => ?_)
    have hcmp := pow_le_sin_pow hc2 hθ
    rw [← ENNReal.ofReal_mul hpi_nn2]
    refine ENNReal.ofReal_le_ofReal ?_
    calc θ ^ (2 - c) * (deriv u θ) ^ 2
        ≤ ((Real.pi / 4) ^ (2 - c) * (Real.sin (2 * θ)) ^ (2 - c)) * (deriv u θ) ^ 2 :=
          mul_le_mul_of_nonneg_right hcmp (sq_nonneg _)
      _ = (Real.pi / 4) ^ (2 - c) * ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2) := by ring
  -- ## the constant bookkeeping
  have hAD : (Real.pi / 4) ^ c * (Real.pi / 4) ^ (2 - c) = (Real.pi / 4) ^ 2 := by
    rw [← Real.rpow_add h4pos c (2 - c)]
    norm_num
  have hmerge : ∀ X : ℝ≥0∞, ENNReal.ofReal ((Real.pi / 4) ^ c) *
        (ENNReal.ofReal (4 / (c - 1) ^ 2) * (ENNReal.ofReal ((Real.pi / 4) ^ (2 - c)) * X))
      = ENNReal.ofReal ((Real.pi / 4) ^ 2 * (4 / (c - 1) ^ 2)) * X := by
    intro X
    have hkey : (Real.pi / 4) ^ c * (4 / (c - 1) ^ 2) * (Real.pi / 4) ^ (2 - c)
        = (Real.pi / 4) ^ 2 * (4 / (c - 1) ^ 2) := by
      rw [← hAD]; ring
    calc ENNReal.ofReal ((Real.pi / 4) ^ c) *
          (ENNReal.ofReal (4 / (c - 1) ^ 2) * (ENNReal.ofReal ((Real.pi / 4) ^ (2 - c)) * X))
        = ENNReal.ofReal ((Real.pi / 4) ^ c * (4 / (c - 1) ^ 2) * (Real.pi / 4) ^ (2 - c)) * X := by
          rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hpi_nn,
            ← ENNReal.ofReal_mul (mul_nonneg hpi_nn hKpos.le)]
      _ = ENNReal.ofReal ((Real.pi / 4) ^ 2 * (4 / (c - 1) ^ 2)) * X := by rw [hkey]
  -- ## assembly
  calc (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal ((Real.pi / 4) ^ c) *
          (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), ENNReal.ofReal (θ ^ (-c) * (u θ) ^ 2)) := hA
    _ ≤ ENNReal.ofReal ((Real.pi / 4) ^ c) * (ENNReal.ofReal (4 / (c - 1) ^ 2) *
          (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal (θ ^ (2 - c) * (deriv u θ) ^ 2))) :=
        mul_le_mul_right hB' (ENNReal.ofReal ((Real.pi / 4) ^ c))
    _ ≤ ENNReal.ofReal ((Real.pi / 4) ^ c) * (ENNReal.ofReal (4 / (c - 1) ^ 2) *
          (ENNReal.ofReal ((Real.pi / 4) ^ (2 - c)) *
            (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
              ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)))) :=
        mul_le_mul_right (mul_le_mul_right hC (ENNReal.ofReal (4 / (c - 1) ^ 2)))
          (ENNReal.ofReal ((Real.pi / 4) ^ c))
    _ = ENNReal.ofReal ((Real.pi / 4) ^ 2 * (4 / (c - 1) ^ 2)) *
          (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := hmerge _
    _ ≤ ENNReal.ofReal (4 / (c - 1) ^ 2) *
          (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := by
        refine mul_le_mul_left ?_ _
        refine ENNReal.ofReal_le_ofReal ?_
        have hle1 : (Real.pi / 4) ≤ 1 := by linarith [Real.pi_lt_four]
        have hsq1 : ((Real.pi / 4)) ^ 2 ≤ 1 := by nlinarith [h4pos.le, hle1]
        nlinarith [hsq1, hKpos.le]

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
