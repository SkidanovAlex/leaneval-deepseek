import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.GbarSetup
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.HarOp_lintegral_swap
import Submission.Work.FTS.EllipticEst.w_tail_lintegral_bound
import Submission.Work.Elliptic.hardy_operator_L2
import Submission.Work.Elliptic.hardy_op_L2_tonelli
import Submission.Work.Elliptic.HardyLeftW

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted `L²` Hardy inequality for the operator `HarOp`

This module proves the `k = 0` case of the weighted Hardy estimate behind Elgindi's
Lemma `HardyInequality4` (Annals 194(3) 2021, §'The singular term', tex line 1030):

  `∫₀^∞ w(z)² (HarOp β f z)² dz ≤ (100/β²) ∫₀^∞ w(z)² f(z)² dz`  for `β ≥ 5`,

where `w(z) = (1+z)²/z²` is the weight of the paper's `H^k` spaces and

  `HarOp β f z = z^{-β} ∫₀^z s^{β-1} f(s) ds`

is the (weighted) Hardy operator of which the singular part `Ḡ` of the elliptic estimate is
`-(3/(4α))` times an instance (`Gbar_eq_HarOp`).

## Proof

The argument is the classical Cauchy–Schwarz / Tonelli pair, but with the *sharp* exponent on
the source: writing `s^{β-1} f(s) = s^{(β-1)/2} · s^{(β-1)/2} f(s)` and applying Cauchy–Schwarz
on `(0,z]` gives the pointwise bound

  `(HarOp β f z)² ≤ (1/β) z^{-β} ∫₀^z s^{β-1} f(s)² ds`      (`HarOp_pointwise_sq`),

whose constant `1/β` is exactly the sharp Hardy rate.  Multiplying by `w(z)²` and integrating,
Tonelli's theorem (`HarOp_lintegral_swap`) turns the double integral into

  `(1/β) ∫₀^∞ s^{β-1} f(s)² (∫_s^∞ w(z)² z^{-β} dz) ds`,

and since `w` is decreasing on `(0,∞)` the inner integral is bounded by
`w(s)² ∫_s^∞ z^{-β} dz = w(s)² s^{1-β}/(β-1)` (`w_tail_lintegral_bound`).  The factors
`s^{β-1} s^{1-β} = 1` cancel exactly, leaving

  `∫₀^∞ w² (HarOp β f)² ≤ (1/(β(β-1))) ∫₀^∞ w² f² ≤ (100/β²) ∫₀^∞ w² f²`,

the last step because `β ≥ 5` gives `100(β-1) ≥ β`.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

theorem HarOp_weighted_lintegral (β : ℝ) (hβ : 5 ≤ β) (f : ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn (fun z : ℝ => (f z) ^ 2) (Set.Ioi 0)) :
    ∫⁻ z in Set.Ioi 0, ENNReal.ofReal
        ((Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.HarOp β f z) ^ 2)
      ≤ ENNReal.ofReal (100 / β ^ 2) *
          ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (f z) ^ 2) := by
  have hβ1 : (1 : ℝ) < β := by linarith
  -- Step A: the pointwise Cauchy--Schwarz bound, then monotonicity of the lintegral.
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ),
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
        ≤ ENNReal.ofReal (1 / β) *
          (ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
            ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2)) := by
    intro z hz
    have hz0 : 0 < z := hz
    have hy := HarOp_pointwise_sq β hβ1 f hf hz0
    calc ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
        = ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * ENNReal.ofReal ((HarOp β f z) ^ 2) :=
          ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))
      _ ≤ ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
            (ENNReal.ofReal (1 / β) * ENNReal.ofReal (z ^ (-β)) *
              ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2)) :=
          mul_le_mul_of_nonneg_left hy bot_le
      _ = ENNReal.ofReal (1 / β) *
            (ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
              ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2)) := by
          rw [mul_assoc (ENNReal.ofReal (1 / β)) (ENNReal.ofReal (z ^ (-β)))
                (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2))]
          rw [mul_left_comm (ENNReal.ofReal ((Work.Spaces.w z) ^ 2))
                (ENNReal.ofReal (1 / β))
                (ENNReal.ofReal (z ^ (-β)) *
                  ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2))]
          rw [← mul_assoc (ENNReal.ofReal ((Work.Spaces.w z) ^ 2))
                (ENNReal.ofReal (z ^ (-β)))
                (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2))]
          rw [← ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
  have hA : ∫⁻ z in Set.Ioi 0, ENNReal.ofReal
        ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      ≤ ENNReal.ofReal (1 / β) *
        ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
          (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2)) := by
    have h := setLIntegral_mono' (μ := volume) measurableSet_Ioi hpt
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
    exact h
  -- Step B: Tonelli.
  rw [HarOp_lintegral_swap β hβ1 f hf] at hA
  -- Step C: the tail bound, pointwise in `s`.
  have hC : ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
        (∫⁻ z in Set.Ici s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)))
      ≤ ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
        ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1)) :=
    setLIntegral_mono' (μ := volume) measurableSet_Ioi
      (fun s hs => mul_le_mul_of_nonneg_left (w_tail_lintegral_bound β hβ1 hs) bot_le)
  -- Step D: the algebra of the two `ofReal`s, where `s^{β-1} s^{1-β} = 1`.
  have hD : ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
        ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1))
      = ENNReal.ofReal (1 / (β - 1)) *
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * f s ^ 2) := by
    have hpt2 : ∀ s ∈ Set.Ioi (0 : ℝ),
        ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
          ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1))
        = ENNReal.ofReal (1 / (β - 1)) *
          ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * f s ^ 2) := by
      intro s hs
      have hs0 : 0 < s := hs
      rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hs0.le _) (sq_nonneg _))]
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (β - 1))]
      congr 1
      have h1 : s ^ (β - 1) * s ^ (1 - β) = 1 := by
        rw [← Real.rpow_add hs0, show β - 1 + (1 - β) = 0 by ring, Real.rpow_zero]
      calc s ^ (β - 1) * f s ^ 2 * ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1))
          = (s ^ (β - 1) * s ^ (1 - β)) * ((Work.Spaces.w s) ^ 2 * f s ^ 2) / (β - 1) := by
            ring
        _ = (Work.Spaces.w s) ^ 2 * f s ^ 2 / (β - 1) := by rw [h1, one_mul]
        _ = 1 / (β - 1) * ((Work.Spaces.w s) ^ 2 * f s ^ 2) := by ring
    rw [setLIntegral_congr_fun measurableSet_Ioi hpt2,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- Step E: the numerical constant `1/(β(β-1)) ≤ 100/β²` for `β ≥ 5`.
  have hconst : (1 : ℝ) / β * (1 / (β - 1)) ≤ 100 / β ^ 2 := by
    rw [div_mul_div_comm, one_mul]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hβ]
  calc ∫⁻ z in Set.Ioi 0, ENNReal.ofReal
        ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      ≤ ENNReal.ofReal (1 / β) *
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
          (∫⁻ z in Set.Ici s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β))) := hA
    _ ≤ ENNReal.ofReal (1 / β) *
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
          ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1)) :=
        mul_le_mul_of_nonneg_left hC bot_le
    _ = ENNReal.ofReal (1 / β) *
        (ENNReal.ofReal (1 / (β - 1)) *
          ∫⁻ s in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * f s ^ 2)) := by
        rw [hD]
    _ = (ENNReal.ofReal (1 / β) * ENNReal.ofReal (1 / (β - 1))) *
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * f s ^ 2) := by
        rw [mul_assoc]
    _ ≤ ENNReal.ofReal (100 / β ^ 2) *
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * f s ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ bot_le
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / β)]
        exact ENNReal.ofReal_le_ofReal hconst

end Work.FTS.EllipticEst
