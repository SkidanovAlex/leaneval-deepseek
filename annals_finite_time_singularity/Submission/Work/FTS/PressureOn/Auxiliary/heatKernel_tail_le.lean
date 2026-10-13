import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Auxiliary.HeatKernel
import Submission.Work.FTS.PressureOn.Auxiliary.integral_heatKernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Tail bound for the heat kernel on `ℝ³`

For `t > 0` and `δ > 0` the mass of the heat kernel
`γ_t z = (4πt)^{-3/2} exp (-‖z‖²/(4t))` outside the ball of radius `δ` is bounded by

  `∫_{‖z‖ ≥ δ} γ_t z ≤ 2^{3/2} exp (-δ²/(8t))`.

The proof is the standard exact scaling comparison.  Writing `P = 4πt` and `Q = 8πt`,

  `2^{3/2} γ_{2t} z = 2^{3/2} Q^{-3/2} exp (-‖z‖²/(8t)) = P^{-3/2} exp (-‖z‖²/(8t))`,

so for `‖z‖ ≥ δ` (whence `δ² ≤ ‖z‖²`)

  `γ_t z = P^{-3/2} exp (-‖z‖²/(4t)) ≤ exp (-δ²/(8t)) · 2^{3/2} γ_{2t} z`,

and integrating over the tail and using the normalisation `∫ γ_{2t} = 1` from
`integral_heatKernel` gives the claim.  (The sibling `tendsto_tail_heatKernel` proves the
same comparison with the cruder constant `4`, which suffices for the limit `t → 0⁺` but not
for the constant `2^{3/2}` of this statement.)
-/

open MeasureTheory Set Filter Topology
open scoped Topology

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

/-- `2^{3/2} · (8πt)^{-3/2} = (4πt)^{-3/2}`: the constant `2^{3/2}` is exactly the factor by
which the prefactor of `γ_{2t}` differs from that of `γ_t`. -/
private lemma rpow_two_mul_eight (t : ℝ) (ht : 0 < t) :
    2 ^ (3 / 2 : ℝ) * (8 * Real.pi * t) ^ (-(3 / 2 : ℝ))
      = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) := by
  have hP : (0 : ℝ) < 4 * Real.pi * t := by positivity
  have h8 : (8 : ℝ) * Real.pi * t = 2 * (4 * Real.pi * t) := by ring
  rw [h8, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hP.le, ← mul_assoc,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    show (3 / 2 : ℝ) + -(3 / 2) = 0 by norm_num, Real.rpow_zero, one_mul]

/-- **Pointwise comparison of the heat kernel at times `t` and `2t`.**  Outside the ball of
radius `δ`, `γ_t z ≤ exp (-δ²/(8t)) · 2^{3/2} γ_{2t} z`. -/
private lemma heatKernel_le_exp_mul (t δ : ℝ) (ht : 0 < t) (hδ : 0 ≤ δ) {z : R3}
    (hz : δ ≤ ‖z‖) :
    heatKernel t z
      ≤ Real.exp (-(δ ^ 2 / (8 * t))) * (2 ^ (3 / 2 : ℝ) * heatKernel (2 * t) z) := by
  have h2t : (0 : ℝ) < 2 * t := by linarith
  have hδz : δ ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hδ hz 2
  -- `γ_{2t}` written with the prefactor `(8πt)^{-3/2}`
  have hγ2 : heatKernel (2 * t) z
      = (8 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖z‖ ^ 2 / (8 * t))) := by
    rw [heatKernel_apply, show (4 : ℝ) * Real.pi * (2 * t) = 8 * Real.pi * t by ring,
      show (4 : ℝ) * (2 * t) = 8 * t by ring]
  -- the exponential factor
  have hexp : Real.exp (-(‖z‖ ^ 2 / (4 * t)))
      ≤ Real.exp (-(δ ^ 2 / (8 * t))) * Real.exp (-(‖z‖ ^ 2 / (8 * t))) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have h1 : δ ^ 2 / (8 * t) ≤ ‖z‖ ^ 2 / (8 * t) :=
      div_le_div_of_nonneg_right hδz (by positivity)
    have h2 : ‖z‖ ^ 2 / (8 * t) + ‖z‖ ^ 2 / (8 * t) = ‖z‖ ^ 2 / (4 * t) := by
      have h8 : (8 : ℝ) * t ≠ 0 := by positivity
      have h4 : (4 : ℝ) * t ≠ 0 := by positivity
      field_simp
      ring
    linarith
  calc heatKernel t z
      = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖z‖ ^ 2 / (4 * t))) :=
        heatKernel_apply t z
    _ ≤ (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))
          * (Real.exp (-(δ ^ 2 / (8 * t))) * Real.exp (-(‖z‖ ^ 2 / (8 * t)))) :=
        mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg (by positivity) _)
    _ = Real.exp (-(δ ^ 2 / (8 * t)))
          * (2 ^ (3 / 2 : ℝ) * heatKernel (2 * t) z) := by
        rw [hγ2]
        rw [show (2 : ℝ) ^ (3 / 2 : ℝ)
              * ((8 * Real.pi * t) ^ (-(3 / 2 : ℝ))
                * Real.exp (-(‖z‖ ^ 2 / (8 * t))))
            = (2 ^ (3 / 2 : ℝ) * (8 * Real.pi * t) ^ (-(3 / 2 : ℝ)))
              * Real.exp (-(‖z‖ ^ 2 / (8 * t))) from by ring]
        rw [rpow_two_mul_eight t ht]
        ring

/-- The heat kernel is integrable at positive times (its mass is `1`). -/
private lemma integrable_heatKernel_aux {t : ℝ} (ht : 0 < t) : Integrable (heatKernel t) := by
  by_contra hf
  have h := integral_heatKernel t ht
  rw [integral_undef hf] at h
  exact one_ne_zero h.symm

theorem heatKernel_tail_le (t δ : ℝ) (ht : 0 < t) (hδ : 0 < δ) :
    (∫ z in {z : Work.FTS.PressureOn.R3 | δ ≤ ‖z‖},
        Work.FTS.PressureOn.Auxiliary.heatKernel t z)
      ≤ 2 ^ (3 / 2 : ℝ) * Real.exp (-(δ ^ 2 / (8 * t))) := by
  set S : Set R3 := {z : R3 | δ ≤ ‖z‖} with hS
  have hSmeas : MeasurableSet S := (isClosed_le continuous_const continuous_norm).measurableSet
  have h2t : (0 : ℝ) < 2 * t := by linarith
  have hint : Integrable (heatKernel t) := integrable_heatKernel_aux ht
  have hint2 : Integrable (fun z : R3 => heatKernel (2 * t) z) := integrable_heatKernel_aux h2t
  have hmaj : Integrable (fun z : R3 =>
      Real.exp (-(δ ^ 2 / (8 * t))) * (2 ^ (3 / 2 : ℝ) * heatKernel (2 * t) z)) :=
    (hint2.const_mul (2 ^ (3 / 2 : ℝ))).const_mul _
  calc ∫ z in S, heatKernel t z
      ≤ ∫ z in S,
          Real.exp (-(δ ^ 2 / (8 * t))) * (2 ^ (3 / 2 : ℝ) * heatKernel (2 * t) z) :=
        setIntegral_mono_on hint.integrableOn hmaj.integrableOn hSmeas
          (fun z hz => heatKernel_le_exp_mul t δ ht hδ.le hz)
    _ = Real.exp (-(δ ^ 2 / (8 * t)))
          * (2 ^ (3 / 2 : ℝ) * ∫ z in S, heatKernel (2 * t) z) := by
        rw [integral_const_mul, integral_const_mul]
    _ ≤ Real.exp (-(δ ^ 2 / (8 * t)))
          * (2 ^ (3 / 2 : ℝ) * ∫ z : R3, heatKernel (2 * t) z) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _))
          (Real.exp_nonneg _)
        exact setIntegral_le_integral hint2
          (Filter.Eventually.of_forall fun z => heatKernel_nonneg h2t.le z)
    _ = 2 ^ (3 / 2 : ℝ) * Real.exp (-(δ ^ 2 / (8 * t))) := by
        rw [integral_heatKernel (2 * t) h2t, mul_one, mul_comm]

end

end Work.FTS.PressureOn.Auxiliary
