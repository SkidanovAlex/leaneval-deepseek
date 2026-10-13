import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.PhiStar.RadialWAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.FlatWAux.Kernels.phiKernelWeightedLe`

The weighted bound for the inner (`Φ`-) rescaled Green kernel.  Writing the inner piece of the
radial Green function in the form

  `Φ z = ∫ u in (0)..1, h (z * u) * u ^ (Q - 1)`

(the substitution `t = z u` in `∫_0^z h(t) t^{Q-1} dt`), the `j`-th `z`-derivative is the same
integral with `h` replaced by `iteratedDeriv j h`.  If that derivative decays like
`B / (1 + t ^ (j + 2))`, then the `j`-th kernel moment obeys

  `(z+1)^{j+1} |∫₀¹ h^{(j)}(z u) u^{j+Q-1} du|  ≤  2^{j+1} B (1/(j+Q) + 1/(Q-2))`

for every `z > 0` and every `j ≤ 10`, `Q > 2`.

The proof is elementary and uses nothing but the pointwise bound on `h^{(j)}` (the smoothness
hypothesis `hh` is not needed):

* for `u ∈ (0,1)` and `t = z u > 0` one has `|h^{(j)}(t)| ≤ B`, hence the integrand is
  dominated by `B u^{j+Q-1}`, and `(z+1)^{j+1} ≤ 2^{j+1}` for `z ≤ 1`;
* for `z ≥ 1` the sharper comparison `u^{j+Q-1}/(1+(zu)^{j+2}) ≤ z^{-(j+2)} u^{Q-3}`, obtained
  from `(zu)^{j+2}/(1+(zu)^{j+2}) ≤ 1`, gives the second summand, and
  `(z+1)^{j+1} z^{-(j+2)} ≤ 2^{j+1}` for `z ≥ 1`.

The elementary integrals are Mathlib's `integral_rpow`; the domination is
`norm_integral_le_integral_norm` together with `integral_mono_of_nonneg` on the set `Ioc 0 1`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedVariables false

namespace Work.FTS.PhiStar.FlatWAux.Kernels

/-- Pointwise comparison used in the large-`z` regime: on `(0,1]` the decaying kernel
`u^{j+Q-1}/(1+(z u)^{j+2})` is dominated by `z^{-(j+2)} u^{Q-3}`. -/
private lemma phiKernel_pointwise {j : ℕ} {Q B : ℝ} (hB : 0 ≤ B) {H : ℝ → ℝ}
    (hb : ∀ t : ℝ, 0 < t → |H t| ≤ B / (1 + t ^ (j + 2))) {z u : ℝ} (hz : 0 < z) (hu : 0 < u) :
    |H (z * u)| * u ^ ((j : ℝ) + Q - 1)
      ≤ B * z ^ (-(((j + 2 : ℕ)) : ℝ)) * u ^ (Q - 3) := by
  have hzu : 0 < z * u := mul_pos hz hu
  have hup : (0 : ℝ) ≤ u ^ ((j : ℝ) + Q - 1) := Real.rpow_nonneg hu.le _
  have huz : (0 : ℝ) ≤ u ^ (Q - 3) := Real.rpow_nonneg hu.le _
  -- `u^p = u^{Q-3} * u^{j+2}`
  have hsplit : u ^ ((j : ℝ) + Q - 1) = u ^ (Q - 3) * u ^ (((j + 2 : ℕ)) : ℝ) := by
    rw [← Real.rpow_add hu]
    congr 1
    push_cast
    ring
  -- `u^{j+2} = (z^{j+2})⁻¹ * (z*u)^{j+2}`
  have huz_nat : u ^ (j + 2) = (z ^ (j + 2))⁻¹ * (z * u) ^ (j + 2) := by
    rw [mul_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (ne_of_gt hz)), one_mul]
  have huz' : u ^ (((j + 2 : ℕ)) : ℝ) = (z ^ (j + 2))⁻¹ * (z * u) ^ (j + 2) := by
    rw [Real.rpow_natCast]
    exact huz_nat
  -- the quotient is at most `1`
  have hfrac : (z * u) ^ (j + 2) / (1 + (z * u) ^ (j + 2)) ≤ 1 := by
    have hp1 : (0 : ℝ) < 1 + (z * u) ^ (j + 2) := by
      have h := pow_nonneg hzu.le (j + 2)
      linarith
    rw [div_le_one hp1]
    have h := pow_nonneg hzu.le (j + 2)
    linarith
  have hkey : u ^ (((j + 2 : ℕ)) : ℝ) / (1 + (z * u) ^ (j + 2))
      ≤ z ^ (-(((j + 2 : ℕ)) : ℝ)) := by
    calc u ^ (((j + 2 : ℕ)) : ℝ) / (1 + (z * u) ^ (j + 2))
        = ((z ^ (j + 2))⁻¹ * (z * u) ^ (j + 2)) / (1 + (z * u) ^ (j + 2)) := by rw [huz']
      _ = (z ^ (j + 2))⁻¹ * ((z * u) ^ (j + 2) / (1 + (z * u) ^ (j + 2))) := by ring
      _ ≤ (z ^ (j + 2))⁻¹ * 1 := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = z ^ (-(((j + 2 : ℕ)) : ℝ)) := by
          rw [mul_one, ← Real.rpow_natCast z (j + 2), ← Real.rpow_neg hz.le]
  calc |H (z * u)| * u ^ ((j : ℝ) + Q - 1)
      ≤ (B / (1 + (z * u) ^ (j + 2))) * u ^ ((j : ℝ) + Q - 1) :=
        mul_le_mul_of_nonneg_right (hb (z * u) hzu) hup
    _ = B * (u ^ (Q - 3) * (u ^ (((j + 2 : ℕ)) : ℝ) / (1 + (z * u) ^ (j + 2)))) := by
        rw [hsplit]
        ring
    _ ≤ B * (u ^ (Q - 3) * z ^ (-(((j + 2 : ℕ)) : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkey huz) hB
    _ = B * z ^ (-(((j + 2 : ℕ)) : ℝ)) * u ^ (Q - 3) := by ring

/-- The `z ≤ 1` regime: the crude bound `|h^{(j)}| ≤ B` suffices. -/
private lemma phiKernel_le_small {j : ℕ} {Q B z : ℝ} (hQ : 2 < Q) (hB : 0 ≤ B) (hz : 0 < z)
    {H : ℝ → ℝ} (hb : ∀ t : ℝ, 0 < t → |H t| ≤ B / (1 + t ^ (j + 2))) :
    |∫ u in (0 : ℝ)..1, H (z * u) * u ^ ((j : ℝ) + Q - 1)| ≤ B / ((j : ℝ) + Q) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hp : (-1 : ℝ) < (j : ℝ) + Q - 1 := by
    have h : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hInt : Integrable (fun u : ℝ => B * u ^ ((j : ℝ) + Q - 1))
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have h1 := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
      (r := (j : ℝ) + Q - 1) hp
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h01] at h1
    exact h1.const_mul B
  have habs : |∫ u in (0 : ℝ)..1, H (z * u) * u ^ ((j : ℝ) + Q - 1)|
      ≤ ∫ u in Ioc (0 : ℝ) 1, |H (z * u) * u ^ ((j : ℝ) + Q - 1)| := by
    rw [intervalIntegral.integral_of_le h01]
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := volume.restrict (Ioc (0 : ℝ) 1))
        (fun u : ℝ => H (z * u) * u ^ ((j : ℝ) + Q - 1))
  have hmono : ∫ u in Ioc (0 : ℝ) 1, |H (z * u) * u ^ ((j : ℝ) + Q - 1)|
      ≤ ∫ u in Ioc (0 : ℝ) 1, B * u ^ ((j : ℝ) + Q - 1) := by
    refine integral_mono_of_nonneg ?_ hInt ?_
    · filter_upwards with u
      exact abs_nonneg _
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hu0 : 0 < u := hu.1
      have hup : (0 : ℝ) ≤ u ^ ((j : ℝ) + Q - 1) := Real.rpow_nonneg hu0.le _
      rw [abs_mul, abs_of_nonneg hup]
      refine mul_le_mul_of_nonneg_right ?_ hup
      have hzu : 0 < z * u := mul_pos hz hu0
      have h1 := hb (z * u) hzu
      have htnn : (0 : ℝ) ≤ (z * u) ^ (j + 2) := pow_nonneg hzu.le _
      have hpos : (0 : ℝ) < 1 + (z * u) ^ (j + 2) := by linarith
      refine le_trans h1 ?_
      rw [div_le_iff₀ hpos]
      nlinarith [hB, htnn]
  have hval : ∫ u in Ioc (0 : ℝ) 1, B * u ^ ((j : ℝ) + Q - 1) = B / ((j : ℝ) + Q) := by
    rw [← intervalIntegral.integral_of_le h01, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl hp), Real.one_rpow,
      Real.zero_rpow (by linarith : (j : ℝ) + Q - 1 + 1 ≠ 0), sub_zero,
      show (j : ℝ) + Q - 1 + 1 = (j : ℝ) + Q from by ring]
    ring
  calc |∫ u in (0 : ℝ)..1, H (z * u) * u ^ ((j : ℝ) + Q - 1)|
      ≤ ∫ u in Ioc (0 : ℝ) 1, |H (z * u) * u ^ ((j : ℝ) + Q - 1)| := habs
    _ ≤ ∫ u in Ioc (0 : ℝ) 1, B * u ^ ((j : ℝ) + Q - 1) := hmono
    _ = B / ((j : ℝ) + Q) := hval

/-- The `z ≥ 1` regime: the decay `|h^{(j)}(t)| ≤ B/(1+t^{j+2})` gives the `z^{-(j+2)}` rate. -/
private lemma phiKernel_le_large {j : ℕ} {Q B z : ℝ} (hQ : 2 < Q) (hB : 0 ≤ B) (hz : 1 ≤ z)
    {H : ℝ → ℝ} (hb : ∀ t : ℝ, 0 < t → |H t| ≤ B / (1 + t ^ (j + 2))) :
    |∫ u in (0 : ℝ)..1, H (z * u) * u ^ ((j : ℝ) + Q - 1)|
      ≤ B * z ^ (-(((j + 2 : ℕ)) : ℝ)) / (Q - 2) := by
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hexp : (-1 : ℝ) < Q - 3 := by linarith
  have hInt : Integrable (fun u : ℝ => B * z ^ (-(((j + 2 : ℕ)) : ℝ)) * u ^ (Q - 3))
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have h1 := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1) (r := Q - 3) hexp
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h01] at h1
    exact h1.const_mul (B * z ^ (-(((j + 2 : ℕ)) : ℝ)))
  have habs : |∫ u in (0 : ℝ)..1, H (z * u) * u ^ ((j : ℝ) + Q - 1)|
      ≤ ∫ u in Ioc (0 : ℝ) 1, |H (z * u) * u ^ ((j : ℝ) + Q - 1)| := by
    rw [intervalIntegral.integral_of_le h01]
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := volume.restrict (Ioc (0 : ℝ) 1))
        (fun u : ℝ => H (z * u) * u ^ ((j : ℝ) + Q - 1))
  have hmono : ∫ u in Ioc (0 : ℝ) 1, |H (z * u) * u ^ ((j : ℝ) + Q - 1)|
      ≤ ∫ u in Ioc (0 : ℝ) 1, B * z ^ (-(((j + 2 : ℕ)) : ℝ)) * u ^ (Q - 3) := by
    refine integral_mono_of_nonneg ?_ hInt ?_
    · filter_upwards with u
      exact abs_nonneg _
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hu0 : 0 < u := hu.1
      have hup : (0 : ℝ) ≤ u ^ ((j : ℝ) + Q - 1) := Real.rpow_nonneg hu0.le _
      rw [abs_mul, abs_of_nonneg hup]
      exact phiKernel_pointwise hB hb hz0 hu0
  have hval : ∫ u in Ioc (0 : ℝ) 1, B * z ^ (-(((j + 2 : ℕ)) : ℝ)) * u ^ (Q - 3)
      = B * z ^ (-(((j + 2 : ℕ)) : ℝ)) / (Q - 2) := by
    rw [← intervalIntegral.integral_of_le h01, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl hexp), Real.one_rpow,
      Real.zero_rpow (by linarith : Q - 3 + 1 ≠ 0), sub_zero,
      show Q - 3 + 1 = Q - 2 from by ring]
    ring
  calc |∫ u in (0 : ℝ)..1, H (z * u) * u ^ ((j : ℝ) + Q - 1)|
      ≤ ∫ u in Ioc (0 : ℝ) 1, |H (z * u) * u ^ ((j : ℝ) + Q - 1)| := habs
    _ ≤ ∫ u in Ioc (0 : ℝ) 1, B * z ^ (-(((j + 2 : ℕ)) : ℝ)) * u ^ (Q - 3) := hmono
    _ = B * z ^ (-(((j + 2 : ℕ)) : ℝ)) / (Q - 2) := hval

/-- `(z+1)^{j+1} z^{-(j+2)} ≤ 2^{j+1}` for `z ≥ 1`. -/
private lemma phiKernel_ratio {j : ℕ} {z : ℝ} (hz : 1 ≤ z) :
    (z + 1) ^ (j + 1) * z ^ (-(((j + 2 : ℕ)) : ℝ)) ≤ (2 : ℝ) ^ (j + 1) := by
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
  have hq : (z + 1) ^ (j + 1) ≤ (2 : ℝ) ^ (j + 1) * z ^ (j + 1) := by
    have h1 : z + 1 ≤ 2 * z := by linarith
    have h0 : (0 : ℝ) ≤ z + 1 := by linarith
    calc (z + 1) ^ (j + 1) ≤ (2 * z) ^ (j + 1) := pow_le_pow_left₀ h0 h1 (j + 1)
      _ = (2 : ℝ) ^ (j + 1) * z ^ (j + 1) := by rw [mul_pow]
  have hzpow : z ^ (((j + 1 : ℕ)) : ℝ) * z ^ (-(((j + 2 : ℕ)) : ℝ)) ≤ 1 := by
    rw [← Real.rpow_add hz0]
    have hexp : (((j + 1 : ℕ)) : ℝ) + (-(((j + 2 : ℕ)) : ℝ)) = -1 := by
      push_cast
      ring
    rw [hexp]
    exact Real.rpow_le_one_of_one_le_of_nonpos hz (by norm_num)
  calc (z + 1) ^ (j + 1) * z ^ (-(((j + 2 : ℕ)) : ℝ))
      ≤ ((2 : ℝ) ^ (j + 1) * z ^ (j + 1)) * z ^ (-(((j + 2 : ℕ)) : ℝ)) :=
        mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hz0.le _)
    _ = (2 : ℝ) ^ (j + 1) * (z ^ (((j + 1 : ℕ)) : ℝ) * z ^ (-(((j + 2 : ℕ)) : ℝ))) := by
        rw [show z ^ (j + 1) = z ^ (((j + 1 : ℕ)) : ℝ) from
          (Real.rpow_natCast z (j + 1)).symm]
        ring
    _ ≤ (2 : ℝ) ^ (j + 1) * 1 :=
        mul_le_mul_of_nonneg_left hzpow (pow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (j + 1) := by ring

theorem phiKernelWeightedLe {Q B : ℝ} (hQ : 2 < Q) (hB : 0 ≤ B) {h : ℝ → ℝ}
    (hh : ContDiffOn ℝ 14 h (Set.Ioi 0))
    (hb : ∀ j : ℕ, j ≤ 10 → ∀ t : ℝ, 0 < t → |iteratedDeriv j h t| ≤ B / (1 + t ^ (j + 2))) :
    ∀ j : ℕ, j ≤ 10 → ∀ z : ℝ, 0 < z →
      (z + 1) ^ (j + 1) *
          |∫ u in (0 : ℝ)..1, iteratedDeriv j h (z * u) * u ^ ((j : ℝ) + Q - 1)|
        ≤ (2 : ℝ) ^ (j + 1) * B * (1 / ((j : ℝ) + Q) + 1 / (Q - 2)) := by
  intro j hj z hz
  have hQ2 : (0 : ℝ) < Q - 2 := by linarith
  have hjQ : (0 : ℝ) < (j : ℝ) + Q := by
    have h : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hden1 : (0 : ℝ) ≤ 1 / ((j : ℝ) + Q) := div_nonneg zero_le_one hjQ.le
  have hden2 : (0 : ℝ) ≤ 1 / (Q - 2) := div_nonneg zero_le_one hQ2.le
  have hpow : (0 : ℝ) ≤ (z + 1) ^ (j + 1) := pow_nonneg (by linarith) _
  have hb' : ∀ t : ℝ, 0 < t → |iteratedDeriv j h t| ≤ B / (1 + t ^ (j + 2)) :=
    fun t ht => hb j hj t ht
  rcases le_or_gt z 1 with hzle | hzlt
  · have hI := phiKernel_le_small (j := j) (Q := Q) (B := B) (z := z) hQ hB hz hb'
    have h2 : (z + 1) ^ (j + 1) ≤ (2 : ℝ) ^ (j + 1) :=
      pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ z + 1) (by linarith) (j + 1)
    have hBQ : (0 : ℝ) ≤ B / ((j : ℝ) + Q) := div_nonneg hB hjQ.le
    calc (z + 1) ^ (j + 1)
          * |∫ u in (0 : ℝ)..1, iteratedDeriv j h (z * u) * u ^ ((j : ℝ) + Q - 1)|
        ≤ (z + 1) ^ (j + 1) * (B / ((j : ℝ) + Q)) := mul_le_mul_of_nonneg_left hI hpow
      _ ≤ (2 : ℝ) ^ (j + 1) * (B / ((j : ℝ) + Q)) := mul_le_mul_of_nonneg_right h2 hBQ
      _ = (2 : ℝ) ^ (j + 1) * B * (1 / ((j : ℝ) + Q)) := by ring
      _ ≤ (2 : ℝ) ^ (j + 1) * B * (1 / ((j : ℝ) + Q) + 1 / (Q - 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact le_add_of_nonneg_right hden2
  · have hz1 : 1 ≤ z := le_of_lt hzlt
    have hI := phiKernel_le_large (j := j) (Q := Q) (B := B) (z := z) hQ hB hz1 hb'
    have hratio := phiKernel_ratio (j := j) hz1
    calc (z + 1) ^ (j + 1)
          * |∫ u in (0 : ℝ)..1, iteratedDeriv j h (z * u) * u ^ ((j : ℝ) + Q - 1)|
        ≤ (z + 1) ^ (j + 1) * (B * z ^ (-(((j + 2 : ℕ)) : ℝ)) / (Q - 2)) :=
          mul_le_mul_of_nonneg_left hI hpow
      _ = ((z + 1) ^ (j + 1) * z ^ (-(((j + 2 : ℕ)) : ℝ))) * B * (1 / (Q - 2)) := by ring
      _ ≤ (2 : ℝ) ^ (j + 1) * B * (1 / (Q - 2)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hratio hB) hden2
      _ ≤ (2 : ℝ) ^ (j + 1) * B * (1 / ((j : ℝ) + Q) + 1 / (Q - 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact le_add_of_nonneg_left hden1

end Work.FTS.PhiStar.FlatWAux.Kernels
