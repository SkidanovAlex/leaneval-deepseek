import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS.EllipticEst.Honest.SliceIbpDefs
import Submission.Work.FTS.EllipticEst.Honest.SliceBoundary

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false

/-!
# The primitive `θ ↦ -(u'·u·σ + η·u²·ρ) + ½ tan θ·u²·σ` vanishes at both endpoints

`Work.FTS.EllipticEst.Honest.SliceBoundary` already shows that

* `sig η θ * u θ * deriv u θ → 0`   (i.e. `u' u σ → 0`) and
* `rho η θ * u θ ^ 2 → 0`           (i.e. `η u² ρ → 0`, since `sigD η = -2η ρ`)

at `θ → 0⁺` and at `θ → π/2⁻`, for a slice bound `|u θ| ≤ min (C θ) (C (π/2 - θ))` and a
bounded derivative `|u' θ| ≤ C`, when `0 ≤ η < 1`.  The remaining third summand is the
`tan`-weighted one, `½ tan θ · u² · σ η θ`, and that is what this file bounds: near `0` we
have `tan θ ≤ 1`, while near `π/2` we have `tan θ ≤ (π/2 - θ)⁻¹` (`tan (π/2 - t) = 1/tan t`
and `tan t ≥ t`).  So on the appropriate half of the interval,

`|tan θ · u² · σ η θ| ≤ C² (4/π)^{-η} · t^{1-η}`  with `t = θ` resp. `t = π/2 - θ`,

using `sin (2θ) ≥ (4/π) t` (`sin_two_ge_four_div_pi_mul` / `sin_two_ge_four_div_pi_mul_sub`)
and `η < 1` for `t^{1-η} → 0`.
-/

/-- Two `rpow` bookkeeping identities used below (for `x > 0`):

`x^{-η} · x² = x^{1-η} · x` and `x⁻¹ · (x^{1-η} · x) = x^{1-η}`. -/
theorem rpow_neg_mul_sq (x : ℝ) (hx : 0 < x) (η : ℝ) : x ^ (-η) * x ^ 2 = x ^ (1 - η) * x := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_add hx]
  conv_rhs => enter [2]; rw [← Real.rpow_one x]
  rw [← Real.rpow_add hx]
  congr 1
  ring

/-- For `x > 0`, `x⁻¹ · (x^{1-η} · x) = x^{1-η}`. -/
theorem inv_mul_rpow_mul_self (x : ℝ) (hx : 0 < x) (η : ℝ) :
    x⁻¹ * (x ^ (1 - η) * x) = x ^ (1 - η) := by
  rw [show x⁻¹ * (x ^ (1 - η) * x) = x ^ (1 - η) * (x⁻¹ * x) by ring,
    inv_mul_cancel₀ (ne_of_gt hx), mul_one]

/-- On `(0, π/4)`, `tan θ ≤ 1` (equivalently `tan θ < 1`, `tan` being increasing). -/
theorem abs_tan_le_one_of_lt_pi_div_four {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 4) :
    |Real.tan θ| ≤ 1 := by
  have hpos : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two h0 (by linarith [Real.pi_pos])
  rw [abs_of_pos hpos]
  have h := Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two (x := θ) (y := Real.pi / 4)
    (le_of_lt h0) (by linarith [Real.pi_pos]) h1
  rw [Real.tan_pi_div_four] at h
  exact le_of_lt h

/-- On `[π/4, π/2)`, `tan θ ≤ (π/2 - θ)⁻¹`. -/
theorem abs_tan_le_inv_of_le_pi_div_four {θ : ℝ} (h0 : Real.pi / 4 ≤ θ)
    (h1 : θ < Real.pi / 2) : |Real.tan θ| ≤ (Real.pi / 2 - θ)⁻¹ := by
  have hpos : 0 < Real.tan θ :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith [Real.pi_pos]) h1
  rw [abs_of_pos hpos]
  have ht0 : 0 < Real.pi / 2 - θ := by linarith [Real.pi_pos]
  have htl : Real.pi / 2 - θ < Real.pi / 2 := by linarith
  have heq : Real.tan θ = (Real.tan (Real.pi / 2 - θ))⁻¹ := by
    conv_lhs => rw [show θ = Real.pi / 2 - (Real.pi / 2 - θ) by ring, Real.tan_pi_div_two_sub]
  rw [heq]
  have h := one_div_le_one_div_of_le ht0 (le_of_lt (Real.lt_tan ht0 htl))
  simpa [one_div] using h

/-- `|sig η θ| ≤ (4/π)^{-η} t^{-η}` whenever `0 < t`, `0 < sin (2θ)` and `(4/π) t ≤ sin (2θ)`
(the pointwise form of the bound via `Real.rpow_le_rpow_of_nonpos`). -/
theorem abs_sig_le_rpow {η θ t : ℝ} (hη0 : 0 ≤ η) (ht0 : 0 < t) (hsin : 0 < Real.sin (2 * θ))
    (hge : (4 / Real.pi) * t ≤ Real.sin (2 * θ)) :
    |sig η θ| ≤ (4 / Real.pi) ^ (-η) * t ^ (-η) := by
  simp only [sig]
  rw [abs_of_nonneg (Real.rpow_nonneg (le_of_lt hsin) _)]
  calc Real.sin (2 * θ) ^ (-η) ≤ ((4 / Real.pi) * t) ^ (-η) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hge (by linarith)
    _ = (4 / Real.pi) ^ (-η) * t ^ (-η) := Real.mul_rpow (by positivity) (le_of_lt ht0)

/-! ## The `tan`-weighted term tends to `0` at the two endpoints -/

/-- `tan θ · u θ² · σ η θ → 0` as `θ → 0⁺`, under `|u θ| ≤ C θ` and `0 ≤ η < 1`. -/
theorem tendsto_tan_mul_sig_mul_sq_nhdsGT_zero (η C : ℝ) (u : ℝ → ℝ) (hη0 : 0 ≤ η)
    (hη1 : η < 1) (_hC : 0 ≤ C) (hb1 : ∀ θ ∈ Iθo, |u θ| ≤ C * θ) :
    Filter.Tendsto (fun θ => Real.tan θ * sig η θ * u θ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hpow := tendsto_rpow_one_sub_nhdsGT_zero (η := η) hη1
  have hA : Filter.Tendsto
      (fun θ : ℝ => C ^ 2 * (4 / Real.pi) ^ (-η) * (Real.pi / 4) * θ ^ (1 - η))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using hpow.const_mul (C ^ 2 * (4 / Real.pi) ^ (-η) * (Real.pi / 4))
  refine squeeze_zero_norm' ?_ hA
  have hsmall : Set.Iio (Real.pi / 4) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 4))
  filter_upwards [self_mem_nhdsWithin, hsmall] with θ hθ0 hθ1
  have h0 : (0 : ℝ) < θ := Set.mem_Ioi.mp hθ0
  have h1 : θ < Real.pi / 4 := Set.mem_Iio.mp hθ1
  have hθI : θ ∈ Iθo := Set.mem_Ioo.mpr ⟨h0, by linarith [Real.pi_pos, h1]⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos, h1])
  rw [Real.norm_eq_abs]
  have htan := abs_tan_le_one_of_lt_pi_div_four h0 h1
  have hsig := abs_sig_le_rpow (η := η) (θ := θ) (t := θ) hη0 h0 hsin
    (sin_two_ge_four_div_pi_mul θ (le_of_lt h0) (le_of_lt h1))
  have hu2 : |u θ| ^ 2 ≤ (C * θ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hb1 θ hθI) 2
  have hq := rpow_neg_mul_sq θ h0 η
  calc |Real.tan θ * sig η θ * u θ ^ 2|
      = |Real.tan θ| * |sig η θ| * |u θ| ^ 2 := by rw [abs_mul, abs_mul, abs_pow]
    _ ≤ 1 * ((4 / Real.pi) ^ (-η) * θ ^ (-η)) * (C * θ) ^ 2 := by
        refine mul_le_mul (mul_le_mul htan hsig (abs_nonneg _) (by positivity)) hu2
          (by positivity) (by positivity)
    _ = C ^ 2 * (4 / Real.pi) ^ (-η) * (θ ^ (-η) * θ ^ 2) := by ring
    _ = C ^ 2 * (4 / Real.pi) ^ (-η) * (θ ^ (1 - η) * θ) := by rw [hq]
    _ ≤ C ^ 2 * (4 / Real.pi) ^ (-η) * (θ ^ (1 - η) * (Real.pi / 4)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_of_lt h1) ?_) ?_
        · exact Real.rpow_nonneg (le_of_lt h0) _
        · positivity
    _ = C ^ 2 * (4 / Real.pi) ^ (-η) * (Real.pi / 4) * θ ^ (1 - η) := by ring

/-- `tan θ · u θ² · σ η θ → 0` as `θ → π/2⁻`, under `|u θ| ≤ C (π/2 - θ)` and `0 ≤ η < 1`. -/
theorem tendsto_tan_mul_sig_mul_sq_nhdsLT_pi_div_two (η C : ℝ) (u : ℝ → ℝ) (hη0 : 0 ≤ η)
    (hη1 : η < 1) (_hC : 0 ≤ C) (hb2 : ∀ θ ∈ Iθo, |u θ| ≤ C * (Real.pi / 2 - θ)) :
    Filter.Tendsto (fun θ => Real.tan θ * sig η θ * u θ ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hpow := tendsto_rpow_one_sub_nhdsLT_pi_div_two (η := η) hη1
  have hA : Filter.Tendsto
      (fun θ : ℝ => C ^ 2 * (4 / Real.pi) ^ (-η) * (Real.pi / 2 - θ) ^ (1 - η))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    simpa using hpow.const_mul (C ^ 2 * (4 / Real.pi) ^ (-η))
  refine squeeze_zero_norm' ?_ hA
  have hbig : Set.Ioi (Real.pi / 4) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
    mem_nhdsWithin_of_mem_nhds
      (Ioi_mem_nhds (by linarith [Real.pi_pos] : Real.pi / 4 < Real.pi / 2))
  filter_upwards [self_mem_nhdsWithin, hbig] with θ hθ1 hθ0
  have h1 : θ < Real.pi / 2 := Set.mem_Iio.mp hθ1
  have h0 : Real.pi / 4 ≤ θ := le_of_lt (Set.mem_Ioi.mp hθ0)
  have hθI : θ ∈ Iθo := Set.mem_Ioo.mpr ⟨by linarith [Real.pi_pos, h0], h1⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos, h0]) (by linarith [Real.pi_pos, h1])
  rw [Real.norm_eq_abs]
  have ht0 : 0 < Real.pi / 2 - θ := by linarith [Real.pi_pos]
  have htan := abs_tan_le_inv_of_le_pi_div_four h0 h1
  have hsig := abs_sig_le_rpow (η := η) (θ := θ) (t := Real.pi / 2 - θ) hη0 ht0 hsin
    (sin_two_ge_four_div_pi_mul_sub θ h0 h1)
  have hu2 : |u θ| ^ 2 ≤ (C * (Real.pi / 2 - θ)) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (hb2 θ hθI) 2
  have hq := rpow_neg_mul_sq (Real.pi / 2 - θ) ht0 η
  have hinv := inv_mul_rpow_mul_self (Real.pi / 2 - θ) ht0 η
  calc |Real.tan θ * sig η θ * u θ ^ 2|
      = |Real.tan θ| * |sig η θ| * |u θ| ^ 2 := by rw [abs_mul, abs_mul, abs_pow]
    _ ≤ (Real.pi / 2 - θ)⁻¹ * ((4 / Real.pi) ^ (-η) * (Real.pi / 2 - θ) ^ (-η))
          * (C * (Real.pi / 2 - θ)) ^ 2 := by
        refine mul_le_mul (mul_le_mul htan hsig (abs_nonneg _) (by positivity)) hu2
          (by positivity) (by positivity)
    _ = C ^ 2 * (4 / Real.pi) ^ (-η)
          * ((Real.pi / 2 - θ)⁻¹ * ((Real.pi / 2 - θ) ^ (-η) * (Real.pi / 2 - θ) ^ 2)) := by
        ring
    _ = C ^ 2 * (4 / Real.pi) ^ (-η)
          * ((Real.pi / 2 - θ)⁻¹ * ((Real.pi / 2 - θ) ^ (1 - η) * (Real.pi / 2 - θ))) := by
        rw [hq]
    _ = C ^ 2 * (4 / Real.pi) ^ (-η) * (Real.pi / 2 - θ) ^ (1 - η) := by rw [hinv]

/-! ## The main statement -/

theorem HonPrimitiveTendsto (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (u : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hb1 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |u θ| ≤ C * θ)
    (hb2 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |u θ| ≤ C * (Real.pi / 2 - θ))
    (hb3 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |deriv u θ| ≤ C) :
    Filter.Tendsto (fun θ => - deriv u θ * u θ * Work.FTS.EllipticEst.Honest.sig η θ
        + (1 / 2) * (u θ) ^ 2 * Work.FTS.EllipticEst.Honest.sigD η θ
        + (1 / 2) * Real.tan θ * (u θ) ^ 2 * Work.FTS.EllipticEst.Honest.sig η θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ => - deriv u θ * u θ * Work.FTS.EllipticEst.Honest.sig η θ
        + (1 / 2) * (u θ) ^ 2 * Work.FTS.EllipticEst.Honest.sigD η θ
        + (1 / 2) * Real.tan θ * (u θ) ^ 2 * Work.FTS.EllipticEst.Honest.sig η θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  obtain ⟨hA1, hA2, hB1, hB2⟩ := SliceBoundary u η C hη0 hη1 hC hb1 hb2 hb3
  have hG1 := tendsto_tan_mul_sig_mul_sq_nhdsGT_zero η C u hη0 hη1 hC hb1
  have hG2 := tendsto_tan_mul_sig_mul_sq_nhdsLT_pi_div_two η C u hη0 hη1 hC hb2
  constructor
  · have hc := (hA1.neg.sub (hB1.const_mul η)).add (hG1.const_mul (1 / 2))
    simp only [neg_zero, mul_zero, sub_zero, add_zero] at hc
    refine Filter.Tendsto.congr' ?_ hc
    filter_upwards with θ
    simp only [sigD_eq_neg_two_mul_rho]
    ring
  · have hc := (hA2.neg.sub (hB2.const_mul η)).add (hG2.const_mul (1 / 2))
    simp only [neg_zero, mul_zero, sub_zero, add_zero] at hc
    refine Filter.Tendsto.congr' ?_ hc
    filter_upwards with θ
    simp only [sigD_eq_neg_two_mul_rho]
    ring

end Work.FTS.EllipticEst.Honest
