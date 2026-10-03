/-
# `Submission.Work.FIArea7CF.regionLowSplitTermPointwise` — clash-free copy of `Submission.Work.FIArea7.regionLowSplitTermPointwise`

Imports redirected to the `FIArea7CF` copies; renamed: norm_uniCoeff_le→crs_norm_uniCoeff_le.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7CF.charRegionSplitAux

namespace Work.FIArea7

/-- Pointwise bound for a pair of region I: `2K + L₀ + 2 ≥ 4` and
`4be(2K+L₀+2) ≤ N^{δ₁}` force `4be ≤ N^{δ₁}`, whence `√(4be) ≤ N^{δ₁/2}`; and `b,e ≥ 1` gives
`4be ≥ 4`, whence `√(4be) ≥ 2` and `15√N/√(4be) ≤ 15√N/2`. -/
lemma regionLowSplitTermPointwise (Pa : Work.FITop.Params) (X K L₀ : ℕ) (δ₁ : ℝ) (hK : 1 ≤ K)
    {p : ℕ × ℕ} (hp : p ∈ Work.FIArea7.charRegionLowFinset Pa X K L₀ δ₁) :
    (1 / (p.1 : ℝ)) * (15 * Real.sqrt Pa.N / Real.sqrt (4 * (p.1 : ℝ) * (p.2 : ℝ))
        + 2 * Real.sqrt (4 * (p.1 : ℝ) * (p.2 : ℝ)))
      ≤ (1 / (p.1 : ℝ)) * (15 * Real.sqrt Pa.N / 2 + 2 * Pa.N ^ (δ₁ / 2)) := by
  obtain ⟨hb, he, hreg⟩ := mem_charRegionLowFinset.mp hp
  rw [Finset.mem_Icc] at hb he
  obtain ⟨hb1, _⟩ := hb
  obtain ⟨he1, _⟩ := he
  have hbR : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hb1
  have heR : (1 : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast he1
  have hNpos : 0 < Pa.N := lt_of_lt_of_le zero_lt_one Pa.hN1
  have hNnn : 0 ≤ Pa.N := le_of_lt hNpos
  -- `4·b·e ≥ 0`
  have hsnn : (0 : ℝ) ≤ 4 * (p.1 : ℝ) * (p.2 : ℝ) := by
    have h := mul_nonneg (by linarith : (0 : ℝ) ≤ (p.1 : ℝ))
      (by linarith : (0 : ℝ) ≤ (p.2 : ℝ))
    nlinarith [h]
  -- `b·e ≥ 1` and hence `4·b·e ≥ 4`
  have hbe : (1 : ℝ) ≤ (p.1 : ℝ) * (p.2 : ℝ) := by
    have h := mul_le_mul hbR heR (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : (0 : ℝ) ≤ (p.1 : ℝ))
    simpa using h
  have hsge4 : (4 : ℝ) ≤ 4 * (p.1 : ℝ) * (p.2 : ℝ) := by nlinarith [hbe]
  -- `2K + L₀ + 2 ≥ 1`
  have hfac : (1 : ℝ) ≤ 2 * (K : ℝ) + (L₀ : ℝ) + 2 := by
    have hK' : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    have hL : (0 : ℝ) ≤ (L₀ : ℝ) := by positivity
    linarith
  -- `4·b·e ≤ N^δ₁`
  have hsle : 4 * (p.1 : ℝ) * (p.2 : ℝ) ≤ Pa.N ^ δ₁ := by
    calc 4 * (p.1 : ℝ) * (p.2 : ℝ)
        = 4 * (p.1 : ℝ) * (p.2 : ℝ) * 1 := by ring
      _ ≤ 4 * (p.1 : ℝ) * (p.2 : ℝ) * (2 * (K : ℝ) + (L₀ : ℝ) + 2) :=
            mul_le_mul_of_nonneg_left hfac hsnn
      _ ≤ Pa.N ^ δ₁ := hreg
  -- `√(N^δ₁) = N^{δ₁/2}`
  have hsqrt_rpow : Real.sqrt (Pa.N ^ δ₁) = Pa.N ^ (δ₁ / 2) := by
    have h1 : Real.sqrt (Pa.N ^ δ₁) = (Pa.N ^ δ₁) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    rw [h1, ← Real.rpow_mul hNnn]
    congr 1
    ring
  -- `√(4·b·e) ≤ N^{δ₁/2}`
  have hsqrt_le : Real.sqrt (4 * (p.1 : ℝ) * (p.2 : ℝ)) ≤ Pa.N ^ (δ₁ / 2) :=
    calc Real.sqrt (4 * (p.1 : ℝ) * (p.2 : ℝ))
        ≤ Real.sqrt (Pa.N ^ δ₁) := Real.sqrt_le_sqrt hsle
      _ = Pa.N ^ (δ₁ / 2) := hsqrt_rpow
  -- `√(4·b·e) ≥ 2`
  have hsqrt_ge2 : (2 : ℝ) ≤ Real.sqrt (4 * (p.1 : ℝ) * (p.2 : ℝ)) := by
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have h := Real.sqrt_le_sqrt hsge4
    linarith
  have hterm1 : 15 * Real.sqrt Pa.N / Real.sqrt (4 * (p.1 : ℝ) * (p.2 : ℝ))
      ≤ 15 * Real.sqrt Pa.N / 2 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hsqrt_ge2
  have hterm2 : 2 * Real.sqrt (4 * (p.1 : ℝ) * (p.2 : ℝ)) ≤ 2 * Pa.N ^ (δ₁ / 2) :=
    mul_le_mul_of_nonneg_left hsqrt_le (by norm_num)
  have hinner := add_le_add hterm1 hterm2
  exact mul_le_mul_of_nonneg_left hinner (div_nonneg zero_le_one (by linarith))

end Work.FIArea7
