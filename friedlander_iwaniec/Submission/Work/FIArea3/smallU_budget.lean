import Mathlib
import Submission.Work.FITop.Defs

namespace Work.FIArea3

/-- The `(τ⁻¹+θ)/θ = 1 + (θτ)⁻¹` factor is at least `N^{1/12}` in the small-`u` regime.
`θ√N ≤ N^{1/4}` gives `θ⁻¹ ≥ N^{1/4}`; `τ ≤ x^{η/3}` (`Pa.hτ2`) gives `τ⁻¹ ≥ x^{-η/3}`;
`x^{1/4+η} < N < x^{1/2}(log x)^{-B}` (`Pa.hNlo`, `Pa.hNhi`) forces `η < 1/4`.  Together,
`(θτ)⁻¹ ≥ N^{1/4}x^{-η/3} > x^{(1-4η)/24} > 1`, so the right-hand side even exceeds
`N^{1/12} = exp(log N / 12)` without the `1 +`. -/
theorem smallU_budget (Pa : Work.FITop.Params)
    (hu : (1 / 10 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N)
    (hu14 : Pa.θ * Real.sqrt Pa.N ≤ Pa.N ^ ((1 : ℝ) / 4)) :
    Real.exp (Real.log (Pa.N : ℝ) / 12) ≤ 1 + (Pa.θ * Pa.τ)⁻¹ := by
  -- basic size facts
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hx1 : 1 < (Pa.x : ℝ) := by linarith
  have hx0 : 0 < (Pa.x : ℝ) := by linarith
  have hN0 : 0 < Pa.N := by linarith [Pa.hN1]
  -- `log x ≥ 1`
  have hlog1 : 1 ≤ Real.log (Pa.x : ℝ) :=
    (Real.le_log_iff_exp_le hx0).mpr (le_of_lt (lt_of_lt_of_le Real.exp_one_lt_three hx3))
  -- `(log x)^{-B} ≤ 1`
  have hlogpow : (Real.log (Pa.x : ℝ)) ^ (-Pa.B) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hlog1 (by linarith [Pa.hB])
  -- the two ends of the range (4.6) force `η < 1/4`
  have hxhalf : (Pa.x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (Pa.x : ℝ)) ^ (-Pa.B)
      ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 2) := by
    simpa using mul_le_mul_of_nonneg_left hlogpow (Real.rpow_nonneg (le_of_lt hx0) ((1 : ℝ) / 2))
  have hlt1 : (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) < (Pa.x : ℝ) ^ ((1 : ℝ) / 2) :=
    Pa.hNlo.trans_le (Pa.hNhi.le.trans hxhalf)
  have hηlt : Pa.η < 1 / 4 := by
    have := (Real.rpow_lt_rpow_left_iff hx1).mp hlt1
    linarith
  -- hence `x^{2η} < N`, so `x^{η/3} < N^{1/6}`
  have hxpow : (Pa.x : ℝ) ^ (2 * Pa.η) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) :=
    Real.rpow_le_rpow_of_exponent_le (le_of_lt hx1) (by linarith)
  have hxpowN : (Pa.x : ℝ) ^ (2 * Pa.η) < Pa.N := hxpow.trans_lt Pa.hNlo
  have hη3 : (Pa.x : ℝ) ^ (Pa.η / 3) < Pa.N ^ ((1 : ℝ) / 6) := by
    have h := Real.rpow_lt_rpow (Real.rpow_nonneg (le_of_lt hx0) (2 * Pa.η)) hxpowN
      (show (0 : ℝ) < (1 : ℝ) / 6 by norm_num)
    rw [← Real.rpow_mul (le_of_lt hx0) (2 * Pa.η) ((1 : ℝ) / 6),
      show 2 * Pa.η * ((1 : ℝ) / 6) = Pa.η / 3 by ring] at h
    exact h
  -- inverting: `N^{-1/6} < x^{-η/3}`
  have hinv : Pa.N ^ (-((1 : ℝ) / 6)) < (Pa.x : ℝ) ^ (-(Pa.η / 3)) := by
    have h := (inv_lt_inv₀ (Real.rpow_pos_of_pos hN0 ((1 : ℝ) / 6))
      (Real.rpow_pos_of_pos hx0 (Pa.η / 3))).mpr hη3
    rwa [← Real.rpow_neg (le_of_lt hN0) ((1 : ℝ) / 6),
      ← Real.rpow_neg (le_of_lt hx0) (Pa.η / 3)] at h
  -- `N^{1/12} < N^{1/4} · x^{-η/3}`
  have hN12 : Pa.N ^ ((1 : ℝ) / 12) < Pa.N ^ ((1 : ℝ) / 4) * (Pa.x : ℝ) ^ (-(Pa.η / 3)) := by
    have h14pos : 0 < Pa.N ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hN0 _
    have hmain := mul_lt_mul_of_pos_left hinv h14pos
    have heq : Pa.N ^ ((1 : ℝ) / 4) * Pa.N ^ (-((1 : ℝ) / 6)) = Pa.N ^ ((1 : ℝ) / 12) := by
      rw [← Real.rpow_add hN0, show (1 : ℝ) / 4 + -((1 : ℝ) / 6) = (1 : ℝ) / 12 by norm_num]
    rwa [heq] at hmain
  -- `θ ≤ N^{-1/4}`, i.e. `N^{1/4} ≤ θ⁻¹`
  have hθle : Pa.θ ≤ Pa.N ^ (-((1 : ℝ) / 4)) := by
    have hb : 0 < Real.sqrt Pa.N := Real.sqrt_pos_of_pos hN0
    have h1 : Pa.θ ≤ Pa.N ^ ((1 : ℝ) / 4) / Real.sqrt Pa.N := (le_div_iff₀ hb).mpr hu14
    have h2 : Pa.N ^ ((1 : ℝ) / 4) / Real.sqrt Pa.N = Pa.N ^ (-((1 : ℝ) / 4)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hN0,
        show (1 : ℝ) / 4 - (1 : ℝ) / 2 = -((1 : ℝ) / 4) by norm_num]
    rwa [h2] at h1
  have hθinv : Pa.N ^ ((1 : ℝ) / 4) ≤ Pa.θ⁻¹ := by
    have hpos : 0 < Pa.N ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hN0 _
    have hle : Pa.θ ≤ (Pa.N ^ ((1 : ℝ) / 4))⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hN0) ((1 : ℝ) / 4)] at hθle
      exact hθle
    have h := (inv_le_inv₀ (inv_pos.mpr hpos) Pa.hθ0).mpr hle
    rwa [inv_inv] at h
  -- `τ ≤ x^{η/3}`, i.e. `x^{-η/3} ≤ τ⁻¹`
  have hlogτ : 1 ≤ (Real.log (Pa.x : ℝ)) ^ (Pa.A + 124) :=
    Real.one_le_rpow hlog1 (by linarith [Pa.hA])
  have hτ1le : 1 ≤ Pa.τ := hlogτ.trans Pa.hτ1
  have hτpos : 0 < Pa.τ := by linarith
  have hxinv : (Pa.x : ℝ) ^ (-(Pa.η / 3)) ≤ Pa.τ⁻¹ := by
    have h := (inv_le_inv₀ (Real.rpow_pos_of_pos hx0 (Pa.η / 3)) hτpos).mpr Pa.hτ2
    rwa [← Real.rpow_neg (le_of_lt hx0) (Pa.η / 3)] at h
  -- assemble
  have hprod : Pa.N ^ ((1 : ℝ) / 12) < Pa.θ⁻¹ * Pa.τ⁻¹ :=
    hN12.trans_le (mul_le_mul hθinv hxinv (Real.rpow_nonneg (le_of_lt hx0) _)
      (le_of_lt (inv_pos.mpr Pa.hθ0)))
  have hexp : Real.exp (Real.log (Pa.N : ℝ) / 12) = Pa.N ^ ((1 : ℝ) / 12) := by
    rw [Real.rpow_def_of_pos hN0]
    congr 1
    ring
  rw [hexp]
  refine le_of_lt ?_
  calc Pa.N ^ ((1 : ℝ) / 12) < (Pa.θ * Pa.τ)⁻¹ := by rwa [mul_inv]
    _ ≤ 1 + (Pa.θ * Pa.τ)⁻¹ := le_add_of_nonneg_left zero_le_one

end Work.FIArea3
