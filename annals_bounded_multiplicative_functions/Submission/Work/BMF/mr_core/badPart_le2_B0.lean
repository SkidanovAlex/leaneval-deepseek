import Mathlib
import Submission.Work.BMF.mr_core_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_core

theorem badPart_le2_B0 (ε C₀ K Cbs Cm Ccp : ℝ)
    (hε : 0 < ε) (hC₀ : 0 < C₀) (hK : 0 < K) (hCbs : 0 < Cbs) (hCm : 0 < Cm)
    (hCcp : 0 < Ccp) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B →
      (8 : ℝ) ≤ B ∧
      Cbs * Cm * K ^ 2 * (Work.BMF.mrCore.Ac B) ^ 4 * (1 + B ^ 2) ^ 2 *
          Real.exp (-(B ^ 2 / 4)) ≤ ε / 64 ∧
      Cbs * (3 + 4 * C₀ / ε) * Ccp * Real.log 3 / Work.BMF.mrCore.Ac B ≤ ε / 96 := by
  -- The two constants that multiply the decaying factors.
  set M1 : ℝ := 4 * (Cbs * Cm * K ^ 2) with hM1
  have hM1pos : 0 < M1 := by rw [hM1]; positivity
  set M2 : ℝ := Cbs * (3 + 4 * C₀ / ε) * Ccp * Real.log 3 with hM2
  have hM2pos : 0 < M2 := by
    rw [hM2]
    have h3 : 0 < 3 + 4 * C₀ / ε := by positivity
    have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    positivity
  -- Asymptotic decay of the two test functions.
  have hlim1 : Filter.Tendsto (fun B : ℝ => M1 * (B ^ 4 * Real.exp (-(3 / 16) * B)))
      Filter.atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 4 (3 / 16) (by norm_num)).const_mul M1
    simpa using h
  have hlim2 : Filter.Tendsto (fun B : ℝ => M2 * Real.exp (-(1 / 64) * B))
      Filter.atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (1 / 64) (by norm_num)).const_mul M2
    simpa using h
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp
    (hlim1.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 64)))
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp
    (hlim2.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 96)))
  refine ⟨max 8 (max N1 N2), lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) (le_max_left _ _), ?_⟩
  intro B hB
  have hB8 : 8 ≤ B := le_trans (le_max_left 8 (max N1 N2)) hB
  have hBN1 : N1 ≤ B := le_trans (le_trans (le_max_left N1 N2) (le_max_right 8 (max N1 N2))) hB
  have hBN2 : N2 ≤ B := le_trans (le_trans (le_max_right N1 N2) (le_max_right 8 (max N1 N2))) hB
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hB2 : B ≤ B ^ 2 := by nlinarith [hB1, sq_nonneg (B - 1)]
  -- `Ac B = exp (B²/64)`, hence `(Ac B)^4 * exp (-(B²/4)) = exp (-(3/16) B²)`.
  have hkey : (Work.BMF.mrCore.Ac B) ^ 4 * Real.exp (-(B ^ 2 / 4)) =
      Real.exp (-(3 / 16) * B ^ 2) := by
    rw [Work.BMF.mrCore.Ac, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hexp_le : Real.exp (-(3 / 16) * B ^ 2) ≤ Real.exp (-(3 / 16) * B) :=
    Real.exp_le_exp.mpr (by nlinarith [hB2])
  have hp : (1 + B ^ 2) ^ 2 ≤ 4 * B ^ 4 := by
    have h1 : (1 : ℝ) ≤ B ^ 2 := by nlinarith [hB1]
    have h3 : 1 + B ^ 2 ≤ 2 * B ^ 2 := by linarith
    have h0 : (0 : ℝ) ≤ 1 + B ^ 2 := by linarith [sq_nonneg B]
    calc (1 + B ^ 2) ^ 2 ≤ (2 * B ^ 2) ^ 2 := pow_le_pow_left₀ h0 h3 2
      _ = 4 * B ^ 4 := by ring
  have hc1pos : (0 : ℝ) < Cbs * Cm * K ^ 2 := by positivity
  have ineq1 : Cbs * Cm * K ^ 2 * (Work.BMF.mrCore.Ac B) ^ 4 * (1 + B ^ 2) ^ 2 *
      Real.exp (-(B ^ 2 / 4)) ≤ ε / 64 := by
    rw [show Cbs * Cm * K ^ 2 * (Work.BMF.mrCore.Ac B) ^ 4 * (1 + B ^ 2) ^ 2 *
          Real.exp (-(B ^ 2 / 4))
        = (Cbs * Cm * K ^ 2) * ((Work.BMF.mrCore.Ac B) ^ 4 * Real.exp (-(B ^ 2 / 4))) *
          (1 + B ^ 2) ^ 2 from by ring, hkey]
    calc (Cbs * Cm * K ^ 2) * Real.exp (-(3 / 16) * B ^ 2) * (1 + B ^ 2) ^ 2
        ≤ (Cbs * Cm * K ^ 2) * Real.exp (-(3 / 16) * B) * (4 * B ^ 4) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp_le hc1pos.le) hp
            (by positivity) (by positivity)
      _ = M1 * (B ^ 4 * Real.exp (-(3 / 16) * B)) := by rw [hM1]; ring
      _ ≤ ε / 64 := (hN1 B hBN1).le
  have ineq2 : Cbs * (3 + 4 * C₀ / ε) * Ccp * Real.log 3 / Work.BMF.mrCore.Ac B ≤ ε / 96 := by
    have hdiv : Cbs * (3 + 4 * C₀ / ε) * Ccp * Real.log 3 / Work.BMF.mrCore.Ac B
        = M2 * Real.exp (-(B ^ 2 / 64)) := by
      rw [← hM2, Work.BMF.mrCore.Ac, div_eq_mul_inv, ← Real.exp_neg]
    rw [hdiv]
    have hexp_le2 : Real.exp (-(B ^ 2 / 64)) ≤ Real.exp (-(1 / 64) * B) :=
      Real.exp_le_exp.mpr (by nlinarith [hB2])
    calc M2 * Real.exp (-(B ^ 2 / 64)) ≤ M2 * Real.exp (-(1 / 64) * B) :=
          mul_le_mul_of_nonneg_left hexp_le2 hM2pos.le
      _ ≤ ε / 96 := (hN2 B hBN2).le
  exact ⟨hB8, ineq1, ineq2⟩

end Work.BMF.mr_core
