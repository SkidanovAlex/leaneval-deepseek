import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.rectInt_logDeriv_gammaFactor_mul_eq
import Submission.Commons.NumberTheory.DirichletCharacter.horizontal_logDeriv_gammaFactor_tendsto_gen
import Submission.Commons.Analysis.Complex.rectInt_tendsto_vertical_gen
import Submission.Commons.NumberTheory.Linnik.tentMellin_bridge_scale

open Complex Filter MeasureTheory intervalIntegral
open scoped Real Topology

namespace Commons.NumberTheory.DirichletCharacter

theorem gammaFactor_shift_identity_gen {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) {Φ : ℂ → ℂ}
    (hΦdiff : Differentiable ℂ Φ) {M : ℝ} (hM : 0 < M)
    (hΦb : ∀ u : ℂ, u.re ≤ α → ‖Φ u‖ ≤ M / (1 + ‖u‖ ^ 2))
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) [Decidable χ.Even]
    (hIGα : MeasureTheory.Integrable (fun t : ℝ => logDeriv (DirichletCharacter.gammaFactor χ) ((α : ℂ) + (t : ℂ) * Complex.I) * Φ ((α : ℂ) + (t : ℂ) * Complex.I)))
    (hIGl : MeasureTheory.Integrable (fun t : ℝ => logDeriv (DirichletCharacter.gammaFactor χ) (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) * Φ (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I))) :
    (1 / (2 * (Real.pi : ℂ))) *
      ((∫ t : ℝ, logDeriv (DirichletCharacter.gammaFactor χ) ((α : ℂ) + (t : ℂ) * Complex.I) * Φ ((α : ℂ) + (t : ℂ) * Complex.I)) -
       (∫ t : ℝ, logDeriv (DirichletCharacter.gammaFactor χ) (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) * Φ (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)))
      = -(if χ.Even then Φ 0 else 0) := by
  classical
  set F : ℂ → ℂ := fun u => logDeriv (DirichletCharacter.gammaFactor χ) u * Φ u with hF
  have hM0 : (0 : ℝ) ≤ M := le_of_lt hM
  have hAB : (-1/2 : ℝ) < α := by linarith
  have hA : -(1/2 : ℝ) ≤ (-1/2 : ℝ) := by norm_num
  have hB2 : α ≤ 2 := le_of_lt hα2
  have hΦb' : ∀ u : ℂ, u.re ≤ α → ‖Φ u‖ ≤ M / (1 + ‖u‖ ^ 2) := hΦb
  obtain ⟨hu, hd⟩ := horizontal_logDeriv_gammaFactor_tendsto_gen (χ := χ) (A := (-1/2 : ℝ))
    (B := α) hA (le_of_lt hAB) hB2 hΦdiff hM0 hΦb'
  have hαint : Integrable (fun t : ℝ => F ((α : ℂ) + (t : ℂ) * Complex.I)) := by
    simpa [hF] using hIGα
  have hlint : Integrable (fun t : ℝ => F (((-1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    simpa [hF] using hIGl
  have hlim1 : Tendsto (fun T : ℝ => rectInt (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I)
      ((α : ℂ) + (T : ℂ) * Complex.I) F) atTop
      (nhds (Complex.I * ((∫ t : ℝ, F ((α : ℂ) + (t : ℂ) * Complex.I)) -
        (∫ t : ℝ, F (((-1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))))) :=
    Commons.Analysis.Complex.rectInt_tendsto_vertical_gen (F := F) (A := (-1/2 : ℝ)) (B := α) hAB hαint hlint
      (by simpa [hF] using hu) (by simpa [hF] using hd)
  have hgoal : (∫ t : ℝ, F ((α : ℂ) + (t : ℂ) * Complex.I)) -
      (∫ t : ℝ, F (((-1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      = -(if χ.Even then 2 * (Real.pi : ℂ) * Φ 0 else 0) := by
    rcases χ.even_or_odd with hE | hO
    · rw [if_pos hE]
      have hconst : ∀ T : ℝ, 0 < T → rectInt (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I)
          ((α : ℂ) + (T : ℂ) * Complex.I) F = -(2 * (Real.pi : ℂ) * Complex.I) * Φ 0 := by
        intro T hT
        have hzre : (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re <
            ((α : ℂ) + (T : ℂ) * Complex.I).re := by
          rw [show (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re = -1/2 by simp,
            show (((α : ℂ) + (T : ℂ) * Complex.I)).re = α by simp]
          linarith
        have hzim : (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).im <
            ((α : ℂ) + (T : ℂ) * Complex.I).im := by
          rw [show (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).im = -T by simp,
            show (((α : ℂ) + (T : ℂ) * Complex.I)).im = T by simp]
          linarith
        have hz1 : -(1 : ℝ) < (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re := by
          rw [show (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re = -1/2 by simp]
          norm_num
        have h0in : (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re < 0 ∧
            0 < ((α : ℂ) + (T : ℂ) * Complex.I).re ∧
            (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).im < 0 ∧
            0 < ((α : ℂ) + (T : ℂ) * Complex.I).im := by
          rw [show (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re = -1/2 by simp,
            show ((α : ℂ) + (T : ℂ) * Complex.I).re = α by simp,
            show (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).im = -T by simp,
            show ((α : ℂ) + (T : ℂ) * Complex.I).im = T by simp]
          exact ⟨by norm_num, by linarith, by linarith, by linarith⟩
        have h := rectInt_logDeriv_gammaFactor_mul_eq (N := N) χ (G := Φ)
          (hG := hΦdiff) (z := (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I))
          (w := ((α : ℂ) + (T : ℂ) * Complex.I)) hzre hzim hz1 h0in hE
        simpa [hF] using h
      have hlim2 : Tendsto (fun T : ℝ => rectInt (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I)
          ((α : ℂ) + (T : ℂ) * Complex.I) F) atTop
          (nhds (-(2 * (Real.pi : ℂ) * Complex.I) * Φ 0)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
        exact (hconst T (by linarith)).symm
      have huniq := tendsto_nhds_unique hlim1 hlim2
      apply mul_left_cancel₀ Complex.I_ne_zero
      rw [huniq]
      ring
    · rw [if_neg hO.not_even, neg_zero]
      have hconst : ∀ T : ℝ, 0 < T → rectInt (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I)
          ((α : ℂ) + (T : ℂ) * Complex.I) F = 0 := by
        intro T hT
        have hzre : (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re <
            ((α : ℂ) + (T : ℂ) * Complex.I).re := by
          rw [show (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re = -1/2 by simp,
            show (((α : ℂ) + (T : ℂ) * Complex.I)).re = α by simp]
          linarith
        have hzim : (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).im <
            ((α : ℂ) + (T : ℂ) * Complex.I).im := by
          rw [show (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).im = -T by simp,
            show (((α : ℂ) + (T : ℂ) * Complex.I)).im = T by simp]
          linarith
        have hz1 : -(1 : ℝ) < (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re := by
          rw [show (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re = -1/2 by simp]
          norm_num
        have h0in : (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re < 0 ∧
            0 < ((α : ℂ) + (T : ℂ) * Complex.I).re ∧
            (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).im < 0 ∧
            0 < ((α : ℂ) + (T : ℂ) * Complex.I).im := by
          rw [show (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re = -1/2 by simp,
            show ((α : ℂ) + (T : ℂ) * Complex.I).re = α by simp,
            show (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).im = -T by simp,
            show ((α : ℂ) + (T : ℂ) * Complex.I).im = T by simp]
          exact ⟨by norm_num, by linarith, by linarith, by linarith⟩
        have h := Commons.NumberTheory.Linnik.rectInt_logDeriv_gammaFactor_mul_eq_odd (N := N) χ (G := Φ)
          (hG := hΦdiff) (z := (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I))
          (w := ((α : ℂ) + (T : ℂ) * Complex.I)) hzre hzim hz1 h0in hO
        simpa [hF] using h
      have hlim2 : Tendsto (fun T : ℝ => rectInt (((-1/2 : ℝ) : ℂ) - (T : ℂ) * Complex.I)
          ((α : ℂ) + (T : ℂ) * Complex.I) F) atTop (nhds 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
        exact (hconst T (by linarith)).symm
      have huniq := tendsto_nhds_unique hlim1 hlim2
      exact mul_left_cancel₀ Complex.I_ne_zero (by rw [huniq, mul_zero])
  change (1 / (2 * (Real.pi : ℂ))) * ((∫ t : ℝ, F ((α : ℂ) + (t : ℂ) * Complex.I)) -
      (∫ t : ℝ, F (((-1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
      = -(if χ.Even then Φ 0 else 0)
  rw [hgoal]
  by_cases hE : χ.Even
  · rw [if_pos hE, if_pos hE]
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
      refine mul_ne_zero two_ne_zero ?_
      exact_mod_cast Real.pi_ne_zero
    field_simp
  · rw [if_neg hE, if_neg hE]
    ring

end Commons.NumberTheory.DirichletCharacter
