import Mathlib
import Submission.Work.ZeroDensity.Defs
import Submission.Work.ZeroDensity.Basic
import Submission.Work.LinnikAreas.Setup
import Submission.Work.LinnikAreas.PrincipalZeroCount
import Submission.Work.LinnikAreas.boxMaxZero

namespace Work.LinnikAreas

open scoped Classical BigOperators
open DirichletCharacter

/-- The family zero count splits into the sum over the non-principal characters and the
contribution of the principal one. -/
theorem famCount_eq_erase_add {q : ℕ} [NeZero q] (σ T : ℝ) :
    Work.ZeroDensity.famCount q σ T
      = (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), zeroCountIn χ σ T)
        + zeroCountIn (1 : DirichletCharacter ℂ q) σ T := by
  rw [Work.ZeroDensity.famCount]
  simp only [Work.ZeroDensity.zCount]
  exact (Finset.sum_erase_add Finset.univ (fun χ : DirichletCharacter ℂ q => zeroCountIn χ σ T)
    (Finset.mem_univ 1)).symm

/-- **The principal character contributes an absolute constant at height `1`.**  The principal
character's zero count at height `1` is (independently of the modulus `q`) the number of zeros of
the completed Riemann zeta function in the rectangle `σ ≤ Re ρ ≤ 1`, `|Im ρ| ≤ 1`, and this is
dominated by the divisor sum of the entire completion `Ξ` over the fixed disk of radius `3`
(`Work.LinnikAreas.zeroCountIn_one_le_divisorSum`). -/
theorem zeroCountIn_one_height_one_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ [NeZero q] (σ : ℝ), (4 : ℝ) / 5 ≤ σ → σ ≤ 1 →
      zeroCountIn (1 : DirichletCharacter ℂ q) σ 1 ≤ C := by
  refine ⟨|(∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiC
      (Metric.closedBall (0 : ℂ) ((1 : ℝ) + 2))) u : ℤ) : ℝ))| + 1, by positivity, ?_⟩
  intro q hqne σ h4 h1
  have hD := zeroCountIn_one_le_divisorSum q σ 1 (by linarith) h1 le_rfl
  refine le_trans hD (le_trans (le_abs_self _) (by linarith))

/-- The `q`-power of the target exponent is the exponential of the target exponent, for `q ≥ 2`. -/
theorem rpow_half_eq_exp (q : ℕ) (hq : 2 ≤ q) (σ : ℝ) :
    (q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ))
      = Real.exp ((5 : ℝ) / 2 * ((1 - σ) * Real.log (q : ℝ))) := by
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (q : ℝ))]
  congr 1
  ring

theorem logFreeFamHalfOfNonPrincipal
    (hJ : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4 : ℝ) / 5 ≤ σ → σ ≤ 1 → 1 ≤ T →
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            Work.LinnikAreas.zeroCountIn χ σ T)
          ≤ C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)))
    (hH : Work.ZeroDensity.FamDensityEpsRange 0 (4/5) (12/5)) :
    Work.ZeroDensity.LogFreeFamHalf (5/2) := by
  -- the three quantitative inputs, all with the auxiliary exponent `1/10`
  obtain ⟨CH, hCH, hHb⟩ := hH (1 / 10) (by norm_num)
  obtain ⟨CJ, hCJ, hJb⟩ := hJ (1 / 10) (by norm_num)
  obtain ⟨CZ, hCZ, hZb⟩ := zeroCountIn_one_height_one_bound
  refine ⟨CH + CJ + CZ + 1, by linarith, 2, fun q hq hqne σ h0 h1 => ?_⟩
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have h1m : (0 : ℝ) ≤ 1 - σ := by linarith
  by_cases hσ : σ ≤ (4 : ℝ) / 5
  · -- **Range `σ ≤ 4/5`**: Huxley's log-free family bound with coefficient `12/5`.
    have h := hHb q hq σ 1 h0 hσ le_rfl
    simp only [mul_one] at h
    have hexp : (q : ℝ) ^ (((12 : ℝ) / 5 + 1 / 10) * (1 - σ))
        = Real.exp ((5 : ℝ) / 2 * ((1 - σ) * Real.log (q : ℝ))) := by
      have hc : ((12 : ℝ) / 5 + 1 / 10) = (5 : ℝ) / 2 := by norm_num
      rw [hc]
      exact rpow_half_eq_exp q hq σ
    rw [hexp] at h
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (Real.exp_pos _))
    linarith
  · -- **Range `4/5 < σ ≤ 1`**: Jutila for the non-principal characters + the zeta bound.
    push_neg at hσ
    set E : ℝ := Real.exp ((5 : ℝ) / 2 * ((1 - σ) * Real.log (q : ℝ))) with hEdef
    have hEpos : 0 < E := by rw [hEdef]; exact Real.exp_pos _
    have hsplit := famCount_eq_erase_add (q := q) σ 1
    rw [hsplit]
    have hp : zeroCountIn (1 : DirichletCharacter ℂ q) σ 1 ≤ CZ := hZb q σ (le_of_lt hσ) h1
    have hnp := hJb q hq σ 1 (le_of_lt hσ) h1 le_rfl
    simp only [mul_one] at hnp
    have hexp : (q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) = E := by
      rw [hEdef]; exact rpow_half_eq_exp q hq σ
    have hqpow : (q : ℝ) ^ ((2 + 1 / 10) * (1 - σ)) ≤ (q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) := by
      refine Real.rpow_le_rpow_of_exponent_le hq1 ?_
      nlinarith [h1m]
    have hnp' : (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), zeroCountIn χ σ 1)
        ≤ CJ * E := by
      refine le_trans hnp ?_
      calc CJ * (q : ℝ) ^ ((2 + 1 / 10) * (1 - σ))
          ≤ CJ * (q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) :=
            mul_le_mul_of_nonneg_left hqpow (le_of_lt hCJ)
        _ = CJ * E := by rw [hexp]
    have hE1 : (1 : ℝ) ≤ E := by
      have : (1 : ℝ) ≤ (q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) :=
        Real.one_le_rpow hq1 (by nlinarith [h1m])
      rwa [hexp] at this
    have hCZle : CZ ≤ CZ * E := by
      calc CZ = CZ * 1 := (mul_one CZ).symm
        _ ≤ CZ * E := mul_le_mul_of_nonneg_left hE1 (le_of_lt hCZ)
    calc (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), zeroCountIn χ σ 1)
            + zeroCountIn (1 : DirichletCharacter ℂ q) σ 1
        ≤ CJ * E + CZ := add_le_add hnp' hp
      _ ≤ CJ * E + CZ * E := by linarith
      _ = (CJ + CZ) * E := by ring
      _ ≤ (CH + CJ + CZ + 1) * E := by
          refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hEpos)
          linarith

end Work.LinnikAreas
