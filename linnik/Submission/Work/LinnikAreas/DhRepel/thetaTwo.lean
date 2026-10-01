import Mathlib

namespace Work.LinnikAreas.DhRepel

open Real

/-- The auxiliary function `θ ↦ sin θ ^ 3 - 2 sin θ + 2 θ cos θ`.

For `θ ∈ (0, π)` the equation `sin θ ^ 2 = 2 * (1 - θ * (cos θ / sin θ))` is equivalent
(after multiplying by `sin θ ≠ 0`) to `sin θ ^ 3 - 2 sin θ + 2 θ cos θ = 0`; see the end of
the proof of `thetaTwo`. -/
private noncomputable def Hfun (θ : ℝ) : ℝ := Real.sin θ ^ 3 - 2 * Real.sin θ + 2 * θ * Real.cos θ

/-- `sin (3/4)` lies between `87/128` and `3/4 - 4 * (95/384)^3`.

The lower bound is the cubic Taylor bound `Real.sin_ge_sub_cube`.
The upper bound uses the triple-angle formula `Real.sin_three_mul` at `θ = 1/4`, together with
`Real.sin_lt` (`sin (1/4) < 1/4`, for the term `3 * sin (1/4)`) and the cubic lower bound
(`sin (1/4) ≥ 1/4 - (1/4)^3/6 = 95/384`, for the term `- 4 * sin (1/4)^3`). -/
private lemma sin_three_quarters_bounds :
    (87 / 128 : ℝ) ≤ Real.sin (3 / 4) ∧ Real.sin (3 / 4) ≤ 3 / 4 - 4 * (95 / 384 : ℝ) ^ 3 := by
  have hs : (87 / 128 : ℝ) ≤ Real.sin (3 / 4) := by
    have h := Real.sin_ge_sub_cube (show (0 : ℝ) ≤ 3 / 4 by norm_num)
    norm_num at h ⊢
    exact h
  have hS : Real.sin (3 / 4) ≤ 3 / 4 - 4 * (95 / 384 : ℝ) ^ 3 := by
    have h3 : Real.sin (3 * (1 / 4 : ℝ)) = 3 * Real.sin (1 / 4) - 4 * Real.sin (1 / 4) ^ 3 :=
      Real.sin_three_mul (1 / 4 : ℝ)
    have hlt : Real.sin (1 / 4 : ℝ) ≤ 1 / 4 := (Real.sin_lt (by norm_num)).le
    have hge : (95 / 384 : ℝ) ≤ Real.sin (1 / 4) := by
      have h := Real.sin_ge_sub_cube (show (0 : ℝ) ≤ 1 / 4 by norm_num)
      norm_num at h ⊢
      exact h
    have hcube : (95 / 384 : ℝ) ^ 3 ≤ Real.sin (1 / 4) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hge 3
    norm_num at h3
    linarith [h3, mul_le_mul_of_nonneg_left hlt (by norm_num : (0 : ℝ) ≤ 3), hcube]
  exact ⟨hs, hS⟩

/-- `Hfun (3/4) > 0`, obtained from the explicit bounds on `sin (3/4)` and the quadratic Taylor
bound `Real.one_sub_sq_div_two_le_cos` for `cos (3/4) ≥ 1 - (3/4)^2/2 = 23/32`. -/
private lemma Hfun_three_quarters_pos : 0 < Hfun (3 / 4) := by
  rw [Hfun]
  obtain ⟨hs, hS⟩ := sin_three_quarters_bounds
  have hc : (23 / 32 : ℝ) ≤ Real.cos (3 / 4) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := (3 / 4 : ℝ))
    norm_num at h ⊢
    exact h
  have hs3 : (87 / 128 : ℝ) ^ 3 ≤ Real.sin (3 / 4) ^ 3 := pow_le_pow_left₀ (by norm_num) hs 3
  nlinarith [hs3, hs, hS, hc]

/-- `Hfun (π/2) = -1`. -/
private lemma Hfun_pi_div_two : Hfun (Real.pi / 2) = -1 := by
  rw [Hfun, Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

theorem thetaTwo : ∃ θ : ℝ, 3 / 4 < θ ∧ θ < Real.pi / 2 ∧
    Real.sin θ ^ 2 = 2 * (1 - θ * (Real.cos θ / Real.sin θ)) := by
  have hcont : Continuous Hfun := by
    unfold Hfun
    fun_prop
  have h34 : 0 < Hfun (3 / 4) := Hfun_three_quarters_pos
  have hpi : Hfun (Real.pi / 2) < 0 := by rw [Hfun_pi_div_two]; norm_num
  have hab : (3 / 4 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hmem : (0 : ℝ) ∈ Set.Icc (Hfun (Real.pi / 2)) (Hfun (3 / 4)) :=
    ⟨hpi.le, h34.le⟩
  -- the intermediate value theorem produces a zero of `Hfun` on `[3/4, π/2]`
  obtain ⟨c, hcIcc, hcH⟩ := intermediate_value_Icc' hab hcont.continuousOn hmem
  -- and the endpoint sign values show that this zero is strictly inside
  have hc34 : 3 / 4 < c := by
    rcases lt_or_eq_of_le hcIcc.1 with h | h
    · exact h
    · rw [← h] at hcH
      linarith [h34, hcH]
  have hcpi : c < Real.pi / 2 := by
    rcases lt_or_eq_of_le hcIcc.2 with h | h
    · exact h
    · rw [h] at hcH
      linarith [hpi, hcH]
  refine ⟨c, hc34, hcpi, ?_⟩
  have hsinpos : 0 < Real.sin c :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_gt_three])
  have hsc : Real.sin c ≠ 0 := hsinpos.ne'
  -- `Hfun c = 0` unfolds to `sin c ^ 3 - 2 sin c + 2 c cos c = 0`, and dividing by `sin c ≠ 0`
  -- gives the required identity
  have key : Real.sin c ^ 3 - 2 * Real.sin c + 2 * c * Real.cos c = 0 := hcH
  field_simp
  linarith [key]

end Work.LinnikAreas.DhRepel
