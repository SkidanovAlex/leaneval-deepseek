import Mathlib

namespace Work.Numeric

theorem Inequalities (t : ℕ) (Hc : ℝ) (hHc : 0 < Hc) (ht : 1 ≤ t)
    (hnum : Hc ^ 2 < (2:ℝ)^t) (D R : ℝ) (hD : 1 ≤ D) (hR : 1/2 < R) (hRD : 1 ≤ R * D)
    (hρ : -((t:ℝ) * Real.log 2 - 2 * Real.log Hc)/4 ≤ Real.log (1 - 1/(2*R))) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (f : ℕ) (U n : ℝ), 1 ≤ f → 0 < U → (2:ℝ) ^ (t * f) ≤ Hc ^ (2 * f) * U →
        n ≤ (4 * R * D) ^ (2 * f) → (2:ℝ) ^ (1 / δ) ≤ n →
        n ^ (1 + δ) ≤ 2⁻¹ * U * (1 - 1 / (2*R)) ^ (2*f) * n := by
  -- `ρ = 1 - 1/(2R)` is positive since `R > 1/2`.
  have hρpos : (0:ℝ) < 1 - 1 / (2 * R) := by
    have hR2 : (0:ℝ) < 2 * R := by linarith
    have h : (1:ℝ) / (2 * R) < 1 := by
      rw [div_lt_one hR2]; linarith
    linarith
  -- `1 < 4RD`, so `log (4RD) > 0`.
  have hRDpos : (0:ℝ) < R * D := mul_pos (by linarith) (by linarith)
  have h4RD : (1:ℝ) < 4 * R * D := by
    have h : (4:ℝ) * R * D = 4 * (R * D) := by ring
    rw [h]; linarith
  have hlog4RD : 0 < Real.log (4 * R * D) := Real.log_pos h4RD
  -- `c := (t log 2 - 2 log Hc)/4` is positive, from `Hc^2 < 2^t`.
  set c := ((t:ℝ) * Real.log 2 - 2 * Real.log Hc) / 4 with hc_def
  have hc : 0 < c := by
    rw [hc_def]
    have h1l : Real.log (Hc ^ 2) < Real.log ((2:ℝ)^t) :=
      Real.log_lt_log (pow_pos hHc 2) hnum
    rw [Real.log_pow, Real.log_pow] at h1l
    push_cast at h1l
    exact div_pos (by linarith) four_pos
  have hρ' : -c ≤ Real.log (1 - 1/(2*R)) := by
    rw [hc_def, ← neg_div]
    exact hρ
  -- The witness `δ := c / (2 log (4RD))`.
  set δ := c / (2 * Real.log (4 * R * D)) with hδ_def
  have hδ : 0 < δ := by
    rw [hδ_def]
    exact div_pos hc (mul_pos two_pos hlog4RD)
  refine ⟨δ, hδ, fun f U n hf hU h1 h2 h3 => ?_⟩
  have hn_pos : (0:ℝ) < n := lt_of_lt_of_le (Real.rpow_pos_of_pos two_pos _) h3
  -- A: `4cf ≤ log U`, from `2^(tf) ≤ Hc^(2f) * U`.
  have hA : 4 * c * (f:ℝ) ≤ Real.log U := by
    have h2pow_pos : (0:ℝ) < (2:ℝ) ^ (t * f) := by positivity
    have hlog := Real.log_le_log h2pow_pos h1
    rw [Real.log_mul (pow_pos hHc _).ne' hU.ne', Real.log_pow, Real.log_pow] at hlog
    push_cast at hlog
    have hX : 4 * c * (f:ℝ) = ((t:ℝ) * Real.log 2 - 2 * Real.log Hc) * (f:ℝ) := by
      rw [hc_def]; ring
    rw [hX]
    linarith
  -- B: `-2cf ≤ 2f log ρ`, from `hρ`.
  have hB : -(2 * c * (f:ℝ)) ≤ 2 * (f:ℝ) * Real.log (1 - 1/(2*R)) := by
    have h2f : (0:ℝ) ≤ 2 * (f:ℝ) := by positivity
    have h := mul_le_mul_of_nonneg_left hρ' h2f
    calc -(2 * c * (f:ℝ)) = 2 * (f:ℝ) * (-c) := by ring
      _ ≤ 2 * (f:ℝ) * Real.log (1 - 1/(2*R)) := h
  -- C: combining A and B.
  have hC : 2 * c * (f:ℝ) ≤ Real.log U + 2 * (f:ℝ) * Real.log (1 - 1/(2*R)) := by
    linarith [hA, hB]
  -- D: `log n ≤ 2f log(4RD)`, from `n ≤ (4RD)^(2f)`.
  have hD' : Real.log n ≤ (2:ℝ) * (f:ℝ) * Real.log (4 * R * D) := by
    have h := Real.log_le_log hn_pos h2
    rw [Real.log_pow] at h
    push_cast at h
    exact h
  -- E: `δ log n ≤ cf`, using the definition of `δ`.
  have hE : δ * Real.log n ≤ c * (f:ℝ) := by
    calc δ * Real.log n ≤ δ * (2 * (f:ℝ) * Real.log (4 * R * D)) :=
            mul_le_mul_of_nonneg_left hD' hδ.le
      _ = c * (f:ℝ) := by
          rw [hδ_def]
          have hne : (2:ℝ) * Real.log (4 * R * D) ≠ 0 :=
            mul_ne_zero two_ne_zero hlog4RD.ne'
          field_simp
  -- F: `log 2 ≤ δ log n`, from `2^(1/δ) ≤ n`.
  have hF : Real.log 2 ≤ δ * Real.log n := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos two_pos (1/δ)) h3
    rw [Real.log_rpow two_pos] at h
    have h2' := mul_le_mul_of_nonneg_left h hδ.le
    rw [one_div, ← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul] at h2'
    exact h2'
  -- G: combining E and F with C.
  have hG : δ * Real.log n + Real.log 2
      ≤ Real.log U + 2 * (f:ℝ) * Real.log (1 - 1/(2*R)) := by
    linarith [hC, hE, hF]
  -- H: exponentiating, `n^δ ≤ 2⁻¹ * U * ρ^(2f)`.
  have hH : n ^ δ ≤ 2⁻¹ * U * (1 - 1/(2*R)) ^ (2*f) := by
    have hρ2f_pos : (0:ℝ) < (1 - 1/(2*R)) ^ (2*f) := pow_pos hρpos _
    have hpos : (0:ℝ) < 2⁻¹ * U * (1 - 1/(2*R)) ^ (2*f) :=
      mul_pos (mul_pos (by norm_num) hU) hρ2f_pos
    rw [Real.rpow_def_of_pos hn_pos]
    have harg : Real.log n * δ ≤ Real.log (2⁻¹ * U * (1 - 1/(2*R))^(2*f)) := by
      have hne1 : (2:ℝ)⁻¹ * U ≠ 0 := (mul_pos (by norm_num : (0:ℝ) < 2⁻¹) hU).ne'
      have hne2 : (1 - 1/(2*R)) ^ (2*f) ≠ 0 := hρ2f_pos.ne'
      have hne3 : (2:ℝ)⁻¹ ≠ 0 := by norm_num
      rw [Real.log_mul hne1 hne2, Real.log_mul hne3 hU.ne', Real.log_inv, Real.log_pow]
      push_cast
      rw [mul_comm (Real.log n) δ]
      linarith [hG]
    calc Real.exp (Real.log n * δ)
          ≤ Real.exp (Real.log (2⁻¹ * U * (1 - 1/(2*R))^(2*f))) :=
            Real.exp_le_exp.mpr harg
      _ = 2⁻¹ * U * (1 - 1/(2*R))^(2*f) := Real.exp_log hpos
  -- Final: multiply by `n`.
  have key : n ^ (1 + δ) = n * n ^ δ := by
    rw [Real.rpow_add hn_pos, Real.rpow_one]
  rw [key]
  calc n * n ^ δ ≤ n * (2⁻¹ * U * (1 - 1/(2*R)) ^ (2*f)) :=
          mul_le_mul_of_nonneg_left hH hn_pos.le
    _ = 2⁻¹ * U * (1 - 1/(2*R)) ^ (2*f) * n := by ring

end Work.Numeric
