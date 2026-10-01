import Mathlib

namespace Work.LinnikAreas.BGTZArith

/-- The comparison `Φ·e ≤ C₀·U·log q` of the detector case: with
`Φ = 1.01·log(q·max 4|γ|)/cZ + log q·U + 106`, `log q·U = (11/5)log q + (11/10)log(5+|γ|)`,
`log(q·max 4|γ|) ≤ log q + log 4 + log(5+|γ|)` and `C₀ = max (1000/cZ) 1000` (so `cZ·C₀ ≥ 1000`),
the whole `1/cZ`-term is absorbed coefficientwise. -/
lemma phi_bound {cZ Lq U X Φ γ : ℝ} (hcZ : 0 < cZ) (hLq : 2000 ≤ Lq) (hX0 : 0 ≤ X)
    (hU : Lq * U = (11 / 5) * Lq + (11 / 10) * Real.log (5 + |γ|))
    (hX : X ≤ Lq + Real.log 4 + Real.log (5 + |γ|))
    (hΦ : Φ = 1.01 * (X / cZ) + Lq * U + 106) :
    Φ * Real.exp 1 ≤ max (1000 / cZ) 1000 * U * Lq := by
  have he1 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  have henn : (0:ℝ) ≤ Real.exp 1 := le_of_lt hepos
  have h1le : (1:ℝ) ≤ 5 + |γ| := by have := abs_nonneg γ; linarith
  have hlogγ_nn : 0 ≤ Real.log (5 + |γ|) := Real.log_nonneg h1le
  set T : ℝ := Lq * U with hTdef
  have hT_ge : 4400 ≤ T := by
    rw [hU]; nlinarith [hlogγ_nn, hLq]
  have hTnn : 0 ≤ T := by linarith
  have hlogγ_eq : Real.log (5 + |γ|) = (10 / 11) * T - 2 * Lq := by
    linarith [hU]
  have hlog4le : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith
  have hXle : X ≤ (10 / 11) * T := by
    have h := hX; rw [hlogγ_eq] at h; nlinarith [h, hlog4le, hLq]
  have hAX : 1.01 * X * Real.exp 1 ≤ 500 * T := by
    nlinarith [hXle, hX0, he1, henn, hTnn]
  have hA : 1.01 * (X / cZ) * Real.exp 1 ≤ 500 * T / cZ := by
    have h := div_le_div_of_nonneg_right hAX (le_of_lt hcZ)
    have heq : 1.01 * X * Real.exp 1 / cZ = 1.01 * (X / cZ) * Real.exp 1 := by ring
    rw [heq] at h; exact h
  have hB : T * Real.exp 1 + 106 * Real.exp 1 ≤ 500 * T := by
    nlinarith [he1, henn, hT_ge]
  have hsum : 1.01 * (X / cZ) * Real.exp 1 + T * Real.exp 1 + 106 * Real.exp 1
      ≤ 500 * T / cZ + 500 * T := by linarith [hA, hB]
  have hfinal : 500 * T / cZ + 500 * T ≤ max (1000 / cZ) 1000 * U * Lq := by
    have hkey : max (1000 / cZ) 1000 * U * Lq = max (1000 / cZ) 1000 * T := by
      rw [hTdef]; ring
    rw [hkey]
    have hC0a : 1000 / cZ ≤ max (1000 / cZ) 1000 := le_max_left _ _
    have hC0b : (1000:ℝ) ≤ max (1000 / cZ) 1000 := le_max_right _ _
    have hsplit : 500 * T / cZ + 500 * T
        = (1 / 2) * (1000 / cZ) * T + (1 / 2) * (1000:ℝ) * T := by ring
    rw [hsplit]
    have h1 : (1 / 2) * (1000 / cZ) * T ≤ (1 / 2) * (max (1000 / cZ) 1000) * T := by
      apply mul_le_mul_of_nonneg_right _ hTnn
      apply mul_le_mul_of_nonneg_left hC0a (by norm_num)
    have h2 : (1 / 2) * (1000:ℝ) * T ≤ (1 / 2) * (max (1000 / cZ) 1000) * T := by
      apply mul_le_mul_of_nonneg_right _ hTnn
      apply mul_le_mul_of_nonneg_left hC0b (by norm_num)
    linarith
  rw [hΦ]
  have hexp : (1.01 * (X / cZ) + T + 106) * Real.exp 1
      = 1.01 * (X / cZ) * Real.exp 1 + T * Real.exp 1 + 106 * Real.exp 1 := by ring
  rw [hexp]
  linarith [hsum, hfinal]

end Work.LinnikAreas.BGTZArith
