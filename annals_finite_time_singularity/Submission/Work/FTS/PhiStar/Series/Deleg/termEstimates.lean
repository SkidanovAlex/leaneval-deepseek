import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

/-- `x ^ (3/2) = x √x` for `x > 0`. -/
private lemma rpow_three_half {x : ℝ} (hx : 0 < x) : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  have h : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
  rw [h, Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- Growth of the Gegenbauer eigenvalue: for `m ≥ 1`,
`(m+1)^4 √(m+1) ≤ (lam m)^2 √(2m+1)`.
Indeed `m + 1 ≤ 2m` and `lam m = 2m(2m+5) ≥ 4m²`, so both sides are at least
`16 m^4 √(2m)`. -/
private lemma core_le (m : ℕ) (hm : 1 ≤ m) :
    ((m : ℝ) + 1) ^ 4 * Real.sqrt ((m : ℝ) + 1)
      ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) := by
  have hy1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hle : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by linarith
  have hx4 : ((m : ℝ) + 1) ^ 4 ≤ 16 * (m : ℝ) ^ 4 := by
    have h : ((m : ℝ) + 1) ^ 4 ≤ (2 * (m : ℝ)) ^ 4 := pow_le_pow_left₀ (by linarith) hle 4
    calc ((m : ℝ) + 1) ^ 4 ≤ (2 * (m : ℝ)) ^ 4 := h
      _ = 16 * (m : ℝ) ^ 4 := by ring
  have hlam_ge : 4 * (m : ℝ) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
    simp only [Work.FTS.PhiStar.Gegenbauer.lam]
    nlinarith [hy1]
  have hlam2 : 16 * (m : ℝ) ^ 4 ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 := by
    have h0 : (0 : ℝ) ≤ 4 * (m : ℝ) ^ 2 := by positivity
    calc 16 * (m : ℝ) ^ 4 = (4 * (m : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 := pow_le_pow_left₀ h0 hlam_ge 2
  have hsx : Real.sqrt ((m : ℝ) + 1) ≤ Real.sqrt (2 * (m : ℝ)) :=
    Real.sqrt_le_sqrt (by linarith)
  have hs2 : Real.sqrt (2 * (m : ℝ)) ≤ Real.sqrt (2 * (m : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  calc ((m : ℝ) + 1) ^ 4 * Real.sqrt ((m : ℝ) + 1)
      ≤ (16 * (m : ℝ) ^ 4) * Real.sqrt (2 * (m : ℝ)) :=
        mul_le_mul hx4 hsx (Real.sqrt_nonneg _) (by positivity)
    _ ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) :=
        mul_le_mul hlam2 hs2 (Real.sqrt_nonneg _) (by positivity)

/-- The decay factor `M` times the growth factor `L` dominates `(m+1)^3`:
for `m ≥ 1`,
`(m+1)^3 ≤ ((m+1)^(3/2))⁻¹ * ((lam m)^2 √(2m+1))`. -/
private lemma x3_le_ML (m : ℕ) (hm : 1 ≤ m) :
    ((m : ℝ) + 1) ^ 3 ≤ (((m : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹ *
      ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) := by
  have hx : (0 : ℝ) < (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith
  have hb : 0 < ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) :=
    mul_pos hx (Real.sqrt_pos.2 hx)
  have hcore := core_le m hm
  have h1 : ((m : ℝ) + 1) ^ 3 * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))
      ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) := by
    calc ((m : ℝ) + 1) ^ 3 * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))
        = ((m : ℝ) + 1) ^ 4 * Real.sqrt ((m : ℝ) + 1) := by ring
      _ ≤ _ := hcore
  have h2 : ((m : ℝ) + 1) ^ 3 ≤
      ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) /
        (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) := (le_div_iff₀ hb).mpr h1
  rw [rpow_three_half hx]
  rw [inv_mul_eq_div]
  exact h2

theorem termEstimates (α : ℝ) (hα : 0 < α) (Cdec CB Kφ : ℝ) (hCdec : 0 < Cdec)
    (hCB : 0 < CB) (hKφ : 0 < Kφ) (cθ : ℝ) (hcθ : 0 < cθ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (m : ℕ), 1 ≤ m →
      let L := (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)
      let M := (((m : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹
      (α ^ 2 * Cdec * CB * Kφ / L * (3 * ((m : ℝ) + 1)) ≤ D * M) ∧
      (α ^ 2 * Cdec * CB * Kφ / L * (900 * ((m : ℝ) + 1) ^ 2 / cθ ^ 2) ≤ D * M) ∧
      (α ^ 2 * Cdec * CB * Kφ / L * (27000 * ((m : ℝ) + 1) ^ 3 / cθ ^ 4) ≤ D * M) ∧
      (α ^ 2 * Cdec * CB * Kφ / L * (9000 * ((m : ℝ) + 1) ^ 2 / cθ ^ 3) ≤ D * M) := by
  have hApos : 0 < α ^ 2 * Cdec * CB * Kφ := by positivity
  have hKpos : 0 < 3 + 900 / cθ ^ 2 + 27000 / cθ ^ 4 + 9000 / cθ ^ 3 := by positivity
  refine ⟨α ^ 2 * Cdec * CB * Kφ * (3 + 900 / cθ ^ 2 + 27000 / cθ ^ 4 + 9000 / cθ ^ 3),
    by positivity, ?_⟩
  intro m hm
  dsimp only
  have hx : (0 : ℝ) < (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith
  have hx1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hLpos : 0 < (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) := by
    have h : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
      simp only [Work.FTS.PhiStar.Gegenbauer.lam]
      have hm0 : (0 : ℝ) < (m : ℝ) := by
        have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
      nlinarith [hm0]
    exact mul_pos (pow_pos h 2) (Real.sqrt_pos.2 (by linarith))
  have hML := x3_le_ML m hm
  have hDpos : 0 < α ^ 2 * Cdec * CB * Kφ *
      (3 + 900 / cθ ^ 2 + 27000 / cθ ^ 4 + 9000 / cθ ^ 3) := by positivity
  -- the four estimates have the common shape: it suffices that the polynomial factor is
  -- bounded by `C (m+1)^3` with `C` one of the three constants below, since `M·L ≥ (m+1)^3`.
  have step : ∀ P C : ℝ, P ≤ C * ((m : ℝ) + 1) ^ 3 →
      C ≤ 3 + 900 / cθ ^ 2 + 27000 / cθ ^ 4 + 9000 / cθ ^ 3 →
      α ^ 2 * Cdec * CB * Kφ /
          ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) * P
        ≤ (α ^ 2 * Cdec * CB * Kφ * (3 + 900 / cθ ^ 2 + 27000 / cθ ^ 4 + 9000 / cθ ^ 3))
            * (((m : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹ := by
    intro P C hP hC
    rw [div_mul_eq_mul_div]
    rw [div_le_iff₀ hLpos]
    rw [rpow_three_half hx]
    rw [rpow_three_half hx] at hML
    have h3 : (0 : ℝ) ≤ ((m : ℝ) + 1) ^ 3 := by positivity
    calc α ^ 2 * Cdec * CB * Kφ * P
        ≤ α ^ 2 * Cdec * CB * Kφ * (C * ((m : ℝ) + 1) ^ 3) :=
          mul_le_mul_of_nonneg_left hP hApos.le
      _ = (α ^ 2 * Cdec * CB * Kφ * C) * ((m : ℝ) + 1) ^ 3 := by ring
      _ ≤ (α ^ 2 * Cdec * CB * Kφ *
            (3 + 900 / cθ ^ 2 + 27000 / cθ ^ 4 + 9000 / cθ ^ 3)) * ((m : ℝ) + 1) ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC hApos.le) h3
      _ ≤ (α ^ 2 * Cdec * CB * Kφ *
            (3 + 900 / cθ ^ 2 + 27000 / cθ ^ 4 + 9000 / cθ ^ 3)) *
            ((((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹ *
              ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hML hDpos.le
      _ = (α ^ 2 * Cdec * CB * Kφ *
            (3 + 900 / cθ ^ 2 + 27000 / cθ ^ 4 + 9000 / cθ ^ 3)) *
            (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹ *
              ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine step (3 * ((m : ℝ) + 1)) 3 ?_ ?_
    · have h13 : ((m : ℝ) + 1) ^ 1 ≤ ((m : ℝ) + 1) ^ 3 := pow_le_pow_right₀ hx1 (by norm_num)
      simpa [pow_one] using mul_le_mul_of_nonneg_left h13 (by norm_num : (0 : ℝ) ≤ 3)
    · have h1 : (0 : ℝ) ≤ 900 / cθ ^ 2 := by positivity
      have h2 : (0 : ℝ) ≤ 27000 / cθ ^ 4 := by positivity
      have h3 : (0 : ℝ) ≤ 9000 / cθ ^ 3 := by positivity
      linarith
  · refine step (900 * ((m : ℝ) + 1) ^ 2 / cθ ^ 2) (900 / cθ ^ 2) ?_ ?_
    · have h23 : ((m : ℝ) + 1) ^ 2 ≤ ((m : ℝ) + 1) ^ 3 := pow_le_pow_right₀ hx1 (by norm_num)
      have hc : (0 : ℝ) ≤ 900 / cθ ^ 2 := by positivity
      calc 900 * ((m : ℝ) + 1) ^ 2 / cθ ^ 2 = 900 / cθ ^ 2 * ((m : ℝ) + 1) ^ 2 := by ring
        _ ≤ 900 / cθ ^ 2 * ((m : ℝ) + 1) ^ 3 := mul_le_mul_of_nonneg_left h23 hc
    · have h1 : (0 : ℝ) ≤ 27000 / cθ ^ 4 := by positivity
      have h3 : (0 : ℝ) ≤ 9000 / cθ ^ 3 := by positivity
      have h4 : (0 : ℝ) ≤ 3 := by norm_num
      linarith
  · refine step (27000 * ((m : ℝ) + 1) ^ 3 / cθ ^ 4) (27000 / cθ ^ 4) ?_ ?_
    · have h : 27000 * ((m : ℝ) + 1) ^ 3 / cθ ^ 4 = 27000 / cθ ^ 4 * ((m : ℝ) + 1) ^ 3 := by ring
      exact le_of_eq h
    · have h2 : (0 : ℝ) ≤ 900 / cθ ^ 2 := by positivity
      have h3 : (0 : ℝ) ≤ 9000 / cθ ^ 3 := by positivity
      have h4 : (0 : ℝ) ≤ 3 := by norm_num
      linarith
  · refine step (9000 * ((m : ℝ) + 1) ^ 2 / cθ ^ 3) (9000 / cθ ^ 3) ?_ ?_
    · have h23 : ((m : ℝ) + 1) ^ 2 ≤ ((m : ℝ) + 1) ^ 3 := pow_le_pow_right₀ hx1 (by norm_num)
      have hc : (0 : ℝ) ≤ 9000 / cθ ^ 3 := by positivity
      calc 9000 * ((m : ℝ) + 1) ^ 2 / cθ ^ 3 = 9000 / cθ ^ 3 * ((m : ℝ) + 1) ^ 2 := by ring
        _ ≤ 9000 / cθ ^ 3 * ((m : ℝ) + 1) ^ 3 := mul_le_mul_of_nonneg_left h23 hc
    · have h1 : (0 : ℝ) ≤ 900 / cθ ^ 2 := by positivity
      have h2 : (0 : ℝ) ≤ 27000 / cθ ^ 4 := by positivity
      have h4 : (0 : ℝ) ≤ 3 := by norm_num
      linarith

end Work.FTS.PhiStar.Series.Deleg
