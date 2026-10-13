import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Cyl.DecayAux

theorem rho_mul_rpow_weight_le {p lam b ρ : ℝ} (hp : 0 < p) (hlam : 0 < lam) (hb : 0 < b)
    (hρ : 0 ≤ ρ) (hpl : 3 ≤ p * lam) :
    ρ * (1 + ρ ^ p / b) ^ (-lam) ≤ 2 * max 1 (b ^ lam) / (1 + ρ) := by
  -- The hypothesis `p > 0` is not needed for the estimate; keep the reference for lint.
  have hp_pos : 0 < p := hp
  -- Write `A := max 1 (b ^ lam)`; then `A ≥ 1` and `A ≥ b ^ lam`.
  set A : ℝ := max 1 (b ^ lam) with hAdef
  have hA1 : 1 ≤ A := le_max_left 1 (b ^ lam)
  have hbA : b ^ lam ≤ A := le_max_right 1 (b ^ lam)
  have hApos : 0 < A := lt_of_lt_of_le one_pos hA1
  have hrp : 0 ≤ ρ ^ p := Real.rpow_nonneg hρ p
  have hb1 : 1 ≤ 1 + ρ ^ p / b := by
    have : 0 ≤ ρ ^ p / b := div_nonneg hrp hb.le
    linarith
  have hden : 0 < 1 + ρ := by linarith
  rcases le_or_gt ρ 1 with hρle | hρgt
  · -- Case `ρ ≤ 1`: the weight factor is at most `1`, and the right-hand side is at least `1`.
    have hfac : (1 + ρ ^ p / b) ^ (-lam) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hb1 (by linarith)
    have hfac0 : 0 ≤ (1 + ρ ^ p / b) ^ (-lam) := Real.rpow_nonneg (by linarith) _
    have h1 : ρ * (1 + ρ ^ p / b) ^ (-lam) ≤ 1 := by
      have h := mul_le_mul hρle hfac hfac0 (by norm_num : (0 : ℝ) ≤ 1)
      linarith [h]
    have h2 : (1 : ℝ) ≤ 2 * A / (1 + ρ) := by
      rw [one_le_div hden]
      linarith
    linarith
  · rcases le_or_gt (ρ ^ p / b) 1 with hxle | hxgt
    · -- Case `1 < ρ` and `ρ ^ p ≤ b`: then `b ^ lam ≥ ρ ^ (p * lam) ≥ ρ ^ 3` and
      -- the weight factor is at most `1`, so it suffices that `ρ ≤ 2 A / (1 + ρ)`.
      have hfac : (1 + ρ ^ p / b) ^ (-lam) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hb1 (by linarith)
      have hL : ρ * (1 + ρ ^ p / b) ^ (-lam) ≤ ρ := by
        simpa using mul_le_mul_of_nonneg_left hfac hρ
      have hub : ρ ^ p ≤ b := (div_le_one hb).mp hxle
      have hrp3 : ρ ^ 3 ≤ ρ ^ (p * lam) := by
        rw [← Real.rpow_natCast ρ 3]
        exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hρgt) hpl
      have hmid : ρ ^ (p * lam) ≤ b ^ lam := by
        calc ρ ^ (p * lam) = (ρ ^ p) ^ lam := Real.rpow_mul hρ p lam
          _ ≤ b ^ lam := Real.rpow_le_rpow hrp hub hlam.le
      have hA3 : ρ ^ 3 ≤ A := le_trans (le_trans hrp3 hmid) hbA
      have h2 : ρ ≤ 2 * A / (1 + ρ) := by
        rw [le_div_iff₀ hden]
        have hkey : 1 + ρ ≤ 2 * ρ ^ 2 := by
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * ρ + 1)
            (by linarith : (0 : ℝ) ≤ ρ - 1)]
        have hmul := mul_le_mul_of_nonneg_left hkey hρ
        nlinarith [hmul, hA3]
      linarith
    · -- Case `1 < ρ` and `ρ ^ p > b`: use `(1 + x) ^ (-lam) ≤ x ^ (-lam)` and
      -- `x ^ (-lam) = b ^ lam * ρ ^ (-(p * lam)) ≤ b ^ lam * ρ ^ (-2)` since `p * lam ≥ 3`.
      have hupos : 0 < ρ ^ p / b := lt_trans zero_lt_one hxgt
      have hρpos : 0 < ρ := lt_trans zero_lt_one hρgt
      have hfac : (1 + ρ ^ p / b) ^ (-lam) ≤ (ρ ^ p / b) ^ (-lam) :=
        Real.rpow_le_rpow_of_nonpos hupos (by linarith) (by linarith)
      have hL : ρ * (1 + ρ ^ p / b) ^ (-lam) ≤ ρ * (ρ ^ p / b) ^ (-lam) :=
        mul_le_mul_of_nonneg_left hfac hρ
      have hu_eq : (ρ ^ p / b) ^ (-lam) = b ^ lam * ρ ^ (-(p * lam)) := by
        rw [Real.div_rpow hrp hb.le (-lam), Real.rpow_neg hrp lam, Real.rpow_neg hb.le lam,
          ← Real.rpow_mul hρ p lam, div_inv_eq_mul, ← Real.rpow_neg hρ (p * lam)]
        ring
      have hmain : ρ * (ρ ^ p / b) ^ (-lam) ≤ b ^ lam * ρ ^ (-2 : ℝ) := by
        calc ρ * (ρ ^ p / b) ^ (-lam) = ρ * (b ^ lam * ρ ^ (-(p * lam))) := by rw [hu_eq]
          _ = b ^ lam * (ρ * ρ ^ (-(p * lam))) := by ring
          _ = b ^ lam * (ρ ^ (1 : ℝ) * ρ ^ (-(p * lam))) := by rw [Real.rpow_one]
          _ = b ^ lam * ρ ^ (1 + -(p * lam)) := by
              rw [Real.rpow_add hρpos (1 : ℝ) (-(p * lam))]
          _ ≤ b ^ lam * ρ ^ (-2 : ℝ) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le (le_of_lt hρgt) (by linarith))
                (Real.rpow_nonneg hb.le lam)
      have hA2 : b ^ lam * ρ ^ (-2 : ℝ) ≤ 2 * A / (1 + ρ) := by
        have hkey : 1 + ρ ≤ 2 * ρ ^ 2 := by
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * ρ + 1)
            (by linarith : (0 : ℝ) ≤ ρ - 1)]
        rw [Real.rpow_neg (le_of_lt hρpos) (2 : ℝ), Real.rpow_two, inv_eq_one_div, mul_one_div]
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < ρ ^ 2) hden]
        calc b ^ lam * (1 + ρ) ≤ A * (1 + ρ) := mul_le_mul_of_nonneg_right hbA (by linarith)
          _ ≤ A * (2 * ρ ^ 2) := mul_le_mul_of_nonneg_left hkey (le_of_lt hApos)
          _ = 2 * A * ρ ^ 2 := by ring
      linarith

end Work.FTS.BSIdent.Cyl.DecayAux
