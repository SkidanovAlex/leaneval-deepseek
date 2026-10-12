import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBogFS.rpow_mul_log_inv_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- Base-power composition: `(t ^ a) ^ b = t` whenever `t > 0` and `a * b = 1`.
Used below to convert the bound `X ≤ (t) ^ (1/p)` into a bound on `X ^ p`. -/
lemma rpow_comp_one {t a b : ℝ} (ht : 0 < t) (hab : a * b = 1) : (t ^ a) ^ b = t := by
  rw [← Real.rpow_mul ht.le, hab, Real.rpow_one]

/-- **Absorption of the two negative powers.**  For `K ≥ 1`, `Vs ≥ 1` and `C ≥ 0` the
function `X ↦ K·Vs²·(X^{-3}·(C + log(1/X)) + X^{-17/4})` is dominated by
`2000·X^{-43/10}` on a right neighbourhood of `0`.  Since `43/10 > 3` and `43/10 > 17/4`
the power `X^{-43/10}` wins against both singularities and against the logarithm
(the latter through `Work.BoseBogFS.rpow_mul_log_inv_le`); the thresholds are the
explicit quantities `(T/2)^{20}`, `(T/8)^{10/3}` and `(T/(8(C+1)))^{10/13}` with
`T = 2000/(K·Vs²)`. -/
theorem absorb_arith {K Vs C : ℝ} (hK : 1 ≤ K) (hVs : 1 ≤ Vs) (hC : 0 ≤ C) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, 0 < X → X ≤ X₀ →
      K * Vs ^ 2 * (X ^ (-(3 : ℝ)) * (C + Real.log (1 / X)) + X ^ (-(17 / 4 : ℝ)))
        ≤ 2000 * X ^ (-(43 / 10 : ℝ)) := by
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  have hVssq : (1 : ℝ) ≤ Vs ^ 2 := by nlinarith
  have hKVs_pos : 0 < K * Vs ^ 2 := mul_pos hKpos (lt_of_lt_of_le one_pos hVssq)
  have hC1pos : 0 < C + 1 := by linarith
  set T : ℝ := 2000 / (K * Vs ^ 2) with hTdef
  have hTpos : 0 < T := by
    rw [hTdef]; exact div_pos (by norm_num) hKVs_pos
  have hTKVs : K * Vs ^ 2 * T = 2000 := by
    rw [hTdef]; field_simp
  refine ⟨min (min 1 ((T / 2) ^ (20 : ℝ)))
      (min ((T / 8) ^ (10 / 3 : ℝ)) ((T / (8 * (C + 1))) ^ (10 / 13 : ℝ))), ?_, ?_⟩
  · refine lt_min (lt_min one_pos ?_) (lt_min ?_ ?_)
    · exact Real.rpow_pos_of_pos (by linarith) _
    · exact Real.rpow_pos_of_pos (by linarith) _
    · exact Real.rpow_pos_of_pos (div_pos hTpos (by nlinarith)) _
  · intro X hXpos hXle
    have hXle1 : X ≤ 1 := le_trans hXle (le_trans (min_le_left _ _) (min_le_left _ _))
    have hXA : X ≤ (T / 2) ^ (20 : ℝ) :=
      le_trans hXle (le_trans (min_le_left _ _) (min_le_right _ _))
    have hXB : X ≤ (T / 8) ^ (10 / 3 : ℝ) :=
      le_trans hXle (le_trans (min_le_right _ _) (min_le_left _ _))
    have hXD : X ≤ (T / (8 * (C + 1))) ^ (10 / 13 : ℝ) :=
      le_trans hXle (le_trans (min_le_right _ _) (min_le_right _ _))
    -- the three power bounds at `X`
    have h20 : X ^ ((1 : ℝ) / 20) ≤ T / 2 := by
      have h := Real.rpow_le_rpow hXpos.le hXA (by norm_num : (0 : ℝ) ≤ 1 / 20)
      rwa [rpow_comp_one (by linarith : (0 : ℝ) < T / 2)
        (by norm_num : (20 : ℝ) * (1 / 20) = 1)] at h
    have h310 : X ^ ((3 : ℝ) / 10) ≤ T / 8 := by
      have h := Real.rpow_le_rpow hXpos.le hXB (by norm_num : (0 : ℝ) ≤ 3 / 10)
      rwa [rpow_comp_one (by linarith : (0 : ℝ) < T / 8)
        (by norm_num : (10 / 3 : ℝ) * (3 / 10) = 1)] at h
    have h1310 : X ^ ((13 : ℝ) / 10) ≤ T / (8 * (C + 1)) := by
      have h := Real.rpow_le_rpow hXpos.le hXD (by norm_num : (0 : ℝ) ≤ 13 / 10)
      rwa [rpow_comp_one (div_pos hTpos (by nlinarith))
        (by norm_num : (10 / 13 : ℝ) * (13 / 10) = 1)] at h
    -- the logarithm is beaten by the power `3/10`
    have hlog : X ^ ((13 : ℝ) / 10) * Real.log (1 / X) ≤ 2 * X ^ ((3 : ℝ) / 10) := by
      have h := rpow_mul_log_inv_le hXpos hXle1 (show (3 : ℝ) / 10 < 13 / 10 by norm_num)
      have hc : (2 : ℝ) / (13 / 10 - 3 / 10) = 2 := by norm_num
      rw [hc] at h
      exact h
    -- `C · X^{13/10} ≤ T/8`
    have hC13 : C * X ^ ((13 : ℝ) / 10) ≤ T / 8 := by
      have h1 : C * X ^ ((13 : ℝ) / 10) ≤ C * (T / (8 * (C + 1))) :=
        mul_le_mul_of_nonneg_left h1310 hC
      have h2 : C * (T / (8 * (C + 1))) ≤ T / 8 := by
        have h3 : C * (T / (8 * (C + 1))) ≤ (C + 1) * (T / (8 * (C + 1))) :=
          mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hTpos.le (by nlinarith))
        have h4 : (C + 1) * (T / (8 * (C + 1))) = T / 8 := by
          field_simp
        linarith
      linarith
    -- collecting the two pieces of the logarithmic term
    have hA : X ^ ((13 : ℝ) / 10) * (C + Real.log (1 / X)) ≤ T / 2 := by
      have hsplit : X ^ ((13 : ℝ) / 10) * (C + Real.log (1 / X))
          = C * X ^ ((13 : ℝ) / 10) + X ^ ((13 : ℝ) / 10) * Real.log (1 / X) := by ring
      rw [hsplit]
      linarith
    -- the rescaled inequality
    have hsum : X ^ ((13 : ℝ) / 10) * (C + Real.log (1 / X)) + X ^ ((1 : ℝ) / 20) ≤ T := by
      linarith
    have hmain : K * Vs ^ 2 *
        (X ^ ((13 : ℝ) / 10) * (C + Real.log (1 / X)) + X ^ ((1 : ℝ) / 20)) ≤ 2000 := by
      have h := mul_le_mul_of_nonneg_left hsum hKVs_pos.le
      rw [hTKVs] at h
      exact h
    -- exponent bookkeeping: factor `X^{-43/10}` out of both singular terms
    have hfac1 : X ^ (-(3 : ℝ)) = X ^ (-(43 / 10 : ℝ)) * X ^ ((13 : ℝ) / 10) := by
      rw [← Real.rpow_add hXpos]
      congr 1
      norm_num
    have hfac2 : X ^ (-(17 / 4 : ℝ)) = X ^ (-(43 / 10 : ℝ)) * X ^ ((1 : ℝ) / 20) := by
      rw [← Real.rpow_add hXpos]
      congr 1
      norm_num
    calc K * Vs ^ 2 * (X ^ (-(3 : ℝ)) * (C + Real.log (1 / X)) + X ^ (-(17 / 4 : ℝ)))
        = K * Vs ^ 2 * (X ^ (-(43 / 10 : ℝ)) *
            (X ^ ((13 : ℝ) / 10) * (C + Real.log (1 / X)) + X ^ ((1 : ℝ) / 20))) := by
          rw [hfac1, hfac2]; ring
      _ = X ^ (-(43 / 10 : ℝ)) * (K * Vs ^ 2 *
            (X ^ ((13 : ℝ) / 10) * (C + Real.log (1 / X)) + X ^ ((1 : ℝ) / 20))) := by
          ring
      _ ≤ X ^ (-(43 / 10 : ℝ)) * 2000 :=
          mul_le_mul_of_nonneg_left hmain (Real.rpow_pos_of_pos hXpos _).le
      _ = 2000 * X ^ (-(43 / 10 : ℝ)) := by ring

end Work.BoseBogFS
