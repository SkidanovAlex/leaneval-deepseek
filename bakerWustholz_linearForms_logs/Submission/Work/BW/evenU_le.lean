import Mathlib
import Submission.Work.BW.even_step_defs
import Submission.Work.BW.num_T
import Submission.Work.BW.num_xi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Numeric bound on the (16)-exponent `evU` of the even step (BW §19–20, pp. 57–58) at descent level `J`, in units of `S·D`.

Route: `evU r d h σ J = d·h·(ξ·(ξ^{rJ}·T)) + 1.055·S·D + 1.008·((R + 4·ξ^{-rJ}·S)/2^{J+1})·D + (0.044(J+1)/log(2rd))·S·D` with `S = pS r d h`, `D = pD r d σ`, `T = pT r d σ`, `ξ = pxi r`, `R = evR r J S = 7.2·evSP`, `evSP = ⌊2ξ^{-rJ}S⌋`.

* `d·h·ξ·ξ^{rJ}T ≤ 0.735·S·D`: `num_T` gives `d·h·T ≤ 0.735 S D`, and `ξ^{rJ+1} ≤ 1`.
* `R + 4ξ^{-rJ}S = 7.2·evSP + 4ξ^{-rJ}S ≤ 14.4ξ^{-rJ}S + 4ξ^{-rJ}S = 18.4ξ^{-rJ}S` since `evSP ≤ 2ξ^{-rJ}S`; dividing by `2^{J+1}` gives `9.2·ξ^{-rJ}/2^J = 9.2·(2ξ^r)^{-J} ≤ 9.2` (using `num_xi`'s `1.07 ≤ 2ξ^r`), so the term is `≤ 1.008·9.2 = 9.2736` in `S·D` units.
* `0.044(J+1)/log(2rd) ≤ 0.044·50 = 2.2` since `hJ : J+1 ≤ pI r d = ⌊50 log(2rd)⌋₊ ≤ 50 log(2rd)`.

Total `0.735 + 1.055 + 9.2736 + 2.2 = 13.2636 ≤ 13.27`. -/
theorem evenU_le {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 19 ≤ h) {σ : Fin r → ℝ}
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) (J : ℕ) (hJ : J + 1 ≤ pI r d) :
    evU r d h σ J ≤ 13.27 * (pS r d h : ℝ) * pD r d σ := by
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
  have hSpos : (0 : ℝ) < (pS r d h : ℝ) := by rw [pS]; push_cast; positivity
  have hSnn : (0 : ℝ) ≤ (pS r d h : ℝ) := hSpos.le
  have hDpos : (0 : ℝ) < pD r d σ := pD_pos hr hd σ hσ
  have hDnn : (0 : ℝ) ≤ pD r d σ := hDpos.le
  have hTnn : (0 : ℝ) ≤ (pT r d σ : ℝ) := by positivity
  have hLpos : (0 : ℝ) < Real.log (2 * r * d) := log_2rd_pos hr hd
  have hxipos : 0 < pxi r := by
    rw [pxi]
    have h : (0.536 : ℝ) / (r : ℝ) < 1 := by rw [div_lt_one hr0]; linarith
    linarith
  have hxile1 : pxi r ≤ 1 := by
    rw [pxi]
    have h : (0 : ℝ) ≤ (0.536 : ℝ) / (r : ℝ) := by positivity
    linarith
  have hξ : pxi r * pxi r ^ (r * J) ≤ 1 := by
    have h1 : pxi r ^ (r * J) ≤ 1 := pow_le_one₀ hxipos.le hxile1
    calc pxi r * pxi r ^ (r * J) ≤ 1 * 1 :=
          mul_le_mul hxile1 h1 (pow_nonneg hxipos.le _) (by norm_num)
      _ = 1 := by ring
  -- Term 1: `d·h·(ξ·(ξ^{rJ}·T)) ≤ 0.735·S·D`
  have hT1 : (d : ℝ) * (h : ℝ) * (pxi r * (pxi r ^ (r * J) * (pT r d σ : ℝ)))
      ≤ 0.735 * (pS r d h : ℝ) * pD r d σ := by
    have hstep : pxi r * (pxi r ^ (r * J) * (pT r d σ : ℝ)) ≤ (pT r d σ : ℝ) := by
      calc pxi r * (pxi r ^ (r * J) * (pT r d σ : ℝ))
          = (pxi r * pxi r ^ (r * J)) * (pT r d σ : ℝ) := by ring
        _ ≤ 1 * (pT r d σ : ℝ) := mul_le_mul_of_nonneg_right hξ hTnn
        _ = (pT r d σ : ℝ) := one_mul _
    have hdh : (0 : ℝ) ≤ (d : ℝ) * (h : ℝ) := by positivity
    calc (d : ℝ) * (h : ℝ) * (pxi r * (pxi r ^ (r * J) * (pT r d σ : ℝ)))
        ≤ (d : ℝ) * (h : ℝ) * (pT r d σ : ℝ) := mul_le_mul_of_nonneg_left hstep hdh
      _ ≤ 0.735 * (pS r d h : ℝ) * pD r d σ := (num_T hr hd hh σ hσ).2.2.1
  -- `ξ^{-rJ} ≤ 2^J` (from `ξ^{-r} ≤ 1.87 ≤ 2`)
  have hβnn : (0 : ℝ) ≤ pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ) :=
    mul_nonneg (zpow_nonneg hxipos.le _) hSnn
  have hpow : pxi r ^ (-((r * J : ℕ) : ℤ)) ≤ (2 : ℝ) ^ J := by
    have hxir : pxi r ^ (-(r : ℤ)) ≤ 1.87 := (num_xi hr).1
    have hxir_nn : (0 : ℝ) ≤ pxi r ^ (-(r : ℤ)) := zpow_nonneg hxipos.le _
    have key : pxi r ^ (-((r * J : ℕ) : ℤ)) = (pxi r ^ (-(r : ℤ))) ^ J := by
      rw [show -((r * J : ℕ) : ℤ) = -(r : ℤ) * (J : ℤ) by push_cast; ring]
      rw [zpow_mul, zpow_natCast]
    rw [key]
    calc (pxi r ^ (-(r : ℤ))) ^ J ≤ 1.87 ^ J := pow_le_pow_left₀ hxir_nn hxir J
      _ ≤ (2 : ℝ) ^ J := pow_le_pow_left₀ (by norm_num) (by norm_num) J
  have hbeta_div : pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ) / (2 : ℝ) ^ (J + 1)
      ≤ (pS r d h : ℝ) / 2 := by
    have hmul : pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ)
        ≤ (2 : ℝ) ^ J * (pS r d h : ℝ) :=
      mul_le_mul_of_nonneg_right hpow hSnn
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (J + 1) := by positivity
    calc pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ) / (2 : ℝ) ^ (J + 1)
        ≤ ((2 : ℝ) ^ J * (pS r d h : ℝ)) / (2 : ℝ) ^ (J + 1) := by
          rw [div_le_div_iff_of_pos_right h2pos]; exact hmul
      _ = (pS r d h : ℝ) / 2 := by
          rw [pow_succ]
          rw [mul_div_mul_left _ _ (by positivity : (2 : ℝ) ^ J ≠ 0)]
  -- Term 3: `1.008·((R + 4ξ^{-rJ}S)/2^{J+1})·D ≤ 9.2736·S·D`
  have hT3 : 1.008 * ((evR r J (pS r d h : ℝ)
        + 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))) / (2 : ℝ) ^ (J + 1))
        * pD r d σ ≤ 9.2736 * (pS r d h : ℝ) * pD r d σ := by
    have he_le : (evSP r J (pS r d h : ℝ) : ℝ)
        ≤ 2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ)) := by
      rw [evSP]
      exact Nat.floor_le (mul_nonneg (by norm_num) hβnn)
    have hnum : evR r J (pS r d h : ℝ)
        + 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))
        ≤ 18.4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ)) := by
      simp only [evR]
      linarith [he_le]
    have hratio : (evR r J (pS r d h : ℝ)
        + 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))) / (2 : ℝ) ^ (J + 1)
        ≤ 9.2 * (pS r d h : ℝ) := by
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ (J + 1) := by positivity
      calc (evR r J (pS r d h : ℝ)
            + 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))) / (2 : ℝ) ^ (J + 1)
          ≤ (18.4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))) / (2 : ℝ) ^ (J + 1) := by
            rw [div_le_div_iff_of_pos_right h2pos]; exact hnum
        _ = 18.4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ) / (2 : ℝ) ^ (J + 1)) := by
            ring
        _ ≤ 18.4 * ((pS r d h : ℝ) / 2) := mul_le_mul_of_nonneg_left hbeta_div (by norm_num)
        _ = 9.2 * (pS r d h : ℝ) := by ring
    calc 1.008 * ((evR r J (pS r d h : ℝ)
            + 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))) / (2 : ℝ) ^ (J + 1))
            * pD r d σ
        ≤ 1.008 * (9.2 * (pS r d h : ℝ)) * pD r d σ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio (by norm_num)) hDnn
      _ = 9.2736 * (pS r d h : ℝ) * pD r d σ := by ring
  -- Term 4: `(0.044(J+1)/log(2rd))·S·D ≤ 2.2·S·D`
  have hJle : ((J + 1 : ℕ) : ℝ) ≤ 50 * Real.log (2 * r * d) := by
    have h1 : (J + 1 : ℕ) ≤ ⌊50 * Real.log (2 * r * d)⌋₊ := by simpa only [pI] using hJ
    have h2 : ((J + 1 : ℕ) : ℝ) ≤ (⌊50 * Real.log (2 * r * d)⌋₊ : ℝ) := by exact_mod_cast h1
    have h3 : (⌊50 * Real.log (2 * r * d)⌋₊ : ℝ) ≤ 50 * Real.log (2 * r * d) :=
      Nat.floor_le (by linarith [hLpos])
    linarith
  have hcL : ((J + 1 : ℕ) : ℝ) / Real.log (2 * r * d) ≤ 50 := by
    rw [div_le_iff₀ hLpos]; exact hJle
  have hT4 : 0.044 * ((J + 1 : ℕ) : ℝ) / Real.log (2 * r * d) * (pS r d h : ℝ) * pD r d σ
      ≤ 2.2 * (pS r d h : ℝ) * pD r d σ := by
    calc 0.044 * ((J + 1 : ℕ) : ℝ) / Real.log (2 * r * d) * (pS r d h : ℝ) * pD r d σ
        = 0.044 * (((J + 1 : ℕ) : ℝ) / Real.log (2 * r * d))
            * ((pS r d h : ℝ) * pD r d σ) := by ring
      _ ≤ 0.044 * 50 * ((pS r d h : ℝ) * pD r d σ) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hSnn hDnn)
          exact mul_le_mul_of_nonneg_left hcL (by norm_num)
      _ = 2.2 * (pS r d h : ℝ) * pD r d σ := by ring
  -- Sum the four term bounds.
  have hXD : (0 : ℝ) ≤ (pS r d h : ℝ) * pD r d σ := mul_nonneg hSnn hDnn
  have hcoef : (0.735 + 1.055 + 9.2736 + 2.2) * ((pS r d h : ℝ) * pD r d σ)
      ≤ 13.27 * ((pS r d h : ℝ) * pD r d σ) :=
    mul_le_mul_of_nonneg_right (by norm_num) hXD
  simp only [evU]
  linarith [hT1, hT3, hT4, hcoef]

end Work.BW
