import Mathlib
import Submission.Work.BW.split_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Condition (E1) of the half split at `m = 0`, `e = e₀`:

  `(r+1) · 𝒟₀ < (𝒮/2) · (𝒯/2)`.

Writing `D = pD r d σ`, `I = pI r d`, `ξ = pxi r` and `L = log(2rd)`, the two sides are

  `(r+1) 𝒟₀ = (r+1) h (D₀+1)`,   `(𝒮/2)(𝒯/2) = 8 r d h ξ T`,

and the numerical core is

  `(r+1)(D₀+1) ≤ (r+1)(rD/(2L) + 1) ≤ rD (3(r+1)/8 + 3/2) < 61.6 r² d D ≤ 8 r d ξ T`,

where `D₀ ≤ rD/(2L)` (`pD0_le`), `1 ≤ D` (`pD_ge_one`), `L ≥ 4/3` (`log_2rd_ge`),
`ξ ≥ 0.7` (`pxi_ge`) and `T ≥ 11 r D` (`pT_ge`). -/
theorem split_E1_case0 {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 1 ≤ h) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) :
    ((r : ℝ) + 1) * calD r d h σ 0 < (calS r d h / 2) * (calT r d σ / 2) := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<2) hr)
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hh0 : (0:ℝ) < h := by exact_mod_cast hh
  have hr2 : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hDpos : 0 < pD r d σ := pD_pos hr hd σ hσ
  have hD1 : 1 ≤ pD r d σ := pD_ge_one hr hd σ hσ
  have hLpos : 0 < Real.log (2*r*d) := log_2rd_pos hr hd
  have hLge : (4:ℝ)/3 ≤ Real.log (2*r*d) := log_2rd_ge hr hd
  have hξpos : 0 < pxi r := pxi_pos hr
  have hξge : (0.7:ℝ) ≤ pxi r := pxi_ge hr
  have hTge : 11 * (r:ℝ) * pD r d σ ≤ (pT r d σ : ℝ) := pT_ge hr hd σ hσ
  have hD0le : (pD0 r d σ : ℝ) ≤ (r:ℝ) * pD r d σ / (2 * Real.log (2*r*d)) :=
    pD0_le hr hd σ hσ
  -- numerical core, after dividing by `h`
  have hmain : ((r:ℝ)+1) * ((pD0 r d σ : ℝ)+1)
      < 8 * (r:ℝ) * (d:ℝ) * pxi r * (pT r d σ : ℝ) := by
    have hinv : (1:ℝ)/(2*Real.log (2*r*d)) ≤ 3/8 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hLge]
    have hA : (r:ℝ) * pD r d σ / (2*Real.log (2*r*d)) ≤ (r:ℝ)*pD r d σ*(3/8) := by
      rw [div_eq_mul_inv]
      rw [one_div] at hinv
      exact mul_le_mul_of_nonneg_left hinv (le_of_lt (mul_pos hr0 hDpos))
    have hB : ((r:ℝ)+1) ≤ 3/2 * ((r:ℝ)*pD r d σ) := by
      nlinarith [hr2, hD1, hr0, hDpos.le]
    have hC : 61.6 * (r:ℝ)^2 * (d:ℝ) * pD r d σ
        ≤ 8 * (r:ℝ) * (d:ℝ) * pxi r * (pT r d σ : ℝ) := by
      have ha : 8 * (r:ℝ) * (d:ℝ) * 0.7 * (11 * (r:ℝ) * pD r d σ)
          ≤ 8 * (r:ℝ) * (d:ℝ) * 0.7 * (pT r d σ : ℝ) :=
        mul_le_mul_of_nonneg_left hTge (by positivity)
      have hb : 8 * (r:ℝ) * (d:ℝ) * 0.7 * (pT r d σ : ℝ)
          ≤ 8 * (r:ℝ) * (d:ℝ) * pxi r * (pT r d σ : ℝ) := by
        have := mul_le_mul_of_nonneg_right hξge
          (by positivity : (0:ℝ) ≤ 8 * (r:ℝ) * (d:ℝ) * (pT r d σ : ℝ))
        nlinarith [this]
      have h2 : 61.6 * (r:ℝ)^2 * (d:ℝ) * pD r d σ
          = 8 * (r:ℝ) * (d:ℝ) * 0.7 * (11 * (r:ℝ) * pD r d σ) := by ring
      linarith [ha, hb, h2]
    have hD' : 3*((r:ℝ)+1)/8 + 3/2 < 61.6 * (r:ℝ) * (d:ℝ) := by nlinarith [hr2, hd1]
    have hpos : 0 < (r:ℝ) * pD r d σ := mul_pos hr0 hDpos
    have s1 : ((r:ℝ)+1) * ((pD0 r d σ : ℝ)+1)
        ≤ ((r:ℝ)+1) * ((r:ℝ)*pD r d σ/(2*Real.log (2*r*d)) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have s2 : ((r:ℝ)+1) * ((r:ℝ)*pD r d σ/(2*Real.log (2*r*d)) + 1)
        ≤ ((r:ℝ)*pD r d σ) * (3*((r:ℝ)+1)/8 + 3/2) := by
      have h1 : ((r:ℝ)+1) * ((r:ℝ)*pD r d σ/(2*Real.log (2*r*d)) + 1)
          ≤ ((r:ℝ)+1) * ((r:ℝ)*pD r d σ*(3/8) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h2 : ((r:ℝ)+1) * ((r:ℝ)*pD r d σ*(3/8) + 1)
          = ((r:ℝ)*pD r d σ) * (3*((r:ℝ)+1)/8) + ((r:ℝ)+1) := by ring
      have h3 : ((r:ℝ)*pD r d σ) * (3*((r:ℝ)+1)/8) + ((r:ℝ)+1)
          ≤ ((r:ℝ)*pD r d σ) * (3*((r:ℝ)+1)/8) + 3/2*((r:ℝ)*pD r d σ) := by
        linarith [hB]
      have h4 : ((r:ℝ)*pD r d σ) * (3*((r:ℝ)+1)/8) + 3/2*((r:ℝ)*pD r d σ)
          = ((r:ℝ)*pD r d σ) * (3*((r:ℝ)+1)/8 + 3/2) := by ring
      linarith [h1, h2, h3, h4]
    have s3 : ((r:ℝ)*pD r d σ) * (3*((r:ℝ)+1)/8 + 3/2)
        < 8 * (r:ℝ) * (d:ℝ) * pxi r * (pT r d σ : ℝ) := by
      have h1 : ((r:ℝ)*pD r d σ) * (3*((r:ℝ)+1)/8 + 3/2)
          < ((r:ℝ)*pD r d σ) * (61.6 * (r:ℝ) * (d:ℝ)) :=
        mul_lt_mul_of_pos_left hD' hpos
      have h2 : ((r:ℝ)*pD r d σ) * (61.6 * (r:ℝ) * (d:ℝ))
          = 61.6 * (r:ℝ)^2 * (d:ℝ) * pD r d σ := by ring
      linarith [h1, h2, hC]
    linarith [s1, s2, s3]
  rw [calD_zero]
  have hR : (calS r d h / 2) * (calT r d σ / 2)
      = 8 * (r:ℝ) * (d:ℝ) * (h:ℝ) * pxi r * (pT r d σ : ℝ) := by
    rw [calS_div_two r d h, calT_div_two]
    rw [show (pxi r) ^ (-((r * pI r d : ℕ) : ℤ)) = ((pxi r) ^ (r * pI r d))⁻¹ by
          rw [zpow_neg, zpow_natCast]]
    have hξ : (pxi r) ^ (r * pI r d) ≠ 0 := pow_ne_zero _ (ne_of_gt (pxi_pos' r))
    have hpS : (pS r d h : ℝ) = 16 * (r:ℝ) * (d:ℝ) * (h:ℝ) := by
      simp only [pS]; push_cast; ring
    rw [hpS]
    field_simp
    ring
  rw [hR]
  have hfin : (h:ℝ) * (((r:ℝ)+1) * ((pD0 r d σ : ℝ)+1))
      < (h:ℝ) * (8 * (r:ℝ) * (d:ℝ) * pxi r * (pT r d σ : ℝ)) :=
    mul_lt_mul_of_pos_left hmain hh0
  nlinarith [hfin]

end Work.BW
