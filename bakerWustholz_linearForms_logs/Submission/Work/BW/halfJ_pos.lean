import Mathlib
import Submission.Work.BW.num19_half
import Submission.Work.BW.num_xi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

private lemma pxi_pos' (r : ℕ) (hr : 2 ≤ r) : 0 < pxi r := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  simp only [pxi]
  rw [sub_pos, div_lt_one hr0]
  linarith

private lemma pxi_le_one' (r : ℕ) (hr : 2 ≤ r) : pxi r ≤ 1 := by
  simp only [pxi]
  have : (0 : ℝ) ≤ 0.536 / (r : ℝ) := by positivity
  linarith

/-- BW §19 outer-circle (𝒥) numerics, *positive/coefficient* half of `half_num_J`: under
`half_num_J`'s hypotheses the bracket `2^r( d·h·Ξ^{J+1}T₀ + 1.087S₀D + 1.008((7.2X/2^r + 2Ξ^{-J}S₀)/2^J)D + (0.044J/log 2rd)S₀D )`
is at most `2^r S₀ D (12.43 ξ^{r-1} − 0.105)`. Route: bound the first term by `0.735ξ^{r-1+rJ}S₀D`
(from `dhT₀ ≤ 0.735S₀D` and `ξ^{r+rJ} ≤ ξ^{r-1+rJ}`), the third by `5.646(2Ξ)^{-J}S₀D` (from
`X ≤ 2^{r-1}Ξ^{-J}S₀`), then apply the first conjunct of `num19_half` with `q = 0`. -/
theorem halfJ_pos {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (J : ℕ)
    (hJ : (J:ℝ) ≤ 50 * Real.log (2*(r:ℝ)*(d:ℝ)))
    {ξ Ξ S₀ Dm T₀ hh : ℝ} {X : ℕ}
    (hξ : ξ = pxi r) (hΞ : Ξ = ξ ^ r)
    (hS608 : 608 ≤ S₀) (hDpos : 0 < Dm) (hT0nn : 0 ≤ T₀) (hh19 : 19 ≤ hh)
    (hDlow : 2 * (r:ℝ)^r * 32^(r+1) * (d:ℝ) * Real.log (2*(r:ℝ)*(d:ℝ)) ≤ Dm)
    (hT3 : (d:ℝ) * hh * T₀ ≤ 0.735 * S₀ * Dm)
    (hXle : (X:ℝ) ≤ 2^(r-1) * (Ξ⁻¹)^J * S₀) :
    2^r * ((d:ℝ) * hh * (Ξ^(J+1) * T₀) + 1.087 * S₀ * Dm +
        1.008 * ((7.2 * (X:ℝ) / 2^r + 2 * (Ξ⁻¹)^J * S₀) / 2^J) * Dm +
        0.044 * J / Real.log (2*(r:ℝ)*(d:ℝ)) * S₀ * Dm)
      ≤ 2^r * S₀ * Dm * (12.43 * ξ^(r-1) - 0.105) := by
  have hr1 : 1 ≤ r := by omega
  have hpxi_pos : 0 < pxi r := pxi_pos' r hr
  have hxi_pos : 0 < ξ := by rw [hξ]; exact hpxi_pos
  have hxi0 : 0 ≤ ξ := le_of_lt hxi_pos
  have hxi1 : ξ ≤ 1 := by rw [hξ]; exact pxi_le_one' r hr
  have hΞpos : 0 < Ξ := by rw [hΞ]; exact pow_pos hxi_pos r
  have hS0 : 0 ≤ S₀ := by linarith
  have hD0 : 0 ≤ Dm := le_of_lt hDpos
  have hLpos : 0 < Real.log (2*(r:ℝ)*(d:ℝ)) := by
    have hrR : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    have hrd : (2:ℝ) ≤ (r:ℝ)*(d:ℝ) := by
      calc (2:ℝ) = 2*1 := by norm_num
        _ ≤ (r:ℝ)*(d:ℝ) := mul_le_mul hrR hdR (by norm_num) (by linarith)
    exact Real.log_pos (by linarith)
  -- clearing `2^r`
  have h2p : (2:ℝ)^(r-1) * 2 = 2^r := by
    conv_rhs => rw [← Nat.sub_add_cancel hr1]
    rw [pow_succ]
  -- ---------- term 1 ----------
  have hA1 : (d:ℝ) * hh * (Ξ^(J+1) * T₀) ≤ 0.735 * ξ^(r-1+r*J) * S₀ * Dm := by
    have hexp : Ξ^(J+1) ≤ ξ^(r-1+r*J) := by
      have hle : r - 1 + r*J ≤ r*(J+1) := by
        rw [Nat.mul_succ]; omega
      rw [hΞ, ← pow_mul]
      exact pow_le_pow_of_le_one hxi0 hxi1 hle
    have hmul := mul_le_mul hT3 hexp (pow_nonneg (le_of_lt hΞpos) (J+1))
      (mul_nonneg (mul_nonneg (by norm_num) hS0) hD0)
    have e1 : (d:ℝ) * hh * (Ξ^(J+1) * T₀) = ((d:ℝ)*hh*T₀) * Ξ^(J+1) := by ring
    have e2 : 0.735 * ξ^(r-1+r*J) * S₀ * Dm = (0.735 * S₀ * Dm) * ξ^(r-1+r*J) := by ring
    rw [e1, e2]; exact hmul
  -- ---------- term 3 ----------
  have hA3 : 1.008 * ((7.2 * (X:ℝ) / 2^r + 2 * (Ξ⁻¹)^J * S₀) / 2^J) * Dm
      ≤ 5.646 * (2*ξ^r)⁻¹^J * S₀ * Dm := by
    have hP0 : 0 ≤ (Ξ⁻¹)^J := pow_nonneg (le_of_lt (inv_pos.mpr hΞpos)) J
    have hXb : 7.2 * (X:ℝ) / 2^r ≤ 3.6 * (Ξ⁻¹)^J * S₀ := by
      have h1 : 7.2 * (X:ℝ) / 2^r ≤ 7.2 * (2^(r-1) * (Ξ⁻¹)^J * S₀) / 2^r :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hXle (by norm_num)) (by positivity)
      have h2 : 7.2 * (2^(r-1) * (Ξ⁻¹)^J * S₀) / 2^r = 3.6 * (Ξ⁻¹)^J * S₀ := by
        rw [← h2p,
          div_eq_iff (ne_of_gt (mul_pos (pow_pos (by norm_num : (0:ℝ) < 2) (r-1)) (by norm_num)))]
        ring
      linarith [h1, h2]
    have hnum : 7.2 * (X:ℝ) / 2^r + 2 * (Ξ⁻¹)^J * S₀ ≤ 5.6 * (Ξ⁻¹)^J * S₀ := by linarith [hXb]
    have hdiv : (7.2 * (X:ℝ) / 2^r + 2 * (Ξ⁻¹)^J * S₀) / (2:ℝ)^J
        ≤ 5.6 * (Ξ⁻¹)^J * S₀ / (2:ℝ)^J :=
      div_le_div_of_nonneg_right hnum (by positivity)
    have hP2 : (Ξ⁻¹)^J / (2:ℝ)^J = (2*ξ^r)⁻¹^J := by
      rw [← div_pow]
      congr 1
      rw [hΞ, mul_inv_rev, div_eq_mul_inv]
    have hstep1 : 1.008 * ((7.2 * (X:ℝ) / 2^r + 2 * (Ξ⁻¹)^J * S₀) / (2:ℝ)^J) * Dm
        ≤ 1.008 * (5.6 * (Ξ⁻¹)^J * S₀ / (2:ℝ)^J) * Dm := by
      apply mul_le_mul_of_nonneg_right _ hD0
      exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
    have hstep2 : 1.008 * (5.6 * (Ξ⁻¹)^J * S₀ / (2:ℝ)^J) * Dm
        = 5.6448 * ((Ξ⁻¹)^J * S₀ / (2:ℝ)^J) * Dm := by ring_nf
    have hstep3 : 5.6448 * ((Ξ⁻¹)^J * S₀ / (2:ℝ)^J) * Dm
        ≤ 5.646 * (2*ξ^r)⁻¹^J * S₀ * Dm := by
      rw [← hP2]
      have e2 : 5.646 * ((Ξ⁻¹)^J / (2:ℝ)^J) * S₀ * Dm
          = 5.646 * ((Ξ⁻¹)^J * S₀ / (2:ℝ)^J) * Dm := by ring_nf
      rw [e2]
      have hR : 0 ≤ ((Ξ⁻¹)^J * S₀ / (2:ℝ)^J) * Dm :=
        mul_nonneg (div_nonneg (mul_nonneg hP0 hS0) (by positivity)) hD0
      nlinarith [hR]
    linarith [hstep1, hstep2, hstep3]
  -- ---------- num19_half ----------
  have hq1 : (0:ℝ) ≤ (2 * pxi r ^ r)⁻¹ ^ J / r :=
    div_nonneg
      (pow_nonneg (inv_nonneg.mpr (le_of_lt (mul_pos (by norm_num) (pow_pos hpxi_pos r)))) J)
      (by positivity)
  have hq2 : (0:ℝ) ≤ (pxi r ^ r)⁻¹ ^ J /
      (2 * (r:ℝ)^r * 32^(r+1) * (d:ℝ) * Real.log (2*(r:ℝ)*(d:ℝ))) :=
    div_nonneg
      (pow_nonneg (inv_nonneg.mpr (le_of_lt (pow_pos hpxi_pos r))) J)
      (mul_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by positivity) r))
          (by positivity)) (by positivity)) (le_of_lt hLpos))
  have h19 := (num19_half hr hd J hJ 0 (le_refl (0:ℝ)) hq1 hq2).1
  rw [← hξ] at h19
  have hEb : 0.735 * ξ ^ (r-1+r*J) + 1.087 + 5.646 * (2*ξ^r)⁻¹^J +
        0.044 * J / Real.log (2*(r:ℝ)*(d:ℝ)) ≤ 12.43 * ξ ^ (r-1) - 0.105 := by linarith
  have hE := mul_le_mul_of_nonneg_left hEb (mul_nonneg hS0 hD0)
  have hAe : S₀ * Dm * (0.735 * ξ ^ (r-1+r*J) + 1.087 + 5.646 * (2*ξ^r)⁻¹^J +
        0.044 * J / Real.log (2*(r:ℝ)*(d:ℝ)))
      = 0.735 * ξ ^ (r-1+r*J) * S₀ * Dm + 1.087 * S₀ * Dm +
        5.646 * (2*ξ^r)⁻¹^J * S₀ * Dm +
        0.044 * J / Real.log (2*(r:ℝ)*(d:ℝ)) * S₀ * Dm := by ring_nf
  have hA : ((d:ℝ) * hh * (Ξ^(J+1) * T₀) + 1.087 * S₀ * Dm +
        1.008 * ((7.2 * (X:ℝ) / 2^r + 2 * (Ξ⁻¹)^J * S₀) / 2^J) * Dm +
        0.044 * J / Real.log (2*(r:ℝ)*(d:ℝ)) * S₀ * Dm)
      ≤ S₀ * Dm * (12.43 * ξ^(r-1) - 0.105) := by
    linarith [hA1, hA3, hAe, hE]
  calc 2^r * ((d:ℝ) * hh * (Ξ^(J+1) * T₀) + 1.087 * S₀ * Dm +
        1.008 * ((7.2 * (X:ℝ) / 2^r + 2 * (Ξ⁻¹)^J * S₀) / 2^J) * Dm +
        0.044 * J / Real.log (2*(r:ℝ)*(d:ℝ)) * S₀ * Dm)
      ≤ 2^r * (S₀ * Dm * (12.43 * ξ^(r-1) - 0.105)) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
    _ = 2^r * S₀ * Dm * (12.43 * ξ^(r-1) - 0.105) := by ring

end Work.BW
