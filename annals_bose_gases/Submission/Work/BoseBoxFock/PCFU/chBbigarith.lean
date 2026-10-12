import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PCFU.chBarith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

theorem chBbigarith {K0 Kimg G0 Wm μ ℓ R a ε₀ : ℝ}
    (hK0le : 2 + 64 * Kimg * G0 * (|ε₀| / a ^ 4) * (R ^ 3 / 2 + 1 / 16) ≤ K0)
    (hKimg : 0 ≤ Kimg) (hG0 : 0 ≤ G0) (hWm : Wm ≤ 2 * G0)
    (ha : 0 < a) (hμ : 0 < μ) (hℓ : 0 < ℓ) (hR : 0 < R) (h2R : 2 * R ≤ ℓ)
    (hε : μ * a ^ 3 ≤ ε₀) :
    32 * (Kimg * Wm) * μ * (ℓ ^ 3 + 1) * (R / ℓ) ^ 4 / a ≤ K0 := by
  -- `|ε₀| ≥ ε₀ ≥ μ a³`
  have habs : μ * a ^ 3 ≤ |ε₀| := le_trans hε (le_abs_self ε₀)
  -- the geometric window bound `(ℓ³+1) (R/ℓ)^4 ≤ R³/2 + 1/16`
  have hRnn : 0 ≤ R / ℓ := div_nonneg hR.le hℓ.le
  have hRle : R / ℓ ≤ 1 / 2 := by
    rw [div_le_iff₀ hℓ]; linarith
  have hpow4 : (R / ℓ) ^ 4 ≤ 1 / 16 := by
    have h := pow_le_pow_left₀ hRnn hRle 4
    norm_num at h
    exact h
  have hls : ℓ ^ 3 * (R / ℓ) ^ 4 ≤ R ^ 3 / 2 := by
    have heq : ℓ ^ 3 * (R / ℓ) ^ 4 = R ^ 4 / ℓ := by field_simp
    rw [heq, div_le_iff₀ hℓ]
    have hR3 : 0 ≤ R ^ 3 := pow_nonneg hR.le 3
    have h := mul_le_mul_of_nonneg_left h2R hR3
    nlinarith only [h]
  have h1 : (ℓ ^ 3 + 1) * (R / ℓ) ^ 4 ≤ R ^ 3 / 2 + 1 / 16 := by
    have hsplit : (ℓ ^ 3 + 1) * (R / ℓ) ^ 4
        = ℓ ^ 3 * (R / ℓ) ^ 4 + (R / ℓ) ^ 4 := by ring
    rw [hsplit]
    linarith only [hls, hpow4]
  have h1nn : 0 ≤ (ℓ ^ 3 + 1) * (R / ℓ) ^ 4 := by
    have : (0 : ℝ) ≤ ℓ ^ 3 + 1 := by positivity
    exact mul_nonneg this (pow_nonneg hRnn 4)
  -- `μ a³ (ℓ³+1)(R/ℓ)^4 ≤ |ε₀| (R³/2+1/16)`
  have hprod : μ * a ^ 3 * ((ℓ ^ 3 + 1) * (R / ℓ) ^ 4)
      ≤ |ε₀| * (R ^ 3 / 2 + 1 / 16) :=
    mul_le_mul habs h1 h1nn (abs_nonneg ε₀)
  have hmid : μ * (ℓ ^ 3 + 1) * (R / ℓ) ^ 4 / a
      ≤ (|ε₀| / a ^ 4) * (R ^ 3 / 2 + 1 / 16) := by
    rw [show (|ε₀| / a ^ 4) * (R ^ 3 / 2 + 1 / 16)
        = |ε₀| * (R ^ 3 / 2 + 1 / 16) / a ^ 4 by ring]
    rw [div_le_div_iff₀ ha (pow_pos ha 4)]
    have h := mul_le_mul_of_nonneg_right hprod ha.le
    linarith only [h]
  -- the `K0` bound dominates the `64 Kimg G0`-multiple of the window bound
  have hP : (0 : ℝ) ≤ 64 * Kimg * G0 := by nlinarith only [hKimg, hG0]
  have hstep2 : 64 * Kimg * G0 * (μ * (ℓ ^ 3 + 1) * (R / ℓ) ^ 4 / a)
      ≤ 64 * Kimg * G0 * ((|ε₀| / a ^ 4) * (R ^ 3 / 2 + 1 / 16)) :=
    mul_le_mul_of_nonneg_left hmid hP
  have hg2 : 64 * Kimg * G0 * (|ε₀| / a ^ 4) * (R ^ 3 / 2 + 1 / 16)
      = 64 * Kimg * G0 * ((|ε₀| / a ^ 4) * (R ^ 3 / 2 + 1 / 16)) := by ring
  have hfin : 64 * Kimg * G0 * ((|ε₀| / a ^ 4) * (R ^ 3 / 2 + 1 / 16)) ≤ K0 := by
    rw [← hg2]; linarith only [hK0le]
  -- replace `Wm` by its bound `2 G0`
  have hKW : Kimg * Wm ≤ Kimg * (2 * G0) := mul_le_mul_of_nonneg_left hWm hKimg
  have h32 : 32 * (Kimg * Wm) ≤ 64 * Kimg * G0 := by nlinarith only [hKW]
  have hfac : (0 : ℝ) ≤ μ * (ℓ ^ 3 + 1) * (R / ℓ) ^ 4 / a := by
    have hL : (0 : ℝ) ≤ ℓ ^ 3 + 1 := by positivity
    exact div_nonneg (mul_nonneg (mul_nonneg hμ.le hL) (pow_nonneg hRnn 4)) ha.le
  have hstep1 : 32 * (Kimg * Wm) * (μ * (ℓ ^ 3 + 1) * (R / ℓ) ^ 4 / a)
      ≤ 64 * Kimg * G0 * (μ * (ℓ ^ 3 + 1) * (R / ℓ) ^ 4 / a) :=
    mul_le_mul_of_nonneg_right h32 hfac
  have hg1 : 32 * (Kimg * Wm) * μ * (ℓ ^ 3 + 1) * (R / ℓ) ^ 4 / a
      = 32 * (Kimg * Wm) * (μ * (ℓ ^ 3 + 1) * (R / ℓ) ^ 4 / a) := by ring
  rw [hg1]
  exact le_trans hstep1 (le_trans hstep2 hfin)

end Work.BoseBoxFock.PCFU
