import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Assembly

theorem budget_near_near (β C q d s εT b : ℝ) (hβ : 0 < β) (hC : 0 ≤ C)
    (hd : 0 < d) (hd1 : d ≤ 1) (hs : 0 < s) (hε : 0 ≤ εT) (hb : 0 ≤ b)
    (hmain : εT + b / β ^ 2 + 8 * C * s ^ 3 ≤ 1) :
    εT * q ^ 2 / (1 + d ^ 2 * q ^ 2) + b * β⁻¹ * (q ^ 2 / (q ^ 2 + β))
      + (1 - εT) * (C * (2 * s) ^ 3 * q ^ 2) + εT * (C * (2 * (d * s)) ^ 3 * q ^ 2)
      ≤ q ^ 2 := by
  -- Work with the (equivalent) form of the main hypothesis in terms of β⁻¹.
  have hq2 : (0 : ℝ) ≤ q ^ 2 := sq_nonneg q
  have hmain' : εT + b * β⁻¹ * β⁻¹ + 8 * C * s ^ 3 ≤ 1 := by
    have hb2 : b * β⁻¹ * β⁻¹ = b / β ^ 2 := by ring
    linarith [hmain]
  -- First term: dropping the (≥ 1) denominator only increases it.
  have h1 : εT * q ^ 2 / (1 + d ^ 2 * q ^ 2) ≤ εT * q ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hε hq2) (sq_nonneg d)) hq2]
  -- Second term: q²/(q²+β) ≤ q²/β, giving the b/β² from the hypothesis.
  have h2 : b * β⁻¹ * (q ^ 2 / (q ^ 2 + β)) ≤ b * β⁻¹ * β⁻¹ * q ^ 2 := by
    have hle : q ^ 2 / (q ^ 2 + β) ≤ q ^ 2 / β :=
      div_le_div_of_nonneg_left hq2 hβ (by linarith)
    calc b * β⁻¹ * (q ^ 2 / (q ^ 2 + β)) ≤ b * β⁻¹ * (q ^ 2 / β) :=
            mul_le_mul_of_nonneg_left hle (mul_nonneg hb (inv_nonneg.mpr hβ.le))
      _ = b * β⁻¹ * β⁻¹ * q ^ 2 := by ring
  -- Third and fourth terms: (2s)³ = 8s³ exactly, and (2ds)³ ≤ (2s)³ since d ≤ 1.
  have h3 : (1 - εT) * (C * (2 * s) ^ 3 * q ^ 2) ≤ (1 - εT) * (8 * C * s ^ 3 * q ^ 2) := by
    nlinarith [sq_nonneg q]
  have h4 : εT * (C * (2 * (d * s)) ^ 3 * q ^ 2) ≤ εT * (8 * C * s ^ 3 * q ^ 2) := by
    have hds : d * s ≤ s := by nlinarith [hd, hs, hd1]
    have hcube : (2 * (d * s)) ^ 3 ≤ (2 * s) ^ 3 := by
      refine pow_le_pow_left₀ ?_ ?_ 3
      · nlinarith [hd, hs]
      · linarith
    have hkey : (2 * (d * s)) ^ 3 * (C * q ^ 2) ≤ (2 * s) ^ 3 * (C * q ^ 2) :=
      mul_le_mul_of_nonneg_right hcube (mul_nonneg hC hq2)
    have hkey2 : εT * ((2 * (d * s)) ^ 3 * (C * q ^ 2)) ≤ εT * ((2 * s) ^ 3 * (C * q ^ 2)) :=
      mul_le_mul_of_nonneg_left hkey hε
    nlinarith [hkey2, sq_nonneg q]
  have h34 : (1 - εT) * (C * (2 * s) ^ 3 * q ^ 2) + εT * (C * (2 * (d * s)) ^ 3 * q ^ 2)
      ≤ 8 * C * s ^ 3 * q ^ 2 := by
    nlinarith [h3, h4]
  -- Assemble: LHS ≤ q²·(εT + b/β² + 8Cs³) ≤ q².
  have hfin : q ^ 2 * (εT + b * β⁻¹ * β⁻¹ + 8 * C * s ^ 3) ≤ q ^ 2 := by
    have := mul_le_mul_of_nonneg_left hmain' hq2
    simpa using this
  nlinarith [h1, h2, h34, hfin]

end Work.BoseKinLoc.Assembly
