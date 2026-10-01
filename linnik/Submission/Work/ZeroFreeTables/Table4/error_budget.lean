import Mathlib

namespace Work.ZeroFreeTables.Table4

private lemma b1 {α δ L C Ct Amax : ℝ} (hα : 0 < α) (hαA : α ≤ Amax) (hδ : 0 < δ) (hL : 1 ≤ L)
    (hC : 0 ≤ C) (hCt : 0 ≤ Ct) :
    (α ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * (C * (L + 2)) + Ct)
      ≤ α * ((Amax * (3 * C * (1 + 4 / δ ^ 2) + Ct)) / L) := by
  field_simp
  nlinarith [sq_nonneg δ, mul_nonneg hC (sq_nonneg δ), mul_nonneg hCt (sq_nonneg δ),
    mul_nonneg hC (by linarith : (0:ℝ) ≤ L - 1), mul_nonneg hCt (by linarith : (0:ℝ) ≤ L - 1),
    mul_nonneg (mul_nonneg hC (sq_nonneg δ)) (by linarith : (0:ℝ) ≤ L - 1),
    mul_nonneg (mul_nonneg hCt (sq_nonneg δ)) (by linarith : (0:ℝ) ≤ L - 1)]

private lemma b2 {α δ L C Ct Amax : ℝ} (hα : 0 < α) (hαA : α ≤ Amax) (hδ : 0 < δ) (hL : 1 ≤ L)
    (hC : 0 ≤ C) (hCt : 0 ≤ Ct) :
    (2 / 3) * (α ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * (C * (L + 2)) + Ct)
      ≤ α * ((2 / 3) * ((Amax ^ 2 * (3 * C * (2 / δ) * (1 + 4 / δ ^ 2) + Ct)) / L)) := by
  field_simp
  have hbB : 0 ≤ 2*(δ^2+4)*C*(L+2)+δ^3*Ct := by positivity
  have hα2 : α^2 ≤ Amax^2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Amax - α) (by linarith : (0:ℝ) ≤ Amax + α)]
  have hX2 : 2*(δ^2+4)*C*(L+2)+δ^3*Ct ≤ L^2*(2*3*(δ^2+4)*C+δ^3*Ct) := by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity : (0:ℝ) ≤ δ^2+4)) (by linarith : (0:ℝ) ≤ 3*L+2)) (by linarith : (0:ℝ) ≤ L-1)) (by norm_num : (0:ℝ) ≤ 2),
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ δ^3) hCt) (by linarith : (0:ℝ) ≤ L-1)) (by linarith : (0:ℝ) ≤ L+1)]
  nlinarith [hα2, hX2, hbB, sq_nonneg Amax]

private lemma b3 {α L Cs Amax : ℝ} (hα : 0 < α) (hαA : α ≤ Amax) (hL : 1 ≤ L) (hCs : 0 ≤ Cs) :
    Cs * (α + α ^ 2 + α ^ 3) * (Real.log L + 2) ^ 4 / L
      ≤ α * (Cs * (1 + Amax + Amax ^ 2) * (Real.log L + 2) ^ 4 / L) := by
  field_simp
  have hpoly : 1 + α + α^2 ≤ 1 + Amax + Amax^2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Amax - α) (by linarith : (0:ℝ) ≤ Amax + α)]
  have hnn : 0 ≤ Cs * (Real.log L + 2)^4 := by positivity
  nlinarith [hpoly, hnn]

private lemma b4 {α δ L : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hL : 1 ≤ L) :
    3 * (8 * α / (δ * L)) ≤ α * ((24 / δ) / L) := by
  field_simp
  norm_num

theorem error_budget {α δ L ε C Ct Cs Amax : ℝ}
    (hα : 0 < α) (hαA : α ≤ Amax) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε)
    (hC : 0 ≤ C) (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs) (hL : 1 ≤ L)
    (hthr : 4 * (Amax * (3 * C * (1 + 4 / δ ^ 2) + Ct)
        + Amax ^ 2 * (3 * C * (2 / δ) * (1 + 4 / δ ^ 2) + Ct) + 24 / δ) / ε ≤ L)
    (hlog : Cs * (1 + Amax + Amax ^ 2) * (Real.log L + 2) ^ 4 / L ≤ ε / 4) :
    ((α ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * (C * (L + 2)) + Ct)
        + (2 / 3) * (α ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * (C * (L + 2)) + Ct)
        + Cs * (α + α ^ 2 + α ^ 3) * (Real.log L + 2) ^ 4 / L)
      + 3 * (8 * α / (δ * L)) ≤ α * ε / 2 := by
  have hLpos : 0 < L := by linarith
  have hS : Amax * (3 * C * (1 + 4 / δ ^ 2) + Ct)
      + Amax ^ 2 * (3 * C * (2 / δ) * (1 + 4 / δ ^ 2) + Ct) + 24 / δ ≤ L * ε / 4 := by
    have h := (div_le_iff₀ hε).mp hthr
    linarith [h]
  have h1 := b1 hα hαA hδ0 hL hC hCt
  have h2 := b2 hα hαA hδ0 hL hC hCt
  have h3 := b3 hα hαA hL hCs
  have h4 := b4 hα hδ0 hL
  have hbrace : (Amax * (3 * C * (1 + 4 / δ ^ 2) + Ct)) / L
      + (2 / 3) * ((Amax ^ 2 * (3 * C * (2 / δ) * (1 + 4 / δ ^ 2) + Ct)) / L)
      + (24 / δ) / L ≤ ε / 4 := by
    have hA2nn : 0 ≤ Amax ^ 2 * (3 * C * (2 / δ) * (1 + 4 / δ ^ 2) + Ct) := by positivity
    have hA : Amax * (3 * C * (1 + 4 / δ ^ 2) + Ct)
        + (2 / 3) * (Amax ^ 2 * (3 * C * (2 / δ) * (1 + 4 / δ ^ 2) + Ct)) + 24 / δ ≤ L * ε / 4 := by
      linarith [hS, hA2nn]
    have hd := div_le_div_of_nonneg_right hA (le_of_lt hLpos)
    have hsplit : (Amax * (3 * C * (1 + 4 / δ ^ 2) + Ct)
        + (2 / 3) * (Amax ^ 2 * (3 * C * (2 / δ) * (1 + 4 / δ ^ 2) + Ct)) + 24 / δ) / L
        = (Amax * (3 * C * (1 + 4 / δ ^ 2) + Ct)) / L
          + (2 / 3) * ((Amax ^ 2 * (3 * C * (2 / δ) * (1 + 4 / δ ^ 2) + Ct)) / L)
          + (24 / δ) / L := by ring
    rw [hsplit] at hd
    have hsimp : (L * ε / 4) / L = ε / 4 := by field_simp
    rwa [hsimp] at hd
  have key : α * ((Amax * (3 * C * (1 + 4 / δ ^ 2) + Ct)) / L
        + (2 / 3) * ((Amax ^ 2 * (3 * C * (2 / δ) * (1 + 4 / δ ^ 2) + Ct)) / L)
        + (24 / δ) / L + Cs * (1 + Amax + Amax ^ 2) * (Real.log L + 2) ^ 4 / L)
      ≤ α * (ε / 2) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hα)
    linarith [hbrace, hlog]
  nlinarith [h1, h2, h3, h4, key]

end Work.ZeroFreeTables.Table4
