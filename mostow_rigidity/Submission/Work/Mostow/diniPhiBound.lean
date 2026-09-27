import Mathlib
import Submission.Work.Mostow.localIsomDefs

/-!
# The Dini `phi` bound in the chart of ℍⁿ

The `localIsom` area needs the elementary chart estimate
`cdist p (p + w) - 1 ≤ gH p w / 2 + ‖w‖ ^ 3`, i.e.

    cosh (hdist p (p + w)) - 1 ≤ gH p w / 2 + ‖w‖ ^ 3 ,

which says that up to a cubic error the "cosh distance" from `p` to the chart point `p + w`
is bounded by half the hyperbolic quadratic form of the chart increment `w`.

## Proof

Write `A = tpart p = √(1+‖p‖²)`, `B = tpart (p+w)`, `T = ‖w‖`, `S = ⟪p,w⟫` and `u = ‖p‖`.  Then
`cdist p (p+w) - 1 = (T² - (A-B)²)/2` and `gH p w = T² - S²/A²`, so the claim is equivalent to

    S²/A² ≤ (A-B)² + 2T³.

Since `B² = A² + 2S + T²` one has `(A-B)(A+B) = -(2S+T²)`, hence
`(A-B)² = (2S+T²)²/(A+B)² ≥ (2S+T²)²/(2A+T)²` because `B ≤ A + T`.  The remaining polynomial
inequality `S²/A² ≤ (2S+T²)²/(2A+T)² + 2T³` is pure algebra, using `u ≤ A` and
`|S| ≤ uT` (Cauchy–Schwarz) as the only inputs.  This polynomial core is isolated as
`diniPhiAlgebra`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- The polynomial core of the Dini `phi` bound.

For reals `A, B, T, S, u` with `1 ≤ A`, `A² = 1 + u²`, `0 ≤ u`, `0 ≤ T`, `|S| ≤ uT`,
`0 ≤ B`, `B² = A² + 2S + T²` and `B ≤ A + T`, one has
`(T² - (A-B)²)/2 ≤ (T² - S²/A²)/2 + T³`. -/
theorem diniPhiAlgebra {A B T S u : ℝ}
    (hA1 : 1 ≤ A) (hA2 : A ^ 2 = 1 + u ^ 2) (hu0 : 0 ≤ u) (hT0 : 0 ≤ T)
    (hSabs : |S| ≤ u * T) (hB0 : 0 ≤ B) (hBrel : B ^ 2 = A ^ 2 + 2 * S + T ^ 2)
    (hBle : B ≤ A + T) :
    (T ^ 2 - (A - B) ^ 2) / 2 ≤ (T ^ 2 - S ^ 2 / A ^ 2) / 2 + T ^ 3 := by
  have hApos : 0 < A := lt_of_lt_of_le one_pos hA1
  have huA : u ≤ A := by
    have h : u ^ 2 ≤ A ^ 2 := by nlinarith [hA2]
    have h2 := sq_le_sq.mp h
    rwa [abs_of_nonneg hu0, abs_of_nonneg (le_of_lt hApos)] at h2
  have hSle : S ≤ u * T := (abs_le.mp hSabs).2
  have hSge : -(u * T) ≤ S := (abs_le.mp hSabs).1
  have hSsq : S ^ 2 ≤ A ^ 2 * T ^ 2 := by
    have h1 : S ^ 2 ≤ (u * T) ^ 2 := by
      rw [sq_le_sq, abs_mul, abs_of_nonneg hu0, abs_of_nonneg hT0]
      exact hSabs
    have h2 : (u * T) ^ 2 ≤ A ^ 2 * T ^ 2 := by nlinarith [huA, hu0, hT0]
    linarith
  have hXeq : S ^ 2 * (2 * A + T) ^ 2 - A ^ 2 * (2 * S + T ^ 2) ^ 2
      = 4 * A * T * S ^ 2 + T ^ 2 * S ^ 2 - 4 * A ^ 2 * S * T ^ 2 - A ^ 2 * T ^ 4 := by
    ring
  have hkey : S ^ 2 * (2 * A + T) ^ 2 - A ^ 2 * (2 * S + T ^ 2) ^ 2 ≤ 8 * A ^ 3 * T ^ 3 := by
    rw [hXeq]
    have hprod1 : A * T * S ^ 2 ≤ A * T * (A ^ 2 * T ^ 2) :=
      mul_le_mul_of_nonneg_left hSsq (by nlinarith [hA1, hT0])
    have hprod2 : T ^ 2 * S ^ 2 ≤ T ^ 2 * (A ^ 2 * T ^ 2) :=
      mul_le_mul_of_nonneg_left hSsq (by nlinarith [hT0])
    have hnegS : -S ≤ A * T := by nlinarith [hSge, huA, hT0]
    have hprod3 : A ^ 2 * T ^ 2 * (-S) ≤ A ^ 2 * T ^ 2 * (A * T) :=
      mul_le_mul_of_nonneg_left hnegS (by nlinarith [hA1, hT0])
    have b1 : 4 * A * T * S ^ 2 ≤ 4 * A ^ 3 * T ^ 3 := by nlinarith [hprod1]
    have b2 : T ^ 2 * S ^ 2 ≤ A ^ 2 * T ^ 4 := by nlinarith [hprod2]
    have b3 : -4 * A ^ 2 * S * T ^ 2 ≤ 4 * A ^ 3 * T ^ 3 := by nlinarith [hprod3]
    linarith
  have h2Apos : 0 < 2 * A + T := by linarith
  have hPsiT : S ^ 2 / A ^ 2 - (2 * S + T ^ 2) ^ 2 / (2 * A + T) ^ 2 ≤ 2 * T ^ 3 := by
    have hden : 0 < A ^ 2 * (2 * A + T) ^ 2 := mul_pos (pow_pos hApos 2) (pow_pos h2Apos 2)
    rw [div_sub_div (S ^ 2) ((2 * S + T ^ 2) ^ 2) (pow_ne_zero 2 (ne_of_gt hApos))
      (pow_ne_zero 2 (ne_of_gt h2Apos))]
    rw [div_le_iff₀ hden]
    have hkey2 : 8 * A ^ 3 * T ^ 3 ≤ 2 * T ^ 3 * (A ^ 2 * (2 * A + T) ^ 2) := by
      have h4A : 0 ≤ (2 * A + T) ^ 2 - 4 * A := by
        have h1 : 0 ≤ A * (A - 1) := mul_nonneg (by linarith) (by linarith)
        have h2 : 0 ≤ A * T := mul_nonneg (by linarith) hT0
        have h3 : 0 ≤ T * T := mul_nonneg hT0 hT0
        nlinarith [h1, h2, h3]
      have hprod : 0 ≤ 2 * T ^ 3 * A ^ 2 * ((2 * A + T) ^ 2 - 4 * A) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (pow_nonneg hT0 3))
          (sq_nonneg A)) h4A
      nlinarith [hprod]
    nlinarith [hkey, hkey2]
  have hABpos : 0 < A + B := by linarith
  have hABsq : (2 * S + T ^ 2) ^ 2 / (2 * A + T) ^ 2 ≤ (A - B) ^ 2 := by
    have h1 : A - B = (-(2 * S + T ^ 2)) / (A + B) := by
      field_simp
      nlinarith [hBrel]
    rw [h1, neg_div, neg_sq, div_pow]
    have hc : 0 < (A + B) ^ 2 := pow_pos hABpos 2
    have hcb : (A + B) ^ 2 ≤ (2 * A + T) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hABpos) (by linarith) 2
    exact div_le_div_of_nonneg_left (sq_nonneg _) hc hcb
  have hfin : S ^ 2 / A ^ 2 ≤ (A - B) ^ 2 + 2 * T ^ 3 := by linarith [hPsiT, hABsq]
  linarith [hfin]

theorem diniPhiBound {n : ℕ} (p w : Submission.Mostow.E n) : Work.Mostow.cdist p (p + w) - 1 ≤ Submission.Mostow.gH p w / 2 + ‖w‖ ^ 3 := by
  have hA2 : tpart p ^ 2 = 1 + ‖p‖ ^ 2 := tpart_sq p
  have hA1 : 1 ≤ tpart p := one_le_tpart_localIsomDefs p
  have hT0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hu0 : 0 ≤ ‖p‖ := norm_nonneg p
  have hB0 : 0 ≤ tpart (p + w) := le_of_lt (tpart_pos (p + w))
  have hSabs : |inner ℝ p w| ≤ ‖p‖ * ‖w‖ := abs_real_inner_le_norm p w
  have hBrel : tpart (p + w) ^ 2 = (tpart p) ^ 2 + 2 * inner ℝ p w + ‖w‖ ^ 2 := by
    have h3 : ‖p + w‖ ^ 2 = ‖p‖ ^ 2 + 2 * inner ℝ p w + ‖w‖ ^ 2 := norm_add_sq_real p w
    have h2 : tpart (p + w) ^ 2 = 1 + ‖p + w‖ ^ 2 := tpart_sq (p + w)
    nlinarith [h2, h3, hA2]
  have hBle : tpart (p + w) ≤ tpart p + ‖w‖ := by
    have hSAT : inner ℝ p w ≤ tpart p * ‖w‖ := by
      have h1 : inner ℝ p w ≤ ‖p‖ * ‖w‖ := (abs_le.mp hSabs).2
      nlinarith [h1, hA1, hA2, hu0, hT0]
    have hb2 : (tpart (p + w)) ^ 2 ≤ (tpart p + ‖w‖) ^ 2 := by nlinarith [hBrel, hSAT]
    have hle := sq_le_sq.mp hb2
    have h1 : 0 < tpart (p + w) := tpart_pos (p + w)
    have h2 : 0 ≤ tpart p + ‖w‖ := by linarith [le_of_lt (tpart_pos p), hT0]
    rwa [abs_of_nonneg (le_of_lt h1), abs_of_nonneg h2] at hle
  have hcore : (‖w‖ ^ 2 - (tpart p - tpart (p + w)) ^ 2) / 2
      ≤ (‖w‖ ^ 2 - (inner ℝ p w) ^ 2 / (tpart p) ^ 2) / 2 + ‖w‖ ^ 3 :=
    diniPhiAlgebra hA1 hA2 hu0 hT0 hSabs hB0 hBrel hBle
  have hcdist : cdist p (p + w) - 1 = (‖w‖ ^ 2 - (tpart p - tpart (p + w)) ^ 2) / 2 := by
    have h3 : ‖p + w‖ ^ 2 = ‖p‖ ^ 2 + 2 * inner ℝ p w + ‖w‖ ^ 2 := norm_add_sq_real p w
    have h2 : tpart (p + w) ^ 2 = 1 + ‖p + w‖ ^ 2 := tpart_sq (p + w)
    rw [cdist, inner_add_right, real_inner_self_eq_norm_sq]
    nlinarith [h2, h3, hA2]
  have hgH : gH p w = ‖w‖ ^ 2 - (inner ℝ p w) ^ 2 / (tpart p) ^ 2 := by
    rw [gH, tpart_sq p]
  rw [hcdist, hgH]
  exact hcore

end Work.Mostow
