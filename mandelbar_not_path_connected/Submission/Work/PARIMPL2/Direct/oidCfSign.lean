import Mathlib
import Submission.Work.PARIMPL2.Direct.oidAux
import Submission.Work.PARIMPL2.Direct.orbitCrossBound
import Submission.Work.PARIMPL2.Direct.oidDefs
import Submission.Work.PARIMPL2.Direct.oidArcNeg
import Submission.Work.PARIMPL2.Direct.oidArcPos
import Submission.Work.PARIMPL2.Direct.oidCg_one_le
import Submission.Work.PARIMPL2.Direct.oidCf_abs_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-! ## Elementary bounds on `oidCf` for `cr ≤ 0`

For `cr ≤ 0` the coefficient `C'_j = oidCf λ cr x y j` equals
`cr·λ·sinh(λ y_j)·cosh(λ y_j) / (y_j · D_j)` (see `oidZeta_im`), hence is `≤ 0`; and the
absolute-value bound `oidCf_abs_le` together with `oidCg_one_le` gives `|C'_j| ≤ 33|cr|/R² ≤
99/(16R) < 1`, so that `1 + C'_j ∈ (0,1]`. -/

/-- `C'_j = -cr (ζ_j).im / y_j` written as `cr λ sinh(λ y) cosh(λ y)/(y D_j)` when `y j ≠ 0`. -/
theorem oidCf_eq (lam cr : ℝ) (x y : ℕ → ℝ) (j : ℕ) (hy : y j ≠ 0) :
    oidCf lam cr x y j
      = cr * (lam * Real.sinh (lam * y j) * Real.cosh (lam * y j))
          / (ocDen lam x y j * y j) := by
  rw [oidCf, oidZeta_im]
  field_simp

/-- For `cr ≤ 0`, the coefficient `oidCf λ cr x y j` is nonpositive. -/
theorem oidCf_nonpos (lam cr : ℝ) (hlam : 0 < lam) (hcr : cr ≤ 0)
    (x y : ℕ → ℝ) (j : ℕ) : oidCf lam cr x y j ≤ 0 := by
  by_cases hy : y j = 0
  · simp [oidCf, hy, oidZeta_im_zero_of lam x y j hy]
  · have hD : 0 < ocDen lam x y j := by
      rw [ocDen]
      nlinarith [sq_pos_of_ne_zero (by
        rcases lt_or_gt_of_ne hy with h | h
        · have : Real.sinh (lam * y j) < 0 := Real.sinh_neg_iff.mpr (by nlinarith)
          exact ne_of_lt this
        · have : 0 < Real.sinh (lam * y j) := Real.sinh_pos_iff.mpr (by nlinarith)
          exact ne_of_gt this), sq_nonneg (Real.sin (lam * x j))]
    have hspos : 0 ≤ Real.sinh (lam * y j) / y j := by
      rcases lt_or_gt_of_ne hy with h | h
      · exact le_of_lt (div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr (by nlinarith)) h)
      · exact le_of_lt (div_pos (Real.sinh_pos_iff.mpr (by nlinarith)) h)
    have hcpos : 0 ≤ lam * Real.cosh (lam * y j) / ocDen lam x y j :=
      div_nonneg (mul_nonneg hlam.le (Real.cosh_pos _).le) hD.le
    have hprod : 0 ≤ (Real.sinh (lam * y j) / y j) * (lam * Real.cosh (lam * y j) / ocDen lam x y j) :=
      mul_nonneg hspos hcpos
    have heq : oidCf lam cr x y j
        = cr * ((Real.sinh (lam * y j) / y j) * (lam * Real.cosh (lam * y j) / ocDen lam x y j)) := by
      rw [oidCf, oidZeta_im]; field_simp
    rw [heq]
    exact mul_nonpos_of_nonpos_of_nonneg hcr hprod

/-- `|oidCf λ cr x y j| ≤ 99/(16R)` under the strip hypotheses, `cr ≤ 0`, `|cr| ≤ 3R/16`. -/
theorem oidCf_abs_le_small (lam R cr : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1) (hcpR : |cr| ≤ 3 * R / 16)
    (x y : ℕ → ℝ) (j : ℕ)
    (hx1 : R / 4 + 2 ≤ x j) (hx2 : x j ≤ Real.pi / lam - R / 4)
    (hDpos : 0 < ocDen lam x y j) :
    |oidCf lam cr x y j| ≤ 99 / (16 * R) := by
  have h1 : |oidCf lam cr x y j| ≤ oidCg lam |cr| x y j := oidCf_abs_le lam cr hlam x y j
  have h2 : oidCg lam |cr| x y j = |cr| * oidCg lam 1 x y j := by rw [oidCg, oidCg]; ring
  have h3 : oidCg lam 1 x y j ≤ 33 / R ^ 2 := oidCg_one_le lam R hlam hR hlamR x y j hx1 hx2 hDpos
  have habs : (0:ℝ) ≤ |cr| := abs_nonneg cr
  have hcgnn : 0 ≤ oidCg lam 1 x y j := by
    rw [oidCg, one_mul]
    have hd : 0 ≤ lam ^ 2 / ocDen lam x y j := div_nonneg (sq_nonneg _) hDpos.le
    linarith [sq_nonneg lam, hd]
  have h4 : |cr| * oidCg lam 1 x y j ≤ (3 * R / 16) * (33 / R ^ 2) :=
    mul_le_mul hcpR h3 hcgnn (by linarith)
  have hRpos : 0 < R := by linarith
  have h5 : (3 * R / 16) * (33 / R ^ 2) = 99 / (16 * R) := by
    field_simp
    norm_num
  linarith [h1, h2.le, h2.ge, h4, h5.le, h5.ge]

/-- `0 < 1 + oidCf λ cr x y j` and `1 + oidCf λ cr x y j ≤ 1` under the hypotheses, `cr ≤ 0`. -/
theorem one_add_oidCf_mem (lam R cr : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1) (hcr : cr ≤ 0) (hcpR : |cr| ≤ 3 * R / 16)
    (x y : ℕ → ℝ) (j : ℕ)
    (hx1 : R / 4 + 2 ≤ x j) (hx2 : x j ≤ Real.pi / lam - R / 4)
    (hDpos : 0 < ocDen lam x y j) :
    0 < 1 + oidCf lam cr x y j ∧ 1 + oidCf lam cr x y j ≤ 1 := by
  have hle := oidCf_nonpos lam cr hlam hcr x y j
  have hsmall := oidCf_abs_le_small lam R cr hlam hR hlamR hcpR x y j hx1 hx2 hDpos
  have hRpos : 0 < R := by linarith
  have hlt : 99 / (16 * R) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have hgt : -1 < oidCf lam cr x y j := by
    have h2 : |oidCf lam cr x y j| < 1 := lt_of_le_of_lt hsmall hlt
    linarith [(abs_lt.mp h2).1]
  exact ⟨by linarith, by linarith⟩

end Work.PARIMPL2.Direct