import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

/-- Packaging of the truncation error `C1 * (y * L^2 / T + L)` of the twisted Perron formula:
with `T ≥ L^2 * exp (L^{1/10})` and `L ≤ y * exp (-(c/8) L^{1/10})` (the second is an eventual
statement in `L` supplied by `Work.BMF.liouville.exp_dominates_poly`), the whole thing is
`≤ 2 C1 * L^10 * y * exp (-(c/8) L^{1/10})`.  Pure real inequality. -/
lemma zetaTwTrunc_absorb {c C1 L T y : ℝ} (hc : 0 < c) (hc8 : c ≤ 8) (hC1 : 0 ≤ C1)
    (hL1 : 1 ≤ L) (hT : 0 < T) (hTge : L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) ≤ T)
    (hy : y = Real.exp L) (hLy : L ≤ y * Real.exp (-(c / 8) * L ^ (1 / 10 : ℝ))) :
    C1 * (y * L ^ 2 / T + L) ≤ 2 * C1 * L ^ (10 : ℝ) * y * Real.exp (-(c / 8) * L ^ (1 / 10 : ℝ)) := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hLnn : 0 ≤ L := le_of_lt hLpos
  have hypos : 0 < y := by rw [hy]; exact Real.exp_pos L
  have hynn : 0 ≤ y := le_of_lt hypos
  have ha : 0 ≤ L ^ (1/10:ℝ) := Real.rpow_nonneg hLnn _
  have hL10 : (1:ℝ) ≤ L ^ (10:ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hc8' : c/8 ≤ 1 := by linarith
  have hexp1 : Real.exp (-(L^(1/10:ℝ))) * Real.exp (L^(1/10:ℝ)) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hkey : (y * Real.exp (-(L^(1/10:ℝ)))) * (L^2 * Real.exp (L^(1/10:ℝ))) = y * L^2 := by
    calc (y * Real.exp (-(L^(1/10:ℝ)))) * (L^2 * Real.exp (L^(1/10:ℝ)))
        = y * L^2 * (Real.exp (-(L^(1/10:ℝ))) * Real.exp (L^(1/10:ℝ))) := by ring
      _ = y * L^2 * 1 := by rw [hexp1]
      _ = y * L^2 := by ring
  have hA1 : y * L^2 / T ≤ y * Real.exp (-(L^(1/10:ℝ))) := by
    rw [div_le_iff₀ hT]
    calc y * L^2 = (y * Real.exp (-(L^(1/10:ℝ)))) * (L^2 * Real.exp (L^(1/10:ℝ))) := hkey.symm
      _ ≤ (y * Real.exp (-(L^(1/10:ℝ)))) * T :=
          mul_le_mul_of_nonneg_left hTge (mul_nonneg hynn (le_of_lt (Real.exp_pos _)))
  have hA2a : Real.exp (-(L^(1/10:ℝ))) ≤ Real.exp (-(c/8) * L^(1/10:ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h1 : (c/8) * L^(1/10:ℝ) ≤ L^(1/10:ℝ) := mul_le_of_le_one_left ha hc8'
    linarith
  have hA2 : y * Real.exp (-(L^(1/10:ℝ))) ≤ L^(10:ℝ) * y * Real.exp (-(c/8)*L^(1/10:ℝ)) := by
    calc y * Real.exp (-(L^(1/10:ℝ))) ≤ y * Real.exp (-(c/8)*L^(1/10:ℝ)) :=
          mul_le_mul_of_nonneg_left hA2a hynn
      _ ≤ L^(10:ℝ) * (y * Real.exp (-(c/8)*L^(1/10:ℝ))) :=
          le_mul_of_one_le_left (mul_nonneg hynn (le_of_lt (Real.exp_pos _))) hL10
      _ = L^(10:ℝ) * y * Real.exp (-(c/8)*L^(1/10:ℝ)) := by ring
  have hA : y * L^2 / T ≤ L^(10:ℝ) * y * Real.exp (-(c/8)*L^(1/10:ℝ)) := le_trans hA1 hA2
  have hB : L ≤ L^(10:ℝ) * y * Real.exp (-(c/8)*L^(1/10:ℝ)) := by
    calc L ≤ y * Real.exp (-(c/8)*L^(1/10:ℝ)) := hLy
      _ ≤ L^(10:ℝ) * (y * Real.exp (-(c/8)*L^(1/10:ℝ))) :=
          le_mul_of_one_le_left (mul_nonneg hynn (le_of_lt (Real.exp_pos _))) hL10
      _ = L^(10:ℝ) * y * Real.exp (-(c/8)*L^(1/10:ℝ)) := by ring
  have hmain : y * L^2 / T + L ≤ 2 * (L^(10:ℝ) * y * Real.exp (-(c/8)*L^(1/10:ℝ))) := by
    have hh := add_le_add hA hB
    simpa only [two_mul] using hh
  calc C1 * (y*L^2/T + L) ≤ C1 * (2 * (L^(10:ℝ)*y*Real.exp (-(c/8)*L^(1/10:ℝ)))) := mul_le_mul_of_nonneg_left hmain hC1
    _ = 2 * C1 * L^(10:ℝ) * y * Real.exp (-(c/8)*L^(1/10:ℝ)) := by ring

end Work.BMF.liouville
