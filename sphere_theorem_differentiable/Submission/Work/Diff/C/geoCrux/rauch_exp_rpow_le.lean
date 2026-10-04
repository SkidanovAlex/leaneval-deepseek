import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C.geoCrux

theorem rauch_exp_rpow_le {c ε₁ A R : ℝ} (hc : 0 < c) (hR : R ≤ 8 / c) (hR1 : 1 ≤ R)
    (hA : A ≤ 6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4)) :
    Real.exp A * R ^ (c / 4) ≤
      Real.exp (6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4)
        + (c / 4) * Real.log (8 / c)) := by
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have h8c : (0 : ℝ) < 8 / c := by positivity
  have hc4 : (0 : ℝ) ≤ c / 4 := by positivity
  have h1 : R ^ (c / 4) ≤ (8 / c) ^ (c / 4) :=
    Real.rpow_le_rpow hRpos.le hR hc4
  have h2 : Real.exp A
      ≤ Real.exp (6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4)) :=
    Real.exp_le_exp.mpr hA
  calc Real.exp A * R ^ (c / 4)
      ≤ Real.exp (6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4))
          * (8 / c) ^ (c / 4) :=
        mul_le_mul h2 h1 (by positivity) (Real.exp_pos _).le
    _ = Real.exp (6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4)
          + (c / 4) * Real.log (8 / c)) := by
        rw [Real.rpow_def_of_pos h8c, ← Real.exp_add]
        ring_nf

end Work.Diff.C.geoCrux
