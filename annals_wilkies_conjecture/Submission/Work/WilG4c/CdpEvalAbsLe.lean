import Mathlib

namespace Work.WilG4c

theorem CdpEvalAbsLe {n : ℕ} (g : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) (M : List (Fin n))
    (h : ‖iteratedFDeriv ℝ M.length g y‖ ≤ 1) :
    |iteratedFDeriv ℝ M.length g y (fun j => Pi.single (M.get j) 1)| ≤ 1 := by
  have h1 : ‖iteratedFDeriv ℝ M.length g y (fun j => Pi.single (M.get j) (1 : ℝ))‖ ≤ 1 := by
    have hle := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ M.length g y)
      (fun j : Fin M.length => (Pi.single (M.get j) (1 : ℝ) : Fin n → ℝ))
    have hprod : (∏ j : Fin M.length, ‖(Pi.single (M.get j) (1 : ℝ) : Fin n → ℝ)‖) = 1 := by
      simp [Pi.norm_single]
    rw [hprod, mul_one] at hle
    exact hle.trans h
  rw [Real.norm_eq_abs] at h1
  exact h1

end Work.WilG4c
