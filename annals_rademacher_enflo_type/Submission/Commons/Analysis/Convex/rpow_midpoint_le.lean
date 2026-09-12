import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Set

namespace Commons.Analysis.Convex

theorem rpow_midpoint_le {p x y : ℝ} (hp : 1 ≤ p) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ((x + y) / 2) ^ p ≤ (x ^ p + y ^ p) / 2 := by
  have hf : ConvexOn ℝ (Ici (0 : ℝ)) (fun x : ℝ ↦ x ^ p) := convexOn_rpow hp
  have h := hf.2 (mem_Ici.mpr hx) (mem_Ici.mpr hy)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp [smul_eq_mul] at h
  have hxeq : (2 : ℝ)⁻¹ * x + (2 : ℝ)⁻¹ * y = (x + y) / 2 := by ring
  have hyeq : (2 : ℝ)⁻¹ * x ^ p + (2 : ℝ)⁻¹ * y ^ p = (x ^ p + y ^ p) / 2 := by ring
  rw [hxeq, hyeq] at h
  exact h

end Commons.Analysis.Convex
