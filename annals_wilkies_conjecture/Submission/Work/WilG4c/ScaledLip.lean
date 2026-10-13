import Mathlib
import Submission.Work.WilG4c.LipDefs

namespace Work.WilG4c

theorem ScaledLip {k p n : ℕ} (K : ℕ) (hK : 1 ≤ K) (q : Fin n → ℝ) (C : ℝ)
    (hCK : C ≤ (K : ℝ)) (F : Work.WilkG4c.Family k p n) (hLip : Work.WilkG4c.LipOnCube F C)
    (z z' : Fin n → ℝ)
    (hz : (fun i => q i + z i / (K : ℝ)) ∈ WilkiesDesign.openCube n)
    (hz' : (fun i => q i + z' i / (K : ℝ)) ∈ WilkiesDesign.openCube n) (i : Fin k)
    (l : Fin p → ℝ) :
    |F i l (fun i => q i + z i / (K : ℝ)) - F i l (fun i => q i + z' i / (K : ℝ))| ≤
      dist z z' := by
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  -- The rescaling `z ↦ q + z/K` contracts distances by the factor `(K:ℝ)⁻¹`.
  have hdist : dist (fun i => q i + z i / (K : ℝ)) (fun i => q i + z' i / (K : ℝ))
      = dist z z' / (K : ℝ) := by
    have h1 : (fun i => q i + z i / (K : ℝ)) - (fun i => q i + z' i / (K : ℝ))
        = (K : ℝ)⁻¹ • (z - z') := by
      ext i; simp [div_eq_inv_mul, smul_eq_mul]; ring
    rw [dist_eq_norm, dist_eq_norm, h1, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hKpos)]
    rw [div_eq_mul_inv, mul_comm]
  calc |F i l (fun i => q i + z i / (K : ℝ)) - F i l (fun i => q i + z' i / (K : ℝ))|
      ≤ C * dist (fun i => q i + z i / (K : ℝ)) (fun i => q i + z' i / (K : ℝ)) :=
        hLip i l _ _ hz hz'
    _ = C * (dist z z' / (K : ℝ)) := by rw [hdist]
    _ ≤ dist z z' := by
        have hCK' : C / (K : ℝ) ≤ 1 := (div_le_one hKpos).mpr hCK
        calc C * (dist z z' / (K : ℝ)) = (C / (K : ℝ)) * dist z z' := by ring
          _ ≤ 1 * dist z z' := mul_le_mul_of_nonneg_right hCK' dist_nonneg
          _ = dist z z' := one_mul _

end Work.WilG4c
