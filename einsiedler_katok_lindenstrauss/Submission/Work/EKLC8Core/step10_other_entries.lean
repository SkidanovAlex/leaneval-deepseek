import Mathlib
import Submission.Work.EKLC8Core.Vol
import Submission.Work.EKLC8Core.shearMat_entries

namespace Work.EKLC8Core

theorem step10_other_entries {ρ δ κ : ℝ} {G : Matrix (Fin 3) (Fin 3) ℝ} {r : ℝ}
    (hρ0 : 0 < ρ) (hκ : 0 < κ) (hκκ : kappa G = κ)
    (hd0 : |G 0 0 - 1| ≤ δ) (hd1 : |G 1 1 - 1| ≤ δ) (hd2 : |G 2 2 - 1| ≤ δ)
    (h2 : |G 1 0 * r| ≤ (ρ⁻¹) ^ 5 * κ) :
    |(shearMat G r) 1 0| ≤ κ ^ 2 ∧ |(shearMat G r) 1 2| ≤ κ ∧ |(shearMat G r) 2 0| ≤ κ ∧
    |(shearMat G r) 0 0 - 1| ≤ δ + (ρ⁻¹) ^ 5 * κ ∧
    |(shearMat G r) 1 1 - 1| ≤ δ + (ρ⁻¹) ^ 5 * κ ∧
    |(shearMat G r) 2 2 - 1| ≤ δ := by
  have hκU : kappaU G ≤ κ := by rw [← hκκ]; exact le_max_right _ _
  have hsqrt : Real.sqrt |G 1 0| ≤ κ := le_trans (le_max_left _ _) hκU
  have h20 : |G 2 0| ≤ κ :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hκU
  have h12 : |G 1 2| ≤ κ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hκU
  have h10 : |G 1 0| ≤ κ ^ 2 := by
    calc |G 1 0| = (Real.sqrt |G 1 0|) ^ 2 := (Real.sq_sqrt (abs_nonneg _)).symm
      _ ≤ κ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
  have e10 : (shearMat G r) 1 0 = G 1 0 := by rw [shearMat_entries]; simp
  have e12 : (shearMat G r) 1 2 = G 1 2 := by rw [shearMat_entries]; simp
  have e20 : (shearMat G r) 2 0 = G 2 0 := by rw [shearMat_entries]; simp
  have e00 : (shearMat G r) 0 0 = G 0 0 + G 1 0 * r := by rw [shearMat_entries]; simp
  have e11 : (shearMat G r) 1 1 = G 1 1 - G 1 0 * r := by rw [shearMat_entries]; simp
  have e22 : (shearMat G r) 2 2 = G 2 2 := by rw [shearMat_entries]; simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e10]; exact h10
  · rw [e12]; exact h12
  · rw [e20]; exact h20
  · rw [e00]
    calc |G 0 0 + G 1 0 * r - 1| = |(G 0 0 - 1) + G 1 0 * r| := by congr 1; ring
      _ ≤ |G 0 0 - 1| + |G 1 0 * r| := abs_add_le _ _
      _ ≤ δ + (ρ⁻¹) ^ 5 * κ := add_le_add hd0 h2
  · rw [e11]
    calc |G 1 1 - G 1 0 * r - 1| = |(G 1 1 - 1) + (-(G 1 0 * r))| := by congr 1; ring
      _ ≤ |G 1 1 - 1| + |-(G 1 0 * r)| := abs_add_le _ _
      _ = |G 1 1 - 1| + |G 1 0 * r| := by rw [abs_neg]
      _ ≤ δ + (ρ⁻¹) ^ 5 * κ := add_le_add hd1 h2
  · rw [e22]; exact hd2

end Work.EKLC8Core
