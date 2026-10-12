import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.farAnisoDefs
import Submission.Work.BoseBoxFock.farK0_summable_lattice_inv_fourth
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped BigOperators

namespace Work.BoseBoxFock

/-- **The uniform (state-independent) bound on the even far-image kernel.**

For `‖u‖ ≤ ℓ` every lattice image `ℓ•latVec m` with `‖latVec m‖ ≥ √2` sits at distance at least
`ℓ(1 − 1/√2)‖latVec m‖` from `u` (reverse triangle plus `√2 ≤ ‖latVec m‖`), so each of the two
translated fourth-inverse-power terms is dominated by
`(ℓ(1 − 1/√2))⁻⁴ ‖latVec m‖⁻⁴`.  Summing the resulting termwise bound against the summable
lattice kernel `(‖latVec m‖⁴)⁻¹` (`farK0_summable_lattice_inv_fourth`) gives the statement. -/
theorem farEven_le_uniformBound {ℓ : ℝ} (hℓ : 0 < ℓ) {u : EuclideanSpace ℝ (Fin 3)}
    (hu : ‖u‖ ≤ ℓ) :
    Work.BoseBoxFock.farEven ℓ u
      ≤ ((ℓ * (1 - (Real.sqrt 2)⁻¹)) ^ 4)⁻¹
          * (∑' m : Fin 3 → ℤ, (‖Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹) := by
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hcpos : 0 < ℓ * (1 - (Real.sqrt 2)⁻¹) :=
    mul_pos hℓ (by have := inv_lt_one_of_one_lt₀ Real.one_lt_sqrt_two; linarith)
  have hC : 0 ≤ ((ℓ * (1 - (Real.sqrt 2)⁻¹)) ^ 4)⁻¹ := inv_nonneg.mpr (pow_nonneg hcpos.le 4)
  have hterm : ∀ m : Fin 3 → ℤ,
      (if Real.sqrt 2 ≤ ‖Work.BoseBoxFock.latVec m‖ then
        (2:ℝ)⁻¹ * ((‖u - ℓ • Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹
          + (‖u + ℓ • Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹) else 0)
        ≤ ((ℓ * (1 - (Real.sqrt 2)⁻¹)) ^ 4)⁻¹ * ((‖Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹) := by
    intro m
    by_cases hm : Real.sqrt 2 ≤ ‖Work.BoseBoxFock.latVec m‖
    · rw [if_pos hm]
      have hNpos : 0 < ‖Work.BoseBoxFock.latVec m‖ := lt_of_lt_of_le hsqrt2pos hm
      have hinv : 1 ≤ (Real.sqrt 2)⁻¹ * ‖Work.BoseBoxFock.latVec m‖ := by
        have h := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hsqrt2pos.le)
        rwa [inv_mul_cancel₀ (ne_of_gt hsqrt2pos)] at h
      have hkey : (1 - (Real.sqrt 2)⁻¹) * ‖Work.BoseBoxFock.latVec m‖
          ≤ ‖Work.BoseBoxFock.latVec m‖ - 1 := by
        have h := sub_le_sub_left hinv ‖Work.BoseBoxFock.latVec m‖
        rw [sub_mul, one_mul]
        exact h
      have hkey2 : ℓ * (1 - (Real.sqrt 2)⁻¹) * ‖Work.BoseBoxFock.latVec m‖
          ≤ ℓ * (‖Work.BoseBoxFock.latVec m‖ - 1) := by
        have h := mul_le_mul_of_nonneg_left hkey hℓ.le
        rw [mul_assoc]
        exact h
      have hsmul : ‖ℓ • Work.BoseBoxFock.latVec m‖ = ℓ * ‖Work.BoseBoxFock.latVec m‖ := by
        rw [norm_smul, Real.norm_of_nonneg hℓ.le]
      have hcomm : ‖ℓ • Work.BoseBoxFock.latVec m + u‖
          = ‖u + ℓ • Work.BoseBoxFock.latVec m‖ := by rw [add_comm]
      have hA : ℓ * (1 - (Real.sqrt 2)⁻¹) * ‖Work.BoseBoxFock.latVec m‖
          ≤ ‖u - ℓ • Work.BoseBoxFock.latVec m‖ := by
        have h1 : ℓ * ‖Work.BoseBoxFock.latVec m‖ - ‖u‖
            ≤ ‖u - ℓ • Work.BoseBoxFock.latVec m‖ := by
          have h := norm_sub_norm_le (ℓ • Work.BoseBoxFock.latVec m) u
          rwa [norm_sub_rev (ℓ • Work.BoseBoxFock.latVec m) u, hsmul] at h
        calc ℓ * (1 - (Real.sqrt 2)⁻¹) * ‖Work.BoseBoxFock.latVec m‖
            ≤ ℓ * (‖Work.BoseBoxFock.latVec m‖ - 1) := hkey2
          _ = ℓ * ‖Work.BoseBoxFock.latVec m‖ - ℓ := by ring
          _ ≤ ℓ * ‖Work.BoseBoxFock.latVec m‖ - ‖u‖ := by linarith [hu]
          _ ≤ ‖u - ℓ • Work.BoseBoxFock.latVec m‖ := h1
      have hB : ℓ * (1 - (Real.sqrt 2)⁻¹) * ‖Work.BoseBoxFock.latVec m‖
          ≤ ‖u + ℓ • Work.BoseBoxFock.latVec m‖ := by
        have h1 : ℓ * ‖Work.BoseBoxFock.latVec m‖ - ‖u‖
            ≤ ‖u + ℓ • Work.BoseBoxFock.latVec m‖ := by
          have h := norm_sub_norm_le (ℓ • Work.BoseBoxFock.latVec m) (-u)
          rw [norm_neg] at h
          rw [sub_neg_eq_add] at h
          rwa [hsmul, hcomm] at h
        calc ℓ * (1 - (Real.sqrt 2)⁻¹) * ‖Work.BoseBoxFock.latVec m‖
            ≤ ℓ * (‖Work.BoseBoxFock.latVec m‖ - 1) := hkey2
          _ = ℓ * ‖Work.BoseBoxFock.latVec m‖ - ℓ := by ring
          _ ≤ ℓ * ‖Work.BoseBoxFock.latVec m‖ - ‖u‖ := by linarith [hu]
          _ ≤ ‖u + ℓ • Work.BoseBoxFock.latVec m‖ := h1
      have hq : ((ℓ * (1 - (Real.sqrt 2)⁻¹) * ‖Work.BoseBoxFock.latVec m‖) ^ 4)⁻¹
          = ((ℓ * (1 - (Real.sqrt 2)⁻¹)) ^ 4)⁻¹
              * ((‖Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹) := by
        rw [mul_pow, mul_inv]
      have hbA : (‖u - ℓ • Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹
          ≤ ((ℓ * (1 - (Real.sqrt 2)⁻¹)) ^ 4)⁻¹ * ((‖Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹) := by
        rw [← hq]
        exact (inv_le_inv₀ (pow_pos (lt_of_lt_of_le (mul_pos hcpos hNpos) hA) 4)
          (pow_pos (mul_pos hcpos hNpos) 4)).mpr (pow_le_pow_left₀ (mul_pos hcpos hNpos).le hA 4)
      have hbB : (‖u + ℓ • Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹
          ≤ ((ℓ * (1 - (Real.sqrt 2)⁻¹)) ^ 4)⁻¹ * ((‖Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹) := by
        rw [← hq]
        exact (inv_le_inv₀ (pow_pos (lt_of_lt_of_le (mul_pos hcpos hNpos) hB) 4)
          (pow_pos (mul_pos hcpos hNpos) 4)).mpr (pow_le_pow_left₀ (mul_pos hcpos hNpos).le hB 4)
      have := add_le_add hbA hbB
      linarith [this]
    · rw [if_neg hm]
      exact mul_nonneg hC (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) 4))
  have hsum : Summable fun m : Fin 3 → ℤ => ((‖Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹) :=
    Work.BoseBoxFock.farK0_summable_lattice_inv_fourth
  have hbdd : Summable fun m : Fin 3 → ℤ =>
      ((ℓ * (1 - (Real.sqrt 2)⁻¹)) ^ 4)⁻¹ * ((‖Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹) :=
    hsum.mul_left _
  have hsum2 : Summable fun m : Fin 3 → ℤ =>
      (if Real.sqrt 2 ≤ ‖Work.BoseBoxFock.latVec m‖ then
        (2:ℝ)⁻¹ * ((‖u - ℓ • Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹
          + (‖u + ℓ • Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹) else 0) := by
    refine Summable.of_nonneg_of_le (fun m => ?_) hterm hbdd
    by_cases hm : Real.sqrt 2 ≤ ‖Work.BoseBoxFock.latVec m‖
    · rw [if_pos hm]
      exact mul_nonneg (by norm_num) (add_nonneg (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) 4))
        (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) 4)))
    · rw [if_neg hm]
  have hle := Summable.tsum_le_tsum hterm hsum2 hbdd
  simp only [Work.BoseBoxFock.farEven]
  calc ∑' m : Fin 3 → ℤ, (if Real.sqrt 2 ≤ ‖Work.BoseBoxFock.latVec m‖ then
        (2:ℝ)⁻¹ * ((‖u - ℓ • Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹
          + (‖u + ℓ • Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹) else 0)
      ≤ ∑' m : Fin 3 → ℤ,
          ((ℓ * (1 - (Real.sqrt 2)⁻¹)) ^ 4)⁻¹ * ((‖Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹) := hle
    _ = ((ℓ * (1 - (Real.sqrt 2)⁻¹)) ^ 4)⁻¹
          * (∑' m : Fin 3 → ℤ, ((‖Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹)) := tsum_mul_left

end Work.BoseBoxFock
