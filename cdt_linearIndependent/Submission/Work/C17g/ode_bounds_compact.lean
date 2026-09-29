import Mathlib

namespace Work.C17g

open Finset

/-- Uniform bounds on a compact set `T` for a continuous matrix-valued coefficient `A` and
inhomogeneity `b`: the family of linear maps `x ↦ A z x` is uniformly bounded on `T` by a constant
`M` (in operator norm), the affine term `A z Y₀ + b z` is uniformly bounded by `C₀`, and `T` is
contained in the closed ball of radius `R` about `z₀`. -/
theorem ode_bounds_compact {k : ℕ} (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ) (z₀ : ℂ)
    (Y₀ : Fin k → ℂ) {T : Set ℂ} (hT : IsCompact T) (hne : T.Nonempty)
    (hAc : ∀ i j, ContinuousOn (fun z => A z i j) T) (hbc : ∀ i, ContinuousOn (fun z => b z i) T) :
    ∃ M C₀ R : ℝ, 0 ≤ M ∧ 0 ≤ C₀ ∧ (∀ z ∈ T, ‖z - z₀‖ ≤ R) ∧
      (∀ z ∈ T, ∀ x : Fin k → ℂ, ‖(fun i => ∑ j, A z i j * x j)‖ ≤ M * ‖x‖) ∧
      (∀ z ∈ T, ‖(fun i => (∑ j, A z i j * Y₀ j) + b z i)‖ ≤ C₀) := by
  have hcontR : ContinuousOn (fun z : ℂ => ‖z - z₀‖) T :=
    (continuousOn_id.sub continuousOn_const).norm
  obtain ⟨zR, hzR, hzRmax⟩ := hT.exists_isMaxOn hne hcontR
  have hcontM : ContinuousOn (fun z : ℂ => ∑ i : Fin k, ∑ j : Fin k, ‖A z i j‖) T := by
    refine continuousOn_finsetSum _ (fun i _ => ?_)
    refine continuousOn_finsetSum _ (fun j _ => ?_)
    exact (hAc i j).norm
  obtain ⟨zM, hzM, hzMmax⟩ := hT.exists_isMaxOn hne hcontM
  have hcontC : ContinuousOn (fun z : ℂ => ∑ i : Fin k, ‖(∑ j : Fin k, A z i j * Y₀ j) + b z i‖) T := by
    refine continuousOn_finsetSum _ (fun i _ => ?_)
    exact ((continuousOn_finsetSum _ (fun j _ => (hAc i j).mul continuousOn_const)).add (hbc i)).norm
  obtain ⟨zC, hzC, hzCmax⟩ := hT.exists_isMaxOn hne hcontC
  have hMnneg : 0 ≤ ∑ i : Fin k, ∑ j : Fin k, ‖A zM i j‖ :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hCnneg : 0 ≤ ∑ i : Fin k, ‖(∑ j : Fin k, A zC i j * Y₀ j) + b zC i‖ :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨∑ i : Fin k, ∑ j : Fin k, ‖A zM i j‖,
          ∑ i : Fin k, ‖(∑ j : Fin k, A zC i j * Y₀ j) + b zC i‖,
          ‖zR - z₀‖, hMnneg, hCnneg, ?_, ?_, ?_⟩
  · intro z hz
    exact hzRmax hz
  · intro z hz x
    have hzle : (∑ i : Fin k, ∑ j : Fin k, ‖A z i j‖) ≤ ∑ i : Fin k, ∑ j : Fin k, ‖A zM i j‖ :=
      hzMmax hz
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg hMnneg (norm_nonneg x))]
    intro i
    calc ‖∑ j : Fin k, A z i j * x j‖
        ≤ ∑ j : Fin k, ‖A z i j * x j‖ := norm_sum_le _ _
      _ = ∑ j : Fin k, ‖A z i j‖ * ‖x j‖ := by simp
      _ ≤ ∑ j : Fin k, ‖A z i j‖ * ‖x‖ := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (norm_nonneg _)
      _ = (∑ j : Fin k, ‖A z i j‖) * ‖x‖ := (Finset.sum_mul _ _ _).symm
      _ ≤ (∑ i : Fin k, ∑ j : Fin k, ‖A z i j‖) * ‖x‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
            exact Finset.single_le_sum
              (fun i' _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i)
      _ ≤ (∑ i : Fin k, ∑ j : Fin k, ‖A zM i j‖) * ‖x‖ :=
            mul_le_mul_of_nonneg_right hzle (norm_nonneg x)
  · intro z hz
    have hzle : (∑ i : Fin k, ‖(∑ j : Fin k, A z i j * Y₀ j) + b z i‖)
        ≤ ∑ i : Fin k, ‖(∑ j : Fin k, A zC i j * Y₀ j) + b zC i‖ := hzCmax hz
    rw [pi_norm_le_iff_of_nonneg hCnneg]
    intro i
    exact (Finset.single_le_sum (f := fun i' => ‖(∑ j : Fin k, A z i' j * Y₀ j) + b z i'‖)
      (fun i' _ => norm_nonneg _) (Finset.mem_univ i)).trans hzle

end Work.C17g
