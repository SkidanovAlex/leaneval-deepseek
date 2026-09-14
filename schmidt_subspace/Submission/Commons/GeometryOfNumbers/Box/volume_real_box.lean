import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace Commons.GeometryOfNumbers.Box

open MeasureTheory MeasureTheory.Measure

theorem volume_real_box {N : ℕ} (hN : 1 ≤ N) (M : Matrix (Fin N) (Fin N) ℝ) (hM : M.det ≠ 0)
    (Q : ℝ) (hQ : 0 < Q) (d : Fin N → ℝ) :
    (MeasureTheory.volume {y : Fin N → ℝ | ∀ j, |∑ k, M j k * y k| ≤ Q ^ (d j)}).toReal
      = 2 ^ N * Q ^ (∑ j, d j) / |M.det| := by
  classical
  have _ := hN
  have hdet : LinearMap.det (M.mulVecLin : (Fin N → ℝ) →ₗ[ℝ] Fin N → ℝ) = M.det := by
    have h : (M.mulVecLin : (Fin N → ℝ) →ₗ[ℝ] Fin N → ℝ) = Matrix.toLin' M := by
      rw [Matrix.toLin'_apply']
    rw [h, LinearMap.det_toLin']
  have hdet_ne : LinearMap.det (M.mulVecLin : (Fin N → ℝ) →ₗ[ℝ] Fin N → ℝ) ≠ 0 := by
    rw [hdet]; exact hM
  have hset : {y : Fin N → ℝ | ∀ j, |∑ k, M j k * y k| ≤ Q ^ (d j)}
      = (M.mulVecLin : (Fin N → ℝ) →ₗ[ℝ] Fin N → ℝ) ⁻¹'
          Set.Icc (fun j => -(Q ^ (d j))) (fun j => Q ^ (d j)) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, Pi.le_def]
    constructor
    · intro h
      exact ⟨fun j => (abs_le.mp (h j)).1, fun j => (abs_le.mp (h j)).2⟩
    · intro h j
      exact abs_le.mpr ⟨h.1 j, h.2 j⟩
  have hbox_real : (MeasureTheory.volume
        (Set.Icc (fun j => -(Q ^ (d j))) (fun j => Q ^ (d j))) : ENNReal).toReal
      = 2 ^ N * Q ^ (∑ j, d j) := by
    have hab : (fun j : Fin N => -(Q ^ (d j))) ≤ (fun j : Fin N => Q ^ (d j)) := by
      intro j
      have hp := Real.rpow_pos_of_pos hQ (d j)
      linarith
    rw [Real.volume_Icc_pi_toReal hab]
    have hfac : ∀ j : Fin N, Q ^ (d j) - -(Q ^ (d j)) = 2 * Q ^ (d j) := fun j => by ring
    simp_rw [hfac]
    rw [Finset.prod_mul_distrib]
    congr 1
    · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · rw [← Real.rpow_sum_of_pos hQ d Finset.univ]
  calc (MeasureTheory.volume {y : Fin N → ℝ | ∀ j, |∑ k, M j k * y k| ≤ Q ^ (d j)}).toReal
      = (MeasureTheory.volume ((M.mulVecLin : (Fin N → ℝ) →ₗ[ℝ] Fin N → ℝ) ⁻¹'
          Set.Icc (fun j => -(Q ^ (d j))) (fun j => Q ^ (d j)))).toReal := by rw [hset]
    _ = |(LinearMap.det (M.mulVecLin : (Fin N → ℝ) →ₗ[ℝ] Fin N → ℝ))⁻¹| *
          (MeasureTheory.volume
            (Set.Icc (fun j => -(Q ^ (d j))) (fun j => Q ^ (d j))) : ENNReal).toReal := by
        rw [MeasureTheory.Measure.addHaar_preimage_linearMap (volume : Measure (Fin N → ℝ)) hdet_ne,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
    _ = |(LinearMap.det (M.mulVecLin : (Fin N → ℝ) →ₗ[ℝ] Fin N → ℝ))⁻¹| *
          (2 ^ N * Q ^ (∑ j, d j)) := by rw [hbox_real]
    _ = 2 ^ N * Q ^ (∑ j, d j) / |M.det| := by
        rw [hdet, abs_inv, div_eq_mul_inv]; ring

end Commons.GeometryOfNumbers.Box