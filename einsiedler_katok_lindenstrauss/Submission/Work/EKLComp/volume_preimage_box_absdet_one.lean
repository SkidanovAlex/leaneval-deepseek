import Mathlib

namespace Work.EKLComp

open MeasureTheory Matrix

/-- For a matrix `M` with `|det M| = 1`, the Lebesgue measure of the preimage of a box
`∏ i [-(a i), a i]` under the linear map `Matrix.toLin' M` equals the volume `∏ i 2*(a i)`
of the box itself, since such a linear map preserves Lebesgue measure. -/
theorem volume_preimage_box_absdet_one (M : Matrix (Fin 3) (Fin 3) ℝ) (hdet : |M.det| = 1)
    (a : Fin 3 → ℝ) :
    MeasureTheory.volume ((Matrix.toLin' M) ⁻¹' (Set.pi Set.univ (fun i => Set.Icc (-(a i)) (a i))))
      = ∏ i, ENNReal.ofReal (2 * (a i)) := by
  -- `det M ≠ 0` because `|det M| = 1`, so `Matrix.toLin' M` is invertible.
  have hdetne : M.det ≠ 0 := by
    intro h; rw [h, abs_zero] at hdet; norm_num at hdet
  -- The linear map `Matrix.toLin' M` preserves Lebesgue measure as `|det M| = 1`.
  have hmap : Measure.map (Matrix.toLin' M) volume = volume := by
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdetne]
    have h1 : ENNReal.ofReal |M.det⁻¹| = 1 := by rw [abs_inv, hdet]; norm_num
    rw [h1, one_smul]
  -- The volume of the box is the product of the lengths of its sides.
  have hbox : MeasureTheory.volume (Set.pi Set.univ (fun i => Set.Icc (-(a i)) (a i)))
      = ∏ i, ENNReal.ofReal (2 * (a i)) := by
    rw [Set.pi_univ_Icc]
    rw [Real.volume_Icc_pi]
    congr 1 with i
    ring_nf
  have hboxmeas : MeasurableSet (Set.pi Set.univ (fun i => Set.Icc (-(a i)) (a i))) :=
    MeasurableSet.univ_pi (fun i => measurableSet_Icc)
  have hfmeas : Measurable (Matrix.toLin' M) :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable
  -- Preimages under a measure-preserving map have the same measure.
  have key : Measure.map (Matrix.toLin' M) volume
      (Set.pi Set.univ (fun i => Set.Icc (-(a i)) (a i)))
      = volume (Set.pi Set.univ (fun i => Set.Icc (-(a i)) (a i))) := by rw [hmap]
  rw [Measure.map_apply hfmeas hboxmeas] at key
  rw [key, hbox]

end Work.EKLComp
