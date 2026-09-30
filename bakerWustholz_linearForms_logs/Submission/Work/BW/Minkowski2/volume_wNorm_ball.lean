import Mathlib
import Submission.Work.BW.basisRed_defs
import Submission.Work.BW.vol_wl1_ball

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

open MeasureTheory MeasureTheory.Measure Matrix

/-- The volume of the unit ball of the weighted `ℓ¹` norm pulled back along an invertible integer
matrix: `Work.BW.wNorm A c y = ∑ i, c i * |(A y) i| = Work.BW.wl1 c (A y)`, so
`{y | Work.BW.wNorm A c y ≤ 1} = A⁻¹ • {x | Work.BW.wl1 c x ≤ 1}`, and the linear change of
variables `Real.map_matrix_volume_pi_eq_smul_volume_pi` (used in the proof of
`Work.BW.vol_wl1_ball`) divides the volume by `|det A|`.  Note the parentheses: the right-hand
side is `2^n / (n! · (∏ i, c i) · |det A|)` (writing `∏ i, c i * |det A|` without parentheses
would parse as `∏ i, (c i * |det A|)`, which is a different, false statement). -/
theorem volume_wNorm_ball {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) :
    MeasureTheory.volume.real {y : Fin n → ℝ | Work.BW.wNorm A c y ≤ 1} =
      2 ^ n / ((n.factorial : ℝ) * (∏ i, c i) * |((A.det : ℤ) : ℝ)|) := by
  classical
  -- `M` is the real matrix underlying `A`; the map `y ↦ M y` pushes `{wNorm A c ≤ 1}` forward
  -- to the weighted `ℓ¹` ball `{wl1 c ≤ 1}`.
  set M : Matrix (Fin n) (Fin n) ℝ := A.map (Int.castRingHom ℝ) with hM
  have hd : M.det = ((A.det : ℤ) : ℝ) := by
    rw [hM]
    exact (RingHom.map_det (Int.castRingHom ℝ) A).symm
  have hdetM : M.det ≠ 0 := by
    rw [hd]
    exact_mod_cast hA
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (M := M) hdetM
  have hmeas : Measurable (Matrix.toLin' M) :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable
  have hSmeas : MeasurableSet {x : Fin n → ℝ | Work.BW.wl1 c x ≤ 1} := by
    refine (isClosed_le ?_ continuous_const).measurableSet
    show Continuous fun x : Fin n → ℝ => ∑ i, c i * |x i|
    fun_prop
  have hpre : (Matrix.toLin' M) ⁻¹' {x : Fin n → ℝ | Work.BW.wl1 c x ≤ 1}
      = {y : Fin n → ℝ | Work.BW.wNorm A c y ≤ 1} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Matrix.toLin'_apply, hM,
      Work.BW.wNorm, Work.BW.wl1]
  -- change of variables: `volume (toLin' M ⁻¹' S) = |det M|⁻¹ * volume S`.
  rw [MeasureTheory.measureReal_def, ← hpre, ← Measure.map_apply hmeas hSmeas, hmap,
    Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), ← MeasureTheory.measureReal_def,
    Work.BW.vol_wl1_ball c hc]
  rw [abs_inv, hd]
  field_simp

end Work.BW.Minkowski2
