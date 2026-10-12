import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.exists_chiLam_zero`

A set of positive volume on which FS's localization function `χ_Λ` vanishes while the box
function `θ = 1_Λ` equals one.

The corpus χ (`Submission.BoseGases.chi`, presented as `Work.BoseK15.corpusBox`) is supported
in the **ball** of radius `1/2`, whereas the unit cell is the cube `[-1/2,1/2]³`: the extra
corners of the cube of volume `(√3/2)³ − (4π/3)(1/2)³ > 0` are exactly what we want.  For a
box side `ℓ > 0` we therefore take the product box

  `B = (3ℓ/10, 49ℓ/100)³ ⊆ Λ(ℓ) = ℓ • unitCell`,

a piece of the corner region: on `B` the rescaled point `ℓ⁻¹ • y` has all coordinates in
`(3/10, 49/100)`, hence on the one hand lies in the unit cube (so `θ(y) = 1`) and on the other
has norm `≥ √3·3/10 > 1/2` (so `χ_Λ(y) = χ(ℓ⁻¹ • y) = 0`).
Its volume is `(49/100 − 3/10)³ ℓ³ = (19ℓ/100)³ > 0`.
-/

open scoped Pointwise
open MeasureTheory

namespace Work.BoseBoxFock

/-- The candidate set: the product box `(3ℓ/10, 49ℓ/100)³` in coordinates. -/
private def chiFreeBox (ℓ : ℝ) : Set ℝ³ := {y | ∀ i, 3 / 10 * ℓ < y i ∧ y i < 49 / 100 * ℓ}

private lemma measurableSet_chiFreeBox (ℓ : ℝ) : MeasurableSet (chiFreeBox ℓ) := by
  have heq : chiFreeBox ℓ
      = ⋂ i : Fin 3, ({y : ℝ³ | 3 / 10 * ℓ < y i} ∩ {y : ℝ³ | y i < 49 / 100 * ℓ}) := by
    ext y
    simp only [chiFreeBox, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [heq]
  refine MeasurableSet.iInter fun i => ?_
  have hcont : Continuous (fun y : ℝ³ => y i) := PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i
  exact (measurableSet_lt measurable_const hcont.measurable).inter
    (measurableSet_lt hcont.measurable measurable_const)

private lemma volume_chiFreeBox (ℓ : ℝ) (hℓ : 0 < ℓ) :
    0 < (volume (chiFreeBox ℓ)).toReal := by
  have hC : MeasurableSet (Set.pi Set.univ
      (fun _ : Fin 3 => Set.Ioo (3 / 10 * ℓ) (49 / 100 * ℓ))) :=
    MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)
  have hpre : chiFreeBox ℓ
      = (WithLp.ofLp : ℝ³ → (Fin 3 → ℝ)) ⁻¹'
          (Set.pi Set.univ (fun _ : Fin 3 => Set.Ioo (3 / 10 * ℓ) (49 / 100 * ℓ))) := by
    ext y
    simp only [chiFreeBox, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Ioo]
  rw [hpre]
  rw [MeasurePreserving.measure_preimage (PiLp.volume_preserving_ofLp (Fin 3))
    hC.nullMeasurableSet]
  rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
  simp only [Real.volume_Ioo, Finset.prod_const, Finset.card_fin]
  rw [← ENNReal.ofReal_pow (by linarith : (0 : ℝ) ≤ 49 / 100 * ℓ - 3 / 10 * ℓ)]
  rw [ENNReal.toReal_ofReal
    (pow_nonneg (by linarith : (0 : ℝ) ≤ 49 / 100 * ℓ - 3 / 10 * ℓ) 3)]
  exact pow_pos (by linarith) 3

/-- The rescaled coordinates of a point of `chiFreeBox ℓ` lie in `(3/10, 49/100)`. -/
private lemma chiFreeBox_coords (ℓ : ℝ) (hℓ : 0 < ℓ) {y : ℝ³} (hy : y ∈ chiFreeBox ℓ) :
    ∀ i, (3 : ℝ) / 10 < (ℓ⁻¹ • y) i ∧ (ℓ⁻¹ • y) i < 49 / 100 := by
  intro i
  obtain ⟨h1, h2⟩ := hy i
  rw [PiLp.smul_apply, smul_eq_mul]
  constructor
  · have h := mul_lt_mul_of_pos_left h1 (inv_pos.mpr hℓ)
    have h3 : ℓ⁻¹ * (3 / 10 * ℓ) = (3 : ℝ) / 10 := by field_simp
    linarith
  · have h := mul_lt_mul_of_pos_left h2 (inv_pos.mpr hℓ)
    have h3 : ℓ⁻¹ * (49 / 100 * ℓ) = (49 : ℝ) / 100 := by field_simp
    linarith

private lemma chiFreeBox_chiLam (ℓ : ℝ) (hℓ : 0 < ℓ) {y : ℝ³} (hy : y ∈ chiFreeBox ℓ) :
    Work.BoseK15.corpusBox.chiLam ℓ y = 0 := by
  have hkey := chiFreeBox_coords ℓ hℓ hy
  rw [Work.BoseB4.BoxData.chiLam_apply, Work.BoseK15.corpusBox_chi]
  refine Submission.BoseGases.chi_eq_zero_of_norm_gt _ ?_
  have hsq : (1 / 2 : ℝ) ^ 2 < ‖ℓ⁻¹ • y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
      _ < ∑ _i : Fin 3, ((3 : ℝ) / 10) ^ 2 := by
            simp [Finset.sum_const, Fintype.card_fin]; norm_num
      _ < ∑ i : Fin 3, ‖(ℓ⁻¹ • y).ofLp i‖ ^ 2 := by
          apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          intro i _
          have h1 := (hkey i).1
          have h0 : (0 : ℝ) < (ℓ⁻¹ • y) i := by linarith
          rw [Real.norm_eq_abs, abs_of_pos h0]
          exact pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have h := sq_lt_sq.mp hsq
  simpa [abs_of_nonneg (norm_nonneg _)] using h

private lemma chiFreeBox_thetaFun (ℓ : ℝ) (hℓ : 0 < ℓ) {y : ℝ³} (hy : y ∈ chiFreeBox ℓ) :
    Work.BoseK15.corpusBox.thetaFun ℓ y = 1 := by
  have hkey := chiFreeBox_coords ℓ hℓ hy
  have hmem : ℓ⁻¹ • y ∈ Work.BoseK15.corpusBox.cell := by
    rw [show Work.BoseK15.corpusBox.cell = Work.BoseB4.unitCell from rfl]
    intro i
    have h := hkey i
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  have hboxL : y ∈ Work.BoseK15.corpusBox.boxL ℓ := by
    show y ∈ ℓ • Work.BoseK15.corpusBox.cell
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hℓ)]
    exact hmem
  rw [Work.BoseB4.BoxData.thetaFun_apply, if_pos hboxL]

theorem exists_chiLam_zero (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ∃ B : Set ℝ³, MeasurableSet B ∧ 0 < (MeasureTheory.volume B).toReal ∧
      (∀ y ∈ B, Work.BoseK15.corpusBox.chiLam ℓ y = 0) ∧
      (∀ y ∈ B, Work.BoseK15.corpusBox.thetaFun ℓ y = 1) :=
  ⟨chiFreeBox ℓ, measurableSet_chiFreeBox ℓ, volume_chiFreeBox ℓ hℓ,
    fun _ hy => chiFreeBox_chiLam ℓ hℓ hy, fun _ hy => chiFreeBox_thetaFun ℓ hℓ hy⟩

end Work.BoseBoxFock
