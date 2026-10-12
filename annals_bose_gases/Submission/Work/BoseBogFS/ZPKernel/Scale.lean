import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseRowsL.LatticeCoulomb.cellSumVsIntegral
import Submission.Work.BoseRowsL.LatticeCoulomb.kernelBoundsCore
import Submission.Work.BoseRowsL.LatticeCoulomb.latToolbox
import Submission.Work.BoseRowsL.LatticeCoulomb.latticeCellExpand
import Submission.Work.BoseRowsL.LatticeCoulomb.reduction_core
import Submission.Work.BoseRowsL.LatticeCoulomb.telescopeCos
import Submission.Work.BoseRowsL.LatticeCoulomb.telescopeInner
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.ZPKernel.Scale`

The `ℓ`-scaling identity of the lattice-Coulomb kernel: the normalised kernel `kcal` of
`Submission.Work.BoseRowsL.LatticeCoulomb.latticeCoulomb_approx` is `(ℓ²/8π²)` times the
*unit-lattice* kernel (`Σ cos(2π⟪n,z⟫)/‖n‖² − ∫_{‖q‖≤R} cos(2π⟪q,z⟫)/‖q‖²dq`) at the
rescaled truncation radius `R = Kℓ/(2π)` and the rescaled position `z = ℓ⁻¹ • w`.
-/

noncomputable section
open scoped Real BigOperators Topology Pointwise
open MeasureTheory Metric

namespace Work.BoseBogFS

set_option autoImplicit false

/-- The pointwise summand identity of `kcalScale`. -/
theorem kcalScale_term (n : Fin 3 → ℤ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (w : Work.BoseRowsL.LatticeCoulomb.E3) :
    Real.cos (inner ℝ (ℓ⁻¹ • Work.BoseB4.vec n) w) / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2)
      = (ℓ ^ 2 / (8 * Real.pi ^ 2))
          * (Real.cos (2 * Real.pi * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n)
                (ℓ⁻¹ • w)) / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 2) := by
  have hvec : ℓ⁻¹ • Work.BoseB4.vec n
      = (2 * Real.pi * ℓ⁻¹) • Work.BoseRowsL.LatticeCoulomb.nvec n := by
    rw [Work.BoseRowsL.LatticeCoulomb.vec_eq_smul_nvec, smul_smul]
    congr 1; ring
  have hinner : inner ℝ (ℓ⁻¹ • Work.BoseB4.vec n) w
      = 2 * Real.pi * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) (ℓ⁻¹ • w) := by
    rw [hvec, real_inner_smul_left, real_inner_smul_right]
    ring
  have hnorm : 2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2
      = (8 * Real.pi ^ 2 / ℓ ^ 2) * ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 2 := by
    rw [hvec, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    ring
  rw [hinner, div_eq_mul_inv, div_eq_mul_inv, hnorm, mul_inv, inv_div]
  ring

/-- **The ball-integral rescaling.** -/
theorem kcalScale_int {ℓ K : ℝ} (hℓ : 0 < ℓ) (hK : 0 ≤ K)
    (w : Work.BoseRowsL.LatticeCoulomb.E3) :
    (∫ p in Metric.closedBall 0 K, Real.cos (inner ℝ p w) / (2 * ‖p‖ ^ 2))
      = (2 * Real.pi / ℓ) / 2 *
          ∫ q in Metric.closedBall 0 (K * ℓ / (2 * Real.pi)),
            Real.cos (2 * Real.pi * inner ℝ q (ℓ⁻¹ • w)) / ‖q‖ ^ 2 := by
  set Rc : ℝ := 2 * Real.pi / ℓ with hRc
  have hRcpos : 0 < Rc := by rw [hRc]; positivity
  have hsub := MeasureTheory.Measure.setIntegral_comp_smul_of_pos
    (volume : Measure Work.BoseRowsL.LatticeCoulomb.E3)
    (f := fun p : Work.BoseRowsL.LatticeCoulomb.E3 =>
      Real.cos (inner ℝ p w) / (2 * ‖p‖ ^ 2))
    (s := Metric.closedBall 0 (K * ℓ / (2 * Real.pi))) hRcpos
  have hball : Rc • Metric.closedBall (0 : Work.BoseRowsL.LatticeCoulomb.E3)
        (K * ℓ / (2 * Real.pi)) = Metric.closedBall 0 K := by
    rw [smul_closedBall Rc 0 (by positivity : (0:ℝ) ≤ K * ℓ / (2 * Real.pi))]
    congr 1
    · simp
    · rw [Real.norm_of_nonneg hRcpos.le, hRc]
      field_simp
  rw [hball] at hsub
  have hfin : (Module.finrank ℝ Work.BoseRowsL.LatticeCoulomb.E3 : ℕ) = 3 := by
    rw [finrank_euclideanSpace_fin]
  have hkey : (∫ x in Metric.closedBall 0 (K * ℓ / (2 * Real.pi)),
        Real.cos (inner ℝ (Rc • x) w) / (2 * ‖Rc • x‖ ^ 2)) * Rc ^ 3
      = ∫ p in Metric.closedBall 0 K, Real.cos (inner ℝ p w) / (2 * ‖p‖ ^ 2) := by
    rw [hsub, hfin]
    simp only [smul_eq_mul]
    field_simp
  rw [← hkey]
  have hpt : ∀ x : Work.BoseRowsL.LatticeCoulomb.E3,
      Real.cos (inner ℝ (Rc • x) w) / (2 * ‖Rc • x‖ ^ 2)
        = (1 / (2 * Rc ^ 2))
          * (Real.cos (2 * Real.pi * inner ℝ x (ℓ⁻¹ • w)) / ‖x‖ ^ 2) := by
    intro x
    have hinner : inner ℝ (Rc • x) w = 2 * Real.pi * inner ℝ x (ℓ⁻¹ • w) := by
      rw [real_inner_smul_left, real_inner_smul_right, hRc]
      ring
    have hnorm : 2 * ‖Rc • x‖ ^ 2 = (2 * Rc ^ 2) * ‖x‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hRcpos.le]
      ring
    rw [hinner, show (2:ℝ) * ‖Rc • x‖ ^ 2 = (2 * Rc ^ 2) * ‖x‖ ^ 2 from hnorm]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hint : (∫ x in Metric.closedBall 0 (K * ℓ / (2 * Real.pi)),
        Real.cos (inner ℝ (Rc • x) w) / (2 * ‖Rc • x‖ ^ 2))
      = (1 / (2 * Rc ^ 2))
        * ∫ x in Metric.closedBall 0 (K * ℓ / (2 * Real.pi)),
            Real.cos (2 * Real.pi * inner ℝ x (ℓ⁻¹ • w)) / ‖x‖ ^ 2 := by
    rw [show (∫ x in Metric.closedBall 0 (K * ℓ / (2 * Real.pi)),
        Real.cos (inner ℝ (Rc • x) w) / (2 * ‖Rc • x‖ ^ 2))
      = ∫ x in Metric.closedBall 0 (K * ℓ / (2 * Real.pi)),
          (1 / (2 * Rc ^ 2))
            * (Real.cos (2 * Real.pi * inner ℝ x (ℓ⁻¹ • w)) / ‖x‖ ^ 2)
        from setIntegral_congr_fun measurableSet_closedBall (fun x _ => hpt x)]
    rw [integral_const_mul]
  rw [hint]
  field_simp

/-- **The `ℓ`-scaling identity of the lattice-Coulomb kernel.** -/
theorem kcalScale (T : Finset (Fin 3 → ℤ)) {ℓ K : ℝ} (hℓ : 0 < ℓ) (hK : 0 ≤ K)
    (w : Work.BoseRowsL.LatticeCoulomb.E3) :
    Work.BoseRowsL.LatticeCoulomb.kcal T ℓ K w
      = (ℓ ^ 2 / (8 * Real.pi ^ 2)) *
          ((∑ n ∈ T, Real.cos (2 * Real.pi
                * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) (ℓ⁻¹ • w))
              / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 2)
            - ∫ q in Metric.closedBall 0 (K * ℓ / (2 * Real.pi)),
                Real.cos (2 * Real.pi * inner ℝ q (ℓ⁻¹ • w)) / ‖q‖ ^ 2) := by
  rw [Work.BoseRowsL.LatticeCoulomb.kcal,
    Finset.sum_congr rfl (fun n _ => kcalScale_term n hℓ w),
    ← Finset.mul_sum, kcalScale_int hℓ hK w]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end Work.BoseBogFS
