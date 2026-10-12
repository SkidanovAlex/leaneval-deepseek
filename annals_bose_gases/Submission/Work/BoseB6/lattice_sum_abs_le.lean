import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseB6.Defs
import Submission.Work.BoseBox.LatticeModel.Estimate
import Submission.Work.BoseBox.bog_model_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB6.lattice_sum_abs_le`

The dimensionless mode lattice sum `latticeSum c n` (mesh `meshD n = 2π/(n+1)`,
`gridD n = (n+1)²` points per coordinate, `lhyR3` summand) approximates the
negative of the Bogoliubov model integral value `lhyValue c`, with the explicit
error `latticeMeshErr c n`:

    |(meshD n)^3 * latticeSum c n + lhyValue c| ≤ latticeMeshErr c n     (c > 0, n ≥ 1).

This is the assembly of the three already-proved ingredients
`Work.BoseBox.cell_error_le` (lattice sum vs. enclosing cube),
`Work.BoseBox.tail_le` (cube vs. full space) and
`Work.BoseBox.bog_model_integral` (value `−lhyValue c` of the full-space integral),
together with the pointwise identification `lhyR3 c x = lhyProfile c (eucNorm3 x)`
of the two forms of the Bogoliubov bracket (`LatticeModel.lhyProfile_basic`).
-/

open MeasureTheory

namespace Work.BoseB6

/-- The dimensionless lattice sum of the Bogoliubov bracket approximates the
negative of the model integral value, with the explicit mesh error. -/
theorem lattice_sum_abs_le {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) :
    |(Work.BoseB6.meshD n) ^ 3 * Work.BoseB6.latticeSum c n + Work.BoseB6.lhyValue c| ≤
      Work.BoseB6.latticeMeshErr c n := by
  have hpb := Work.BoseBox.LatticeModel.lhyProfile_basic hc
  -- The two forms of the bracket (`lhyR3`'s unrationalised form and
  -- `lhyProfile`'s rationalised form) coincide on the nonnegative half-line.
  have hpoint : ∀ x : Fin 3 → ℝ,
      lhyR3 c x = Work.BoseBox.lhyProfile c (Submission.BoseGases.eucNorm3 x) :=
    fun x => (hpb.1 _ (Submission.BoseGases.eucNorm3_nonneg x)).symm
  have hmeshD : meshD n = Work.BoseBox.mesh n := rfl
  have hsum_eq : latticeSum c n = ∑ k : Fin 3 → Fin (Work.BoseBox.gridN n),
      Work.BoseBox.lhyProfile c (Submission.BoseGases.eucNorm3
        (Work.BoseBox.latticeCenter (Work.BoseBox.mesh n) (Work.BoseBox.gridN n) k)) := by
    simp only [latticeSum, meshD, Work.BoseBox.mesh, gridD, Work.BoseBox.gridN]
    exact Finset.sum_congr rfl fun k _ => hpoint _
  have herr_eq : latticeMeshErr c n = Work.BoseBox.latticeErr c n := by
    simp only [latticeMeshErr, Work.BoseBox.latticeErr, meshD, Work.BoseBox.mesh,
      gridD, Work.BoseBox.gridN]
  -- The full-space integral of the bracket is `−lhyValue c`
  -- (`bog_model_integral`, transported along the measure-preserving
  -- identification `Fin 3 → ℝ ≃ EuclideanSpace ℝ (Fin 3)`).
  have hint : (∫ x : Fin 3 → ℝ, Work.BoseBox.lhyProfile c (Submission.BoseGases.eucNorm3 x))
      = - lhyValue c := by
    have hmp : MeasurePreserving
        (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) volume volume :=
      PiLp.volume_preserving_toLp (Fin 3)
    have h1 : (∫ x : Fin 3 → ℝ, Work.BoseBox.lhyProfile c (Submission.BoseGases.eucNorm3 x))
        = ∫ y : EuclideanSpace ℝ (Fin 3), Work.BoseBox.lhyProfile c ‖y‖ := by
      rw [← hmp.integral_comp (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
        (fun y : EuclideanSpace ℝ (Fin 3) => Work.BoseBox.lhyProfile c ‖y‖)]
      apply integral_congr_ae
      filter_upwards with x
      rw [Work.BoseBox.eucNorm3_eq_norm]
    rw [h1]
    have h2 : (∫ y : EuclideanSpace ℝ (Fin 3), Work.BoseBox.lhyProfile c ‖y‖)
        = ∫ y : EuclideanSpace ℝ (Fin 3),
            ((‖y‖ ^ 2 + c) - Real.sqrt ((‖y‖ ^ 2 + c) ^ 2 - c ^ 2) - c ^ 2 / (2 * ‖y‖ ^ 2)) := by
      apply integral_congr_ae
      filter_upwards with y
      exact hpb.1 ‖y‖ (norm_nonneg y)
    rw [h2, Work.BoseBox.bog_model_integral hc]
    unfold lhyValue
    ring
  rw [hmeshD, hsum_eq, herr_eq]
  -- Split the lattice/continuum difference through the enclosing cube.
  have hkey : (Work.BoseBox.mesh n) ^ 3 * (∑ k : Fin 3 → Fin (Work.BoseBox.gridN n),
        Work.BoseBox.lhyProfile c (Submission.BoseGases.eucNorm3
          (Work.BoseBox.latticeCenter (Work.BoseBox.mesh n) (Work.BoseBox.gridN n) k))) + lhyValue c
      = ((Work.BoseBox.mesh n) ^ 3 * (∑ k : Fin 3 → Fin (Work.BoseBox.gridN n),
            Work.BoseBox.lhyProfile c (Submission.BoseGases.eucNorm3
              (Work.BoseBox.latticeCenter (Work.BoseBox.mesh n) (Work.BoseBox.gridN n) k)))
          - ∫ x in Work.BoseBox.latticeBox (Work.BoseBox.mesh n) (Work.BoseBox.gridN n),
              Work.BoseBox.lhyProfile c (Submission.BoseGases.eucNorm3 x))
        + ((∫ x in Work.BoseBox.latticeBox (Work.BoseBox.mesh n) (Work.BoseBox.gridN n),
              Work.BoseBox.lhyProfile c (Submission.BoseGases.eucNorm3 x))
            - ∫ x : Fin 3 → ℝ, Work.BoseBox.lhyProfile c (Submission.BoseGases.eucNorm3 x)) := by
    rw [hint]; ring
  rw [hkey]
  refine le_trans (abs_add_le _ _) ?_
  rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]
  have h1 := Work.BoseBox.cell_error_le (c := c) hc hn
  have h2 := Work.BoseBox.tail_le (c := c) hc hn
  unfold Work.BoseBox.latticeErr
  linarith

end Work.BoseB6
