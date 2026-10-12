import ChallengeDeps
import Mathlib.Tactic.Have
import Submission.Work.BoseFixR.FarLatDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

namespace Work.BoseFixR.FarLat

open MeasureTheory Metric
open scoped Real BigOperators ENNReal

-- (`ℝ³` is the global notation `EuclideanSpace ℝ (Fin 3)` of `Work.BoseKinLoc.Defs`,
-- which is in the import cone of this file.)

-- imports used below: Submission.ScatT3 (scattering_bounds_ae), Submission.ScatGChosen (chosen_newton_double_eq),
-- Submission.Work.BoseFixR.LatGreen.G0WeightedMoment, Submission.Work.BoseFixR.FarLatDefs
theorem g0_coulPot_lintegral_ae_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin 3),
      (∫⁻ y : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (Submission.BoseGases.g0 v h y * ‖x - y‖⁻¹))
        ≤ ENNReal.ofReal (8 * Real.pi) := by
  classical
  -- The chosen scattering solution `ω := Classical.choose h` and the source `g₀ := g₀ v h = v(1−ω)`.
  have hspec := Classical.choose_spec h
  have hrad : BoseGases.IsRadial (Classical.choose h) := hspec.1
  have hws : BoseGases.IsScatteringSolution (Classical.choose h) v := hspec.2
  have hg : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → Submission.BoseGases.g0 v h y = 0 :=
    fun y hy => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hy h
  -- The Newton representation: `ω` is the Coulomb potential of `g₀` divided by `8π`.
  have hrep : ∀ᵐ x : ℝ³,
      Classical.choose h x = (1 / (8 * Real.pi)) *
        ∫ y : ℝ³, Submission.BoseGases.g0 v h y * Submission.BoseGases.nPotKernel x y := by
    filter_upwards [Submission.BoseGases.scattering_newton_representation (v := v)
      (w := Classical.choose h) (R := R) hR hvrad hv_supp hrad hws] with x hx
    simpa [Submission.BoseGases.g0, Submission.BoseGases.nPotKernel] using hx
  -- The maximum-principle bound `ω ≤ 1` a.e.
  have hle1 : ∀ᵐ x : ℝ³, Classical.choose h x ≤ 1 :=
    (Submission.BoseGases.scattering_bounds_ae (v := v) (w := Classical.choose h) (R := R)
      hR hv hvrad hv_supp hrad hws).2
  -- Nonnegativity of `g₀` a.e.
  have hgnn : ∀ᵐ y : ℝ³, 0 ≤ Submission.BoseGases.g0 v h y :=
    Submission.BoseGases.scattering_g_nonneg (v := v) (w := Classical.choose h) (R := R)
      hR hv hvrad hv_supp hrad hws
  -- A.e. finiteness of the slice `y ↦ |g₀ y|·‖x−y‖⁻¹`: it holds on every ball, hence everywhere.
  have hball : ∀ n : ℕ, ∀ᵐ x : ℝ³, x ∈ Metric.ball (0 : ℝ³) ((n : ℝ) + 1) →
      MeasureTheory.Integrable (fun y : ℝ³ =>
        |Submission.BoseGases.g0 v h y| * Submission.BoseGases.nPotKernel x y) := by
    intro n
    rw [← MeasureTheory.ae_restrict_iff' Metric.isOpen_ball.measurableSet]
    exact Submission.BoseGases.kernel_abs_slice_integrable_ae (g := Submission.BoseGases.g0 v h)
      (R := R) (M := (n : ℝ) + 1) hg hgsupp hR.le (by positivity)
  have hslice : ∀ᵐ x : ℝ³, MeasureTheory.Integrable (fun y : ℝ³ =>
      |Submission.BoseGases.g0 v h y| * Submission.BoseGases.nPotKernel x y) := by
    filter_upwards [MeasureTheory.ae_all_iff.mpr hball] with x hx
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    exact hx n (by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_lt_of_le hn (by linarith))
  filter_upwards [hrep, hle1, hgnn, hslice] with x hrep_x hle1_x hgnn_x hslice_x
  calc (∫⁻ y : ℝ³, ENNReal.ofReal (Submission.BoseGases.g0 v h y * ‖x - y‖⁻¹))
      = ∫⁻ y : ℝ³, ENNReal.ofReal (Submission.BoseGases.g0 v h y *
          Submission.BoseGases.nPotKernel x y) := by
        refine MeasureTheory.lintegral_congr (fun y => ?_)
        simp only [Submission.BoseGases.nPotKernel]
    _ ≤ ∫⁻ y : ℝ³, ENNReal.ofReal (|Submission.BoseGases.g0 v h y| *
          Submission.BoseGases.nPotKernel x y) := by
        refine MeasureTheory.lintegral_mono (fun y => ?_)
        refine ENNReal.ofReal_le_ofReal ?_
        exact mul_le_mul_of_nonneg_right (le_abs_self _)
          (Submission.BoseGases.nPotKernel_nonneg x y)
    _ = ENNReal.ofReal (∫ y : ℝ³, |Submission.BoseGases.g0 v h y| *
          Submission.BoseGases.nPotKernel x y) := by
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (f := fun y : ℝ³ =>
          |Submission.BoseGases.g0 v h y| * Submission.BoseGases.nPotKernel x y) hslice_x
          (Filter.Eventually.of_forall (fun y => mul_nonneg (abs_nonneg _)
            (Submission.BoseGases.nPotKernel_nonneg x y)))]
    _ = ENNReal.ofReal (∫ y : ℝ³, Submission.BoseGases.g0 v h y *
          Submission.BoseGases.nPotKernel x y) := by
        congr 1
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hgnn] with y hy
        rw [abs_of_nonneg hy]
    _ ≤ ENNReal.ofReal (8 * Real.pi) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hc : (8 : ℝ) * Real.pi ≠ 0 := by positivity
        have hI : (∫ y : ℝ³, Submission.BoseGases.g0 v h y *
            Submission.BoseGases.nPotKernel x y) = 8 * Real.pi * Classical.choose h x := by
          rw [hrep_x, ← mul_assoc, mul_one_div_cancel hc, one_mul]
        rw [hI]
        exact mul_le_of_le_one_right (by positivity) hle1_x

end Work.BoseFixR.FarLat
