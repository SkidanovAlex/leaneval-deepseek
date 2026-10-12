import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Order.Group.Lattice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory Measure Set Filter Metric
open scoped ENNReal

noncomputable section

namespace Commons.Analysis.Fourier

private abbrev V := EuclideanSpace ℝ (Fin 3)

private lemma finrank_V : Module.finrank ℝ V = 3 := by simp [V]

/-- `z ↦ ‖z‖⁻¹` is integrable on the open unit ball of `V` (the 1/‖z‖ singularity is mild in
dimension three: `1 < 3`). -/
private lemma newton_kernel_integrableOn_unitBall :
    IntegrableOn (fun z : V => (‖z‖⁻¹ : ℝ)) (ball (0 : V) 1) volume := by
  refine integrableOn_ball_of_norm_le_rpow (E := V) (F := ℝ) (μ := volume)
    (f := fun z : V => (‖z‖⁻¹ : ℝ)) (C := 1) (α := 1) (r := 1) ?hd ?hα ?hdecay ?hmeas
  · rw [finrank_V]
    norm_num
  · rw [finrank_V]
    norm_num
  · apply Eventually.of_forall
    intro x
    have h1 : ‖(‖x‖⁻¹ : ℝ)‖ = ‖x‖⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact inv_nonneg.mpr (norm_nonneg x)
    rw [h1, one_mul, Real.rpow_neg_one]
  · apply Measurable.aestronglyMeasurable
    exact measurable_inv.comp measurable_norm

/-- For a measurable, bounded, integrable real function `u` on `V = EuclideanSpace ℝ (Fin 3)`,
the Newton double-kernel `(x, y) ↦ u x * u y * ‖x − y‖⁻¹` is integrable w.r.t. the product of two
copies of `volume` on `V × V`.

Strategy: split `‖x−y‖ ≤ 1` (near) and `‖x−y‖ > 1` (far).
Far part is bounded by `|u x| * |u y|` (use `MeasureTheory.Integrable.mul_prod`).
Near part: bound `|u x * u y * ‖x−y‖⁻¹| ≤ M * |u x| * 1_{‖x−y‖≤1} ‖x−y‖⁻¹` where `M` bounds `|u|`;
integrate in `y` first (Fubini, `MeasureTheory.integrable_prod_iff`), use translation invariance
(`Measure.measurePreserving_sub_left volume`, `MeasurePreserving.integral_comp`) to see
`∫_y 1_{‖x−y‖≤1}‖x−y‖⁻¹ dy` is the constant `C := ∫ 1_{ball 0 1} ‖·‖⁻¹`, finite by
`MeasureTheory.integrableOn_ball_of_norm_le_rpow` (`α = 1 < 3`, decay
`|‖z‖⁻¹| = ‖z‖⁻¹ = ‖z‖^(-1:ℝ)` via `Real.rpow_neg_one`) lifted with
`MeasureTheory.integrable_indicator_iff`. -/
theorem newton_double_integrable (u : EuclideanSpace ℝ (Fin 3) → ℝ) (hmu : Measurable u)
    (hu_bdd : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin 3), |u x| ≤ C)
    (hui : MeasureTheory.Integrable u) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        u p.1 * u p.2 * ‖p.1 - p.2‖⁻¹)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  classical
  rcases hu_bdd with ⟨M, hM⟩
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (u 0)) (hM 0)
  let k : V → ℝ := (ball (0 : V) 1).indicator (fun z : V => (‖z‖⁻¹ : ℝ))
  have hk_nonneg : ∀ z : V, 0 ≤ k z := by
    intro z
    dsimp [k]
    by_cases hz : z ∈ ball (0 : V) 1
    · simp [hz]
    · simp [hz]
  have hk_meas : Measurable k := by
    dsimp [k]
    apply Measurable.indicator (measurable_inv.comp measurable_norm) measurableSet_ball
  have hk : Integrable k volume := by
    dsimp [k]
    exact (integrable_indicator_iff (s := ball (0 : V) 1)
      (f := fun z : V => (‖z‖⁻¹ : ℝ)) measurableSet_ball).2 newton_kernel_integrableOn_unitBall
  have hk_shift : ∀ x : V, (∫ y : V, k (x - y)) = ∫ z : V, k z := by
    intro x
    exact integral_sub_left_eq_self k volume x
  let C : ℝ := ∫ z : V, k z
  let F : V × V → ℝ := fun p => u p.1 * u p.2 * ‖p.1 - p.2‖⁻¹
  let B1 : V × V → ℝ := fun p => |u p.1| * |u p.2|
  let B2 : V × V → ℝ := fun p => M * |u p.1| * k (p.1 - p.2)
  -- B1 integrable
  have hB1 : Integrable B1 (volume.prod volume) := by
    have huabs : Integrable (fun x : V => |u x|) volume := hui.abs
    simpa [B1] using huabs.mul_prod huabs
  -- B2 integrable
  have hB2_meas : AEStronglyMeasurable B2 (volume.prod volume) := by
    have hm : Measurable B2 := by
      dsimp [B2]
      fun_prop
    exact hm.aestronglyMeasurable
  have hB2 : Integrable B2 (volume.prod volume) := by
    have hiff := integrable_prod_iff (μ := (volume : Measure V)) (ν := (volume : Measure V)) (f := B2) hB2_meas
    rw [hiff]
    constructor
    · filter_upwards with x
      have hkx : Integrable (fun y : V => k (x - y)) volume := hk.comp_sub_left x
      have hcx : Integrable (fun y : V => (M * |u x|) * k (x - y)) volume := by
        simpa using hkx.const_mul (M * |u x|)
      simpa [B2] using hcx
    · have hQmeas : AEStronglyMeasurable (fun x : V => ∫ y : V, ‖B2 (x, y)‖) volume := by
        exact (hB2_meas.norm.integral_prod_right' (μ := (volume : Measure V)) (ν := (volume : Measure V)))
      have hQval : ∀ x : V, (∫ y : V, ‖B2 (x, y)‖) = (M * C) * |u x| := by
        intro x
        calc
          (∫ y : V, ‖B2 (x, y)‖) = ∫ y : V, B2 (x, y) := by
            apply integral_congr_ae
            apply Eventually.of_forall
            intro y
            change ‖B2 (x, y)‖ = B2 (x, y)
            rw [Real.norm_eq_abs, abs_of_nonneg]
            dsimp [B2]
            exact mul_nonneg (mul_nonneg hM0 (abs_nonneg _)) (hk_nonneg (x - y))
          _ = ∫ y : V, (M * |u x|) * k (x - y) := by
            apply integral_congr_ae
            apply Eventually.of_forall
            intro y
            change B2 (x, y) = (M * |u x|) * k (x - y)
            dsimp [B2]
          _ = (M * |u x|) * (∫ y : V, k (x - y)) := by
            rw [integral_const_mul]
          _ = (M * |u x|) * C := by
            rw [hk_shift x]
          _ = (M * C) * |u x| := by ring
      have hQint : Integrable (fun x : V => (M * C) * |u x|) volume := by
        have huabs : Integrable (fun x : V => |u x|) volume := hui.abs
        simpa using huabs.const_mul (M * C)
      refine hQint.congr ?_
      apply Eventually.of_forall
      intro x
      exact (hQval x).symm
  -- pointwise domination
  have hBle : ∀ p : V × V, |F p| ≤ B1 p + B2 p := by
    intro p
    have ht0 : 0 ≤ ‖p.1 - p.2‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    have h1' : |u p.1 * u p.2 * ‖p.1 - p.2‖⁻¹| = |u p.1| * |u p.2| * ‖p.1 - p.2‖⁻¹ := by
      rw [abs_mul (u p.1 * u p.2) (‖p.1 - p.2‖⁻¹),
        abs_mul (u p.1) (u p.2),
        abs_of_nonneg ht0]
    have h1 : |F p| ≤ |u p.1| * |u p.2| * ‖p.1 - p.2‖⁻¹ := by
      dsimp [F]
      rw [h1']
    have h2 : ‖p.1 - p.2‖⁻¹ ≤ 1 + k (p.1 - p.2) := by
      by_cases hz : p.1 - p.2 ∈ ball (0 : V) 1
      · have hkz : k (p.1 - p.2) = ‖p.1 - p.2‖⁻¹ := by
          dsimp [k]
          simp [hz]
        rw [hkz]
        linarith
      · have hge : 1 ≤ ‖p.1 - p.2‖ := by
          rw [mem_ball, dist_eq_norm, sub_zero] at hz
          exact le_of_not_gt hz
        have hinv : ‖p.1 - p.2‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hge
        have hkz : k (p.1 - p.2) = 0 := by
          dsimp [k]
          simp [hz]
        rw [hkz]
        linarith
    have hmul_nonneg : 0 ≤ |u p.1| * |u p.2| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have h3 : |u p.1| * |u p.2| * ‖p.1 - p.2‖⁻¹ ≤ |u p.1| * |u p.2| * (1 + k (p.1 - p.2)) := by
      exact mul_le_mul_of_nonneg_left h2 hmul_nonneg
    have h4 : |u p.1| * |u p.2| * (1 + k (p.1 - p.2))
        = |u p.1| * |u p.2| + |u p.1| * |u p.2| * k (p.1 - p.2) := by
      ring
    have hk0 : 0 ≤ k (p.1 - p.2) := hk_nonneg (p.1 - p.2)
    have huu : |u p.1| * |u p.2| * k (p.1 - p.2) ≤ M * |u p.1| * k (p.1 - p.2) := by
      calc
        |u p.1| * |u p.2| * k (p.1 - p.2) = (|u p.1| * k (p.1 - p.2)) * |u p.2| := by ring
        _ ≤ (|u p.1| * k (p.1 - p.2)) * M := by
          exact mul_le_mul_of_nonneg_left (hM p.2) (mul_nonneg (abs_nonneg _) hk0)
        _ = M * |u p.1| * k (p.1 - p.2) := by ring
    have h5 : |u p.1| * |u p.2| + |u p.1| * |u p.2| * k (p.1 - p.2)
        ≤ |u p.1| * |u p.2| + M * |u p.1| * k (p.1 - p.2) := by
      exact add_le_add (le_refl (|u p.1| * |u p.2|)) huu
    calc
      |F p| ≤ |u p.1| * |u p.2| * ‖p.1 - p.2‖⁻¹ := h1
      _ ≤ |u p.1| * |u p.2| * (1 + k (p.1 - p.2)) := h3
      _ = |u p.1| * |u p.2| + |u p.1| * |u p.2| * k (p.1 - p.2) := h4
      _ ≤ |u p.1| * |u p.2| + M * |u p.1| * k (p.1 - p.2) := h5
      _ = B1 p + B2 p := by
        dsimp [B1, B2]
  have hFmeas : AEStronglyMeasurable F (volume.prod volume) := by
    have hm : Measurable F := by
      dsimp [F]
      fun_prop
    exact hm.aestronglyMeasurable
  change Integrable F (volume.prod volume)
  exact (hB1.add hB2).mono' hFmeas
    (Eventually.of_forall (fun p => by simpa [Real.norm_eq_abs] using hBle p))

end Commons.Analysis.Fourier