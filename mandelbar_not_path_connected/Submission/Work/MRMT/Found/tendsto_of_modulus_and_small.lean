import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Found.exists_delta_of_log_modulus
import Submission.Work.MRMT.Found.norm_sub_le_sqrt_of_modulus
import Submission.Work.MRMT.Found.exists_norm_le_of_eLpNorm_two_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Work.MRMT.Found

/-- **Assembly step for the principal solution.**  A continuous family `φs` which is
(i) equicontinuous on each ball with a logarithmic modulus and (ii) `L²`-close to the
identity on each ball in terms of `‖μs j‖_∞`, converges locally uniformly to the identity
as soon as `‖μs j‖_∞ → 0`.

The proof is the classical "average point" argument.  Fix `x` and `ε > 0`, let `ρ = ‖x‖ + 1`
and let `C₁`, `C₂` be the constants delivered by `hmod`, `hsmall`.  Choose `δ ∈ (0, 1/8]` with
`2 * sqrt (C₁ / log (1/δ)) + δ < 3ε/4`.  The `L²` bound says that on `B(0,ρ)` the deviation
`φs j - id` is small in `L²` once `‖μs j‖_∞` is, so on the *small* ball `B(x, δ/2)` — whose
volume is a fixed positive number — there is a point `w` with `‖φs j w - w‖ ≤ ε/4`, as soon as
`‖μs j‖_∞ < η` for a suitable explicit `η`.  For `z` in the closed ball `B(x, δ/2)`, the
modulus of continuity at the radius `δ` then gives
`‖φs j z - z‖ ≤ 2 sqrt (C₁ / log (1/δ)) + ε/4 + δ < ε`. -/
theorem tendsto_of_modulus_and_small {μs : ℕ → ℂ → ℂ} {φs : ℕ → ℂ → ℂ}
    (hcont : ∀ j, Continuous (φs j))
    (hmod : ∀ ρ : ℝ, 0 < ρ → ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (z₀ z : ℂ), ‖z₀‖ ≤ ρ →
      ‖z - z₀‖ ≤ 1 / 4 → ‖φs j z - φs j z₀‖ ^ 2 ≤ C / Real.log (1 / ‖z - z₀‖))
    (hsmall : ∀ ρ : ℝ, 0 < ρ → ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ,
      MeasureTheory.eLpNorm (fun z => φs j z - z) 2
          (MeasureTheory.volume.restrict (Metric.ball 0 ρ))
        ≤ ENNReal.ofReal C *
            MeasureTheory.eLpNorm (μs j) ⊤ (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (h0 : Filter.Tendsto (fun j => MeasureTheory.eLpNorm (μs j) ⊤
      (MeasureTheory.volume : MeasureTheory.Measure ℂ)) Filter.atTop (nhds 0)) :
    TendstoLocallyUniformly φs id Filter.atTop := by
  rw [tendstoLocallyUniformly_iff_filter]
  intro x
  rw [Metric.tendstoUniformlyOnFilter_iff]
  intro ε hε
  rw [Filter.eventually_prod_iff]
  have hρ : (0 : ℝ) < ‖x‖ + 1 := by positivity
  obtain ⟨C₁, hC₁pos, hC₁⟩ := hmod (‖x‖ + 1) hρ
  obtain ⟨C₂, hC₂pos, hC₂⟩ := hsmall (‖x‖ + 1) hρ
  obtain ⟨δ, hδpos, hδle8, hδbound⟩ := exists_delta_of_log_modulus hC₁pos hε
  have hδ4 : δ ≤ 1 / 4 := by linarith
  have hhalf : (0 : ℝ) < δ / 2 := by linarith
  have hvolne : (volume : Measure ℂ) (Metric.ball x (δ / 2)) ≠ ⊤ :=
    (MeasureTheory.measure_ball_lt_top (μ := (volume : Measure ℂ)) (x := x) (r := δ / 2)).ne
  have hvpos : 0 < ((volume : Measure ℂ) (Metric.ball x (δ / 2))).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos (volume : Measure ℂ) x hhalf).ne' hvolne
  set V : ℝ := ((volume : Measure ℂ) (Metric.ball x (δ / 2))).toReal with hV
  have hVpos : 0 < V := by rw [hV]; exact hvpos
  set η : ℝ := (ε / 4) * V / (C₂ * (1 + V)) with hη
  have hηpos : 0 < η := by rw [hη]; positivity
  have hev : ∀ᶠ j in Filter.atTop, eLpNorm (μs j) ⊤ (volume : Measure ℂ) < ENNReal.ofReal η :=
    h0 (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hηpos))
  refine ⟨{j | ∃ w ∈ Metric.ball x (δ / 2), ‖φs j w - w‖ ≤ ε / 4}, ?_, Metric.closedBall x (δ / 2),
    Metric.closedBall_mem_nhds x hhalf, ?_⟩
  · refine Filter.mem_of_superset hev ?_
    intro j hj
    have hae : AEStronglyMeasurable (fun z => φs j z - z) (volume : Measure ℂ) :=
      ((hcont j).sub continuous_id).aestronglyMeasurable
    have hst : Metric.ball x (δ / 2) ⊆ Metric.ball 0 (‖x‖ + 1) := by
      intro z hz
      have h1 : ‖z - x‖ < δ / 2 := by
        have h2 := Metric.mem_ball.mp hz
        rwa [dist_eq_norm] at h2
      simp only [Metric.mem_ball, dist_zero_right]
      calc ‖z‖ = ‖(z - x) + x‖ := by ring_nf
        _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
        _ < ‖x‖ + 1 := by linarith
    have hCη : C₂ * η = (ε / 4) * V / (1 + V) := by
      rw [hη]; field_simp
    have hstep : V ^ 2 / (1 + V) ^ 2 < V := by
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < (1 + V) ^ 2)]
      nlinarith [hVpos]
    have heq : (ε / 4 * V / (1 + V)) ^ 2 = (ε / 4) ^ 2 * (V ^ 2 / (1 + V) ^ 2) := by field_simp
    have hB2 : (C₂ * η) ^ 2 < (ε / 4) ^ 2 * V := by
      rw [hCη, heq]
      exact mul_lt_mul_of_pos_left hstep (by positivity)
    have hle : eLpNorm (fun z => φs j z - z) 2 (volume.restrict (Metric.ball 0 (‖x‖ + 1)))
        ≤ ENNReal.ofReal (C₂ * η) := by
      calc eLpNorm (fun z => φs j z - z) 2 (volume.restrict (Metric.ball 0 (‖x‖ + 1)))
          ≤ ENNReal.ofReal C₂ * eLpNorm (μs j) ⊤ (volume : Measure ℂ) := hC₂ j
        _ ≤ ENNReal.ofReal C₂ * ENNReal.ofReal η := mul_le_mul' le_rfl hj.le
        _ = ENNReal.ofReal (C₂ * η) := by rw [ENNReal.ofReal_mul hC₂pos.le]
    have hlt : (C₂ * η) ^ 2 < (ε / 4) ^ 2 * ((volume : Measure ℂ) (Metric.ball x (δ / 2))).toReal := by
      rw [← hV]; exact hB2
    exact exists_norm_le_of_eLpNorm_two_le (B := C₂ * η) (c := ε / 4) hst measurableSet_ball
      hvolne hae (by positivity) (by linarith) hle hlt
  · intro j hj z hz
    obtain ⟨w, hw, hwle⟩ := hj
    have hzx : ‖z - x‖ ≤ δ / 2 := by
      have h2 := Metric.mem_closedBall.mp hz
      rwa [dist_eq_norm] at h2
    have hwx : ‖w - x‖ < δ / 2 := by
      have h2 := Metric.mem_ball.mp hw
      rwa [dist_eq_norm] at h2
    have h1 : ‖φs j z - φs j x‖ ≤ Real.sqrt (C₁ / Real.log (1 / δ)) :=
      norm_sub_le_sqrt_of_modulus hC₁pos hδpos hδ4 (by linarith)
        (hC₁ j x z (by linarith) (by linarith))
    have h2 : ‖φs j x - φs j w‖ ≤ Real.sqrt (C₁ / Real.log (1 / δ)) := by
      rw [norm_sub_rev]
      exact norm_sub_le_sqrt_of_modulus hC₁pos hδpos hδ4 (by linarith)
        (hC₁ j x w (by linarith) (by linarith))
    have hwz : ‖w - z‖ ≤ δ := by
      have h4 : ‖w - z‖ ≤ ‖w - x‖ + ‖z - x‖ := by
        have h := dist_triangle w x z
        rw [dist_comm x z] at h
        simpa only [dist_eq_norm] using h
      linarith
    have htri : ‖φs j z - z‖ ≤ ‖φs j z - φs j x‖ + ‖φs j x - φs j w‖ + ‖φs j w - w‖ + ‖w - z‖ := by
      have h4 := dist_triangle4 (φs j z) (φs j x) (φs j w) w
      have h5 := dist_triangle (φs j z) w z
      simp only [dist_eq_norm] at h4 h5
      linarith
    have hfin : ‖φs j z - z‖ < ε := by linarith
    rw [dist_eq_norm, norm_sub_rev]
    exact hfin

end Work.MRMT.Found
