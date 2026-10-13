import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Alpha4.Assembly

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Alpha4

/-! ## Slice integrability of `(D_z^j ∂_θ^i G)² · σ`

The angular weight `thEta θ = sin(2θ)^{-η}` is integrable on the closed angular interval
`Iθ = [0,π/2]`, and the `θ`-slice of `D_z^j ∂_θ^i G` at a *fixed* `z > 0` is continuous
on the compact set `Iθ`, hence the slice is bounded and its square is dominated by a
constant multiple of the integrable weight.

The only technical point is that `θ ↦ (F z θ)² · thEta θ` is not *continuous* on
`Iθ` (the weight blows up at the endpoints), so almost-everywhere strong measurability is
obtained on the co-null open sub-interval `(0,π/2)`. -/

/-- The open interval `(0,π/2)` and the closed interval `Iθ` carry the same restriction of
Lebesgue measure, since they differ by the two null points `0` and `π/2`. -/
theorem restrict_Ioo_eq_restrict_Iθ_alpha4 :
    MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
  Measure.restrict_congr_set
    (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)

/-- The angular weight `thEta` is continuous on the *open* interval `(0,π/2)`
(where `sin(2θ) > 0`, so the `rpow` branch is continuous). -/
theorem continuousOn_thEta_Ioo :
    ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have h := hsin.rpow_const (p := -(Work.Spaces.eta)) (fun θ hθ => Or.inl (ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))))
  simpa only [Work.FTS.EllipticEst.thEta] using h

/-- **Single-slice integrability.**  If a one-dimensional slice `f` is continuous on the
closed angular interval, then `θ ↦ f(θ)² · sin(2θ)^{-η}` is integrable against
`volume.restrict Iθ`. -/
theorem integrable_slice_sq_mul_thEta {f : ℝ → ℝ} (hf : ContinuousOn f Work.Spaces.Iθ) :
    MeasureTheory.Integrable
      (fun θ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hdom : MeasureTheory.Integrable
      (fun θ => M ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.integrableOn_thEta.1.const_mul (M ^ 2)
  have hcont : ContinuousOn
      (fun θ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) (Set.Ioo 0 (Real.pi / 2)) :=
    ((hf.mono (fun θ hθ => ⟨hθ.1.le, hθ.2.le⟩)).pow 2).mul continuousOn_thEta_Ioo
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [← restrict_Ioo_eq_restrict_Iθ_alpha4]
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  refine MeasureTheory.Integrable.mono' hdom haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  have hθ' : |f θ| ≤ M := by
    simpa [Real.norm_eq_abs] using hM θ hθ
  have hsq : (f θ) ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hθ' 2
  have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
  have hnn : 0 ≤ (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := mul_nonneg (sq_nonneg _) hσ
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact mul_le_mul_of_nonneg_right hsq hσ

theorem integrable_slice_pthDz_sigma {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G) (j i : ℕ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => (Work.Spaces.DzIter j (Work.Spaces.pthIter i G) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
  exact integrable_slice_sq_mul_thEta ((hG.pthIter i).continuousOn_slice_DzIter j hz)

end Work.FTS.EllipticEst.Alpha4
