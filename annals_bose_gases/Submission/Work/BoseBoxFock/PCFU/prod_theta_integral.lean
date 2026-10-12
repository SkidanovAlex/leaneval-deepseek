import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PCFU.chan_int_y_generic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

theorem prod_theta_integral {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (G : Submission.BoseGases.X n → ℂ) (hGm : Measurable G)
    (hGs : Function.support G ⊆ Submission.BoseGases.abox n ℓ) (Cg : ℝ) (hGb : ∀ x, ‖G x‖ ≤ Cg)
    (H : Submission.BoseGases.X n → EuclideanSpace ℝ (Fin 3) → ℂ)
    (hHm : Measurable (fun p : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) => H p.1 p.2))
    (Ch : ℝ) (hHb : ∀ p : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3), ‖H p.1 p.2‖ ≤ Ch) :
    (∫ p : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3),
        G p.1 * Work.BoseK15.corpusBox.thetaFun ℓ p.2 * H p.1 p.2)
      = ∫ x : Submission.BoseGases.X n, G x * ∫ u in Submission.BoseGases.acube ℓ, H x u := by
  -- Write the product measure on `X n × ℝ³` explicitly so that Fubini's theorem applies
  -- syntactically (`volume` on a product type is `volume.prod volume` by definition).
  change (∫ p : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3),
        G p.1 * Work.BoseK15.corpusBox.thetaFun ℓ p.2 * H p.1 p.2
          ∂((volume : Measure (Submission.BoseGases.X n)).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))))
      = ∫ x : Submission.BoseGases.X n, G x * ∫ u in Submission.BoseGases.acube ℓ, H x u
  have hCg0 : 0 ≤ Cg := le_trans (norm_nonneg (G 0)) (hGb 0)
  have hCh0 : 0 ≤ Ch := le_trans (norm_nonneg (H 0 0)) (hHb (0, 0))
  -- Integrability of the product integrand: bounded, measurable, supported in the
  -- finite-measure set `abox n ℓ × acube ℓ`.
  have hf : Integrable (fun p : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) =>
      G p.1 * Work.BoseK15.corpusBox.thetaFun ℓ p.2 * H p.1 p.2) := by
    refine integrable_of_bounded_support (M := Cg * Ch)
      (volume_abox_prod_acube_lt_top n hℓ) ?_ ?_ ?_
    · exact ((hGm.comp measurable_fst).mul
        ((measurable_thetaFun hℓ).comp measurable_snd)).mul hHm
    · rintro ⟨x, u⟩
      calc ‖G x * Work.BoseK15.corpusBox.thetaFun ℓ u * H x u‖
          ≤ ‖G x * Work.BoseK15.corpusBox.thetaFun ℓ u‖ * ‖H x u‖ := norm_mul_le _ _
        _ ≤ (‖G x‖ * ‖Work.BoseK15.corpusBox.thetaFun ℓ u‖) * ‖H x u‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ (Cg * 1) * Ch :=
            mul_le_mul (mul_le_mul (hGb x) (norm_thetaFun_le_one ℓ u) (norm_nonneg _) hCg0)
              (hHb (x, u)) (norm_nonneg _) (by positivity)
        _ = Cg * Ch := by ring
    · rintro ⟨x, u⟩ hq
      by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
      · have hu : u ∉ Submission.BoseGases.acube ℓ := fun hu => hq (by simp [hx, hu])
        rw [thetaFun_eq_zero_of_notMem_acube hℓ hu]; ring
      · have hG0 : G x = 0 := by
          by_contra hne
          exact hx (hGs (Function.mem_support.mpr hne))
        rw [hG0]; ring
  -- Fubini, then the two trivial per-`x` rewritings.
  rw [MeasureTheory.integral_prod _ hf]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  calc ∫ u, G x * Work.BoseK15.corpusBox.thetaFun ℓ u * H x u
      = G x * ∫ u, Work.BoseK15.corpusBox.thetaFun ℓ u * H x u := by
        rw [show (fun u : EuclideanSpace ℝ (Fin 3) =>
              G x * Work.BoseK15.corpusBox.thetaFun ℓ u * H x u)
              = (fun u : EuclideanSpace ℝ (Fin 3) =>
                G x * (Work.BoseK15.corpusBox.thetaFun ℓ u * H x u)) from by
            funext u; ring,
          MeasureTheory.integral_const_mul]
    _ = G x * ∫ u in Submission.BoseGases.acube ℓ, H x u := by
        rw [thetaFun_mul_eq_indicator hℓ (H x),
          MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]

end Work.BoseBoxFock.PCFU
