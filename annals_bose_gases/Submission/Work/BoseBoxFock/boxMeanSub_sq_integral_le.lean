import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Defs
import Submission.Work.BoseBoxFock.acubePVFacts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxMeanSub_sq_integral_le`

The deviation of a smooth one-body state `ψ` from its anchored box mean
`m = bsMean ℓ 0 ψ = (ℓ³)⁻¹ ∫_{Λ(ℓ)} ψ` satisfies, on the box `Λ(ℓ) = corpusBox.boxL ℓ`,

    ∫_{Λ(ℓ)} (ψ - m)²  ≤  4 ∫_{Λ(ℓ)} ψ² .

This is the crude (`4`) form of the exact identity

    ∫_{Λ(ℓ)} (ψ - m)² = ∫_{Λ(ℓ)} ψ² - ℓ³ m²  ≤  ∫_{Λ(ℓ)} ψ² ,

together with the trivial `∫_{Λ}ψ² ≤ 4 ∫_{Λ}ψ²`.  The identity is the standard expansion
`(ψ - m)² = ψ² - 2mψ + m²` combined with `∫_{Λ} ψ = ℓ³ m` (`m` is the mean over the box of
volume `ℓ³`) and `vol (corpusBox.boxL ℓ) = ℓ³`.

Everything is elementary; the only bookkeeping is that `Λ(ℓ)` is compact, so that a smooth
`ψ` is integrable on it together with `ψ²`.  (`boxL_eq_acube` identifies the corpus box with
the centred cube `acube ℓ`, whose volume is `ℓ³`.)
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

/-- A point of the centred cube `acube ℓ` has norm at most `√3 ℓ/2` (the circumradius of the
cube of side `ℓ`). -/
private lemma norm_le_of_mem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ Submission.BoseGases.acube ℓ) : ‖x‖ ≤ Real.sqrt 3 * ℓ / 2 := by
  have hcoord : ∀ m : Fin 3, |x m| ≤ ℓ / 2 := by
    intro m
    have h := (Submission.BoseGases.mem_acube_iff ℓ x).mp hx m
    rw [Set.mem_Icc] at h
    exact abs_le.mpr ⟨by linarith [h.1], h.2⟩
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i : Fin 3, ‖x.ofLp i‖ ^ 2 ≤ 3 * (ℓ / 2) ^ 2 := by
    calc ∑ i : Fin 3, ‖x.ofLp i‖ ^ 2 ≤ ∑ _i : Fin 3, (ℓ / 2) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hi := hcoord i
          have hsq : ‖x.ofLp i‖ ^ 2 = |x i| ^ 2 := by rw [Real.norm_eq_abs]
          rw [hsq]
          nlinarith [abs_nonneg (x i), hi, sq_nonneg (ℓ / 2)]
      _ = 3 * (ℓ / 2) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          simp [nsmul_eq_mul]
  calc Real.sqrt (∑ i : Fin 3, ‖x.ofLp i‖ ^ 2) ≤ Real.sqrt (3 * (ℓ / 2) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 3 * ℓ / 2 := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
        ring

/-- The centred cube `acube ℓ` is compact (for `ℓ > 0`): it is closed (an intersection of
preimages of closed intervals under the coordinate projections) and contained in the closed
ball of radius `√3 ℓ / 2`. -/
private lemma isCompact_acube {ℓ : ℝ} (hℓ : 0 < ℓ) : IsCompact (Submission.BoseGases.acube ℓ) := by
  have hclosed : IsClosed (Submission.BoseGases.acube ℓ) := by
    rw [show Submission.BoseGases.acube ℓ =
        ⋂ m : Fin 3, (fun y : EuclideanSpace ℝ (Fin 3) => y m) ⁻¹'
          (Set.Icc (-ℓ / 2) (ℓ / 2)) by
      ext y; simp [Submission.BoseGases.acube]]
    exact isClosed_iInter (fun m => isClosed_Icc.preimage (by fun_prop))
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3))
    (Real.sqrt 3 * ℓ / 2)) hclosed ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_of_mem_acube hℓ hx

/-- A smooth one-body state deviates from its anchored box mean by at most `2` in `L²` norm
on the box: `∫_{Λ(ℓ)} (ψ - m)² ≤ 4 ∫_{Λ(ℓ)} ψ²`, where `m = bsMean ℓ 0 ψ` is the mean of `ψ`
over the box of volume `ℓ³`. -/
theorem boxMeanSub_sq_integral_le {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    (∫ z in Work.BoseK15.corpusBox.boxL ℓ, (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) ^ 2)
      ≤ 4 * ∫ z in Work.BoseK15.corpusBox.boxL ℓ, (ψ z) ^ 2 := by
  set m : ℝ := Work.BSKinetic.bsMean ℓ 0 ψ with hm_def
  have hBeq : Work.BoseK15.corpusBox.boxL ℓ = Submission.BoseGases.acube ℓ :=
    Work.BoseBoxFock.boxL_eq_acube hℓ
  have hK : IsCompact (Submission.BoseGases.acube ℓ) := isCompact_acube hℓ
  have hcont : Continuous ψ := hψ.continuous
  -- Integrability of `ψ`, of `ψ²`, of `2mψ` and of the constant `m²` on the box.
  have hIntψ : IntegrableOn ψ (Submission.BoseGases.acube ℓ) volume :=
    ContinuousOn.integrableOn_compact hK hcont.continuousOn
  have hIntψ2 : IntegrableOn (fun z => (ψ z) ^ 2) (Submission.BoseGases.acube ℓ) volume :=
    ContinuousOn.integrableOn_compact hK (hcont.pow 2).continuousOn
  have hIntlin : IntegrableOn (fun z => (2 * m) * ψ z) (Submission.BoseGases.acube ℓ) volume :=
    (MeasureTheory.IntegrableOn.integrable hIntψ).const_mul (2 * m)
  have hIntc : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 3) => m ^ 2)
      (Submission.BoseGases.acube ℓ) volume := by
    refine MeasureTheory.integrableOn_const ?_ ?_
    · rw [Submission.BoseGases.acube_volume ℓ hℓ.le]
      exact ENNReal.ofReal_ne_top
    · simp
  -- The box has volume `ℓ³`.
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (Submission.BoseGases.acube ℓ)
      = ℓ ^ 3 := by
    rw [Measure.real_def, Submission.BoseGases.acube_volume ℓ hℓ.le,
      ENNReal.toReal_ofReal (by positivity)]
  -- `m` is the average of `ψ` over the box, so `∫_{Λ} ψ = ℓ³ m`.
  have hm : m = (ℓ ^ 3)⁻¹ * (∫ z in Submission.BoseGases.acube ℓ, ψ z) := by
    rw [hm_def, Work.BSKinetic.bsMean]
    simp
  have hI : (∫ z in Submission.BoseGases.acube ℓ, ψ z) = ℓ ^ 3 * m := by
    rw [hm, ← mul_assoc, mul_inv_cancel₀ (by positivity : (ℓ ^ 3 : ℝ) ≠ 0), one_mul]
  -- The exact expansion of the mean-free square.
  have hkey : (∫ z in Submission.BoseGases.acube ℓ, (ψ z - m) ^ 2)
      = (∫ z in Submission.BoseGases.acube ℓ, (ψ z) ^ 2) - ℓ ^ 3 * m ^ 2 := by
    have hcongr : (∫ z in Submission.BoseGases.acube ℓ, (ψ z - m) ^ 2)
        = ∫ z in Submission.BoseGases.acube ℓ,
            ((fun z => (ψ z) ^ 2 - (2 * m) * ψ z) z
              + (fun _ : EuclideanSpace ℝ (Fin 3) => m ^ 2) z) := by
      apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      intro z _
      ring
    rw [hcongr]
    rw [MeasureTheory.integral_add]
    · rw [MeasureTheory.integral_sub]
      · rw [MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_const, hvol, hI,
          smul_eq_mul]
        ring
      · exact hIntψ2
      · exact hIntlin
    · exact hIntψ2.sub hIntlin
    · exact hIntc
  have h1 : (∫ z in Submission.BoseGases.acube ℓ, (ψ z - m) ^ 2)
      ≤ ∫ z in Submission.BoseGases.acube ℓ, (ψ z) ^ 2 := by
    rw [hkey]
    have : 0 ≤ ℓ ^ 3 * m ^ 2 := by positivity
    linarith
  have h2 : (∫ z in Submission.BoseGases.acube ℓ, (ψ z) ^ 2)
      ≤ 4 * ∫ z in Submission.BoseGases.acube ℓ, (ψ z) ^ 2 := by
    have h0 : 0 ≤ ∫ z in Submission.BoseGases.acube ℓ, (ψ z) ^ 2 :=
      MeasureTheory.setIntegral_nonneg (Submission.BoseGases.acube_measurable ℓ)
        (fun z _ => sq_nonneg _)
    linarith
  have hgoal := le_trans h1 h2
  rwa [← hBeq] at hgoal

end Work.BoseBoxFock
