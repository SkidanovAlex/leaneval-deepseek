import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

set_option maxHeartbeats 1600000

noncomputable section

/-! ## Helpers -/

/-- The product measure of the two restricted measures. -/
def Lprod : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)

theorem abs_c2m_le_two (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  have hs : |Real.sin θ ^ 2| ≤ 1 := by rw [abs_sq]; nlinarith [Real.sin_sq_le_one θ]
  have hc : |Real.cos (2*θ)| ≤ 1 := Real.abs_cos_le_one _
  have h : Work.Construction.c2m θ = Real.cos (2*θ) - Real.sin θ ^ 2 := rfl
  rw [h]
  calc |Real.cos (2*θ) - Real.sin θ ^ 2| ≤ |Real.cos (2*θ)| + |Real.sin θ ^ 2| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add hc hs
    _ = 2 := by norm_num

theorem continuousOn_c2m_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Construction.c2m p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) := by
  have h : ContinuousOn (fun p : ℝ × ℝ => Real.cos (2 * p.2) - Real.sin p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) :=
    ((Real.continuous_cos.comp (continuous_const.mul continuous_snd)).continuousOn).sub
      ((Real.continuous_sin.comp continuous_snd).continuousOn.pow 2)
  exact h.congr (fun p _ => rfl)

theorem aemeasurable_sin_rpow_Iθ (q : ℝ) :
    AEMeasurable (fun θ : ℝ => (Real.sin (2*θ)) ^ (-q))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hsin : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hcont : ContinuousOn (fun θ : ℝ => (Real.sin (2*θ)) ^ (-q)) (Set.Ioo 0 (π/2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hsin θ hθ)))
  rw [MeasureTheory.Measure.restrict_congr_set
    (Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d_Ith_ae)]
  exact hcont.aemeasurable measurableSet_Ioo

theorem aemeasurable_c2m_Iθ :
    AEMeasurable (fun θ : ℝ => Work.Construction.c2m θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  (((Real.continuous_cos.comp (continuous_const.mul continuous_id)).sub
    (Real.continuous_sin.pow 2)).aemeasurable.restrict)

/-- Integrability of a slot with angular weight `σ` from integrability with the dominating
`sin(2θ)^{-q}`-weight. -/
theorem slot_sigma_integrable {X : ℝ → ℝ → ℝ} {σ : ℝ → ℝ} {q : ℝ}
    (hσcont : ContinuousOn (fun p : ℝ × ℝ => σ p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)))
    (hσnn : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ σ θ)
    (hσle : ∀ θ ∈ Set.Ioo 0 (π / 2), σ θ ≤ (Real.sin (2*θ)) ^ (-q))
    (hXc : ContinuousOn (Function.uncurry X)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)))
    (hbig : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1)^2 * (Real.sin (2*p.2)) ^ (-q) * (X p.1 p.2)^2) Lprod) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1)^2 * σ p.2 * (X p.1 p.2)^2) Lprod := by
  refine hbig.mono' ?_ ?_
  · have hw : AEStronglyMeasurable (fun p : ℝ × ℝ => (Work.Spaces.w p.1)^2) Lprod :=
      Work.Spaces.aesm_of_continuousOn_Qd _
        Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0
    have hσ : AEStronglyMeasurable (fun p : ℝ × ℝ => σ p.2) Lprod :=
      Work.Spaces.aesm_of_continuousOn_Qd _ hσcont
    have hX : AEStronglyMeasurable (fun p : ℝ × ℝ => (X p.1 p.2)^2) Lprod :=
      (Work.Spaces.aesm_of_continuousOn_Qd _ hXc).pow 2
    exact (hw.mul hσ).mul hX
  · have hpt : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2), ∀ z ∈ Set.Ioi (0:ℝ),
        ‖(Work.Spaces.w z)^2 * σ θ * (X z θ)^2‖
          ≤ (Work.Spaces.w z)^2 * (Real.sin (2*θ)) ^ (-q) * (X z θ)^2 := by
      intro θ hθ z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (hσnn θ hθ))
        (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hσle θ hθ) (sq_nonneg _)) (sq_nonneg _)
    exact Work.FTS.StrongPersist.H6Pair6Aux.ae_prod_Ioo hpt

/-- The Cauchy–Schwarz input `|θw θ| ≤ 2 σ θ` when `θw = σ · c2m` and `|c2m| ≤ 2`. -/
theorem thetaW_abs_le (σ : ℝ → ℝ) (θ : ℝ) (hσ : 0 ≤ σ θ) :
    |σ θ * Work.Construction.c2m θ| ≤ 2 * σ θ := by
  rw [abs_mul, abs_of_nonneg hσ]
  nlinarith [abs_c2m_le_two θ, hσ]


end

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
