import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.TT.Heta_le_of_sin_bound
import Submission.Work.FTS.EllipticEst.TT.SliceCoercDefs
import Submission.Work.FTS.H2.STBounds2
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.sliceCSWeightedOpen
import Submission.Work.FTS.EllipticEst.SgamBound.abs_deriv_sub_le_integral_abs_D2
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists
import Submission.Work.FTS.EllipticEst.WeakMoment.Open.IntegrableD2OfWeighted
import Submission.Work.FTS.EllipticEst.WeakMoment.Open.D2CsBound
import Submission.Work.FTS.EllipticEst.WeakMoment.Open.DerivLeIntegralAbsD2
import Submission.Work.FTS.EllipticEst.WeakMoment.Open.ULeIntegralDerivBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.WeakMoment

/-! ## Weighted `L²` bounds from a pointwise bound

The estimate below is the `θ`-slice form of the weighted Poincaré inequality used by the
weak-moment interface: a function that is continuous on the open interval `(0, π/2)` and bounded
by a constant `M` there has weighted square `∫ f² sin(2θ)^{-η}` integrable, and the weighted
square integral is at most `M² ∫ sin(2θ)^{-η}`. -/

theorem sq_mul_sEta_integrableOn_and_integral_le {f : ℝ → ℝ} {M : ℝ}
    (hf : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 2))) (hM : 0 ≤ M)
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ M) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ M ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ) := by
  have hIoo : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hae : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    MeasureTheory.Ioo_ae_eq_Icc.symm
  have hms : volume.restrict Work.Spaces.Iθ
      = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set hae
  -- the weight is integrable on `Iθ`
  have hsEta_int : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := (Work.FTS.EllipticEst.integrableOn_thEta).1
  -- the weight is positive and continuous on the open interval
  have hsEta_pos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 < Work.FTS.EllipticEst.sEta θ := by
    intro θ hθ
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    exact Real.rpow_pos_of_pos hsin _
  have hsEta_cont : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
    refine hsin.rpow_const (fun θ hθ => Or.inl ?_)
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  -- the dominating function on the open interval
  have hmaj : MeasureTheory.IntegrableOn (fun θ : ℝ => M ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hsEta_int.mono_set hsub).const_mul (M ^ 2)
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    ((hf.aestronglyMeasurable hIoo).pow 2).mul (hsEta_cont.aestronglyMeasurable hIoo)
  have hle : (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))]
      (fun θ : ℝ => M ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    filter_upwards [ae_restrict_mem hIoo] with θ hθ
    have hs0 : 0 ≤ Work.FTS.EllipticEst.sEta θ := le_of_lt (hsEta_pos θ hθ)
    have hf2 : (f θ) ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs (f θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (h θ hθ) 2
    exact mul_le_mul_of_nonneg_right hf2 hs0
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))]
      (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    filter_upwards [ae_restrict_mem hIoo] with θ hθ
    exact mul_nonneg (sq_nonneg _) (le_of_lt (hsEta_pos θ hθ))
  have hnorm : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      ‖(f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ‖ ≤ M ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    filter_upwards [hle, hnn] with θ h1 h2
    rwa [Real.norm_of_nonneg h2]
  have hint_Ioo := hmaj.mono' hmeas hnorm
  constructor
  · change MeasureTheory.Integrable
        (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (volume.restrict Work.Spaces.Iθ)
    rw [hms]
    exact hint_Ioo
  · have hmono := MeasureTheory.integral_mono_of_nonneg hnn hmaj hle
    have e1 : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
      MeasureTheory.setIntegral_congr_set hae
    have e2 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.sEta θ :=
      MeasureTheory.setIntegral_congr_set hae
    have e3 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          M ^ 2 * Work.FTS.EllipticEst.sEta θ)
        = M ^ 2 * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            Work.FTS.EllipticEst.sEta θ) :=
      MeasureTheory.integral_const_mul _ _
    rw [e1, e2, ← e3]
    exact hmono

/-! ## The arithmetic of the final constant -/

private lemma slice_arith_two {A G : ℝ} (hG : 0 ≤ G)
    (hAG : A ^ 2 ≤ G * (Real.pi / 2)) :
    (Real.pi / 2 * A) ^ 2 * 10000 ≤ 100000 * G := by
  have hpi : (Real.pi / 2) ^ 3 * 10000 ≤ 100000 := by
    have h1 : Real.pi / 2 ≤ 2 := by linarith [Real.pi_le_four]
    have h2 : (Real.pi / 2) ^ 3 ≤ (2 : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
    norm_num at h2
    linarith
  have h2 : (Real.pi / 2) ^ 2 * A ^ 2 * 10000
      ≤ (Real.pi / 2) ^ 2 * (G * (Real.pi / 2)) * 10000 := by
    have hk : 0 ≤ (Real.pi / 2) ^ 2 * 10000 := by positivity
    have hstep := mul_le_mul_of_nonneg_right hAG hk
    nlinarith [hstep]
  calc (Real.pi / 2 * A) ^ 2 * 10000 = (Real.pi / 2) ^ 2 * A ^ 2 * 10000 := by ring
    _ ≤ (Real.pi / 2) ^ 2 * (G * (Real.pi / 2)) * 10000 := h2
    _ = ((Real.pi / 2) ^ 3 * 10000) * G := by ring
    _ ≤ 100000 * G := mul_le_mul_of_nonneg_right hpi hG

private lemma slice_arith_one {A G : ℝ} (hG : 0 ≤ G)
    (hAG : A ^ 2 ≤ G * (Real.pi / 2)) :
    A ^ 2 * 10000 ≤ 100000 * G := by
  have hpi : (Real.pi / 2) * 10000 ≤ 100000 := by
    have h1 : Real.pi / 2 ≤ 2 := by linarith [Real.pi_le_four]
    linarith
  calc A ^ 2 * 10000 ≤ (G * (Real.pi / 2)) * 10000 :=
        mul_le_mul_of_nonneg_right hAG (by norm_num)
    _ = ((Real.pi / 2) * 10000) * G := by ring
    _ ≤ 100000 * G := mul_le_mul_of_nonneg_right hpi hG

/-! ## The slice bounds, with the four open-interval ingredients

The four inputs (unweighted integrability of `u''`, the weighted Cauchy–Schwarz bound, the
Rolle/Newton–Leibniz bound on `u'`, and the mean-value bound on `u`) are delegated lemmas in
`Submission/Work/FTS/EllipticEst/WeakMoment/Open/`. -/

theorem SliceSqBoundsOpen : ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ → ℝ,
    (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2))) →
    ContinuousOn u Work.Spaces.Iθ → u 0 = 0 → u (Real.pi / 2) = 0 →
    MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) ∧
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := by
  refine ⟨100000, by norm_num, ?_⟩
  intro u hsm hcont h0 hpi h5
  -- the hypothesis rewritten in the vocabulary of `TT.D2`
  have h5D : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := h5
  -- integrability of `(u'')²` and of `|u''|`
  obtain ⟨_, hD2abs⟩ := Work.FTS.EllipticEst.WeakMoment.Open.IntegrableD2OfWeighted h5D
  -- Cauchy–Schwarz: `(∫|u''|)² ≤ (∫(u'')² sin(2θ)^{-η}) · π/2`
  have hcs := Work.FTS.EllipticEst.WeakMoment.Open.D2CsBound hsm h5D
  -- the pointwise bound `|u'| ≤ ∫|u''|`
  have hderiv := Work.FTS.EllipticEst.WeakMoment.Open.DerivLeIntegralAbsD2 hsm hcont h0 hpi hD2abs
  have hA0 : 0 ≤ ∫ x in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 u x| :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun _ _ => abs_nonneg _)
  -- the pointwise bound `|u| ≤ (π/2)∫|u''|`
  have hu := Work.FTS.EllipticEst.WeakMoment.Open.ULeIntegralDerivBound hsm hcont h0 hA0 hderiv
  -- the weight
  have hsEta_le : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ) ≤ 10000 :=
    (Work.FTS.EllipticEst.integrableOn_thEta).2
  have hG0 : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun x hx => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.TT.sEta_nonneg hx))
  -- continuity, to feed the pointwise bounds into the weighted estimates
  have hcont_u : ContinuousOn u (Set.Ioo (0 : ℝ) (Real.pi / 2)) := (hsm 1).continuousOn
  have hcont_du : ContinuousOn (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (hsm 2).deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact h.continuousOn
  obtain ⟨hu_int, hu_le⟩ := sq_mul_sEta_integrableOn_and_integral_le hcont_u (by positivity) hu
  obtain ⟨hdu_int, hdu_le⟩ := sq_mul_sEta_integrableOn_and_integral_le hcont_du hA0 hderiv
  refine ⟨hu_int, ?_, hdu_int, ?_⟩
  · refine le_trans hu_le ?_
    calc ((Real.pi / 2) * ∫ x in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 u x|) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
        ≤ ((Real.pi / 2) * ∫ x in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 u x|) ^ 2
            * 10000 := mul_le_mul_of_nonneg_left hsEta_le (sq_nonneg _)
      _ ≤ 100000 * (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := slice_arith_two hG0 hcs
      _ = 100000 * (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := by
          simp only [Work.FTS.EllipticEst.TT.D2]
  · refine le_trans hdu_le ?_
    calc (∫ x in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 u x|) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
        ≤ (∫ x in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 u x|) ^ 2 * 10000 :=
          mul_le_mul_of_nonneg_left hsEta_le (sq_nonneg _)
      _ ≤ 100000 * (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := slice_arith_one hG0 hcs
      _ = 100000 * (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := by
          simp only [Work.FTS.EllipticEst.TT.D2]

end Work.FTS.EllipticEst.WeakMoment
