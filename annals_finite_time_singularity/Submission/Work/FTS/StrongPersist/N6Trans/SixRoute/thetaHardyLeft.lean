import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 2000000

/-! ## The left half `(0, π/4]` -/

/-- **The weighted Hardy inequality on the left half `(0,π/4]`.**

For `0 < β ≤ 1`, `f` of class `C¹` on `(0,π/2)` whose `sin(2·)`-weighted squared derivative is
integrable on `(0,π/4]`:

`∫_{(0,π/4]} f² sin(2θ)^{β-1} ≤ (4/β²)(π/4)² ∫_{(0,π/4]} (f')² sin(2θ)^{1-β} + π/(2β) f(π/4)²`,

and the left-hand integrand is integrable. -/
theorem hardy_half_left_open {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {f : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
      (Set.Ioc (0 : ℝ) (Real.pi / 4))) :
    IntegrableOn (fun θ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        (Set.Ioc (0 : ℝ) (Real.pi / 4)) ∧
      (∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        ≤ 4 / β ^ 2 * (Real.pi / 4) ^ 2
            * (∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 4),
                (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
          + Real.pi / (2 * β) * (f (Real.pi / 4)) ^ 2 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hqpos : (0 : ℝ) < Real.pi / 4 := by linarith
  have hqle : Real.pi / 4 ≤ Real.pi / 2 := by linarith
  have hπ4lt : Real.pi / 4 < Real.pi / 2 := by linarith
  have hβne : β ≠ 0 := ne_of_gt hβ
  -- `sin (2θ) > 0` on `[δ, π/4]` for `0 < δ`
  have hsinpos : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), ∀ θ ∈ Set.Icc δ (Real.pi / 4),
      0 < Real.sin (2 * θ) := by
    intro δ hδ θ hθ
    exact sin_two_pos_of_lt_half (by linarith [hδ.1, hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  -- continuity of `f` and of `deriv f` on `[δ, π/4]`
  have hfcont : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), ContinuousOn f (Set.Icc δ (Real.pi / 4)) :=
    fun δ hδ => hsm.continuousOn.mono (fun x hx =>
      ⟨lt_of_lt_of_le hδ.1 hx.1, lt_of_le_of_lt hx.2 hπ4lt⟩)
  have hdfcont : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      ContinuousOn (deriv f) (Set.Icc δ (Real.pi / 4)) :=
    fun δ hδ => (hsm.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono
      (fun x hx => ⟨lt_of_lt_of_le hδ.1 hx.1, lt_of_le_of_lt hx.2 hπ4lt⟩)
  have hsincont : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (β - 1)) (Set.Icc δ (Real.pi / 4)) := by
    intro δ hδ
    exact (Real.continuous_sin.comp_continuousOn (continuousOn_id.const_mul 2)).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hsinpos δ hδ θ hθ)))
  have hsincont' : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (1 - β)) (Set.Icc δ (Real.pi / 4)) := by
    intro δ hδ
    exact (Real.continuous_sin.comp_continuousOn (continuousOn_id.const_mul 2)).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hsinpos δ hδ θ hθ)))
  have hthcont : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      ContinuousOn (fun θ : ℝ => θ ^ (β - 1)) (Set.Icc δ (Real.pi / 4)) := by
    intro δ hδ
    exact continuousOn_id.rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (lt_of_lt_of_le hδ.1 hθ.1)))
  have hthcont' : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      ContinuousOn (fun θ : ℝ => θ ^ (β + 1)) (Set.Icc δ (Real.pi / 4)) := by
    intro δ hδ
    exact continuousOn_id.rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (lt_of_lt_of_le hδ.1 hθ.1)))
  -- interval integrability of the four integrands on `[δ, π/4]`
  have hIIF : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      IntervalIntegrable (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        volume δ (Real.pi / 4) :=
    fun δ hδ => (((hfcont δ hδ).pow 2).mul (hsincont δ hδ)).intervalIntegrable_of_Icc hδ.2.le
  have hIIFp : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      IntervalIntegrable (fun θ : ℝ => (f θ) ^ 2 * θ ^ (β - 1)) volume δ (Real.pi / 4) :=
    fun δ hδ => (((hfcont δ hδ).pow 2).mul (hthcont δ hδ)).intervalIntegrable_of_Icc hδ.2.le
  have hIIG : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      IntervalIntegrable (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        volume δ (Real.pi / 4) :=
    fun δ hδ => (((hdfcont δ hδ).pow 2).mul (hsincont' δ hδ)).intervalIntegrable_of_Icc hδ.2.le
  have hIIGp : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      IntervalIntegrable (fun θ : ℝ => (deriv f θ) ^ 2 * θ ^ (β + 1))
        volume δ (Real.pi / 4) :=
    fun δ hδ => (((hdfcont δ hδ).pow 2).mul (hthcont' δ hδ)).intervalIntegrable_of_Icc hδ.2.le
  -- ## the per-`δ` bound
  have hdelta : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      (∫ θ in Set.Ioc δ (Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        ≤ 4 / β ^ 2 * (Real.pi / 4) ^ 2
            * (∫ θ in Set.Ioc δ (Real.pi / 4),
                (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
          + Real.pi / (2 * β) * (f (Real.pi / 4)) ^ 2 := by
    intro δ hδ
    have hδle : δ ≤ Real.pi / 4 := hδ.2.le
    have hsub : Set.Icc δ (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
      ⟨lt_of_lt_of_le hδ.1 hx.1, lt_of_le_of_lt hx.2 hπ4lt⟩
    -- the power-weight Hardy inequality on `[δ, π/4]`
    have hA := power_hardy_interval (c := β - 1) (ε := δ) (b := Real.pi / 4) (f := f)
      (by linarith) hδ.1 hδ.2 (hsm.mono hsub)
    rw [show β - 1 + 1 = β from by ring, show β - 1 + 2 = β + 1 from by ring] at hA
    -- in interval-integral form
    have hA' : (∫ θ in δ..(Real.pi / 4), (f θ) ^ 2 * θ ^ (β - 1))
        ≤ 4 / β ^ 2 * (∫ θ in δ..(Real.pi / 4), (deriv f θ) ^ 2 * θ ^ (β + 1))
          + 2 / β * (f (Real.pi / 4)) ^ 2 * (Real.pi / 4) ^ β := by
      simpa only [intervalIntegral.integral_of_le hδle] using hA
    -- comparison 1 : `sin(2θ)^{β-1} ≤ (4/π)^{β-1} θ^{β-1}`
    have hc1 : (∫ θ in δ..(Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        ≤ (4 / Real.pi) ^ (β - 1) * (∫ θ in δ..(Real.pi / 4), (f θ) ^ 2 * θ ^ (β - 1)) := by
      have h := intervalIntegral.integral_mono_on_of_le_Ioo hδle (hIIF δ hδ)
        ((hIIFp δ hδ).const_mul ((4 / Real.pi) ^ (β - 1))) (fun θ hθ => ?_)
      · rwa [intervalIntegral.integral_const_mul] at h
      · have hpt := Work.FTS.H2.Transport3Aux.sin_rpow_sub_le_theta (β := β) hβ1
          (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4) from
            ⟨lt_trans hδ.1 hθ.1, hθ.2⟩)
        calc (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1)
            ≤ (f θ) ^ 2 * ((4 / Real.pi) ^ (β - 1) * θ ^ (β - 1)) :=
              mul_le_mul_of_nonneg_left hpt (sq_nonneg _)
          _ = (4 / Real.pi) ^ (β - 1) * ((f θ) ^ 2 * θ ^ (β - 1)) := by ring
    -- comparison 2 : `θ^{β+1} ≤ (π/4)^{β+1} sin(2θ)^{1-β}`
    have hc2 : (∫ θ in δ..(Real.pi / 4), (deriv f θ) ^ 2 * θ ^ (β + 1))
        ≤ (Real.pi / 4) ^ (β + 1)
            * (∫ θ in δ..(Real.pi / 4), (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) := by
      have h := intervalIntegral.integral_mono_on_of_le_Ioo hδle (hIIGp δ hδ)
        ((hIIG δ hδ).const_mul ((Real.pi / 4) ^ (β + 1))) (fun θ hθ => ?_)
      · rwa [intervalIntegral.integral_const_mul] at h
      · have hpt := Work.FTS.H2.Transport3Aux.theta_rpow_le_sin_rpow (β := β) hβ.le
          (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4) from
            ⟨lt_trans hδ.1 hθ.1, hθ.2⟩)
        calc (deriv f θ) ^ 2 * θ ^ (β + 1)
            ≤ (deriv f θ) ^ 2 * ((Real.pi / 4) ^ (β + 1) * (Real.sin (2 * θ)) ^ (1 - β)) :=
              mul_le_mul_of_nonneg_left hpt (sq_nonneg _)
          _ = (Real.pi / 4) ^ (β + 1)
                * ((deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) := by ring
    -- the constants
    have hcpos : (0 : ℝ) ≤ (4 / Real.pi) ^ (β - 1) := Real.rpow_nonneg (by positivity) _
    have hdpos : (0 : ℝ) ≤ 4 / β ^ 2 := by positivity
    have hcomb : (∫ θ in δ..(Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        ≤ 4 / β ^ 2 * (Real.pi / 4) ^ 2
            * (∫ θ in δ..(Real.pi / 4),
                (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
          + Real.pi / (2 * β) * (f (Real.pi / 4)) ^ 2 := by
      have hdpos2 : (0 : ℝ) ≤ 4 / β ^ 2 := by positivity
      calc (∫ θ in δ..(Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
          ≤ (4 / Real.pi) ^ (β - 1)
              * (∫ θ in δ..(Real.pi / 4), (f θ) ^ 2 * θ ^ (β - 1)) := hc1
        _ ≤ (4 / Real.pi) ^ (β - 1)
              * (4 / β ^ 2 * (∫ θ in δ..(Real.pi / 4), (deriv f θ) ^ 2 * θ ^ (β + 1))
                + 2 / β * (f (Real.pi / 4)) ^ 2 * (Real.pi / 4) ^ β) :=
              mul_le_mul_of_nonneg_left hA' hcpos
        _ ≤ (4 / Real.pi) ^ (β - 1)
              * (4 / β ^ 2 * ((Real.pi / 4) ^ (β + 1)
                  * (∫ θ in δ..(Real.pi / 4),
                      (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)))
                + 2 / β * (f (Real.pi / 4)) ^ 2 * (Real.pi / 4) ^ β) := by
              refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) hcpos
              exact mul_le_mul_of_nonneg_left hc2 hdpos2
        _ = (4 / Real.pi) ^ (β - 1) * (4 / β ^ 2) * (Real.pi / 4) ^ (β + 1)
              * (∫ θ in δ..(Real.pi / 4),
                  (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
            + (4 / Real.pi) ^ (β - 1) * (2 / β) * (Real.pi / 4) ^ β
              * (f (Real.pi / 4)) ^ 2 := by ring
        _ = 4 / β ^ 2 * (Real.pi / 4) ^ 2
              * (∫ θ in δ..(Real.pi / 4),
                  (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
            + Real.pi / (2 * β) * (f (Real.pi / 4)) ^ 2 := by
              rw [Work.FTS.H2.Transport3Aux.quarter_const_mul β,
                Work.FTS.H2.Transport3Aux.bdry_const_mul hβne]
    simpa only [intervalIntegral.integral_of_le hδle] using hcomb
  -- ## integrability of the left-hand integrand
  have hFcont_Ioo : ContinuousOn (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
      (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
    ((hsm.continuousOn.mono (fun x hx =>
        ⟨hx.1, lt_trans hx.2 hπ4lt⟩)).pow 2).mul
      ((Real.continuous_sin.comp_continuousOn (continuousOn_id.const_mul 2)).rpow_const
        (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_of_lt_half hθ.1 (lt_trans hθ.2 hπ4lt)))))
  have hGnn : ∀ x ∈ Set.Ioc (0 : ℝ) (Real.pi / 4),
      0 ≤ (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β) := fun x hx =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
        (by linarith [hx.2, Real.pi_pos])) _)
  have hunif : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      (∫ θ in Set.Ioc δ (Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        ≤ 4 / β ^ 2 * (Real.pi / 4) ^ 2
            * (∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 4),
                (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
          + Real.pi / (2 * β) * (f (Real.pi / 4)) ^ 2 := by
    intro δ hδ
    have hmono : (∫ θ in Set.Ioc δ (Real.pi / 4),
          (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        ≤ ∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 4),
            (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β) :=
      setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hGnn))
        (Ioc_subset_Ioc_left hδ.1.le).eventuallyLE
    have h1 := mul_le_mul_of_nonneg_left hmono
      (by positivity : (0 : ℝ) ≤ 4 / β ^ 2 * (Real.pi / 4) ^ 2)
    linarith [hdelta δ hδ, h1]
  have hFint_Ioo : IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
      (Set.Ioo (0 : ℝ) (Real.pi / 4)) := by
    refine Work.FTS.EllSol.VthAux.traceAux.integrableOn_of_forall_Ioc_le
      (C := 4 / β ^ 2 * (Real.pi / 4) ^ 2
        * (∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 4),
            (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        + Real.pi / (2 * β) * (f (Real.pi / 4)) ^ 2) hqpos ?_ hFcont_Ioo ?_ hunif
    · intro δ hδ
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.2.le).mp (hIIF δ hδ)
    · exact Filter.Eventually.of_forall (fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
          (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
            (by linarith [hx.2, Real.pi_pos])) _))
  have hFint_Ioc : IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
      (Set.Ioc (0 : ℝ) (Real.pi / 4)) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo).mpr hFint_Ioo
  refine ⟨hFint_Ioc, ?_⟩
  -- ## pass to the limit `δ → 0⁺`
  exact setIntegral_Ioc_le_of_uniform_bound hqpos hFint_Ioc hint (fun δ hδ => hdelta δ hδ)

end

end Work.FTS.StrongPersist.N6Trans.SixRoute
