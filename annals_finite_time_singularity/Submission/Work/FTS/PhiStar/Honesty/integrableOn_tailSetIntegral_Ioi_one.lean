import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.PhiStar.Honesty.lintegral_tail_swap_Ioi_one

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set

open scoped ENNReal

/-- Bochner-integral form of the tail Fubini identity on `(1,∞)`: for `Q` integrable on
`(1,∞)` with `Q ≥ 0` a.e. and `t ↦ Q t * t` integrable, the function
`z ↦ ∫_z^∞ Q t dt` is integrable on `(1,∞)` and
`∫_1^∞ (∫_z^∞ Q t dt) dz = ∫_1^∞ Q t (t - 1) dt`.

The proof passes to `ℝ≥0∞`-valued `lintegral`s (`ofReal_integral_eq_lintegral_ofReal`), applies
the Tonelli-type identity `lintegral_tail_swap_Ioi_one` there, and returns with
`integral_eq_lintegral_of_nonneg_ae`; finiteness of the `lintegral` comes from the integrability
of `t ↦ Q t * (t - 1)`, which is `(Q t * t) - Q t`. -/
theorem integrableOn_tailSetIntegral_Ioi_one {Q : ℝ → ℝ}
    (hQ : MeasureTheory.IntegrableOn Q (Set.Ioi (1 : ℝ)))
    (hQnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))] Q)
    (hQt : MeasureTheory.IntegrableOn (fun t : ℝ => Q t * t) (Set.Ioi (1 : ℝ))) :
    MeasureTheory.IntegrableOn (fun z : ℝ => ∫ t in Set.Ioi z, Q t) (Set.Ioi (1 : ℝ)) ∧
      (∫ z in Set.Ioi (1 : ℝ), (∫ t in Set.Ioi z, Q t))
        = ∫ t in Set.Ioi (1 : ℝ), Q t * (t - 1) := by
  have hSmeas : MeasurableSet (Set.Ioi (1 : ℝ)) := measurableSet_Ioi
  -- (1) the integrand `t ↦ Q t * (t - 1)` is integrable: it is `(Q t * t) - Q t`
  have hQ1 : MeasureTheory.IntegrableOn (fun t : ℝ => Q t * (t - 1)) (Set.Ioi (1 : ℝ)) := by
    refine (hQt.sub hQ).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply]
    ring
  -- (2) the tail integral is nonnegative on `(1,∞)`
  have hGnn : ∀ z ∈ Set.Ioi (1 : ℝ), 0 ≤ ∫ t in Set.Ioi z, Q t := by
    intro z hz
    have hz' : (1 : ℝ) < z := hz
    have hsub : Set.Ioi z ⊆ Set.Ioi (1 : ℝ) := fun y hy => lt_trans hz' hy
    exact integral_nonneg_of_ae (ae_restrict_of_ae_restrict_of_subset hsub hQnn)
  -- (3) `ofReal` of the tail integral is the tail `lintegral` of `ofReal Q`
  have hinner : ∀ z ∈ Set.Ioi (1 : ℝ),
      ENNReal.ofReal (∫ t in Set.Ioi z, Q t)
        = ∫⁻ t in Set.Ioi z, ENNReal.ofReal (Q t) := by
    intro z hz
    have hz' : (1 : ℝ) < z := hz
    have hsub : Set.Ioi z ⊆ Set.Ioi (1 : ℝ) := fun y hy => lt_trans hz' hy
    exact ofReal_integral_eq_lintegral_ofReal (hQ.mono_set hsub)
      (ae_restrict_of_ae_restrict_of_subset hsub hQnn)
  -- (4) the `lintegral` identity (Tonelli on the triangle `1 < z < t`)
  have hkey : ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (∫ t in Set.Ioi z, Q t)
      = ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal (Q t * (t - 1)) := by
    have hQme : AEMeasurable (fun t : ℝ => ENNReal.ofReal (Q t))
        (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
      hQ.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    have hswap := lintegral_tail_swap_Ioi_one
      (P := fun _ : ℝ => (1 : ENNReal)) (Q := fun t : ℝ => ENNReal.ofReal (Q t))
      aemeasurable_const hQme (fun _ => ENNReal.one_ne_top) (fun _ => ENNReal.ofReal_ne_top)
    calc ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (∫ t in Set.Ioi z, Q t)
        = ∫⁻ z in Set.Ioi (1 : ℝ), (∫⁻ t in Set.Ioi z, ENNReal.ofReal (Q t)) :=
          setLIntegral_congr_fun hSmeas (fun z hz => hinner z hz)
      _ = ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal (Q t)
            * (∫⁻ z in (Set.Ioi (1 : ℝ) ∩ Set.Iio t), (1 : ENNReal)) := by
          simpa using hswap
      _ = ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal (Q t * (t - 1)) := by
          apply setLIntegral_congr_fun hSmeas
          intro t ht
          have ht1 : (1 : ℝ) < t := ht
          change ENNReal.ofReal (Q t) * (∫⁻ z in (Set.Ioi (1 : ℝ) ∩ Set.Iio t), (1 : ENNReal))
            = ENNReal.ofReal (Q t * (t - 1))
          rw [show (Set.Ioi (1 : ℝ) ∩ Set.Iio t) = Set.Ioo (1 : ℝ) t from rfl,
            setLIntegral_one, Real.volume_Ioo]
          rw [← ENNReal.ofReal_mul' (show (0 : ℝ) ≤ t - 1 by linarith)]
  -- (5) the right-hand `lintegral` is finite
  have hQ1nn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))]
      (fun t : ℝ => Q t * (t - 1)) := by
    filter_upwards [hQnn, ae_restrict_mem hSmeas] with t htQ htS
    exact mul_nonneg htQ (by simp only [Set.mem_Ioi] at htS; linarith)
  have hfin : ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal (Q t * (t - 1)) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal hQ1nn).mp (Integrable.hasFiniteIntegral hQ1)
  have hGlinn : ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (∫ t in Set.Ioi z, Q t) < ⊤ := by
    rw [hkey]; exact hfin
  -- (6) the tail integral is continuous (hence a.e. strongly measurable) on `(1,∞)`
  have hGcont : ContinuousOn (fun z : ℝ => ∫ t in Set.Ioi z, Q t) (Set.Ioi (1 : ℝ)) :=
    hQ.continuousOn_Ici_primitive_Ioi.mono
      (Set.Ioi_subset_Ici_self : Set.Ioi (1 : ℝ) ⊆ Set.Ici (1 : ℝ))
  have hGmeas : AEStronglyMeasurable (fun z : ℝ => ∫ t in Set.Ioi z, Q t)
      (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
    hGcont.aestronglyMeasurable hSmeas
  -- (7) nonnegativity of the tail integral a.e. on `(1,∞)`
  have hGnn_ae : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))]
      (fun z : ℝ => ∫ t in Set.Ioi z, Q t) :=
    (ae_restrict_mem hSmeas).mono (fun z hz => hGnn z hz)
  refine ⟨?_, ?_⟩
  · exact ⟨hGmeas, (hasFiniteIntegral_iff_ofReal hGnn_ae).mpr hGlinn⟩
  · have e1 : ∫ z in Set.Ioi (1 : ℝ), (∫ t in Set.Ioi z, Q t)
        = ENNReal.toReal (∫⁻ z in Set.Ioi (1 : ℝ),
            ENNReal.ofReal (∫ t in Set.Ioi z, Q t)) :=
      integral_eq_lintegral_of_nonneg_ae hGnn_ae hGmeas
    have e2 : ∫ t in Set.Ioi (1 : ℝ), Q t * (t - 1)
        = ENNReal.toReal (∫⁻ t in Set.Ioi (1 : ℝ),
            ENNReal.ofReal (Q t * (t - 1))) :=
      integral_eq_lintegral_of_nonneg_ae hQ1nn (Integrable.aestronglyMeasurable hQ1)
    rw [e1, e2, hkey]

end Work.FTS.PhiStar.Honesty
