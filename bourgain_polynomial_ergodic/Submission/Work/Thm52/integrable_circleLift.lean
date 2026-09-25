import Mathlib
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs

namespace Work.Thm52

open MeasureTheory Set
open scoped ENNReal

/-- The fundamental-domain lift of an essentially bounded circle function is integrable on `ℝ`:
`circleLift f x = f (-(x : Circle))` for `x ∈ Ioc (-1/2) (1/2]` and `0` outside, so it is supported
in an interval of length `1` and bounded a.e. by the essential supremum of `f`. -/
theorem integrable_circleLift {f : Work.BourgainPlan.IonescuWainger.Circle → ℂ}
    (hf : MeasureTheory.MemLp f ⊤ (AddCircle.haarAddCircle (T := 1))) :
    MeasureTheory.Integrable (Work.BourgainPlan.Thm52.circleLift f) := by
  -- The fundamental domain and its measure.
  have hs_meas : MeasurableSet (Set.Ioc (-(1/2 : ℝ)) (1/2)) := measurableSet_Ioc
  have hvols : volume (Set.Ioc (-(1/2 : ℝ)) (1/2)) = 1 := by
    rw [Real.volume_Ioc]; norm_num
  -- The standard measure on the circle is the (normalised) Haar measure.
  have hvol : (volume : Measure (AddCircle (1 : ℝ))) = AddCircle.haarAddCircle (T := 1) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
  -- The covering map restricted to the fundamental domain, followed by negation, is
  -- measure preserving from `volume.restrict (Ioc (-1/2) (1/2))` to the Haar measure.
  have hmk := AddCircle.measurePreserving_mk (T := 1) (-(1/2 : ℝ))
  rw [show (-(1/2 : ℝ) + 1) = 1/2 by norm_num] at hmk
  have hneg : MeasurePreserving (fun y : AddCircle (1 : ℝ) => -y)
      (volume : Measure (AddCircle (1 : ℝ))) (volume : Measure (AddCircle (1 : ℝ))) :=
    Measure.measurePreserving_neg _
  have hgmp : MeasurePreserving (fun x : ℝ => -(x : AddCircle (1 : ℝ)))
      (volume.restrict (Set.Ioc (-(1/2 : ℝ)) (1/2)))
      (AddCircle.haarAddCircle (T := 1)) := by
    have h : MeasurePreserving (fun x : ℝ => -(x : AddCircle (1 : ℝ)))
        (volume.restrict (Set.Ioc (-(1/2 : ℝ)) (1/2)))
        (volume : Measure (AddCircle (1 : ℝ))) :=
      hneg.comp hmk
    rwa [hvol] at h
  -- An a.e. bound for `f`, from the finiteness of its essential supremum.
  obtain ⟨A, hA⟩ : ∃ A : ℝ, ∀ᵐ (y : AddCircle (1 : ℝ)) ∂(AddCircle.haarAddCircle (T := 1)),
      ‖f y‖ₑ ≤ ENNReal.ofReal A := by
    refine ⟨(essSup (fun y => ‖f y‖ₑ) (AddCircle.haarAddCircle (T := 1))).toReal, ?_⟩
    have htop : essSup (fun y => ‖f y‖ₑ) (AddCircle.haarAddCircle (T := 1)) < ⊤ := by
      have h := hf.eLpNorm_lt_top
      rwa [eLpNorm_exponent_top hf.aestronglyMeasurable, eLpNormEssSup_eq_essSup_enorm] at h
    rw [ENNReal.ofReal_toReal htop.ne]
    exact ae_le_essSup
  -- Pull the bound back to the fundamental domain along the measure-preserving map.
  have hA' : ∀ᵐ (x : ℝ) ∂(volume.restrict (Set.Ioc (-(1/2 : ℝ)) (1/2))),
      ‖f (-(x : AddCircle (1 : ℝ)))‖ₑ ≤ ENNReal.ofReal A :=
    Measure.QuasiMeasurePreserving.ae (f := fun x : ℝ => -(x : AddCircle (1 : ℝ)))
      hgmp.quasiMeasurePreserving hA
  -- The lift is the indicator of the fundamental domain applied to the lifted function.
  have hlift : Work.BourgainPlan.Thm52.circleLift f
      = (Set.Ioc (-(1/2 : ℝ)) (1/2)).indicator
          (fun x : ℝ => f (-(x : AddCircle (1 : ℝ)))) := by
    funext x
    by_cases hx : x ∈ Set.Ioc (-(1/2 : ℝ)) (1/2)
    · rw [Set.indicator_of_mem hx, Work.BourgainPlan.Thm52.circleLift_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Work.BourgainPlan.Thm52.circleLift_of_notMem hx]
  -- The same, for the pointwise norm.
  have hen : (fun a : ℝ => ‖Work.BourgainPlan.Thm52.circleLift f a‖ₑ)
      = (Set.Ioc (-(1/2 : ℝ)) (1/2)).indicator
          (fun x : ℝ => ‖f (-(x : AddCircle (1 : ℝ)))‖ₑ) := by
    funext x
    by_cases hx : x ∈ Set.Ioc (-(1/2 : ℝ)) (1/2)
    · rw [Set.indicator_of_mem hx, Work.BourgainPlan.Thm52.circleLift_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Work.BourgainPlan.Thm52.circleLift_of_notMem hx]
      simp
  refine ⟨?_, ?_⟩
  · -- Almost-everywhere strong measurability, from the measure-preserving map and the fact that
    -- the lift is an indicator.
    rw [hlift]
    exact (aestronglyMeasurable_indicator_iff hs_meas).mpr (hf.aestronglyMeasurable.comp_measurePreserving hgmp)
  · -- Finiteness of the integral, from the a.e. bound on the finite-measure fundamental domain.
    show ∫⁻ (a : ℝ), ‖Work.BourgainPlan.Thm52.circleLift f a‖ₑ < ⊤
    rw [hen, lintegral_indicator hs_meas]
    calc ∫⁻ x in Set.Ioc (-(1/2 : ℝ)) (1/2), ‖f (-(x : AddCircle (1 : ℝ)))‖ₑ
        ≤ ∫⁻ x in Set.Ioc (-(1/2 : ℝ)) (1/2), ENNReal.ofReal A := lintegral_mono_ae hA'
      _ = ENNReal.ofReal A := by
          rw [lintegral_const, Measure.restrict_apply_univ, hvols, mul_one]
      _ < ⊤ := ENNReal.ofReal_lt_top

end Work.Thm52
