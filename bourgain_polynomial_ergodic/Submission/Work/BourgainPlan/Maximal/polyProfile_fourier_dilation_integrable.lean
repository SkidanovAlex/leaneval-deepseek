import Mathlib
import Submission.Work.BourgainPlan.Maximal.polyProfile_fourier_dilation

namespace Work.BourgainPlan.Maximal

open MeasureTheory Set
open scoped ENNReal

/-- Same dilation identity as `polyProfile_fourier_dilation`, but with the (unused) integrability
hypothesis on `𝓕⁻G` dropped: for an integrable amplitude `G` the conjugated `polyProfile P N`
multiplier acts on `𝓕⁻G` by the dilation average along the polynomial values `P(N s)`,

`𝓕⁻ (G · conj (polyProfile P N)) (x) = ∫_{(0,1]} 𝓕⁻G (x − P(N s)) ds`.

The joint integrand used for Fubini is integrable from `hG` alone, since `|e(·)| = 1`; hence the
extra hypothesis `Integrable (𝓕⁻G)` is not needed for the identity to hold. -/
theorem polyProfile_fourier_dilation_integrable (P : Polynomial ℤ) (N : ℕ) {G : ℝ → ℂ}
    (hG : MeasureTheory.Integrable G) (x : ℝ) :
    FourierTransformInv.fourierInv (fun β : ℝ => G β * starRingEnd ℂ (Work.BourgainPlan.Maximal.polyProfile P N β)) x
      = ∫ s in (0:ℝ)..1, FourierTransformInv.fourierInv G (x - (Work.BourgainPlan.Maximal.toRealPoly P).eval ((N:ℝ) * s)) := by
  have key : FourierTransform.fourierInv
        (fun β : ℝ => G β * starRingEnd ℂ (polyProfile P N β)) x
      = ∫ s in (0:ℝ)..1,
          FourierTransform.fourierInv G (x - (toRealPoly P).eval ((N:ℝ) * s)) := by
    have hν : IsFiniteMeasure (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
      ⟨by rw [Measure.restrict_apply_univ, Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Real.volume_Ioc]
          norm_num⟩
    have := hν
    -- the joint integrand `(s, β) ↦ e(β(x − P(Ns))) G β` is integrable for the product measure
    have hint : Integrable
        (Function.uncurry (fun s β : ℝ => polyE (β * (x - (toRealPoly P).eval ((N:ℝ)*s))) * G β))
        ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod volume) := by
      have hcont : Continuous (fun p : ℝ × ℝ =>
          polyE (p.2 * (x - (toRealPoly P).eval ((N:ℝ) * p.1)))) := by
        refine continuous_polyE.comp ?_
        refine Continuous.mul continuous_snd ?_
        refine Continuous.sub continuous_const ?_
        exact (Polynomial.continuous (toRealPoly P)).comp (continuous_const.mul continuous_fst)
      refine (hG.norm.comp_snd (volume.restrict (Set.uIoc (0:ℝ) 1))).mono' ?_ ?_
      · exact (hcont.aestronglyMeasurable.mul hG.aestronglyMeasurable.comp_snd)
      · filter_upwards with p
        rw [Function.uncurry, norm_mul, norm_polyE, one_mul]
    -- Fubini for an interval integral against a full integral
    have hfub := intervalIntegral_integral_swap (μ := volume) (a := (0:ℝ)) (b := 1)
        (f := fun s β => polyE (β * (x - (toRealPoly P).eval ((N:ℝ)*s))) * G β) hint
    rw [fourierInv_eq_polyE_integral]
    rw [show (∫ s in (0:ℝ)..1, FourierTransform.fourierInv G
            (x - (toRealPoly P).eval ((N:ℝ)*s)))
        = ∫ s in (0:ℝ)..1, ∫ β, polyE (β * (x - (toRealPoly P).eval ((N:ℝ)*s))) * G β from by
      apply intervalIntegral.integral_congr
      intro s _
      exact fourierInv_eq_polyE_integral G _]
    rw [hfub]
    -- the two iterated integrals agree by the pointwise computation
    apply integral_congr_ae
    filter_upwards with β
    rw [star_polyProfile]
    rw [show polyE (β * x) * (G β * ∫ s in (0:ℝ)..1, polyE (-(β * (toRealPoly P).eval ((N:ℝ)*s))))
        = (polyE (β * x) * G β) * (∫ s in (0:ℝ)..1, polyE (-(β * (toRealPoly P).eval ((N:ℝ)*s))))
        from by ring]
    rw [← intervalIntegral.integral_const_mul (polyE (β * x) * G β)
        (fun s => polyE (-(β * (toRealPoly P).eval ((N:ℝ)*s))))]
    apply intervalIntegral.integral_congr
    intro s _
    show (polyE (β * x) * G β) * polyE (-(β * (toRealPoly P).eval ((N:ℝ)*s)))
        = polyE (β * (x - (toRealPoly P).eval ((N:ℝ)*s))) * G β
    rw [show (polyE (β * x) * G β) * polyE (-(β * (toRealPoly P).eval ((N:ℝ)*s)))
        = (polyE (β * x) * polyE (-(β * (toRealPoly P).eval ((N:ℝ)*s)))) * G β from by ring]
    rw [polyE_mul_neg]
    rw [show β * x - β * (toRealPoly P).eval ((N:ℝ)*s)
        = β * (x - (toRealPoly P).eval ((N:ℝ)*s)) from by ring]
  exact key

end Work.BourgainPlan.Maximal
