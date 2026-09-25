import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.polyProfile_fourier_dilation

/-!
# The curve average identity for the polynomial profile

`mstMax_curve` identifies the inverse Fourier transform of the product of the *conjugated*
oscillatory profile `x ↦ polyProfile P N (-x)` with an amplitude `W` with the average of
`𝓕⁻W` along the polynomial curve `u ↦ P(N u)`:

`𝓕⁻ (polyProfile P N (-·) · W) (y) = ∫_{0}^{1} 𝓕⁻W (y − P(N u)) du`.

This is the `G = W` instance of `polyProfile_fourier_dilation`, the point being that the
conjugation there is exactly `polyProfile P N (-x) = conj (polyProfile P N x)`; the auxiliary
lemma below records that identity.  Unlike `polyProfile_fourier_dilation` no integrability of
`𝓕⁻W` is needed: the interchange of the two integrals only uses `Integrable W`.
-/

namespace Work.Maximal

open MeasureTheory Set
open scoped ENNReal

/-- The oscillatory profile at `−β` is the complex conjugate of the profile at `β`:
`polyProfile P N (−β) = conj (polyProfile P N β)`. -/
lemma polyProfile_neg (P : Polynomial ℤ) (N : ℕ) (β : ℝ) :
    Work.BourgainPlan.Maximal.polyProfile P N (-β)
      = starRingEnd ℂ (Work.BourgainPlan.Maximal.polyProfile P N β) := by
  rw [Work.BourgainPlan.Maximal.star_polyProfile,
      Work.BourgainPlan.Maximal.polyProfile_eq_polyE]
  apply intervalIntegral.integral_congr
  intro s _
  apply congrArg Work.BourgainPlan.Maximal.polyE
  ring

/-- **The conjugated profile multiplier acts by the curve average.**
For an integrable amplitude `W`, the inverse Fourier transform of `β ↦ polyProfile P N (−β) · W β`
is the average of `𝓕⁻W` along the polynomial values `P(N s)`:
`𝓕⁻ (polyProfile P N (−·) · W) (y) = ∫_{(0,1]} 𝓕⁻W (y − P(N s)) ds`. -/
theorem fourierInv_polyProfile_neg {P : Polynomial ℤ} {N : ℕ} {W : ℝ → ℂ}
    (hW : Integrable W) (y : ℝ) :
    FourierTransformInv.fourierInv
        (fun β : ℝ => Work.BourgainPlan.Maximal.polyProfile P N (-β) * W β) y
      = ∫ s in (0:ℝ)..1, FourierTransformInv.fourierInv W
          (y - (Work.BourgainPlan.Maximal.toRealPoly P).eval ((N:ℝ)*s)) := by
  have hν : IsFiniteMeasure (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),
        Real.volume_Ioc]
        norm_num⟩
  have := hν
  -- the joint integrand `(s, β) ↦ e(β(y − P(N s))) W β` is integrable for the product measure
  have hint : Integrable
      (Function.uncurry (fun s β : ℝ =>
        Work.BourgainPlan.Maximal.polyE (β * (y - (Work.BourgainPlan.Maximal.toRealPoly P).eval ((N:ℝ)*s))) * W β))
      ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod volume) := by
    have hcont : Continuous (fun p : ℝ × ℝ =>
        Work.BourgainPlan.Maximal.polyE (p.2 * (y - (Work.BourgainPlan.Maximal.toRealPoly P).eval ((N:ℝ) * p.1)))) := by
      refine Work.BourgainPlan.Maximal.continuous_polyE.comp ?_
      refine Continuous.mul continuous_snd ?_
      refine Continuous.sub continuous_const ?_
      exact (Polynomial.continuous (Work.BourgainPlan.Maximal.toRealPoly P)).comp
        (continuous_const.mul continuous_fst)
    refine (hW.norm.comp_snd (volume.restrict (Set.uIoc (0:ℝ) 1))).mono' ?_ ?_
    · exact (hcont.aestronglyMeasurable.mul hW.aestronglyMeasurable.comp_snd)
    · filter_upwards with p
      rw [Function.uncurry, norm_mul, Work.BourgainPlan.Maximal.norm_polyE, one_mul]
  -- Fubini for an interval integral against a full integral
  have hfub := intervalIntegral_integral_swap (μ := volume) (a := (0:ℝ)) (b := 1)
      (f := fun s β => Work.BourgainPlan.Maximal.polyE
        (β * (y - (Work.BourgainPlan.Maximal.toRealPoly P).eval ((N:ℝ)*s))) * W β) hint
  rw [Work.BourgainPlan.Maximal.fourierInv_eq_polyE_integral]
  rw [show (∫ s in (0:ℝ)..1, FourierTransformInv.fourierInv W
          (y - (Work.BourgainPlan.Maximal.toRealPoly P).eval ((N:ℝ)*s)))
      = ∫ s in (0:ℝ)..1, ∫ β, Work.BourgainPlan.Maximal.polyE
          (β * (y - (Work.BourgainPlan.Maximal.toRealPoly P).eval ((N:ℝ)*s))) * W β from by
    apply intervalIntegral.integral_congr
    intro s _
    exact Work.BourgainPlan.Maximal.fourierInv_eq_polyE_integral W _]
  rw [hfub]
  -- the two iterated integrals agree by the pointwise computation
  apply integral_congr_ae
  filter_upwards with β
  rw [polyProfile_neg, Work.BourgainPlan.Maximal.star_polyProfile]
  rw [show Work.BourgainPlan.Maximal.polyE (β * y)
        * ((∫ s in (0:ℝ)..1, Work.BourgainPlan.Maximal.polyE
              (-(β * (Work.BourgainPlan.Maximal.toRealPoly P).eval ((N:ℝ)*s)))) * W β)
      = (Work.BourgainPlan.Maximal.polyE (β * y) * W β)
        * (∫ s in (0:ℝ)..1, Work.BourgainPlan.Maximal.polyE
              (-(β * (Work.BourgainPlan.Maximal.toRealPoly P).eval ((N:ℝ)*s))))
      from by ring]
  rw [← intervalIntegral.integral_const_mul (Work.BourgainPlan.Maximal.polyE (β * y) * W β)
      (fun s => Work.BourgainPlan.Maximal.polyE
        (-(β * (Work.BourgainPlan.Maximal.toRealPoly P).eval ((N:ℝ)*s))))]
  apply intervalIntegral.integral_congr
  intro s _
  show (Work.BourgainPlan.Maximal.polyE (β * y) * W β)
        * Work.BourgainPlan.Maximal.polyE (-(β * (Work.BourgainPlan.Maximal.toRealPoly P).eval ((N:ℝ)*s)))
      = Work.BourgainPlan.Maximal.polyE
          (β * (y - (Work.BourgainPlan.Maximal.toRealPoly P).eval ((N:ℝ)*s))) * W β
  rw [show (Work.BourgainPlan.Maximal.polyE (β * y) * W β)
        * Work.BourgainPlan.Maximal.polyE (-(β * (Work.BourgainPlan.Maximal.toRealPoly P).eval ((N:ℝ)*s)))
      = (Work.BourgainPlan.Maximal.polyE (β * y)
          * Work.BourgainPlan.Maximal.polyE (-(β * (Work.BourgainPlan.Maximal.toRealPoly P).eval ((N:ℝ)*s)))) * W β
      from by ring]
  rw [Work.BourgainPlan.Maximal.polyE_mul_neg]
  rw [show β * y - β * (Work.BourgainPlan.Maximal.toRealPoly P).eval ((N:ℝ)*s)
      = β * (y - (Work.BourgainPlan.Maximal.toRealPoly P).eval ((N:ℝ)*s)) from by ring]

/-- **The curve average identity.** The inverse Fourier transform of the product of the conjugated
profile `x ↦ polyProfile P N (−x)` with an integrable amplitude `W` equals the average of
`𝓕⁻W` over the polynomial curve `u ↦ P(N u)`. -/
theorem mstMax_curve (P : Polynomial ℤ) (N : ℕ) (W : ℝ → ℂ)
    (hW : MeasureTheory.Integrable W MeasureTheory.volume) (y : ℝ) :
    FourierTransformInv.fourierInv
        (fun x : ℝ => Work.BourgainPlan.Maximal.polyProfile P N (-x) * W x) y
      = ∫ u in (0:ℝ)..1, FourierTransformInv.fourierInv W
          (y - Polynomial.eval ((N : ℝ) * u) (Polynomial.map (Int.castRingHom ℝ) P)) :=
  fourierInv_polyProfile_neg hW y

end Work.Maximal
