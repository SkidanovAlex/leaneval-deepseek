import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_freeze_defs
import Submission.Work.BourgainPlan.Maximal.polyProfile_fourier_dilation

namespace Work.BourgainPlan.Maximal

open MeasureTheory

/-- **The Fubini step of the freezing estimate** (the `* Complex.I` sits INSIDE each
`Complex.exp`, i.e. the characters are `e^{−2πi θ}`; an earlier version of this statement had it
outside and was rightly rejected in review).  Swapping the `u`-integral (the fundamental offset,
`u ∈ (−1/2,1/2)`) with the `σ`-integral (the profile variable, `σ ∈ (0,1)`); the inner
`σ`-integrand is the profile character `e^{−2πi u P(2^k σ)}`, which combines with the frozen phase
`e^{−2πi u m}` into `e^{−2πi u (P(2^k σ) + m)}`.

Route: apply `intervalIntegral_integral_swap` (as in `polyProfile_fourier_dilation`); it needs the
uncurried integrand to be integrable on `(volume.restrict (uIoc 0 1)).prod volume`, which follows
from continuity of `u ↦ mstTht P J β (iwRep β) u * η (c*u)` (`star_polyWeylKernel_expand` plus
`ContDiff ℝ 2 η`) and the boundedness of the characters.  Note `e^{−2πiuP(2^k σ)} e^{−2πium}
= e^{−2πiu(P(2^k σ)+m)}`. -/
theorem mst_freeze_fubini (P : Polynomial ℤ) (J : ℕ)
    (β : Work.BourgainPlan.IonescuWainger.Circle) (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η)
    (c : ℝ) (k : ℕ) (m : ℤ) :
    (∫ u in (-(1 / 2))..(1 / 2), Work.BourgainPlan.Maximal.mstTht P J β
        (Work.BourgainPlan.Maximal.iwRep β) u * η (c * u) *
        (∫ σ in (0 : ℝ)..1, Complex.exp ((((-(2 * Real.pi * (u *
          (Work.BourgainPlan.Maximal.toRealPoly P).eval ((2 ^ k : ℝ) * σ)))) : ℝ) : ℂ)
          * Complex.I)) *
        Complex.exp ((((-(2 * Real.pi * (u * (m : ℝ)))) : ℝ) : ℂ) * Complex.I))
      = ∫ σ in (0 : ℝ)..1, ∫ u in (-(1 / 2))..(1 / 2), Work.BourgainPlan.Maximal.mstTht P J β
          (Work.BourgainPlan.Maximal.iwRep β) u * η (c * u) *
        Complex.exp ((((-(2 * Real.pi * (u * ((Work.BourgainPlan.Maximal.toRealPoly P).eval
          ((2 ^ k : ℝ) * σ) + (m : ℝ))))) : ℝ) : ℂ) * Complex.I) := by
  -- The two characters combine into the character of the sum of the phases.
  have hchar : ∀ σ u : ℝ,
      Complex.exp ((((-(2 * Real.pi * (u *
          (toRealPoly P).eval ((2 ^ k : ℝ) * σ)))) : ℝ) : ℂ) * Complex.I) *
        Complex.exp ((((-(2 * Real.pi * (u * (m : ℝ)))) : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((((-(2 * Real.pi * (u * ((toRealPoly P).eval
          ((2 ^ k : ℝ) * σ) + (m : ℝ))))) : ℝ) : ℂ) * Complex.I) := by
    intro σ u
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- The lifted symbol is continuous in the offset.
  have hAcont : Continuous (fun u : ℝ => mstTht P J β (iwRep β) u) := by
    rw [show (fun u : ℝ => mstTht P J β (iwRep β) u)
        = fun u : ℝ => star (mstG P β) - star (polyWeylKernel P J (iwRep β + u)) from by
      funext u; rw [mstTht_apply]]
    exact continuous_const.sub (((continuous_polyWeylKernel P J).comp
      (continuous_const.add continuous_id)).star)
  have hBcont : Continuous (fun u : ℝ => η (c * u)) :=
    hηc.continuous.comp (continuous_const.mul continuous_id)
  have hXcont : Continuous (fun p : ℝ × ℝ =>
      Complex.exp ((((-(2 * Real.pi * (p.1 *
        (toRealPoly P).eval ((2 ^ k : ℝ) * p.2)))) : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  have hYcont : Continuous (fun p : ℝ × ℝ =>
      Complex.exp ((((-(2 * Real.pi * (p.1 * (m : ℝ)))) : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  have hcont : Continuous (fun p : ℝ × ℝ =>
      mstTht P J β (iwRep β) p.1 * η (c * p.1) *
        (Complex.exp ((((-(2 * Real.pi * (p.1 *
          (toRealPoly P).eval ((2 ^ k : ℝ) * p.2)))) : ℝ) : ℂ) * Complex.I) *
         Complex.exp ((((-(2 * Real.pi * (p.1 * (m : ℝ)))) : ℝ) : ℂ) * Complex.I))) :=
    ((hAcont.comp continuous_fst).mul (hBcont.comp continuous_fst)).mul (hXcont.mul hYcont)
  -- Integrability of the uncurried integrand on the product of the two intervals.
  have hInt : IntegrableOn (Function.uncurry (fun u σ : ℝ =>
      mstTht P J β (iwRep β) u * η (c * u) *
        (Complex.exp ((((-(2 * Real.pi * (u *
          (toRealPoly P).eval ((2 ^ k : ℝ) * σ)))) : ℝ) : ℂ) * Complex.I) *
         Complex.exp ((((-(2 * Real.pi * (u * (m : ℝ)))) : ℝ) : ℂ) * Complex.I))))
      (Set.uIoc (-(1 / 2)) (1 / 2) ×ˢ Set.uIoc (0 : ℝ) 1) := by
    have hbox : IsCompact (Set.uIcc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.uIcc (0 : ℝ) 1) :=
      isCompact_uIcc.prod isCompact_uIcc
    have hmain : IntegrableOn (Function.uncurry (fun u σ : ℝ =>
        mstTht P J β (iwRep β) u * η (c * u) *
          (Complex.exp ((((-(2 * Real.pi * (u *
            (toRealPoly P).eval ((2 ^ k : ℝ) * σ)))) : ℝ) : ℂ) * Complex.I) *
           Complex.exp ((((-(2 * Real.pi * (u * (m : ℝ)))) : ℝ) : ℂ) * Complex.I))))
        (Set.uIcc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.uIcc (0 : ℝ) 1) :=
      hcont.continuousOn.integrableOn_compact hbox
    exact hmain.mono_set (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  -- Pull the constant `mstTht · η` and the frozen character out of the `σ`-integral.
  rw [show (∫ u in (-(1 / 2))..(1 / 2), mstTht P J β (iwRep β) u * η (c * u) *
        (∫ σ in (0 : ℝ)..1, Complex.exp ((((-(2 * Real.pi * (u *
          (toRealPoly P).eval ((2 ^ k : ℝ) * σ)))) : ℝ) : ℂ) * Complex.I)) *
        Complex.exp ((((-(2 * Real.pi * (u * (m : ℝ)))) : ℝ) : ℂ) * Complex.I))
      = ∫ u in (-(1 / 2))..(1 / 2), ∫ σ in (0 : ℝ)..1,
          mstTht P J β (iwRep β) u * η (c * u) *
            (Complex.exp ((((-(2 * Real.pi * (u *
              (toRealPoly P).eval ((2 ^ k : ℝ) * σ)))) : ℝ) : ℂ) * Complex.I) *
             Complex.exp ((((-(2 * Real.pi * (u * (m : ℝ)))) : ℝ) : ℂ) * Complex.I)) from by
    apply intervalIntegral.integral_congr
    intro u _
    simp only []
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
    ring]
  -- Fubini.
  rw [MeasureTheory.intervalIntegral_intervalIntegral_swap (a := -(1 / 2)) (b := (1 / 2 : ℝ))
      (c := (0 : ℝ)) (d := (1 : ℝ))
      (F := fun u σ : ℝ => mstTht P J β (iwRep β) u * η (c * u) *
            (Complex.exp ((((-(2 * Real.pi * (u *
              (toRealPoly P).eval ((2 ^ k : ℝ) * σ)))) : ℝ) : ℂ) * Complex.I) *
             Complex.exp ((((-(2 * Real.pi * (u * (m : ℝ)))) : ℝ) : ℂ) * Complex.I))) hInt]
  -- Combine the two characters in the inner integral.
  apply intervalIntegral.integral_congr
  intro σ _
  apply intervalIntegral.integral_congr
  intro u _
  simp only []
  rw [hchar σ u]

end Work.BourgainPlan.Maximal
