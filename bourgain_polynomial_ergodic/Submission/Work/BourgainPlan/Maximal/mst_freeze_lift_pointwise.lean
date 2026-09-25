import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_freeze_defs
import Submission.Work.BourgainPlan.Maximal.polyProfile_fourier_dilation

namespace Work.BourgainPlan.Maximal

/-- **The single-arc error term, read on the fundamental interval** (the `* Complex.I` sits INSIDE
each `Complex.exp`, i.e. the character is `e^{−2πi θ}`; an earlier version of this statement had it
outside and was rightly rejected in review).

For `x` in the fundamental interval centred at `r = iwRep β` (i.e. `x ∈ Ioc (r−1/2) (r+1/2)`),
the one-arc error term equals the lifted symbol at the offset `x − r`, times the profile average of
the character `e^{−2πi (x−r) P(2^k σ)}`, times the level bump at `c (x−r)`.

Ingredients available in the corpus:
* `Work.BourgainPlan.Maximal.mstProf_apply`, `Work.BourgainPlan.Maximal.mstWeyl_apply` (definitions);
* `Work.BourgainPlan.Maximal.coe_iwRep`, `Work.BourgainPlan.Maximal.mstEta_eq_mstScale`;
* `polyWeylKernel_of_coe_eq` (`Maximal/mst_major_err1_l2`) for `polyWeylKernel P J (iwRep ((x:ℝ):𝕋))
  = polyWeylKernel P J x`;
* `star_polyProfile` (`Maximal/polyProfile_fourier_dilation`) for
  `star (polyProfile P N β) = ∫_s e^{−2πi β P(N s)} ds`;
* `AddCircle.liftIoc_coe_apply` for `iwRep ((u:ℝ):𝕋) = u` when `u ∈ Ioc (−1/2) (1/2]`. -/
theorem mst_freeze_lift_pointwise (P : Polynomial ℤ) (J d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s k : ℕ)
    (β : Work.BourgainPlan.IonescuWainger.Circle) (x : ℝ)
    (hx : x ∈ Set.Ioc (Work.BourgainPlan.Maximal.iwRep β - 1 / 2)
      (Work.BourgainPlan.Maximal.iwRep β + 1 / 2)) :
    Work.BourgainPlan.Maximal.mstFreezeFn P J d χ η s k β
        ((x : ℝ) : Work.BourgainPlan.IonescuWainger.Circle)
      = Work.BourgainPlan.Maximal.mstTht P J β (Work.BourgainPlan.Maximal.iwRep β)
          (x - Work.BourgainPlan.Maximal.iwRep β) *
          ((∫ σ in (0 : ℝ)..1, Complex.exp ((((-(2 * Real.pi * ((x -
            Work.BourgainPlan.Maximal.iwRep β) * (Work.BourgainPlan.Maximal.toRealPoly P).eval
            ((2 ^ k : ℝ) * σ)))) : ℝ) : ℂ) * Complex.I)) *
          η (Work.BourgainPlan.Maximal.mstScale d χ s *
            (x - Work.BourgainPlan.Maximal.iwRep β))) := by
  -- The offset `x − iwRep β` lies in the fundamental interval `Ioc (−1/2) (1/2]`
  -- (`(-1/2) + 1 = 1/2`), so it is the canonical lift of `(x : 𝕋) − β`.
  have hxIoc : x - iwRep β ∈ Set.Ioc (-(1/2)) (-(1/2) + 1) := by
    rw [Set.mem_Ioc] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  have hcoe : (((x - iwRep β : ℝ)) : Work.BourgainPlan.IonescuWainger.Circle)
      = (((x : ℝ)) : Work.BourgainPlan.IonescuWainger.Circle) - β := by
    rw [AddCircle.coe_sub, coe_iwRep]
  have hiw : iwRep ((((x : ℝ)) : Work.BourgainPlan.IonescuWainger.Circle) - β)
      = x - iwRep β := by
    rw [← hcoe, iwRep]
    exact AddCircle.liftIoc_coe_apply hxIoc
  -- first factor: the Weyl kernel at `(x : 𝕋)` is the lifted Weyl kernel at `x`
  have hWeyl : star (mstWeyl P J ((x : ℝ) : Work.BourgainPlan.IonescuWainger.Circle))
      = star (polyWeylKernel P J x) := by
    rw [mstWeyl_apply]
    exact congrArg star (polyWeylKernel_of_coe_eq P J (coe_iwRep _))
  -- the lifted symbol at the offset `x − iwRep β` is that same difference
  have hTht : mstTht P J β (iwRep β) (x - iwRep β)
      = star (mstG P β) - star (polyWeylKernel P J x) := by
    rw [mstTht_apply, show iwRep β + (x - iwRep β) = x from by ring]
  -- second factor: the profile average of the character `e^{−2πi (x−r) P(2^k σ)}`
  have hProf : star (mstProf P (2 ^ k)
        ((((x : ℝ)) : Work.BourgainPlan.IonescuWainger.Circle) - β))
      = ∫ σ in (0 : ℝ)..1,
          polyE (-((x - iwRep β) * (toRealPoly P).eval ((2 ^ k : ℝ) * σ))) := by
    rw [mstProf_apply, hiw]
    change starRingEnd ℂ (polyProfile P (2 ^ k) (x - iwRep β)) = _
    rw [star_polyProfile]
    apply intervalIntegral.integral_congr
    intro σ _
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  -- `polyE (t) = exp(2πi t)`, so the average is the one displayed in the statement
  have hInt : (∫ σ in (0 : ℝ)..1,
        polyE (-((x - iwRep β) * (toRealPoly P).eval ((2 ^ k : ℝ) * σ))))
      = ∫ σ in (0 : ℝ)..1, Complex.exp ((((-(2 * Real.pi * ((x - iwRep β) *
          (toRealPoly P).eval ((2 ^ k : ℝ) * σ)))) : ℝ) : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro σ _
    unfold polyE
    push_cast
    ring_nf
  -- third factor: the level bump read through the level scale
  have hEta : mstEta d χ η s ((((x : ℝ)) : Work.BourgainPlan.IonescuWainger.Circle) - β)
      = η (mstScale d χ s * (x - iwRep β)) := by
    rw [mstEta_eq_mstScale, hiw]
  rw [mstFreezeFn_apply, hWeyl, hProf, hInt, hEta, ← hTht]

end Work.BourgainPlan.Maximal
