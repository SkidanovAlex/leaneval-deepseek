import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.dilation_hl

namespace Work.BourgainPlan.Maximal

open MeasureTheory Set
open scoped ENNReal

/-! ## The inverse Fouriertransform of the conjugated profile

The identity proved here is the bridge between the two halves of Bourgain §7:
the multiplier given by the (conjugated) oscillatory profile `polyProfile P N` acts on `𝓕⁻G`
by averaging over the polynomial values `P(N s)`,

`𝓕⁻ (G · conj (polyProfile P N)) (x) = ∫_{(0,1]} 𝓕⁻G (x − P(N s)) ds`.

The right-hand side is exactly the shape of the real-variable dilation average of §7.1
(`dilation_hl`: `purePower_dilation_le_hlMax`), so this lemma is what converts a §7.2 model
operator into a §7.1 maximal function.

We write `polyE t = e(t) = exp(2πi t)` for the complex-valued exponential character; the on-disk
profile is `polyProfile P N β = ∫_0^1 polyE (β P(N s)) ds` (`polyProfile_eq_polyE`), and Mathlib's
`fourierInv` is `𝓕⁻G w = ∫ β, polyE (β w) G β` (`fourierInv_eq_polyE_integral`).  The whole proof
is then the double-integral computation

`∫ β, e(βx) G β ∫_s conj e(β P(N s)) = ∫_s ∫ β e(β(x − P(N s))) G β`,

conjugation producing the minus sign. -/

/-- The complex-valued exponential character `t ↦ e(t) = exp(2πi t)`. -/
noncomputable def polyE (t : ℝ) : ℂ := Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

lemma polyE_add (a b : ℝ) : polyE a * polyE b = polyE (a + b) := by
  unfold polyE
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The character is unitary: `conj (e t) = e (−t)`. -/
lemma star_polyE (t : ℝ) : starRingEnd ℂ (polyE t) = polyE (-t) := by
  unfold polyE
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

lemma polyE_mul_neg (a b : ℝ) : polyE a * polyE (-b) = polyE (a - b) := by
  rw [polyE_add, sub_eq_add_neg]

@[simp] lemma norm_polyE (t : ℝ) : ‖polyE t‖ = 1 := by
  unfold polyE
  rw [Complex.norm_exp]
  simp

lemma continuous_polyE : Continuous polyE := by
  unfold polyE
  fun_prop

/-- The on-disk profile in terms of the character: `polyProfile P N β = ∫_0^1 e(β P(N s)) ds`. -/
lemma polyProfile_eq_polyE (P : Polynomial ℤ) (N : ℕ) (β : ℝ) :
    polyProfile P N β = ∫ s in (0:ℝ)..1, polyE (β * (toRealPoly P).eval ((N:ℝ)*s)) := by
  rw [polyProfile]
  apply intervalIntegral.integral_congr
  intro s _
  show Complex.exp (2 * ↑Real.pi * Complex.I * ↑(β * Polynomial.eval (↑N * s) (toRealPoly P)))
      = polyE (β * Polynomial.eval (↑N * s) (toRealPoly P))
  unfold polyE
  congr 1
  push_cast
  ring

/-- The conjugated profile as the average of the conjugate character. -/
lemma star_polyProfile (P : Polynomial ℤ) (N : ℕ) (β : ℝ) :
    starRingEnd ℂ (polyProfile P N β)
      = ∫ s in (0:ℝ)..1, polyE (-(β * (toRealPoly P).eval ((N:ℝ)*s))) := by
  rw [polyProfile_eq_polyE P N β, ← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro s _
  exact star_polyE _

/-- Mathlib's `fourierInv` on `ℝ` as an integral against the character `e(βw)`. -/
lemma fourierInv_eq_polyE_integral (G : ℝ → ℂ) (w : ℝ) :
    FourierTransform.fourierInv G w = ∫ β, polyE (β * w) * G β := by
  rw [Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with β
  rw [Real.inner_apply, smul_eq_mul]
  rfl

/-- **The conjugated `polyProfile` multiplier acts by a dilation average.**  With the on-disk
oscillatory profile `polyProfile P N β = ∫_0^1 e(+β P(N s)) ds` and Mathlib's `fourierInv`
(which also carries the sign `+`), the inverse transform of the product against an amplitude `G` is
the dilation average of `𝓕⁻G` along the polynomial values `P(N s)`:

`𝓕⁻ (G · conj (polyProfile P N)) (x) = ∫_{(0,1]} 𝓕⁻G (x − P(N s)) ds`.

The conjugate is exactly what makes the sign match: the *non-conjugated* profile gives the average
along `x + P(N s)`.  (In the corpus's model the multiplier is `conj (polyMajorArcModelPre P δ N ·)`,
see `polyTkMax` in `Submission/Work/BourgainPlan/Maximal/l2_defs.lean`.)  For the pure powers
`P = X^d` this is the identity that turns the §7.2 model into the real-variable dilation average of
§7.1, for which `Submission.Work.BourgainPlan.Maximal.dilation_hl` proves the `hlMax`/`L^p` bound
(`purePower_dilation_le_hlMax`, `purePower_sup_lintegral_rpow_le`). -/
theorem polyProfile_fourier_dilation (P : Polynomial ℤ) (N : ℕ) {G : ℝ → ℂ} (hG : Integrable G)
    (hGinv : Integrable (FourierTransform.fourierInv G)) (x : ℝ) :
    FourierTransform.fourierInv
        (fun β => G β * starRingEnd ℂ (Work.BourgainPlan.Maximal.polyProfile P N β)) x
      = ∫ s in (0:ℝ)..1,
          FourierTransform.fourierInv G
            (x - (Work.BourgainPlan.Maximal.toRealPoly P).eval ((N:ℝ) * s)) := by
  have _hGinv := hGinv
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

end Work.BourgainPlan.Maximal
