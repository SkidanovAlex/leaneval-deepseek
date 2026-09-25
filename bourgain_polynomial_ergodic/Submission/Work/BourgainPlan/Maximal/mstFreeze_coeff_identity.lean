import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_lvl_err_aux
import Submission.Work.BourgainPlan.Maximal.mst_freeze_defs
import Submission.Work.BourgainPlan.Maximal.mstFreezeFn_fourierCoeff
import Submission.Work.BourgainPlan.Maximal.mst_freeze_lift_pointwise

/-!
# The coefficient identity of the frozen single-arc error term

This file proves `mstFreeze_coeff_identity`: the `m`-th Fourier coefficient of the frozen arc error
`mstFreezeFn P J d χ η s k β` (MST §4.4, eq. (99)) is the average over `σ ∈ (0,1)` of
`c⁻¹ mstHat Ξ ((P(2^kσ) + m)/c)`, multiplied by `star (fourier m β)`.

The companion file `mstFreezeFn_fourierCoeff.lean` proves the same identity under the *stronger*
hypothesis `ContDiff ℝ 2 η` (continuity of the bump), which enters only through the Fubini step
`mst_freeze_fubini`.  Here the bump is only assumed bounded (`hηbd`), supported in `|x| ≤ 1/2`
(`hη2`) and a.e. strongly measurable (`hηm`), so the Fubini step is replaced by its a.e. version
`mst_freeze_fubini_ae` below: on the rectangle `(u,σ) ∈ (−1/2,1/2) × (0,1)`, of finite measure, the
uncurried integrand is bounded by `2M` and a.e. strongly measurable (the composition `u ↦ η (c u)`
of an a.e. strongly measurable function with the quasi-measure-preserving dilation `u ↦ c u`), hence
integrable (`IntegrableOn.of_bound`), and Fubini applies.
-/

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-- **A.e. strong measurability is preserved by a nontrivial dilation**: the function
`u ↦ η (c u)` (`c ≠ 0`) is a.e. strongly measurable whenever `η` is.  The dilation `u ↦ c u` is
quasi-measure-preserving for the Lebesgue measure (`Measure.quasiMeasurePreserving_smul`). -/
theorem aestronglyMeasurable_eta_comp_mul {η : ℝ → ℂ}
    (hηm : AEStronglyMeasurable η (volume : Measure ℝ)) {c : ℝ} (hc : c ≠ 0) :
    AEStronglyMeasurable (fun u : ℝ => η (c * u)) (volume : Measure ℝ) := by
  have h := hηm.aemeasurable.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (E := ℝ) hc)
  simpa [Function.comp_def, smul_eq_mul] using h.aestronglyMeasurable

/-- The local `mstTht_norm` helper: `mstTht` is a difference of two numbers of modulus at most
one, hence `‖mstTht P J β r u‖ ≤ 2`. -/
theorem norm_polyWeylKernel_le_one_self (P : Polynomial ℤ) (N : ℕ) (θ : ℝ) :
    ‖polyWeylKernel P N θ‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [polyWeylKernel]
  · have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hscal : ‖((((N : ℝ))⁻¹) : ℂ)‖ = (N : ℝ)⁻¹ := by
      rw [show ((((N : ℝ))⁻¹) : ℂ) = ((N : ℂ))⁻¹ by push_cast; ring, norm_inv,
        Complex.norm_natCast]
    have hsum : ‖∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I *
        (((θ * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ))‖ ≤ (N : ℝ) := by
      calc ‖∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I *
              (((θ * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ))‖
          ≤ ∑ n ∈ Finset.range N, ‖Complex.exp (2 * Real.pi * Complex.I *
              (((θ * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ))‖ := norm_sum_le _ _
        _ = ∑ _n ∈ Finset.range N, (1 : ℝ) := by
            refine Finset.sum_congr rfl (fun n _ => ?_)
            rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I *
                (((θ * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ)
              = (((2 * Real.pi * (θ * ((P.eval (n : ℤ) : ℤ) : ℝ))) : ℝ) : ℂ) * Complex.I by
              push_cast; ring]
            exact Complex.norm_exp_ofReal_mul_I _
        _ = (N : ℝ) := by simp
    calc ‖polyWeylKernel P N θ‖
        = ‖((((N : ℝ))⁻¹) : ℂ)‖ * ‖∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I *
            (((θ * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ))‖ := by
          rw [polyWeylKernel, norm_mul]
      _ ≤ (N : ℝ)⁻¹ * (N : ℝ) := by
          rw [hscal]
          exact mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hN0)

/-- `‖mstTht P J β r u‖ ≤ 2`. -/
theorem norm_mstTht_le_two (P : Polynomial ℤ) (J : ℕ) (β : Circ) (r u : ℝ) :
    ‖mstTht P J β r u‖ ≤ 2 := by
  rw [mstTht_apply]
  calc ‖star (mstG P β) - star (polyWeylKernel P J (r + u))‖
      ≤ ‖star (mstG P β)‖ + ‖star (polyWeylKernel P J (r + u))‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := by
        refine add_le_add ?_ ?_
        · rw [norm_star]; exact mstG_norm_le_one P β
        · rw [norm_star]; exact norm_polyWeylKernel_le_one_self P J (r + u)
    _ = 2 := by norm_num

/-- The lifted error symbol is continuous in the offset. -/
theorem continuous_mstTht_self (P : Polynomial ℤ) (J : ℕ) (β : Circ) (r : ℝ) :
    Continuous (fun u : ℝ => mstTht P J β r u) := by
  rw [show (fun u : ℝ => mstTht P J β r u)
      = fun u : ℝ => star (mstG P β) - star (polyWeylKernel P J (r + u)) from by
    funext u; rw [mstTht_apply]]
  exact continuous_const.sub (((continuous_polyWeylKernel P J).comp
    (continuous_const.add continuous_id)).star)

/-- **The Fubini step of the freezing estimate, with an a.e. measurable bump.**  The same statement
as `mst_freeze_fubini`, but with `ContDiff ℝ 2 η` replaced by the boundedness and a.e. strong
measurability of `η`: the uncurried integrand is bounded by `2M` on the rectangle
`(−1/2,1/2) × (0,1)`, of finite measure, and a.e. strongly measurable, hence integrable. -/
theorem mst_freeze_fubini_ae (P : Polynomial ℤ) (J : ℕ)
    (β : Circ) (η : ℝ → ℂ) {M : ℝ}
    (hηm : AEStronglyMeasurable η (volume : Measure ℝ))
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (c : ℝ) (k : ℕ) (m : ℤ) :
    (∫ u in (-(1 / 2))..(1 / 2), mstTht P J β (iwRep β) u * η (c * u) *
        (∫ σ in (0 : ℝ)..1, Complex.exp ((((-(2 * Real.pi * (u *
          (toRealPoly P).eval ((2 ^ k : ℝ) * σ)))) : ℝ) : ℂ)
          * Complex.I)) *
        Complex.exp ((((-(2 * Real.pi * (u * (m : ℝ)))) : ℝ) : ℂ) * Complex.I))
      = ∫ σ in (0 : ℝ)..1, ∫ u in (-(1 / 2))..(1 / 2), mstTht P J β (iwRep β) u * η (c * u) *
        Complex.exp ((((-(2 * Real.pi * (u * ((toRealPoly P).eval
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
  have hAcont : Continuous (fun u : ℝ => mstTht P J β (iwRep β) u) :=
    continuous_mstTht_self P J β (iwRep β)
  have hBmeas : AEStronglyMeasurable (fun u : ℝ => η (c * u))
      (volume.restrict (Set.uIoc (-(1 / 2)) (1 / 2))) := by
    by_cases hc : c = 0
    · subst hc
      have hconst : (fun u : ℝ => η (0 * u)) = fun _ : ℝ => η 0 := by
        funext u; rw [zero_mul]
      rw [hconst]
      exact aestronglyMeasurable_const
    · exact (aestronglyMeasurable_eta_comp_mul hηm hc).mono_measure Measure.restrict_le_self
  have hXcont : Continuous (fun p : ℝ × ℝ =>
      Complex.exp ((((-(2 * Real.pi * (p.1 *
        (toRealPoly P).eval ((2 ^ k : ℝ) * p.2)))) : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  have hYcont : Continuous (fun p : ℝ × ℝ =>
      Complex.exp ((((-(2 * Real.pi * (p.1 * (m : ℝ)))) : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  -- Integrability of the uncurried integrand on the product of the two intervals.
  have hInt : IntegrableOn (Function.uncurry (fun u σ : ℝ =>
      mstTht P J β (iwRep β) u * η (c * u) *
        (Complex.exp ((((-(2 * Real.pi * (u *
          (toRealPoly P).eval ((2 ^ k : ℝ) * σ)))) : ℝ) : ℂ) * Complex.I) *
         Complex.exp ((((-(2 * Real.pi * (u * (m : ℝ)))) : ℝ) : ℂ) * Complex.I))))
      (Set.uIoc (-(1 / 2)) (1 / 2) ×ˢ Set.uIoc (0 : ℝ) 1) := by
    refine IntegrableOn.of_bound ?_ ?_ (2 * M) ?_
    · rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl, Measure.prod_prod,
        Real.volume_uIoc, Real.volume_uIoc]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    · rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl, ← Measure.prod_restrict]
      have h1 : AEStronglyMeasurable (fun z : ℝ × ℝ => mstTht P J β (iwRep β) z.1)
          ((volume.restrict (Set.uIoc (-(1 / 2)) (1 / 2))).prod
            (volume.restrict (Set.uIoc (0 : ℝ) 1))) :=
        hAcont.aestronglyMeasurable.comp_fst
      have h2 : AEStronglyMeasurable (fun z : ℝ × ℝ => η (c * z.1))
          ((volume.restrict (Set.uIoc (-(1 / 2)) (1 / 2))).prod
            (volume.restrict (Set.uIoc (0 : ℝ) 1))) :=
        hBmeas.comp_fst
      have h3 : AEStronglyMeasurable (fun z : ℝ × ℝ =>
          Complex.exp ((((-(2 * Real.pi * (z.1 *
            (toRealPoly P).eval ((2 ^ k : ℝ) * z.2)))) : ℝ) : ℂ) * Complex.I))
          ((volume.restrict (Set.uIoc (-(1 / 2)) (1 / 2))).prod
            (volume.restrict (Set.uIoc (0 : ℝ) 1))) :=
        hXcont.aestronglyMeasurable
      have h4 : AEStronglyMeasurable (fun z : ℝ × ℝ =>
          Complex.exp ((((-(2 * Real.pi * (z.1 * (m : ℝ)))) : ℝ) : ℂ) * Complex.I))
          ((volume.restrict (Set.uIoc (-(1 / 2)) (1 / 2))).prod
            (volume.restrict (Set.uIoc (0 : ℝ) 1))) :=
        hYcont.aestronglyMeasurable
      exact (h1.mul h2).mul (h3.mul h4)
    · refine Filter.Eventually.of_forall (fun z => ?_)
      simp only [Function.uncurry]
      have hb : ‖mstTht P J β (iwRep β) z.1 * η (c * z.1) *
            (Complex.exp ((((-(2 * Real.pi * (z.1 *
              (toRealPoly P).eval ((2 ^ k : ℝ) * z.2)))) : ℝ) : ℂ) * Complex.I) *
             Complex.exp ((((-(2 * Real.pi * (z.1 * (m : ℝ)))) : ℝ) : ℂ) * Complex.I))‖
          = ‖mstTht P J β (iwRep β) z.1‖ * ‖η (c * z.1)‖ := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
          Complex.norm_exp_ofReal_mul_I, mul_one, mul_one]
      rw [hb]
      exact mul_le_mul (norm_mstTht_le_two P J β (iwRep β) z.1) (hηbd (c * z.1))
        (norm_nonneg _) (by norm_num)
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

/-- `star (fourier m β) = fourier (-m)` read at the canonical lift of `β`. -/
theorem star_fourier_eq_mstFreezeChar (m : ℤ) (β : Circ) :
    star (fourier m β) = mstFreezeChar (iwRep β) (m : ℝ) := by
  calc star (fourier m β) = fourier (-m) (((iwRep β : ℝ) : Circ)) := by
        rw [coe_iwRep, fourier_neg, starRingEnd_apply]
    _ = mstFreezeChar (iwRep β) (m : ℝ) := fourier_neg_coe_eq m (iwRep β)


theorem mstFreeze_coeff_identity (P : Polynomial ℤ) {d : ℕ} {χ : ℝ} {η : ℝ → ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hχ : χ + 1 ≤ (d : ℝ)) (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hηm : MeasureTheory.AEStronglyMeasurable η (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (J s k : ℕ) (β : Work.BourgainPlan.IonescuWainger.Circle) (m : ℤ) :
    fourierCoeff (Work.BourgainPlan.Maximal.mstFreezeFn P J d χ η s k β) m
      = star (fourier m β) * ∫ σ in (0 : ℝ)..1,
          (Work.BourgainPlan.Maximal.mstScale d χ s)⁻¹ *
            Work.BourgainPlan.Maximal.mstHat
              (Work.BourgainPlan.Maximal.mstFreezeXi P J β
                (Work.BourgainPlan.Maximal.mstScale d χ s) η)
              (((Work.BourgainPlan.Maximal.toRealPoly P).eval ((2 ^ k : ℝ) * σ) + (m : ℝ))
                / Work.BourgainPlan.Maximal.mstScale d χ s) := by
  have _hM := hM
  have hcpos : 0 < mstScale d χ s := mstScale_pos d χ s
  have hc1 : 1 ≤ mstScale d χ s := one_le_mstScale hχ s
  have hcne : mstScale d χ s ≠ 0 := hcpos.ne'
  have hcne' : ((mstScale d χ s : ℝ) : ℂ) ≠ 0 := by
    intro h
    exact hcne (Complex.ofReal_inj.mp (by simpa using h))
  have hΛ0 : ∀ w : ℝ, 1 / 2 < |w| → mstFreezeXi P J β (mstScale d χ s) η w = 0 := by
    intro w hw
    rw [mstFreezeXi_apply, hη2 w hw, mul_zero]
  -- Step 1 : the coefficient as an integral over the interval centred at the arc
  have h1 : fourierCoeff (mstFreezeFn P J d χ η s k β) m
      = ∫ x in (iwRep β - 1 / 2)..(iwRep β + 1 / 2),
          (fourier (-m)) ((x : ℝ) : Circ) * mstFreezeFn P J d χ η s k β ((x : ℝ) : Circ) := by
    rw [fourierCoeff_eq_intervalIntegral (T := 1) _ m (iwRep β - 1 / 2)]
    rw [show iwRep β - 1 / 2 + 1 = iwRep β + 1 / 2 by ring,
      show ((1 : ℝ) / 1) = 1 by norm_num, one_smul]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [smul_eq_mul]
  -- Step 2 : the integrand read on the fundamental interval
  set G : ℝ → ℂ := fun x => mstFreezeChar (iwRep β) (m : ℝ) *
      (mstFreezeChar (x - iwRep β) (m : ℝ) *
        (mstTht P J β (iwRep β) (x - iwRep β) *
          ((∫ σ in (0 : ℝ)..1, mstFreezeChar (x - iwRep β)
              ((toRealPoly P).eval ((2 ^ k : ℝ) * σ))) *
            η (mstScale d χ s * (x - iwRep β))))) with hG
  have hstep1 : (∫ x in (iwRep β - 1 / 2)..(iwRep β + 1 / 2),
        (fourier (-m)) ((x : ℝ) : Circ) * mstFreezeFn P J d χ η s k β ((x : ℝ) : Circ))
      = ∫ x in (iwRep β - 1 / 2)..(iwRep β + 1 / 2), G x := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => ?_))
    have hmem : x ∈ Set.Ioc (iwRep β - 1 / 2) (iwRep β + 1 / 2) := by
      rwa [Set.uIoc_of_le (by linarith : iwRep β - 1 / 2 ≤ iwRep β + 1 / 2)] at hx
    rw [hG]
    simp only
    rw [mst_freeze_lift_pointwise P J d χ η s k β x hmem, fourier_neg_coe_eq]
    rw [show mstFreezeChar x (m : ℝ)
        = mstFreezeChar (iwRep β) (m : ℝ) * mstFreezeChar (x - iwRep β) (m : ℝ) by
      rw [mstFreezeChar_mul, show iwRep β + (x - iwRep β) = x by ring]]
    simp only [mstFreezeChar]
    ring
  -- Step 3 : the translation `x = iwRep β + u`
  have hstep2 : (∫ x in (iwRep β - 1 / 2)..(iwRep β + 1 / 2), G x)
      = ∫ u in (-(1 / 2))..(1 / 2), G (u + iwRep β) := by
    have h := intervalIntegral.integral_comp_add_right (a := (-(1 / 2) : ℝ)) (b := (1 / 2 : ℝ))
      (f := G) (d := iwRep β)
    rw [show (-(1 / 2) : ℝ) + iwRep β = iwRep β - 1 / 2 by ring,
      show (1 / 2 : ℝ) + iwRep β = iwRep β + 1 / 2 by ring] at h
    exact h.symm
  -- Step 4 : the integrand in the offset variable
  set H : ℝ → ℂ := fun u => mstTht P J β (iwRep β) u * η (mstScale d χ s * u) *
      (∫ σ in (0 : ℝ)..1, mstFreezeChar u ((toRealPoly P).eval ((2 ^ k : ℝ) * σ))) *
      mstFreezeChar u (m : ℝ) with hH
  have hstep3 : (∫ u in (-(1 / 2))..(1 / 2), G (u + iwRep β))
      = mstFreezeChar (iwRep β) (m : ℝ) * ∫ u in (-(1 / 2))..(1 / 2), H u := by
    rw [hG, hH]
    simp only [add_sub_cancel_right]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    ring
  -- Step 5 : Fubini
  have hstep4 : (∫ u in (-(1 / 2))..(1 / 2), H u)
      = ∫ σ in (0 : ℝ)..1, ∫ u in (-(1 / 2))..(1 / 2), mstTht P J β (iwRep β) u *
          η (mstScale d χ s * u) *
          mstFreezeChar u ((toRealPoly P).eval ((2 ^ k : ℝ) * σ) + (m : ℝ)) := by
    rw [hH]
    have hf := mst_freeze_fubini_ae P J β η hηm hηbd (mstScale d χ s) k m
    simpa only [mstFreezeChar] using hf
  -- Step 6 : the dilation, one `σ` at a time
  have hstep5 : (∫ σ in (0 : ℝ)..1, ∫ u in (-(1 / 2))..(1 / 2), mstTht P J β (iwRep β) u *
          η (mstScale d χ s * u) *
          mstFreezeChar u ((toRealPoly P).eval ((2 ^ k : ℝ) * σ) + (m : ℝ)))
      = ((mstScale d χ s : ℝ) : ℂ)⁻¹ *
        ∫ σ in (0 : ℝ)..1, mstHat (mstFreezeXi P J β (mstScale d χ s) η)
          (((m : ℝ) + (toRealPoly P).eval ((2 ^ k : ℝ) * σ)) / mstScale d χ s) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun σ _ => ?_)
    rw [show ((m : ℝ) + (toRealPoly P).eval ((2 ^ k : ℝ) * σ))
        = ((toRealPoly P).eval ((2 ^ k : ℝ) * σ) + (m : ℝ)) by ring]
    have hd := mstHat_dilate_char (mstFreezeXi P J β (mstScale d χ s) η) (mstScale d χ s)
      ((toRealPoly P).eval ((2 ^ k : ℝ) * σ) + (m : ℝ)) hc1 hΛ0
    have hid : (∫ u in (-(1 / 2))..(1 / 2), mstFreezeXi P J β (mstScale d χ s) η
          (mstScale d χ s * u) * mstFreezeChar u
            ((toRealPoly P).eval ((2 ^ k : ℝ) * σ) + (m : ℝ)))
        = ∫ u in (-(1 / 2))..(1 / 2), mstTht P J β (iwRep β) u * η (mstScale d χ s * u) *
            mstFreezeChar u ((toRealPoly P).eval ((2 ^ k : ℝ) * σ) + (m : ℝ)) := by
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      rw [mstFreezeXi_apply,
        show (mstScale d χ s * u) / mstScale d χ s = u by field_simp]
    rw [hd, hid, inv_mul_cancel_left₀ hcne']
  rw [h1, hstep1, hstep2, hstep3, hstep4, hstep5]
  rw [← star_fourier_eq_mstFreezeChar]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun σ _ => ?_)
  rw [Complex.ofReal_inv]
  congr 1
  ring

end

end Work.BourgainPlan.Maximal
