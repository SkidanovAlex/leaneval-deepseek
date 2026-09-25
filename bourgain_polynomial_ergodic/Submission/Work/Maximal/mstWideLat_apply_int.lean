import Mathlib
import Submission.Work.Maximal.mstWideLat_defs
import Submission.Work.Maximal.mstMax_bridge
import Submission.Work.BourgainPlan.IonescuWainger.ftLp_eq_discFourier
import Submission.Work.BourgainPlan.Maximal.iw_superset
import Submission.Work.Maximal.opMul_apply_eq_integral

/-!
# The values of the band-limited interpolant `mstWideLat` at the integers

This module proves the *sampling* identity of the wide-model route (MST arXiv:1512.07518, the
large-scale half of Theorem 8): the band-limited interpolant `mstWideLat` of the wide-bump
multiplier takes at the integers exactly the *multiplier values*

`mstWideLat P χ η s F T j = (opMul (ϱ_s) F) (-j)`.

The proof is the comparison of two formulas for the same circle Fourier coefficient of the symbol
`ϱ_s · 𝓕F`:

* `mstWideLat_eq_circleFourierCoeff_aux` (below): the inverse Fourier transform
  `mstWideLat = 𝓕⁻ (mstWideExt)` at `j` is the integral `∫_𝕋 e^{2πi j θ} ϱ_s(θ) 𝓕F(θ) dθ`.  Since
  `mstWideExt x = η (c_s x) · Σ_{n∈T} F n e^{2πi n x}` and `c_s ≥ 1` with `supp η ⊆ [-1/2,1/2]`,
  the amplitude lives inside one fundamental period `Ioc (-1/2) (1/2)`, where `ϱ_s` is
  `η (c_s ·)` and `𝓕F` is the finite sum over `T`; `AddCircle.integral_preimage` converts the
  set integral over the period into the Haar integral over `𝕋`.
* `Work.Maximal.opMul_apply_eq_integral` (colleague's lemma, imported): the coefficients of the
  multiplier `opMul Φ F` are the circle integrals `∫_𝕋 Φ θ · 𝓕F(θ) · conj (e^{2πi m θ}) dθ`.

With `m = -j` and `Φ = ϱ_s` (the `L^∞`-class of `hφ`) the two agree, since
`star (fourier (-j) θ) = fourier j θ` and `ftLp F hF =ᵐ discFourier F` (finite support).
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Maximal

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

noncomputable section

/-- **`mstWideLat` at the integers is a circle Fourier coefficient.**  The value at `j ∈ ℤ` of the
band-limited interpolant `𝓕⁻ (mstWideExt)` is the `j`-th Fourier coefficient of the circle symbol
`θ ↦ ϱ_s(θ) · 𝓕F(θ)`.

Route: `𝓕⁻ (mstWideExt) j = ∫_ℝ e^{2πi j x} mstWideExt x dx` (`Real.fourierInv_eq'`); the
integrand vanishes a.e. off the fundamental period `Ioc (-1/2) (1/2)` because `η (c_s x) = 0` for
`|x| > 1/2` (`c_s ≥ 1`), so the integral is the set integral over that period; on the period
`mstWideExt x = η (c_s x) · 𝓕F x = ϱ_s (x : 𝕋) · 𝓕F (x : 𝕋)` and `e^{2πi j x} = fourier j (x : 𝕋)`
(`iwRep (x : 𝕋) = x` for `x ∈ Ioc (-1/2) (1/2)`, `fourier_coe_apply`); and
`AddCircle.integral_preimage` (plus `AddCircle.integral_haarAddCircle`, the Haar measure of `𝕋`
being normalised) turns the set integral over the period into the Haar integral over `𝕋`. -/
private theorem mstWideLat_eq_circleFourierCoeff_aux (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ)
    (s : ℕ) (F : ℤ → ℂ) (T : Finset ℤ) (hηc : ContDiff ℝ 2 η)
    (hηsup : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (hT : ∀ n ∉ T, F n = 0) (j : ℤ) :
    mstWideLat P χ η s F T (j : ℝ)
      = ∫ θ : Circ, fourier j θ
          * (mstWideBump P χ η s θ
            * Work.BourgainPlan.IonescuWainger.discFourier F θ) ∂haarT := by
  set f : ℝ → ℂ := fun x => Complex.exp (↑(2 * Real.pi * (x * (j : ℝ))) * Complex.I)
      * mstWideExt P χ η s F T x with hfdef
  have hfapply : ∀ x : ℝ, f x = Complex.exp (↑(2 * Real.pi * (x * (j : ℝ))) * Complex.I)
      * mstWideExt P χ η s F T x := fun x => by rw [hfdef]
  -- Step 1: unfold `fourierInv` as the defining integral.
  have h1 : mstWideLat P χ η s F T (j : ℝ) = ∫ x : ℝ, f x := by
    rw [mstWideLat_apply, Real.fourierInv_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.inner_apply, smul_eq_mul]
    rw [hfapply x]
  -- Step 2: the integrand vanishes a.e. off the fundamental period.
  have hc1 : (1 : ℝ) ≤ mstWideC P s := one_le_mstWideC P s
  have hzero : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Set.Ioc (-(1/2:ℝ)) (1/2) → f x = 0 := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (t := ({-(1/2:ℝ)} : Set ℝ) ∪ {(1/2:ℝ)}) ?_ ?_
    · intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      push Not at hx
      obtain ⟨hxI, hxf⟩ := hx
      rw [Set.mem_union, Set.mem_singleton_iff, Set.mem_singleton_iff]
      by_contra hcon
      push Not at hcon
      refine hxf (by
        have hxabs : 1/2 < |x| := by
          have hx' : x ≤ -(1/2:ℝ) ∨ 1/2 < x := by
            by_contra h
            push Not at h
            exact hxI ⟨h.1, h.2⟩
          rcases hx' with h1 | h1
          · have hlt : x < -(1/2:ℝ) := lt_of_le_of_ne h1 hcon.1
            rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        have harg : 1/2 < |mstWideC P s * x| := by
          rw [abs_mul, abs_of_nonneg (le_trans zero_le_one hc1)]
          nlinarith [abs_nonneg x, hxabs]
        have heta : η (mstWideC P s * x) = 0 := hηsup _ harg
        rw [hfapply x, mstWideExt, heta, zero_mul, mul_zero])
    · exact MeasureTheory.measure_union_null (measure_singleton _) (measure_singleton _)
  -- Step 3: on the fundamental period the integrand is the circle symbol.
  have hpoint : ∀ x ∈ Set.Ioc (-(1/2:ℝ)) (1/2),
      f x = fourier j (x : Circ)
        * (mstWideBump P χ η s (x : Circ)
          * Work.BourgainPlan.IonescuWainger.discFourier F (x : Circ)) := by
    intro x hx
    have hx' : x ∈ Set.Ioc (-(1/2:ℝ)) (-(1/2:ℝ) + 1) := by
      rw [show (-(1/2:ℝ) + 1) = 1/2 by norm_num]; exact hx
    have hrep : Work.BourgainPlan.Maximal.iwRep (x : Circ) = x := by
      simp only [Work.BourgainPlan.Maximal.iwRep]
      exact AddCircle.liftIoc_coe_apply (f := fun y : ℝ => y) hx'
    rw [hfapply x, mstWideExt_eq_discFourier P χ η s F hT x, mstWideBump_apply, hrep,
      fourier_coe_apply]
    have hexp : (↑(2 * Real.pi * (x * (j : ℝ))) * Complex.I : ℂ)
        = 2 * ↑Real.pi * Complex.I * ↑j * ↑x / ↑(1:ℝ) := by push_cast; ring
    rw [hexp]
  -- Step 4: assemble, converting the period integral into the circle integral.
  rw [h1, ← MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero hzero]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun x hx => hpoint x hx)]
  rw [AddCircle.integral_haarAddCircle, inv_one, one_smul]
  have hfinal := AddCircle.integral_preimage (T := 1) (-(1/2))
    (fun θ : Circ => fourier j θ
      * (mstWideBump P χ η s θ * Work.BourgainPlan.IonescuWainger.discFourier F θ))
  rw [show (-(1/2:ℝ) + 1) = 1/2 by norm_num] at hfinal
  exact hfinal

end

theorem mstWideLat_apply_int (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ) (F : ℤ → ℂ)
    (T : Finset ℤ) (hηc : ContDiff ℝ 2 η) (hηsup : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hT : ∀ n ∉ T, F n = 0) (hF : Memℓp F 2)
    (hφ : MeasureTheory.MemLp (Work.Maximal.mstWideBump P χ η s) ⊤
      (AddCircle.haarAddCircle (T := 1))) (j : ℤ) :
    Work.Maximal.mstWideLat P χ η s F T (j : ℝ)
      = Work.BourgainPlan.IonescuWainger.opMul
          (hφ.toLp (Work.Maximal.mstWideBump P χ η s)) F hF (-j) := by
  -- The left-hand side is a circle Fourier coefficient of the symbol `ϱ_s · 𝓕F`.
  have hL := mstWideLat_eq_circleFourierCoeff_aux P χ η s F T hηc hηsup hT j
  -- The right-hand side is the same coefficient of the same symbol.
  have hsumm : Summable fun m : ℤ => ‖F m‖ :=
    summable_of_ne_finset_zero (s := T) (fun n hn => by rw [hT n hn, norm_zero])
  have hft : (Work.BourgainPlan.IonescuWainger.ftLp F hF : Circ → ℂ)
      =ᵐ[haarT] Work.BourgainPlan.IonescuWainger.discFourier F :=
    Work.BourgainPlan.IonescuWainger.ftLp_eq_discFourier hsumm hF
  have hΦ : ((hφ.toLp (Work.Maximal.mstWideBump P χ η s)
        : MeasureTheory.Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) : Circ → ℂ)
      =ᵐ[haarT] Work.Maximal.mstWideBump P χ η s := MemLp.coeFn_toLp hφ
  have hR := Work.Maximal.opMul_apply_eq_integral
    (hφ.toLp (Work.Maximal.mstWideBump P χ η s)) F hF (-j)
  rw [hL, hR]
  refine integral_congr_ae ?_
  filter_upwards [hft, hΦ] with θ hftθ hΦθ
  have hstar : star (fourier (-j) θ) = fourier j θ := by
    rw [← starRingEnd_apply, ← fourier_neg (n := (-j)) (x := θ), neg_neg]
  rw [hftθ, hΦθ, hstar]
  ring

end Work.Maximal
