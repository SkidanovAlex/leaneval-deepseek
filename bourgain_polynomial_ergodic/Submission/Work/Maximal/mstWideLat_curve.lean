import Mathlib
import Submission.Work.Maximal.mstWideLat_defs
import Submission.Work.BourgainPlan.Maximal.polyProfile_fourier_dilation
import Submission.Work.Maximal.mstMax_bridge
import Submission.Work.Maximal.mstMax_curve
import Submission.Work.Maximal.ftLp_eq_finset_sum
import Submission.Work.Maximal.circleLift_ae_eq_congr
import Submission.Work.BourgainPlan.Maximal.mstProf_neg_ae

/-!
# The curve average identity for the wide-bump multiplier (`mstWideLat_curve`)

This module proves the third of the three outputs advertised in `mstWideLat_defs.lean`: the
multiplier `opMul (star (Φ_N) · ϱ_s) F` is the average of the band-limited interpolant
`mstWideLat` along the polynomial curve `u ↦ P(N u)`,

`opMul (hφ.toLp φ) F hF n = ∫_0^1 mstWideLat (-n - P(N u)) du`.

The route is the one prepared by the companion modules:

* `mstMax_bridge` rewrites the multiplier as the inverse Fourier transform at `n` of the
  fundamental-domain lift `circleLift (φ · 𝓕F)`;
* `ftLp_eq_finset_sum` replaces `𝓕F` by the finite trigonometric sum `Σ_{m∈T} F m e^{2πi m ·}`
  and `mstProf_neg_ae` replaces `star (Φ_N ξ)` by `Φ_N (-ξ)`, turning the lift a.e. into
  `x ↦ 𝒫_N(x) · mstWideExt(-x)` where `𝒫_N = polyProfile P N` and
  `mstWideExt x = η (c_s x) Σ_{m∈T} F m e^{2πi m x}` is the amplitude of `mstWideLat`;
* `fourierInv_comp_neg` turns the reflection `x ↦ -x` into `ξ ↦ -ξ` in the inverse transform;
* `mstMax_curve` (the `W = mstWideExt` instance of `polyProfile_fourier_dilation`) evaluates the
  inverse transform of `𝒫_N(-·) · mstWideExt` as the curve average of
  `𝓕⁻ mstWideExt = mstWideLat`.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.Maximal

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

noncomputable section

/-- **`𝓕⁻` respects the reflection of the real variable.**  The inverse Fourier transform of
`x ↦ f (-x)` at `ξ` is the inverse Fourier transform of `f` at `-ξ`, since the kernel
`x ↦ e^{2πi x ξ}` becomes `e^{-2πi x ξ} = e^{2πi x (-ξ)}` under `x ↦ -x`. -/
lemma fourierInv_comp_neg (f : ℝ → ℂ) (ξ : ℝ) :
    FourierTransformInv.fourierInv (fun x => f (-x)) ξ
      = FourierTransformInv.fourierInv f (-ξ) := by
  rw [Real.fourierInv_eq', Real.fourierInv_eq']
  simp only [Real.inner_apply, smul_eq_mul]
  rw [← MeasureTheory.integral_neg_eq_self (μ := volume)
        (f := fun v : ℝ => Complex.exp (↑(2 * Real.pi * (v * ξ)) * Complex.I) * f (-v))]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with v
  rw [neg_neg]
  have hexp : Complex.exp (↑(2 * Real.pi * ((-v) * ξ)) * Complex.I)
      = Complex.exp (↑(2 * Real.pi * (v * (-ξ))) * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [hexp]

/-- **`𝓕⁻` respects a.e. equality.** -/
lemma fourierInv_congr_ae {f g : ℝ → ℂ} (h : f =ᵐ[volume] g) (ξ : ℝ) :
    FourierTransformInv.fourierInv f ξ = FourierTransformInv.fourierInv g ξ := by
  rw [Real.fourierInv_eq', Real.fourierInv_eq']
  apply MeasureTheory.integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

/-- On the fundamental domain `Ioc (-1/2) (1/2)` the canonical lift `iwRep` is the identity. -/
lemma iwRep_coe_of_mem_aux {y : ℝ} (hy : y ∈ Set.Ioc (-(1/2:ℝ)) (1/2)) :
    Work.BourgainPlan.Maximal.iwRep (y : Circ) = y := by
  have h := AddCircle.liftIoc_coe_apply (p := (1:ℝ)) (a := -(1/2:ℝ))
    (f := fun x : ℝ => x) (x := y) (by
      rw [show (-(1/2:ℝ) + 1) = 1/2 by norm_num]; exact hy)
  simpa only [Work.BourgainPlan.Maximal.iwRep] using h

/-- The `m`-th character at the reflection of a real point, written in the exponential form that
`mstWideExt` uses: `e_m(-x) = e^{2πi m (-x)}`. -/
lemma fourier_neg_coe_aux (m : ℤ) (x : ℝ) :
    fourier m (-(x : Circ))
      = Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) * ((-x : ℝ) : ℂ))) := by
  rw [← AddCircle.coe_neg (p := (1:ℝ)) (x := x), fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- **The wide amplitude `mstWideExt` is integrable**: it is the product of the compactly supported
continuous function `x ↦ η (c_s x)` with a bounded trigonometric polynomial, hence continuous with
compact support (contained in `Icc (-1/(2 c_s)) (1/(2 c_s))` by the support hypothesis on `η`). -/
lemma integrable_mstWideExt (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ) (F : ℤ → ℂ)
    (T : Finset ℤ) (hηc : Continuous η) (hηsup : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    Integrable (mstWideExt P χ η s F T) := by
  have hc1 : (1:ℝ) ≤ mstWideC P s := one_le_mstWideC P s
  have hcpos : 0 < mstWideC P s := lt_of_lt_of_le zero_lt_one hc1
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · unfold mstWideExt
    refine Continuous.mul (hηc.comp (continuous_const.mul continuous_id)) ?_
    exact continuous_finset_sum _ fun n _ => Continuous.mul continuous_const
      (Complex.continuous_exp.comp (by fun_prop))
  · refine HasCompactSupport.intro
      (K := Set.Icc (-(1 / (2 * mstWideC P s))) (1 / (2 * mstWideC P s))) isCompact_Icc ?_
    intro x hx
    unfold mstWideExt
    rw [show η (mstWideC P s * x) = 0 from ?_, zero_mul]
    refine hηsup _ ?_
    have hpos : 0 < 1 / (2 * mstWideC P s) := by positivity
    have hxabs : 1 / (2 * mstWideC P s) < |x| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [abs_mul, abs_of_pos hcpos]
    have h1 : mstWideC P s * (1 / (2 * mstWideC P s)) < mstWideC P s * |x| :=
      mul_lt_mul_of_pos_left hxabs hcpos
    have h2 : mstWideC P s * (1 / (2 * mstWideC P s)) = 1 / 2 := by
      field_simp
    linarith

/-- **The a.e. identification of the lifted symbol with the reflected amplitude.**  The
fundamental-domain lift of `ξ ↦ (star (Φ_N ξ) · ϱ_s ξ) · 𝓕F ξ` is a.e. equal to the function
`x ↦ 𝒫_N(x) · mstWideExt(-x)`.

On the circle, `ftLp F =ᵐ Σ_{m∈T} F m e_m` and `star (Φ_N ·) =ᵐ Φ_N (-·)`; the lift then evaluates
at `x ∈ (-1/2, 1/2)` to `𝒫_N(x) · η(-c_s x) · Σ_{m∈T} F m e^{-2πi m x}`, which is exactly
`mstWideExt(-x)`; outside the fundamental domain both sides vanish a.e. (`η` is supported in
`[-1/2, 1/2]` and `c_s ≥ 1`), the only exceptional points being `±1/2`. -/
lemma circleLift_mstWide_ae_eq (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ)
    (s : ℕ) (F : ℤ → ℂ) (T : Finset ℤ) (N : ℕ) (hF : Memℓp F 2)
    (hηsup : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (hT : ∀ n ∉ T, F n = 0) :
    Work.BourgainPlan.Thm52.circleLift
        (fun ξ : Circ => (star (Work.BourgainPlan.Maximal.mstProf P N ξ)
          * mstWideBump P χ η s ξ) * Work.BourgainPlan.IonescuWainger.ftLp F hF ξ)
      =ᵐ[volume]
      fun x : ℝ => Work.BourgainPlan.Maximal.polyProfile P N x * mstWideExt P χ η s F T (-x) := by
  have hft := ftLp_eq_finset_sum T hT hF
  have h1 : (fun ξ : Circ => (star (Work.BourgainPlan.Maximal.mstProf P N ξ)
        * mstWideBump P χ η s ξ) * Work.BourgainPlan.IonescuWainger.ftLp F hF ξ)
      =ᵐ[haarT]
      (fun ξ : Circ => (star (Work.BourgainPlan.Maximal.mstProf P N ξ)
        * mstWideBump P χ η s ξ) * (∑ n ∈ T, F n * fourier n ξ)) := by
    filter_upwards [hft] with ξ hξ
    rw [hξ]
  have h2 : (fun ξ : Circ => (star (Work.BourgainPlan.Maximal.mstProf P N ξ)
        * mstWideBump P χ η s ξ) * (∑ n ∈ T, F n * fourier n ξ))
      =ᵐ[haarT]
      (fun ξ : Circ => (Work.BourgainPlan.Maximal.mstProf P N (-ξ)
        * mstWideBump P χ η s ξ) * (∑ n ∈ T, F n * fourier n ξ)) := by
    filter_upwards [Work.BourgainPlan.Maximal.mstProf_neg_ae P N] with ξ hξ
    rw [← hξ]
  refine ((circleLift_ae_eq_congr h1).trans (circleLift_ae_eq_congr h2)).trans ?_
  have hbad1 : ∀ᵐ x : ℝ ∂volume, x ≠ (1/2:ℝ) := by
    rw [MeasureTheory.ae_iff]; simpa using measure_singleton (1/2:ℝ)
  have hbad2 : ∀ᵐ x : ℝ ∂volume, x ≠ -(1/2:ℝ) := by
    rw [MeasureTheory.ae_iff]; simpa using measure_singleton (-(1/2:ℝ))
  filter_upwards [hbad1, hbad2] with x hx1 hx2
  by_cases hxI : x ∈ Set.Ioc (-(1/2:ℝ)) (1/2)
  · rw [Work.BourgainPlan.Thm52.circleLift_of_mem hxI]
    have hxlt : x < 1/2 := lt_of_le_of_ne (Set.mem_Ioc.mp hxI).2 hx1
    have hmem : (-x) ∈ Set.Ioc (-(1/2:ℝ)) (1/2) := by
      rw [Set.mem_Ioc] at hxI ⊢
      exact ⟨by linarith [hxI.2, hxlt], by linarith [hxI.1]⟩
    have hprof : Work.BourgainPlan.Maximal.mstProf P N (-(-(x:Circ)))
        = Work.BourgainPlan.Maximal.polyProfile P N x := by
      rw [neg_neg, Work.BourgainPlan.Maximal.mstProf_apply, iwRep_coe_of_mem_aux hxI]
    have hbump : mstWideBump P χ η s (-(x:Circ)) = η (mstWideC P s * (-x)) := by
      rw [mstWideBump_apply]
      congr 1
      rw [← AddCircle.coe_neg (p := (1:ℝ)) (x := x), iwRep_coe_of_mem_aux hmem]
    have hsum : (∑ n ∈ T, F n * fourier n (-(x:Circ)))
        = ∑ n ∈ T, F n * Complex.exp (2 * Real.pi * Complex.I * ((n:ℂ) * ((-x:ℝ):ℂ))) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [fourier_neg_coe_aux]
    simp only [hprof, hbump, hsum]
    unfold mstWideExt
    ring
  · rw [Work.BourgainPlan.Thm52.circleLift_of_notMem hxI]
    have hxabs : 1/2 < |x| := by
      rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hxI
      rcases hxI with h | h
      · have : x < -(1/2) := lt_of_le_of_ne h hx2
        rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hc1 : (1:ℝ) ≤ mstWideC P s := one_le_mstWideC P s
    have hcpos : 0 < mstWideC P s := lt_of_lt_of_le zero_lt_one hc1
    have hzero : mstWideExt P χ η s F T (-x) = 0 := by
      unfold mstWideExt
      rw [show η (mstWideC P s * (-x)) = 0 from ?_, zero_mul]
      refine hηsup _ ?_
      rw [abs_mul, abs_neg, abs_of_pos hcpos]
      nlinarith [hxabs, hc1, hcpos]
    rw [hzero, mul_zero]

theorem mstWideLat_curve (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ) (F : ℤ → ℂ)
    (T : Finset ℤ) (hηc : ContDiff ℝ 2 η) (hηsup : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hT : ∀ n ∉ T, F n = 0) (hF : Memℓp F 2) (N : ℕ) (n : ℤ)
    (hφ : MeasureTheory.MemLp (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
      star (Work.BourgainPlan.Maximal.mstProf P N ξ) * Work.Maximal.mstWideBump P χ η s ξ) ⊤
      (AddCircle.haarAddCircle (T := 1))) :
    Work.BourgainPlan.IonescuWainger.opMul (hφ.toLp _) F hF n
      = ∫ u in (0:ℝ)..1,
          Work.Maximal.mstWideLat P χ η s F T
            (-(n : ℝ) - Polynomial.eval ((N : ℝ) * u) (Polynomial.map (Int.castRingHom ℝ) P)) := by
  have hηcont : Continuous η := hηc.continuous
  have hInt : Integrable (mstWideExt P χ η s F T) :=
    integrable_mstWideExt P χ η s F T hηcont hηsup
  rw [Work.Maximal.mstMax_bridge
        (fun ξ : Circ => star (Work.BourgainPlan.Maximal.mstProf P N ξ) * mstWideBump P χ η s ξ)
        hφ F hF n]
  rw [show (∫ u in (0:ℝ)..1, Work.Maximal.mstWideLat P χ η s F T
            (-(n : ℝ) - Polynomial.eval ((N : ℝ) * u) (Polynomial.map (Int.castRingHom ℝ) P)))
        = ∫ u in (0:ℝ)..1, FourierTransformInv.fourierInv (mstWideExt P χ η s F T)
            (-(n : ℝ) - Polynomial.eval ((N : ℝ) * u) (Polynomial.map (Int.castRingHom ℝ) P))
        from rfl]
  rw [← Work.Maximal.mstMax_curve P N (mstWideExt P χ η s F T) hInt (-(n:ℝ))]
  rw [← fourierInv_comp_neg
        (fun x : ℝ => Work.BourgainPlan.Maximal.polyProfile P N (-x) * mstWideExt P χ η s F T x)
        (n:ℝ)]
  refine fourierInv_congr_ae ?_ _
  filter_upwards [circleLift_mstWide_ae_eq P χ η s F T N hF hηsup hT] with x hx
  rw [hx, neg_neg]

end

end Work.Maximal
