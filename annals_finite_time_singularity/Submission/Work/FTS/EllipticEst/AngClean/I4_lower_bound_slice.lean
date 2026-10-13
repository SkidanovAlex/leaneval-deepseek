import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.I4_aux_defs
import Submission.Work.FTS.EllipticEst.AngSecond.I4_tan_mul_sub_deriv
import Submission.Work.FTS.EllipticEst.AngSecond.I4_psi_bounds_alt
import Submission.Work.FTS.EllipticEst.AngSecond.I4_Gprim_deriv
import Submission.Work.FTS.EllipticEst.AngSecond.I4_lower_bound
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngClean

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Work.FTS.EllipticEst.AngSecond
open Work.Spaces

/-! ## Integrability of the angular weight and of bounded functions against it -/

/-- `σ ∈ L¹(Iθ)`, from `Work.Spaces.sin_two_rpow` with `p = -η ∈ (-1, 0]`. -/
theorem integrableOn_sig : IntegrableOn sig Iθ := by
  have h : IntegrableOn (fun θ : ℝ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) Iθ volume :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by linarith [Work.Spaces.eta_lt_one])
      (by linarith [Work.Spaces.eta_pos])).1
  exact h

/-- `σ` is measurable. -/
theorem measurable_sig : Measurable sig := by
  show Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _

/-- **Domination by an integrable multiple of the angular weight.**  A function `f` which is
bounded by `C` on the open quadrant is square-integrable against `σ θ = sin(2θ)^{-η}` there,
because `σ` is integrable on `Iθ` and `f² σ ≤ C² σ`.

The continuity hypothesis on `(0,π/2)` is what supplies the (a.e.) strong measurability. -/
theorem integrableOn_sq_mul_sig_of_abs_le {f : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)))
    (hb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ C) :
    IntegrableOn (fun θ => f θ ^ 2 * sig θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hI : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  have hsigm : IntegrableOn (fun θ => C ^ 2 * sig θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (integrableOn_sig.mono_set Set.Ioo_subset_Icc_self).const_mul (C ^ 2)
  refine hsigm.mono' ?_ ?_
  · have h1 : AEStronglyMeasurable (fun θ => f θ ^ 2)
        (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      (hf.aestronglyMeasurable hI).pow 2
    have h2 : AEStronglyMeasurable (fun θ => sig θ)
        (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      measurable_sig.aestronglyMeasurable
    exact h1.mul h2
  · filter_upwards [MeasureTheory.ae_restrict_mem hI] with θ hθ
    have hsig0 : 0 ≤ sig θ := sig_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hf2 : f θ ^ 2 ≤ C ^ 2 := by
      have h := hb θ hθ
      exact sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (f θ)), abs_of_nonneg hsig0]
    exact mul_le_mul_of_nonneg_right hf2 hsig0

/-- **The slicewise integrability facts needed by the `I₄`-identity.**  For `u` of class `C^∞`
on a neighbourhood of the closed quadrant with `u (π/2) = 0`, the two functions
`θ ↦ (u θ/cos θ)²·σ θ` and `θ ↦ ((u/cos θ)'(θ))²·σ θ` are integrable on `(0, π/2)`.

This is the replacement for the two `IPMem` hypotheses of
`Work.FTS.EllipticEst.AngSecond.slice_le`: it needs no honest iterated `z`-integral, and is
proved from `I4_psi_bounds_alt` (the uniform bound on `Ψ̄ = u/cos θ` and its derivative) and
`integrableOn_sig`. -/
theorem integrableOn_div_cos_sq_mul_sig (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ ⊤ u (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)))
    (hu1 : u (Real.pi / 2) = 0) :
    (IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 * sig θ) (Set.Ioo 0 (Real.pi / 2))) ∧
      (IntegrableOn (fun θ => (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * sig θ)
        (Set.Ioo 0 (Real.pi / 2))) := by
  have h2 : ContDiffOn ℝ 2 u (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := hu.of_le (by norm_num)
  obtain ⟨C, hC0, hCb⟩ := I4_psi_bounds_alt u h2 hu1
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hcos_ne : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos x ≠ 0 := fun x hx =>
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
  have hsm : ContDiffOn ℝ ⊤ (fun θ => u θ / Real.cos θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hu.mono hsub).div Real.contDiff_cos.contDiffOn hcos_ne
  have hcont : ContinuousOn (fun θ => u θ / Real.cos θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.continuousOn
  have hdcont : ContinuousOn (deriv (fun θ => u θ / Real.cos θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.continuousOn_deriv_of_isOpen isOpen_Ioo le_top
  exact ⟨integrableOn_sq_mul_sig_of_abs_le hC0 hcont fun θ hθ => (hCb θ hθ).1,
    integrableOn_sq_mul_sig_of_abs_le hC0 hdcont fun θ hθ => (hCb θ hθ).2⟩

/-! ## The slicewise inequality without the `Ψ/cos θ`-honesty hypotheses -/

/-- **`slice_le` without the `Ψ̄`-honesty hypotheses.**

The statement of `Work.FTS.EllipticEst.AngSecond.slice_le` with the last two hypotheses
(`IPMem (Ψ/cos θ) (Ψ/cos θ)` and `IPMem (∂_θ(Ψ/cos θ)) (∂_θ(Ψ/cos θ))`) removed: the two
slicewise integrability facts they provided are rebuilt with
`integrableOn_div_cos_sq_mul_sig`. -/
theorem slice_le_clean (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hpi : ∀ z, Ψ z (Real.pi / 2) = 0) {z : ℝ} (hz : 0 < z)
    (hM1 : IPMem (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (Work.Spaces.pthIter 2 Ψ))
    (hM2 : IPMem Ψ (Work.Spaces.pthIter 2 Ψ))
    (hM3 : IPMem Ψ Ψ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
        * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
      - (∫ θ in Work.Spaces.Iθ, Ψ z θ * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
      ≤ (1 - Work.Spaces.eta) * (∫ θ in Work.Spaces.Iθ, Ψ z θ * Ψ z θ * w2 z * sig θ) := by
  have hzI : z ∈ Iz := le_of_lt hz
  have hz1 : (-1 : ℝ) < z := by linarith
  have hIooM : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  set u : ℝ → ℝ := fun θ => Ψ z θ with hu
  set ψ : ℝ → ℝ := fun θ => u θ / Real.cos θ with hψ
  have hzu : ContDiffOn ℝ ⊤ u (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
    have hp : ContDiffOn ℝ ⊤ (fun t : ℝ => (z, t)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
      contDiffOn_const.prodMk contDiffOn_id
    have h := hsm.comp hp (fun t ht => ⟨hz1, ht⟩)
    simpa [Function.comp_def, Function.uncurry, hu] using h
  have hzu2 : ContDiffOn ℝ 2 u (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := hzu.of_le (by norm_num)
  have hu1 : u (Real.pi / 2) = 0 := by simp only [hu]; exact hpi z
  -- the two slicewise integrability facts (this is where `hM4`, `hM5` used to enter)
  obtain ⟨hB, hA⟩ := integrableOn_div_cos_sq_mul_sig u hzu hu1
  have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |u θ / Real.cos θ| ≤ C ∧ |deriv (fun θ' => u θ' / Real.cos θ') θ| ≤ C :=
    I4_psi_bounds_alt u hzu2 hu1
  have hN : IntegrableOn (fun θ => Ψ z θ * Ψ z θ * sig θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h := hM3.1 z hzI
    have h' : IntegrableOn (fun θ => (Ψ z θ * Ψ z θ * sig θ) * w2 z) Iθ := by
      refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Icc
      intro θ hθ
      simp only [Pi.sub_apply]
      ring
    exact (integrableOn_of_mul_w2 hz measurableSet_Icc h').mono_set Set.Ioo_subset_Icc_self
  have hC : IntegrableOn (fun θ => Real.sin θ * deriv ψ θ * deriv (deriv u) θ * sig θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hd : IntegrableOn (fun θ => (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
        - Ψ z θ) * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ) Iθ := by
      have h := (hM1.1 z hzI).sub (hM2.1 z hzI)
      refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Icc
      intro θ hθ
      simp only [Pi.sub_apply]
      ring
    have hd' : IntegrableOn
        (fun θ => (Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
          * deriv (deriv u) θ * sig θ) * w2 z) (Set.Ioo 0 (Real.pi / 2)) := by
      refine MeasureTheory.IntegrableOn.congr_fun (hd.mono_set Set.Ioo_subset_Icc_self)
        ?_ hIooM
      intro θ hθ
      have htan := pth_tan_sub Ψ hsm hz hθ
      have hf : Work.Spaces.pthIter 2 Ψ z θ = deriv (deriv u) θ := rfl
      dsimp only
      rw [htan, hf]
      ring
    exact integrableOn_of_mul_w2 hz hIooM hd'
  have hident := slice_ident u hzu2 hu1 hbdd hA hB hC
  have htan_all : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ
        = Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ :=
    fun θ hθ => pth_tan_sub Ψ hsm hz hθ
  have step1 :
      (∫ θ in Iθ, Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
          * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
        - (∫ θ in Iθ, Ψ z θ * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
      = ∫ θ in Iθ, (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
          * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ := by
    rw [← MeasureTheory.integral_sub (hM1.1 z hzI) (hM2.1 z hzI)]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by
      simp only [Pi.sub_apply]; ring
  have step2 :
      (∫ θ in Iθ, (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
          * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
          * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ := by
    rw [setIntegral_Ioo_Iθ]
  have step3 :
      (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
          * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
            * deriv (deriv u) θ * sig θ) * w2 z := by
    refine MeasureTheory.setIntegral_congr_fun hIooM ?_
    intro θ hθ
    have hf : Work.Spaces.pthIter 2 Ψ z θ = deriv (deriv u) θ := rfl
    dsimp only
    rw [htan_all θ hθ, hf]
    ring
  have step4 :
      (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
            * deriv (deriv u) θ * sig θ) * w2 z)
      = w2 z * ∫ θ in Set.Ioo 0 (Real.pi / 2),
          Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
            * deriv (deriv u) θ * sig θ := by
    rw [MeasureTheory.integral_mul_const, mul_comm]
  have step5 :
      (∫ θ in Set.Ioo 0 (Real.pi / 2),
          Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
            * deriv (deriv u) θ * sig θ)
      = ((1 - Work.Spaces.eta) / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2), Real.cos (2 * θ)
            * (Ψ z θ / Real.cos θ) ^ 2 * sig θ)
        - ∫ θ in Set.Ioo 0 (Real.pi / 2), acoef θ
            * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sig θ := by
    simpa [Work.Spaces.pth] using hident
  have hPnn : 0 ≤ ∫ θ in Set.Ioo 0 (Real.pi / 2), acoef θ
      * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sig θ := by
    refine MeasureTheory.setIntegral_nonneg hIooM fun θ hθ => ?_
    exact mul_nonneg (mul_nonneg (acoef_nonneg θ) (sq_nonneg _))
      (sig_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have hcos_le : (∫ θ in Set.Ioo 0 (Real.pi / 2), Real.cos (2 * θ)
        * (Ψ z θ / Real.cos θ) ^ 2 * sig θ)
      ≤ 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2), Ψ z θ * Ψ z θ * sig θ := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_mono_on ?_ ?_ hIooM fun θ hθ => ?_
    · have h := integrableOn_continuousOn_mul (g := fun θ => Real.cos (2 * θ)) hB
        (by fun_prop) hIooM fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      refine MeasureTheory.IntegrableOn.congr_fun h ?_ hIooM
      intro θ hθ
      first
        | (simp only [hψ, hu]; ring)
        | (simp only [hu]; ring)
        | (simp only [hψ]; ring)
        | ring
    · exact hN.const_mul 2
    · have h1 := cos_two_mul_mul_div_cos_sq_le (a := Ψ z θ) hθ
      have h2 : 0 ≤ sig θ := sig_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have h3 := mul_le_mul_of_nonneg_right h1 h2
      nlinarith [h3]
  have hE3 : (∫ θ in Iθ, Ψ z θ * Ψ z θ * w2 z * sig θ)
      = w2 z * ∫ θ in Set.Ioo 0 (Real.pi / 2), Ψ z θ * Ψ z θ * sig θ := by
    rw [← setIntegral_Ioo_Iθ (fun θ => Ψ z θ * Ψ z θ * w2 z * sig θ)]
    have hcongr : (∫ θ in Set.Ioo 0 (Real.pi / 2), Ψ z θ * Ψ z θ * w2 z * sig θ)
        = ∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ * Ψ z θ * sig θ) * w2 z :=
      MeasureTheory.setIntegral_congr_fun hIooM fun θ _ => by ring
    rw [hcongr, MeasureTheory.integral_mul_const, mul_comm]
  rw [step1, step2, step3, step4, step5, hE3]
  have hw2nn : 0 ≤ w2 z := w2_nonneg z
  have heta2nn : 0 ≤ (1 - Work.Spaces.eta) / 2 := by linarith [one_sub_eta_pos]
  set B : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2),
      Real.cos (2 * θ) * (Ψ z θ / Real.cos θ) ^ 2 * sig θ with hBdef
  set P : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), acoef θ
      * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sig θ with hPdef
  set N : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), Ψ z θ * Ψ z θ * sig θ with hNdef
  have hB' : B ≤ 2 * N := by rw [hBdef, hNdef]; exact hcos_le
  have hP' : 0 ≤ P := by rw [hPdef]; exact hPnn
  have e1 : w2 z * ((1 - Work.Spaces.eta) / 2 * B - P)
      ≤ w2 z * ((1 - Work.Spaces.eta) / 2 * B) := by
    apply mul_le_mul_of_nonneg_left _ hw2nn
    linarith [hP']
  have e2 : w2 z * ((1 - Work.Spaces.eta) / 2 * B)
      ≤ w2 z * ((1 - Work.Spaces.eta) / 2 * (2 * N)) := by
    apply mul_le_mul_of_nonneg_left _ hw2nn
    exact mul_le_mul_of_nonneg_left hB' heta2nn
  have e3 : w2 z * ((1 - Work.Spaces.eta) / 2 * (2 * N))
      = (1 - Work.Spaces.eta) * (w2 z * N) := by ring
  linarith [e1, e2, e3]

/-- **The `I₄` lower bound, weakened honesty (no `Ψ/cos θ`-honesty hypotheses).**

This is `Work.FTS.EllipticEst.AngSecond.I4_lower_bound` with its last two hypotheses

* `IPMem (fun z θ => Ψ z θ / cos θ) (fun z θ => Ψ z θ / cos θ)` and
* `IPMem (fun z θ => ∂_θ(Ψ z θ / cos θ)) (fun z θ => ∂_θ(Ψ z θ / cos θ))`

**removed**.  Those two were used in `slice_le` only to obtain the *slicewise* integrability of
`(Ψ/cos θ)²σ` and of `(∂_θ(Ψ/cos θ))²σ` on `(0,π/2)` (their `z`-integrability — a third-order
weighted bound — is never used).  Slicewise, that integrability is automatic: with
`Ψ̄ = Ψ/cos θ`, `I4_psi_bounds_alt` gives uniform bounds for `Ψ̄` and `∂_θΨ̄` on `(0,π/2)` as soon
as `Ψ` is `C²` on a neighbourhood of the closed quadrant with `Ψ z (π/2) = 0`, and `σ ∈ L¹(Iθ)`
(`Work.FTS.EllipticEst.integrable_sig`); the `z = 0` slice is the `w² 0 = 0` case as in the
existing proof.

The prover should copy `Submission/Work/FTS/EllipticEst/AngSecond/I4_lower_bound.lean` into this
file, weaken the statements of `slice_le` and of the main result by deleting the `hM4`/`hM5`
arguments, and rebuild the two integrability facts from `I4_psi_bounds_alt` + `integrable_sig`
instead of from `hM4.1`/`hM5.1`.  Everything else (the `Ψ = cos θ·Ψ̄` substitution, the choice of
the positive quadratic coefficient, the `cos 2θ` bookkeeping) can be reused verbatim.
(Despite the module name this is the full `z`-integrated bound, not a slicewise one.) -/
theorem I4_lower_bound_slice : ∃ C : ℝ, 0 < C ∧ ∀ (Ψ : ℝ → ℝ → ℝ),
    Work.Spaces.SmoothNbhd Ψ → (∀ z, Ψ z 0 = 0) → (∀ z, Ψ z (Real.pi / 2) = 0) →
    Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (Work.Spaces.pthIter 2 Ψ) →
    Work.FTS.EllipticEst.AngSecond.IPMem Ψ (Work.Spaces.pthIter 2 Ψ) →
    Work.FTS.EllipticEst.AngSecond.IPMem Ψ Ψ →
    - Work.FTS.EllipticEst.AngSecond.IP Ψ (Work.Spaces.pthIter 2 Ψ)
      - C * Work.FTS.EllipticEst.AngSecond.IP Ψ Ψ
      ≤ - Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
          (Work.Spaces.pthIter 2 Ψ) := by
  refine ⟨1, one_pos, ?_⟩
  intro Ψ hsm h0 hpi hM1 hM2 hM3
  have hmono : IP (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
      (Work.Spaces.pthIter 2 Ψ) ≤ (1 - Work.Spaces.eta) * IP Ψ Ψ := by
    rw [IP, IP]
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Ici fun z hz => ?_
    · have h := (hM1.2).sub (hM2.2)
      refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Ici
      intro z hz
      simp only [Pi.sub_apply]
      rw [← MeasureTheory.integral_sub (hM1.1 z hz) (hM2.1 z hz)]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by
        simp only [Pi.sub_apply]; ring
    · exact hM3.2.const_mul (1 - Work.Spaces.eta)
    · have hz' : (0 : ℝ) ≤ z := hz
      rcases eq_or_lt_of_le hz' with h | h
      · subst h
        have hw0 : w2 (0 : ℝ) = 0 := by rw [w2, Work.Spaces.w]; norm_num
        simp [hw0]
      · have hinner : (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
              * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
            = ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
                    * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ
                  - Ψ z θ * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by ring
        rw [hinner, MeasureTheory.integral_sub (hM1.1 z hz) (hM2.1 z hz)]
        exact slice_le_clean Ψ hsm hpi h hM1 hM2 hM3
  have hkey : IP (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
        (Work.Spaces.pthIter 2 Ψ) - IP Ψ (Work.Spaces.pthIter 2 Ψ)
      ≤ 1 * IP Ψ Ψ := by
    rw [IP_sub_left hM1 hM2]
    have hnonneg : 0 ≤ IP Ψ Ψ := IP_self_nonneg Ψ
    have hle : (1 - Work.Spaces.eta) * IP Ψ Ψ ≤ 1 * IP Ψ Ψ := by
      have h1 : (1 - Work.Spaces.eta) ≤ 1 := by rw [Work.Spaces.eta]; norm_num
      exact mul_le_mul_of_nonneg_right h1 hnonneg
    linarith [hmono, hle]
  linarith [hkey]

end Work.FTS.EllipticEst.AngClean
