import Mathlib
import Submission.Work.BourgainPlan.Maximal.MtaDefs
import Submission.Work.BourgainPlan.MtaLin.fourierInv_mul_fourier_add
import Submission.Work.BourgainPlan.MtaLin.integrable_tildeFam
import Submission.Work.BourgainPlan.MtaLin.mtaBlkOp_aemeasurable
import Submission.Work.BourgainPlan.MtaLin.mtaBlkOp_smul

/-!
# `L¹` linearity of the block operators `mtaBlkOp`

This module proves the three structural properties of the block operator

`mtaBlkOp P K ε s h = ∑_{k < K} S̃_{d k + s} (ε_k · S_{d k + s} (D_k h))`,  `d = P.natDegree`,

that the interpolation argument `mtaBlkOp_trunc_interp` consumes:

* **additivity** on `L¹` inputs (conjunct 1),
* **`ℂ`-homogeneity** in the input (conjunct 2), which needs no integrability,
* **a.e. measurability of the extended norm** for `L¹` input (conjunct 3).

The additivity is the only delicate part: the curve average `σ_N h` is a Bochner integral, so its
additivity holds *almost everywhere* in `x` (only there are both curve fibres integrable), while the
Littlewood–Paley projections are multiplier operators.  The bridge is that for an integrable input
`G` the projection is an honest convolution,
`S_l G = ∫ y, G y * κ_l (· - y)`, which only sees the a.e. class of `G`; and the key operator
identity is the additivity of `𝓕⁻ (m · 𝓕 ·)` in the argument, `fourierInv_mul_fourier_add`, which
holds *pointwise* because `𝓕` of an `L¹` function is bounded, so that `m · 𝓕 f` is integrable for
integrable `m`.

## Main results

* `Work.BourgainPlan.Maximal.curveSigma_add_ae`
* `Work.BourgainPlan.Maximal.mtaBlkOp_add`
* `Work.BourgainPlan.Maximal.mtaBlkOp_l1_linear`
-/

open MeasureTheory Finset
open scoped ENNReal BigOperators FourierTransform

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

noncomputable section

/-! ## Additivity of the curve average on `L¹` inputs -/

/-- The integrand `(x,t) ↦ h (x - Q t)` of the curve average is integrable on the product
`volume ⊗ tslpNu` when `h` is integrable: its modulus has product integral
`∫⁻ t, (∫⁻ x, ‖h x‖ₑ) = ∫⁻ x, ‖h x‖ₑ < ∞` by the translation invariance of Lebesgue measure. -/
lemma integrable_curve_product (P : Polynomial ℤ) (N : ℕ) {h : ℝ → ℂ}
    (hh : MeasureTheory.Integrable h) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => h (p.1 - (toRealPoly P).eval ((N:ℝ) * p.2)))
      ((volume : Measure ℝ).prod tslpNu) := by
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => h (p.1 - (toRealPoly P).eval ((N:ℝ) * p.2)))
      ((volume : Measure ℝ).prod tslpNu) :=
    hh.aestronglyMeasurable.comp_quasiMeasurePreserving (tslpNu_qmp P N)
  refine ⟨hm, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hF : AEMeasurable
      (Function.uncurry (fun x t : ℝ => ‖h (x - (toRealPoly P).eval ((N:ℝ) * t))‖ₑ))
      ((volume : Measure ℝ).prod tslpNu) := by
    change AEMeasurable (fun p : ℝ × ℝ =>
      ‖h (p.1 - (toRealPoly P).eval ((N:ℝ) * p.2))‖ₑ) _
    exact hm.enorm
  rw [show (∫⁻ p : ℝ × ℝ, ‖h (p.1 - (toRealPoly P).eval ((N:ℝ) * p.2))‖ₑ
        ∂((volume : Measure ℝ).prod tslpNu))
      = ∫⁻ t : ℝ, ∫⁻ x : ℝ, ‖h (x - (toRealPoly P).eval ((N:ℝ) * t))‖ₑ
        ∂(volume : Measure ℝ) ∂tslpNu from
      (lintegral_prod (fun p : ℝ × ℝ => ‖h (p.1 - (toRealPoly P).eval ((N:ℝ) * p.2))‖ₑ) hF).trans
        (lintegral_lintegral_swap hF)]
  have hfin : ∫⁻ x : ℝ, ‖h x‖ₑ ∂(volume : Measure ℝ) ≠ ⊤ := hh.2.ne
  have hkey : (∫⁻ t : ℝ, ∫⁻ x : ℝ,
        ‖h (x - (toRealPoly P).eval ((N:ℝ) * t))‖ₑ ∂(volume : Measure ℝ) ∂tslpNu)
      = ∫⁻ x : ℝ, ‖h x‖ₑ ∂(volume : Measure ℝ) := by
    calc ∫⁻ t : ℝ, ∫⁻ x : ℝ,
          ‖h (x - (toRealPoly P).eval ((N:ℝ) * t))‖ₑ ∂(volume : Measure ℝ) ∂tslpNu
        = ∫⁻ t : ℝ, (∫⁻ x : ℝ, ‖h x‖ₑ ∂(volume : Measure ℝ)) ∂tslpNu := by
          apply lintegral_congr
          intro t
          have h := lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
            (fun y : ℝ => ‖h y‖ₑ) (-((toRealPoly P).eval ((N:ℝ) * t)))
          simpa [sub_eq_add_neg] using h
      _ = (∫⁻ x : ℝ, ‖h x‖ₑ ∂(volume : Measure ℝ)) * tslpNu Set.univ :=
          lintegral_const _
      _ = ∫⁻ x : ℝ, ‖h x‖ₑ ∂(volume : Measure ℝ) := by rw [tslpNu_univ, mul_one]
  rw [hkey]
  exact lt_top_iff_ne_top.mpr hfin

/-- **Additivity of the curve average for `L¹` inputs.**  For integrable `u, v` the two curve
functions `t ↦ u (x - Q t)`, `t ↦ v (x - Q t)` are integrable for almost every `x`, hence
`σ_N (u + v) = σ_N u + σ_N v` almost everywhere. -/
theorem curveSigma_add_ae (P : Polynomial ℤ) (N : ℕ) {u v : ℝ → ℂ}
    (hu : MeasureTheory.Integrable u) (hv : MeasureTheory.Integrable v) :
    curveSigma P N (u + v)
      =ᵐ[(volume : Measure ℝ)] fun x : ℝ => curveSigma P N u x + curveSigma P N v x := by
  have hQI : ∀ f : ℝ → ℂ, (∫ t in (0:ℝ)..1, f t) = ∫ t, f t ∂tslpNu := by
    intro f
    rw [tslpNu, intervalIntegral.integral_of_le (μ := volume) (by norm_num : (0:ℝ) ≤ 1)]
  have h1 : ∀ᵐ x ∂(volume : Measure ℝ),
      MeasureTheory.Integrable (fun t : ℝ => u (x - (toRealPoly P).eval ((N:ℝ) * t))) tslpNu :=
    (integrable_curve_product P N hu).prod_right_ae
  have h2 : ∀ᵐ x ∂(volume : Measure ℝ),
      MeasureTheory.Integrable (fun t : ℝ => v (x - (toRealPoly P).eval ((N:ℝ) * t))) tslpNu :=
    (integrable_curve_product P N hv).prod_right_ae
  filter_upwards [h1, h2] with x hx1 hx2
  rw [curveSigma_apply, curveSigma_apply, curveSigma_apply, hQI, hQI, hQI]
  have hfun : (fun t : ℝ => (u + v) (x - (toRealPoly P).eval ((N:ℝ) * t)))
      = (fun t : ℝ => u (x - (toRealPoly P).eval ((N:ℝ) * t)))
        + (fun t : ℝ => v (x - (toRealPoly P).eval ((N:ℝ) * t))) := rfl
  rw [hfun]
  rw [show ((fun t : ℝ => u (x - (toRealPoly P).eval ((N:ℝ) * t)))
        + (fun t : ℝ => v (x - (toRealPoly P).eval ((N:ℝ) * t))))
      = (fun t : ℝ => u (x - (toRealPoly P).eval ((N:ℝ) * t))
          + v (x - (toRealPoly P).eval ((N:ℝ) * t))) from rfl]
  exact integral_add hx1 hx2

/-! ## Additivity of the block operator -/

/-- **Additivity of `mtaBlkOp` on `L¹` inputs.** -/
theorem mtaBlkOp_add (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) (s : ℤ) {u v : ℝ → ℂ}
    (hu : MeasureTheory.Integrable u) (hv : MeasureTheory.Integrable v) (x : ℝ) :
    mtaBlkOp P K ε s (u + v) x = mtaBlkOp P K ε s u x + mtaBlkOp P K ε s v x := by
  -- the `L¹`-calculus of the curve averages and their dyadic differences
  have hcur : ∀ {h : ℝ → ℂ}, MeasureTheory.Integrable h → ∀ N : ℕ,
      MeasureTheory.Integrable (curveSigma P N h) := by
    intro h hh N
    have h1 : MemLp h (ENNReal.ofReal (1:ℝ)) (volume : Measure ℝ) := by
      rw [ENNReal.ofReal_one]; exact memLp_one_iff_integrable.mpr hh
    have h2 := (memLp_curveSigma' P N (le_refl (1:ℝ)) h1).1
    rw [ENNReal.ofReal_one] at h2
    exact memLp_one_iff_integrable.mp h2
  have hDD : ∀ {h : ℝ → ℂ}, MeasureTheory.Integrable h → ∀ k : ℕ,
      MeasureTheory.Integrable (dyadD P k h) := by
    intro h hh k
    exact (hcur hh (2^k)).sub (hcur hh (2^(k+1)))
  have hA : ∀ {h : ℝ → ℂ}, MeasureTheory.Integrable h → ∀ k : ℕ,
      MeasureTheory.Integrable
        (fun y : ℝ => ε k * dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s)
          (dyadD P k h) y) := by
    intro h hh k
    exact (integrable_dyadicProj (hDD hh k)).const_mul (ε k)
  -- the dyadic differences are additive almost everywhere
  have hDae : ∀ k : ℕ, dyadD P k (u + v) =ᵐ[volume] dyadD P k u + dyadD P k v := by
    intro k
    have h1 := curveSigma_add_ae P (2^k) hu hv
    have h2 := curveSigma_add_ae P (2^(k+1)) hu hv
    filter_upwards [h1, h2] with z hz1 hz2
    simp only [dyadD, Pi.add_apply]
    rw [hz1, hz2]
    ring
  -- both Littlewood–Paley stages are additive pointwise in `x`
  have hkey : ∀ k : ℕ, ∀ z : ℝ,
      dyadicProj dyadTilde ((P.natDegree : ℤ) * (k : ℤ) + s)
          (fun y : ℝ => ε k * dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s)
            (dyadD P k (u + v)) y) z
        = dyadicProj dyadTilde ((P.natDegree : ℤ) * (k : ℤ) + s)
            (fun y : ℝ => ε k * dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s)
              (dyadD P k u) y) z
          + dyadicProj dyadTilde ((P.natDegree : ℤ) * (k : ℤ) + s)
              (fun y : ℝ => ε k * dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s)
                (dyadD P k v) y) z := by
    intro k z
    -- inner projection: only the a.e. class of `D_k` matters, and `𝓕⁻ (m · 𝓕 ·)` is additive
    have hin : ∀ w : ℝ,
        dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s) (dyadD P k (u + v)) w
          = dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s) (dyadD P k u) w
            + dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s) (dyadD P k v) w := by
      intro w
      have hF : FourierTransform.fourier (dyadD P k (u + v))
          = FourierTransform.fourier (dyadD P k u + dyadD P k v) := by
        funext ξ
        exact Real.fourier_congr_ae (hDae k) ξ
      simp only [dyadicProj]
      rw [hF]
      simpa only [psiFam] using
        Work.BourgainPlan.MtaLin.fourierInv_mul_fourier_add
          (m := psiFam ((P.natDegree : ℤ) * (k : ℤ) + s))
          (integrable_psiFam _) (hDD hu k) (hDD hv k) w
    -- outer projection: the arguments agree pointwise by the inner step
    have harg2 : (fun y : ℝ => ε k * dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s)
          (dyadD P k (u + v)) y)
        = (fun y : ℝ => ε k * dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s)
              (dyadD P k u) y)
          + (fun y : ℝ => ε k * dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s)
              (dyadD P k v) y) := by
      funext y
      simp only [Pi.add_apply, hin y, mul_add]
    rw [harg2]
    exact Work.BourgainPlan.MtaLin.fourierInv_mul_fourier_add
      (m := tildeFam ((P.natDegree : ℤ) * (k : ℤ) + s))
      (Work.BourgainPlan.MtaLin.integrable_tildeFam _) (hA hu k) (hA hv k) z
  have hsum : (∑ k ∈ Finset.range K,
        dyadicProj dyadTilde ((P.natDegree : ℤ) * (k : ℤ) + s)
          (fun y : ℝ => ε k * dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s)
            (dyadD P k (u + v)) y) x)
      = ∑ k ∈ Finset.range K,
          (dyadicProj dyadTilde ((P.natDegree : ℤ) * (k : ℤ) + s)
            (fun y : ℝ => ε k * dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s)
              (dyadD P k u) y) x
           + dyadicProj dyadTilde ((P.natDegree : ℤ) * (k : ℤ) + s)
            (fun y : ℝ => ε k * dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s)
              (dyadD P k v) y) x) :=
    Finset.sum_congr rfl (fun k _ => hkey k x)
  simp only [mtaBlkOp]
  rw [hsum, Finset.sum_add_distrib]

/-! ## The target -/

theorem mtaBlkOp_l1_linear (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) (s : ℤ) :
    (∀ {u v : ℝ → ℂ}, MeasureTheory.Integrable u → MeasureTheory.Integrable v → ∀ x : ℝ,
        Work.BourgainPlan.Maximal.mtaBlkOp P K ε s (u + v) x
          = Work.BourgainPlan.Maximal.mtaBlkOp P K ε s u x
            + Work.BourgainPlan.Maximal.mtaBlkOp P K ε s v x)
    ∧ (∀ (c : ℂ) (u : ℝ → ℂ) (x : ℝ),
        Work.BourgainPlan.Maximal.mtaBlkOp P K ε s (c • u) x
          = c * Work.BourgainPlan.Maximal.mtaBlkOp P K ε s u x)
    ∧ (∀ {u : ℝ → ℂ}, MeasureTheory.Integrable u →
        AEMeasurable (fun x : ℝ => ‖Work.BourgainPlan.Maximal.mtaBlkOp P K ε s u x‖ₑ)
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v hu hv x
    exact mtaBlkOp_add P K ε s hu hv x
  · intro c u x
    exact Work.BourgainPlan.MtaLin.mtaBlkOp_smul P K ε s c u x
  · intro u hu
    exact Work.BourgainPlan.MtaLin.mtaBlkOp_aemeasurable P K ε s hu

end

end Work.BourgainPlan.Maximal
