/-
# `Coer1T` — the `T₄`-slot bound for `D_θ𝓛_Γ^T f` in the interior class `RegQ`

This file proves the requested lemma

  `Work.FTS.CoercivityFix.Coer1T.wip_T4_ge_Q`,

the **interior-class port** of `Work.Coercivity.wip_T4_ge` (`Submission/Work/Coercivity/
wip_T4_ge.lean`).  The mathematics is the paper's Cauchy–Schwarz estimate for the projector
term `T4 α f = (D_θΓ/c)·(2z²/(1+z)³)·L₁₂(Transport f)(0)` of `D_θ𝓛_Γ^T f`:

  `|⟨T4 α f, D_θ f⟩_{w² sin^{-γ}}| ≤ |C₀ f/c| · 2α · ‖T4A‖₂ · ‖T4B‖₂`,

where `T4A` carries the angular data `Γ(θ)·sin(2θ)^{-γ/2}` and `T4B α f` the unknown
`sin(2θ)^{-γ/2}·w·D_θ f`.  The two changes with respect to the delivered analytic-class
version are:

* the smoothness class `Spaces.SmoothNbhd f` (**analyticity** on a neighbourhood of the closed
  quadrant, destroyed by every cut-off) is replaced by the genuine `C^∞`-on-the-open-quadrant
  class `Work.FTS.LocData.SmoothQuad f`, which is what `RegQ α 2 f` provides.  The only place
  the class is used is the a.e. strong measurability of `D_θ f`, and that is
  `Work.FTS.CoercivityFix.Coer1T.aesm_Dth_smoothQuad`;
* the bound on the zero mode is the *sharp* interior-class inequality
  `(C₀ f)² ≤ EDthW f` (`C0_sq_le_EDthW_Q`) instead of the crude `(C₀ f)² ≤ 100·Ef f`, i.e.
  `|C₀ f/c| ≤ 10·√(EDthW f) ≤ 10·√(EDth α f)` (`EDthW_le_EDth_Q`).

With that, the whole estimate is `|wip| ≤ 10√EDth · 4α√(T4J α)·√EDth` and
`T4J α ≤ 120/(17α)`, so the bound is `40·α·√(T4J α)·EDth ≤ (1/200)·EDth`, the constant
`1/200` being legitimate precisely because `α ≤ 10⁻⁹` (the sharp threshold is
`α ≤ 17/(7.68·10⁹)`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Vocab
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.wip_T4_ge
import Submission.Work.Coercivity.T4aux
import Submission.Work.Coercivity.C0_sq_le_Ef
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.FTS.CoercivityFix.Coer1.Defs
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts
import Submission.Work.FTS.CoercivityFix.Coer1.Estimates
import Submission.Work.FTS.CoercivityFix.Coer1T.C0_sq_le_EDthW_Q
import Submission.Work.FTS.CoercivityFix.Coer1T.SlotsDzGam
import Submission.Work.FTS.CoercivityFix.Coer1T.aesm_T2G_Q

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The interior integrability of the two `D_θ`-blocks used below -/

/-- `(D_θ f)²·w²·sin(2θ)^{-γ}` is integrable on the quadrant for `f ∈ RegQ α 2`: this is
`IntPkg.sqMixedGam` at `(i,j) = (1,0)`, rewritten through `Dth = mixed 0 1` and
`Rho γ = w²·sin(2θ)^{-γ}`. -/
theorem Dth_sq_gam_of_RegQ (α : ℝ) (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hIP := Work.FTS.CoercivityFix.Coer1.IntPkg_Q α hα hf
  have h := Work.FTS.CoercivityFix.Coer1.to_h1 (β := Work.Spaces.gam α)
    (u := Work.Spaces.Dth f) (hIP.sqMixedGam 1 0 (by norm_num) (by norm_num))
  simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
    Work.Spaces.DthIter_zero, Work.FTS.CoercivityFix.Coer1.sig, pow_two] using h

/-- `(D_θ f)²·w²` is integrable on the quadrant for `f ∈ RegQ α 2` (`IntPkg.sqMixedOne` at
`(i,j) = (1,0)`). -/
theorem Dth_sq_w_sq_of_RegQ (α : ℝ) (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * Work.Spaces.w z ^ 2)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hIP := Work.FTS.CoercivityFix.Coer1.IntPkg_Q α hα hf
  have h := hIP.sqMixedOne 1 0 (by norm_num) (by norm_num)
  simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
    Work.Spaces.DthIter_zero, pow_two] using h

/-! ## The scalar arithmetic closing the constant `1/200` -/

/-- If `J² ≤ 120/(17α)` with `0 < α ≤ 10⁻⁹`, then `40αJ ≤ 1/200`.  This is the numerical
step converting the angular bound `T4J α ≤ 120/(17α)` into the constant of the target.  (The
numeric content: `40α√(120/(17α)) ≤ 1/200` is equivalent to `7.68·10⁹·α ≤ 17`, and
`7.68·10⁹·10⁻⁹ = 7.68 < 17`.) -/
theorem T4Q_arith (α J : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 9) (hJ : 0 ≤ J)
    (hJle : J ^ 2 ≤ 120 / (17 * α)) : 40 * α * J ≤ 1 / 200 := by
  have h17 : (0 : ℝ) < 17 * α := by linarith
  have hJ' : J ≤ Real.sqrt (120 / (17 * α)) := by
    calc J = Real.sqrt (J ^ 2) := (Real.sqrt_sq hJ).symm
      _ ≤ Real.sqrt (120 / (17 * α)) := Real.sqrt_le_sqrt hJle
  have h1 : Real.sqrt (120 / (17 * α)) ≤ 1 / (8000 * α) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have e : (1 / (8000 * α)) ^ 2 = 1 / (64000000 * α ^ 2) := by
      rw [div_pow, one_pow]
      rw [show (8000 * α) ^ 2 = 64000000 * α ^ 2 by ring]
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hα1, hα]
  have h2 : 40 * α * Real.sqrt (120 / (17 * α)) ≤ 1 / 200 := by
    calc 40 * α * Real.sqrt (120 / (17 * α))
        ≤ 40 * α * (1 / (8000 * α)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 / 200 := by field_simp; ring
  have h3 : 40 * α * J ≤ 40 * α * Real.sqrt (120 / (17 * α)) :=
    mul_le_mul_of_nonneg_left hJ' (by positivity)
  linarith

/-! ## A.e. strong measurability of the `L²` factors in the interior class -/

/-- `T4B α f` is a.e. strongly measurable on the quadrant for `SmoothQuad` data: it is the
measurable factor `sin(2θ)^{-γ/2}·w` times `D_θ f`. -/
theorem aesm_T4B_Q (α : ℝ) {f : ℝ → ℝ → ℝ} (hsq : Work.FTS.LocData.SmoothQuad f) :
    MeasureTheory.AEStronglyMeasurable (Work.Coercivity.T4B α f) Work.Coercivity.T4P := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      Work.Coercivity.T4h α p.2 * Work.Spaces.w p.1) :=
    ((Work.Coercivity.measurable_T4h α).comp measurable_snd).mul
      ((Work.Coercivity.measurable_w).comp measurable_fst)
  have h := hm.aestronglyMeasurable.mul (aesm_Dth_smoothQuad hsq)
  have h2 : ((fun p : ℝ × ℝ => Work.Coercivity.T4h α p.2 * Work.Spaces.w p.1)
        * fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2) = Work.Coercivity.T4B α f := by
    funext p
    rw [Pi.mul_apply]
    rfl
  rw [← h2]
  exact h

/-- `T4W α f` is a.e. strongly measurable on the quadrant for `SmoothQuad` data: it is a
measurable factor (the angular data `D_θΓ`, the radial factor `T4g`, the weight
`sin(2θ)^{-γ}w²`) times `D_θ f`. -/
theorem aesm_T4W_Q (α : ℝ) {f : ℝ → ℝ → ℝ} (hsq : Work.FTS.LocData.SmoothQuad f) :
    MeasureTheory.AEStronglyMeasurable (Work.Coercivity.T4W α f) Work.Coercivity.T4P := by
  have h1 : Measurable (fun p : ℝ × ℝ => Work.Coercivity.DthGam α p.1 p.2) :=
    Work.Coercivity.measurable_DthGam_prod α
  have h2 : Measurable (fun p : ℝ × ℝ => Work.Coercivity.T4g p.1) :=
    Work.Coercivity.measurable_T4g.comp measurable_fst
  have h3 : Measurable
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))) :=
    (Real.measurable_sin.comp (measurable_const.mul measurable_snd)).pow_const _
  have h4 : Measurable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2) :=
    (Work.Coercivity.measurable_w.comp measurable_fst).pow_const (2 : ℕ)
  have hm : Measurable (fun p : ℝ × ℝ => Work.Coercivity.DthGam α p.1 p.2
      * Work.Coercivity.T4g p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.w p.1) ^ 2) :=
    ((h1.mul h2).mul h3).mul h4
  have h := hm.aestronglyMeasurable.mul (aesm_Dth_smoothQuad hsq)
  have h2' : ((fun p : ℝ × ℝ => Work.Coercivity.DthGam α p.1 p.2
        * Work.Coercivity.T4g p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.w p.1) ^ 2)
        * fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2) = Work.Coercivity.T4W α f := by
    funext p
    rw [Pi.mul_apply]
    rfl
  rw [← h2']
  exact h

/-! ## Integrability and the value of the `L²` norm of `T4B` -/

/-- `(T4B α f)²` is integrable on the product measure as soon as the `γ`-weighted square of
`D_θ f` is integrable on the quadrant. -/
theorem integrable_T4B_sq_Q (α : ℝ) {f : ℝ → ℝ → ℝ}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Integrable (fun p : ℝ × ℝ => (Work.Coercivity.T4B α f p) ^ 2)
      Work.Coercivity.T4P := by
  have h' := Work.Coercivity.integrableOn_prod
    (g := fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
      * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) h
  refine h'.congr ?_
  filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
  exact (Work.Coercivity.T4B_sq_eq α f hp.2).symm

/-- `∫ (T4B α f)² = EDth α f`. -/
theorem integral_T4B_sq_Q (α : ℝ) {f : ℝ → ℝ → ℝ}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    ∫ p : ℝ × ℝ, (Work.Coercivity.T4B α f p) ^ 2 ∂Work.Coercivity.T4P
      = Work.Coercivity.EDth α f := by
  have hIntOn : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine h.congr ?_
    filter_upwards with p
    simp only [Function.uncurry]
    ring
  rw [Work.Coercivity.EDth_eq_wip α f,
    Work.Coercivity.wip_eq_integral_prod
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (Work.Spaces.Dth f) (Work.Spaces.Dth f) hIntOn]
  refine integral_congr_ae ?_
  filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
  rw [Work.Coercivity.T4B_sq_eq α f hp.2]
  ring

/-- Integrability of the `T4W`-integrand in the interior class: dominated pointwise by
`2α·|T4A·T4B|`, whose integral is finite by Cauchy–Schwarz. -/
theorem integrable_T4W_Q (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hΓ2 : Work.Coercivity.GammaPointwiseBnd α) {f : ℝ → ℝ → ℝ}
    (hsq : Work.FTS.LocData.SmoothQuad f)
    (hB2 : Integrable (fun p : ℝ × ℝ => (Work.Coercivity.T4B α f p) ^ 2)
      Work.Coercivity.T4P) :
    Integrable (Work.Coercivity.T4W α f) Work.Coercivity.T4P := by
  have hAB : Integrable (fun p : ℝ × ℝ =>
      Work.Coercivity.T4A α p * Work.Coercivity.T4B α f p) Work.Coercivity.T4P :=
    (Work.Coercivity.integrable_mul_abs_integral_le_sqrt (Work.Coercivity.T4A α)
      (Work.Coercivity.T4B α f) (Work.Coercivity.aesm_T4A α) (aesm_T4B_Q α hsq)
      (Work.Coercivity.integrable_T4A_sq α hα hα1) hB2).1
  refine (hAB.abs.const_mul (2 * α)).mono' (aesm_T4W_Q α hsq) ?_
  filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
  rw [Real.norm_eq_abs]
  exact Work.Coercivity.T4W_abs_le α hα hΓ2 f hp.1 hp.2

/-! ## The target -/

theorem wip_T4_ge_Q (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 9) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) (hΓ2 : Work.Coercivity.GammaPointwiseBnd α) :
    MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Coercivity.T4 α f z θ * Work.Spaces.Dth f z θ
          * Work.Coercivity.thetaW α z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ -((1 / 200) * Work.Coercivity.EDth α f)
        ≤ Work.Coercivity.wip (Work.Coercivity.thetaW α)
            (Work.Coercivity.T4 α f) (Work.Spaces.Dth f) := by
  have hreg := hf
  obtain ⟨hsq, hm2, -⟩ := hreg
  have hα1' : α ≤ 1 := by linarith [hα1]
  -- ### the integrability certificates
  have hgam := Dth_sq_gam_of_RegQ α hα hf
  have hw2i := Dth_sq_w_sq_of_RegQ α hα hf
  have hT4A2 : Integrable (fun p : ℝ × ℝ => (Work.Coercivity.T4A α p) ^ 2)
      Work.Coercivity.T4P := Work.Coercivity.integrable_T4A_sq α hα hα1'
  have hT4B2 : Integrable (fun p : ℝ × ℝ => (Work.Coercivity.T4B α f p) ^ 2)
      Work.Coercivity.T4P := integrable_T4B_sq_Q α hgam
  have hB2val : ∫ p : ℝ × ℝ, (Work.Coercivity.T4B α f p) ^ 2 ∂Work.Coercivity.T4P
      = Work.Coercivity.EDth α f := integral_T4B_sq_Q α hgam
  have hA2val : ∫ p : ℝ × ℝ, (Work.Coercivity.T4A α p) ^ 2 ∂Work.Coercivity.T4P
      = 4 * Work.Coercivity.T4J α := Work.Coercivity.integral_T4A_sq α hα hα1'
  have haesmB := aesm_T4B_Q α hsq
  obtain ⟨hABint, hABle⟩ := Work.Coercivity.integrable_mul_abs_integral_le_sqrt
    (Work.Coercivity.T4A α) (Work.Coercivity.T4B α f) (Work.Coercivity.aesm_T4A α)
    haesmB hT4A2 hT4B2
  have hT4Wint : Integrable (Work.Coercivity.T4W α f) Work.Coercivity.T4P :=
    integrable_T4W_Q α hα hα1' hΓ2 hsq hT4B2
  -- ### the first conjunct
  have hT4intP : Integrable (fun p : ℝ × ℝ =>
      Work.Coercivity.T4 α f p.1 p.2 * Work.Spaces.Dth f p.1 p.2
        * Work.Coercivity.thetaW α p.1 p.2) Work.Coercivity.T4P := by
    refine (hT4Wint.const_mul (Work.Coercivity.C0 f / Work.Spaces.c α)).congr ?_
    filter_upwards with p
    exact (Work.Coercivity.T4_integrand_eq α f p).symm
  have hOn : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.T4 α f z θ * Work.Spaces.Dth f z θ
        * Work.Coercivity.thetaW α z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [IntegrableOn, Work.Coercivity.volume_restrict_prod]
    exact hT4intP
  refine ⟨hOn, ?_⟩
  -- ### nonnegativity of the energy
  have hEDthnn : 0 ≤ Work.Coercivity.EDth α f := by
    rw [Work.FTS.CoercivityFix.Coer1.EDth_eq_En]
    exact Work.FTS.CoercivityFix.Coer1.En_nonneg (Work.Spaces.gam α) (Work.Spaces.Dth f)
  -- ### `wip` as `(C₀/c) ∫ T4W`
  have hwip2 : Work.Coercivity.wip (Work.Coercivity.thetaW α)
        (Work.Coercivity.T4 α f) (Work.Spaces.Dth f)
      = (Work.Coercivity.C0 f / Work.Spaces.c α)
        * ∫ p : ℝ × ℝ, Work.Coercivity.T4W α f p ∂Work.Coercivity.T4P := by
    rw [Work.Coercivity.wip_eq_integral_prod (Work.Coercivity.thetaW α)
      (Work.Coercivity.T4 α f) (Work.Spaces.Dth f) hOn, ← integral_const_mul]
    exact integral_congr_ae
      (Eventually.of_forall fun p => Work.Coercivity.T4_integrand_eq α f p)
  -- ### the bound on `∫ T4W`
  have hWb : |∫ p : ℝ × ℝ, Work.Coercivity.T4W α f p ∂Work.Coercivity.T4P|
      ≤ 2 * α * ∫ p : ℝ × ℝ,
          |Work.Coercivity.T4A α p * Work.Coercivity.T4B α f p| ∂Work.Coercivity.T4P := by
    have h1 : |∫ p : ℝ × ℝ, Work.Coercivity.T4W α f p ∂Work.Coercivity.T4P|
        ≤ ∫ p : ℝ × ℝ, |Work.Coercivity.T4W α f p| ∂Work.Coercivity.T4P :=
      abs_integral_le_integral_abs
    have h2 : ∫ p : ℝ × ℝ, |Work.Coercivity.T4W α f p| ∂Work.Coercivity.T4P
        ≤ ∫ p : ℝ × ℝ,
            2 * α * |Work.Coercivity.T4A α p * Work.Coercivity.T4B α f p|
              ∂Work.Coercivity.T4P := by
      refine integral_mono_ae hT4Wint.abs (hABint.abs.const_mul (2 * α)) ?_
      filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
      exact Work.Coercivity.T4W_abs_le α hα hΓ2 f hp.1 hp.2
    have h3 : ∫ p : ℝ × ℝ,
          2 * α * |Work.Coercivity.T4A α p * Work.Coercivity.T4B α f p|
            ∂Work.Coercivity.T4P
        = 2 * α * ∫ p : ℝ × ℝ,
            |Work.Coercivity.T4A α p * Work.Coercivity.T4B α f p|
              ∂Work.Coercivity.T4P :=
      integral_const_mul _ _
    linarith
  have hABb : ∫ p : ℝ × ℝ,
        |Work.Coercivity.T4A α p * Work.Coercivity.T4B α f p| ∂Work.Coercivity.T4P
      ≤ Real.sqrt (∫ p : ℝ × ℝ, (Work.Coercivity.T4A α p) ^ 2 ∂Work.Coercivity.T4P)
        * Real.sqrt (∫ p : ℝ × ℝ, (Work.Coercivity.T4B α f p) ^ 2
            ∂Work.Coercivity.T4P) := by
    have hAabs : AEStronglyMeasurable (fun p : ℝ × ℝ => |Work.Coercivity.T4A α p|)
        Work.Coercivity.T4P := (Work.Coercivity.aesm_T4A α).norm
    have hBabs : AEStronglyMeasurable
        (fun p : ℝ × ℝ => |Work.Coercivity.T4B α f p|) Work.Coercivity.T4P := haesmB.norm
    have hAabs2 : Integrable (fun p : ℝ × ℝ => (|Work.Coercivity.T4A α p|) ^ 2)
        Work.Coercivity.T4P :=
      hT4A2.congr (Eventually.of_forall fun p => (sq_abs (Work.Coercivity.T4A α p)).symm)
    have hBabs2 : Integrable (fun p : ℝ × ℝ => (|Work.Coercivity.T4B α f p|) ^ 2)
        Work.Coercivity.T4P :=
      hT4B2.congr (Eventually.of_forall fun p => (sq_abs (Work.Coercivity.T4B α f p)).symm)
    obtain ⟨-, hle⟩ := Work.Coercivity.integrable_mul_abs_integral_le_sqrt
      (fun p => |Work.Coercivity.T4A α p|) (fun p => |Work.Coercivity.T4B α f p|)
      hAabs hBabs hAabs2 hBabs2
    have e1 : ∫ p : ℝ × ℝ, (|Work.Coercivity.T4A α p|) ^ 2 ∂Work.Coercivity.T4P
        = ∫ p : ℝ × ℝ, (Work.Coercivity.T4A α p) ^ 2 ∂Work.Coercivity.T4P :=
      integral_congr_ae (Eventually.of_forall fun p => sq_abs (Work.Coercivity.T4A α p))
    have e2 : ∫ p : ℝ × ℝ, (|Work.Coercivity.T4B α f p|) ^ 2 ∂Work.Coercivity.T4P
        = ∫ p : ℝ × ℝ, (Work.Coercivity.T4B α f p) ^ 2 ∂Work.Coercivity.T4P :=
      integral_congr_ae (Eventually.of_forall fun p => sq_abs (Work.Coercivity.T4B α f p))
    have e3 : ∫ p : ℝ × ℝ,
          |Work.Coercivity.T4A α p * Work.Coercivity.T4B α f p| ∂Work.Coercivity.T4P
        = |∫ p : ℝ × ℝ,
            |Work.Coercivity.T4A α p| * |Work.Coercivity.T4B α f p|
              ∂Work.Coercivity.T4P| := by
      rw [abs_of_nonneg (integral_nonneg fun p => mul_nonneg (abs_nonneg _) (abs_nonneg _))]
      exact integral_congr_ae (Eventually.of_forall fun p => abs_mul _ _)
    calc ∫ p : ℝ × ℝ,
          |Work.Coercivity.T4A α p * Work.Coercivity.T4B α f p| ∂Work.Coercivity.T4P
        = |∫ p : ℝ × ℝ,
            |Work.Coercivity.T4A α p| * |Work.Coercivity.T4B α f p|
              ∂Work.Coercivity.T4P| := e3
      _ ≤ Real.sqrt (∫ p : ℝ × ℝ, (|Work.Coercivity.T4A α p|) ^ 2 ∂Work.Coercivity.T4P)
            * Real.sqrt (∫ p : ℝ × ℝ, (|Work.Coercivity.T4B α f p|) ^ 2
                ∂Work.Coercivity.T4P) := hle
      _ = Real.sqrt (∫ p : ℝ × ℝ, (Work.Coercivity.T4A α p) ^ 2 ∂Work.Coercivity.T4P)
            * Real.sqrt (∫ p : ℝ × ℝ, (Work.Coercivity.T4B α f p) ^ 2
                ∂Work.Coercivity.T4P) := by rw [e1, e2]
  have hW2 : |∫ p : ℝ × ℝ, Work.Coercivity.T4W α f p ∂Work.Coercivity.T4P|
      ≤ 2 * α * (2 * Real.sqrt (Work.Coercivity.T4J α))
        * Real.sqrt (Work.Coercivity.EDth α f) := by
    have hstep1 : 2 * α * ∫ p : ℝ × ℝ,
          |Work.Coercivity.T4A α p * Work.Coercivity.T4B α f p| ∂Work.Coercivity.T4P
        ≤ 2 * α * (Real.sqrt
              (∫ p : ℝ × ℝ, (Work.Coercivity.T4A α p) ^ 2 ∂Work.Coercivity.T4P)
            * Real.sqrt (∫ p : ℝ × ℝ, (Work.Coercivity.T4B α f p) ^ 2
                ∂Work.Coercivity.T4P)) :=
      mul_le_mul_of_nonneg_left hABb (by positivity)
    have heq : 2 * α * (Real.sqrt
              (∫ p : ℝ × ℝ, (Work.Coercivity.T4A α p) ^ 2 ∂Work.Coercivity.T4P)
            * Real.sqrt (∫ p : ℝ × ℝ, (Work.Coercivity.T4B α f p) ^ 2
                ∂Work.Coercivity.T4P))
        = 2 * α * (2 * Real.sqrt (Work.Coercivity.T4J α))
            * Real.sqrt (Work.Coercivity.EDth α f) := by
      rw [hA2val, hB2val]
      have h4 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [show Real.sqrt (4 * Work.Coercivity.T4J α)
          = 2 * Real.sqrt (Work.Coercivity.T4J α) by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) (Work.Coercivity.T4J α), h4]]
      ring
    exact le_trans hWb (le_trans hstep1 (le_of_eq heq))
  -- ### the sharp `C₀` bound: `|C₀ f / c α| ≤ 10 √EDth`
  have hC0 : (Work.Coercivity.C0 f) ^ 2 ≤ Work.Coercivity.EDthW f :=
    C0_sq_le_EDthW_Q hsq hw2i
  have hC0abs : |Work.Coercivity.C0 f| ≤ Real.sqrt (Work.Coercivity.EDth α f) := by
    have h1 : Real.sqrt ((Work.Coercivity.C0 f) ^ 2)
        ≤ Real.sqrt (Work.Coercivity.EDthW f) := Real.sqrt_le_sqrt hC0
    rw [Real.sqrt_sq_eq_abs] at h1
    exact le_trans h1 (Real.sqrt_le_sqrt (EDthW_le_EDth_Q α hα hsq hm2))
  have hcinv : |(1 : ℝ) / Work.Spaces.c α| ≤ 10 := by
    have hc := (Work.Spaces.c_bounds α hα hα1').1
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (Work.Coercivity.c_pos hα hα1')]
    linarith
  have hC0c : |Work.Coercivity.C0 f / Work.Spaces.c α|
      ≤ 10 * Real.sqrt (Work.Coercivity.EDth α f) := by
    calc |Work.Coercivity.C0 f / Work.Spaces.c α|
        = |Work.Coercivity.C0 f| * |(1 : ℝ) / Work.Spaces.c α| := by
          rw [div_eq_mul_one_div, abs_mul]
      _ ≤ Real.sqrt (Work.Coercivity.EDth α f) * 10 :=
          mul_le_mul hC0abs hcinv (abs_nonneg _) (Real.sqrt_nonneg _)
      _ = 10 * Real.sqrt (Work.Coercivity.EDth α f) := by ring
  -- ### the angular bound and the arithmetic
  have hJnn : 0 ≤ Work.Coercivity.T4J α := by
    rw [Work.Coercivity.T4J]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])) _)
  have hJle : Work.Coercivity.T4J α ≤ 120 / (17 * α) :=
    (Work.Coercivity.Gam_sq_sin_neg_gam α hα hα1').2
  have hJsq : (Real.sqrt (Work.Coercivity.T4J α)) ^ 2 ≤ 120 / (17 * α) := by
    rw [Real.sq_sqrt hJnn]
    exact hJle
  have harith : 40 * α * Real.sqrt (Work.Coercivity.T4J α) ≤ 1 / 200 :=
    T4Q_arith α (Real.sqrt (Work.Coercivity.T4J α)) hα hα1 (Real.sqrt_nonneg _) hJsq
  have harith' : 40 * (α * Real.sqrt (Work.Coercivity.T4J α)) ≤ 1 / 200 := by
    linarith [harith]
  -- ### the final chain
  have hmain : |Work.Coercivity.wip (Work.Coercivity.thetaW α) (Work.Coercivity.T4 α f)
        (Work.Spaces.Dth f)| ≤ (1 / 200) * Work.Coercivity.EDth α f := by
    rw [hwip2, abs_mul]
    have hstep : |Work.Coercivity.C0 f / Work.Spaces.c α|
          * |∫ p : ℝ × ℝ, Work.Coercivity.T4W α f p ∂Work.Coercivity.T4P|
        ≤ 10 * Real.sqrt (Work.Coercivity.EDth α f)
          * (2 * α * (2 * Real.sqrt (Work.Coercivity.T4J α))
              * Real.sqrt (Work.Coercivity.EDth α f)) :=
      mul_le_mul hC0c hW2 (abs_nonneg _) (by positivity)
    have hshape : 10 * Real.sqrt (Work.Coercivity.EDth α f)
          * (2 * α * (2 * Real.sqrt (Work.Coercivity.T4J α))
              * Real.sqrt (Work.Coercivity.EDth α f))
        = 40 * (α * Real.sqrt (Work.Coercivity.T4J α))
            * (Real.sqrt (Work.Coercivity.EDth α f)) ^ 2 := by ring
    calc |Work.Coercivity.C0 f / Work.Spaces.c α|
          * |∫ p : ℝ × ℝ, Work.Coercivity.T4W α f p ∂Work.Coercivity.T4P|
        ≤ 10 * Real.sqrt (Work.Coercivity.EDth α f)
          * (2 * α * (2 * Real.sqrt (Work.Coercivity.T4J α))
              * Real.sqrt (Work.Coercivity.EDth α f)) := hstep
      _ = 40 * (α * Real.sqrt (Work.Coercivity.T4J α))
            * (Real.sqrt (Work.Coercivity.EDth α f)) ^ 2 := hshape
      _ ≤ (1 / 200) * (Real.sqrt (Work.Coercivity.EDth α f)) ^ 2 :=
          mul_le_mul_of_nonneg_right harith' (sq_nonneg _)
      _ = (1 / 200) * Work.Coercivity.EDth α f := by
          rw [Real.sq_sqrt hEDthnn]
  exact (abs_le.mp hmain).1

end Work.FTS.CoercivityFix.Coer1T
