/-
# The sharp `L²` coercivity of `𝓛_Γ^T`

This file proves the sharp form of Proposition `prop:L2CoercivityTransport` of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021),

namely `(𝓛_Γ^T(f) w, f w)_{L²} ≥ (1/5)|f w|²_{L²} - 1000|D_θ f w|²_{L²}`.  The file
`L2CoercivityTransport.lean` proves the same inequality with the cruder constant `10⁴`,
which is too large for the assembly of `FirstDerivativeCoercivity` (`H1IP` has
coefficients `10, 10¹⁰, 10¹⁷, 10²¹`, so multiplying by `10¹⁷` and combining with the
`D_θ`-estimate whose `EDth`-gain is `(1/4)·10²¹` forces the error constant to be at most
`2489`).

The only difference from the existing proof is the treatment of the projector term
`𝕡(Transport f)·w`:  with `U = 𝕡(Transport f)·w` one has the pointwise identity
`U = (1/(1+z))·(3·D_θ f·w - 2·(Γ/c)·C0 f)` (with `C0 f = L₁₂(Transport f)(0)`), hence

* `U² ≤ 18 (D_θ f · w)² + 8 (Γ/c)² (C0 f)²/(1+z)²`  (using `(a-2b)² ≤ 2a² + 8b²`);
* integrating and using `∫_z (1+z)^{-2} = 1`, `(C0 f)² ≤ EDthW f` (`C0_sq_le_EDthW`)
  and the *integrated* sharp angular bound `∫_θ (Γ/c)² ≤ 5` gives
  `∫∫ U² ≤ 18 EDthW f + 8·5·EDthW f = 58 EDthW f`,

replacing the pointwise bound `(Γ/c)² ≤ 100` (hence `2000`) of the existing file.  The
final AM–GM step `(1/4)|fw|² - √58 |D_θfw||fw| ≥ (1/5)|fw|² - 290 |D_θfw|²` then gives
the constant `290 ≤ 1000`.

The sharp angular bound `∫_θ (Γ/c)² ≤ 5` is `GamDivCSqInt_le_five` and the separated
projector-correction integral is `projCorr_sepIntegral_le_five`; both are proved in
separate modules of this directory.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.L2Coercivity
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.Coercivity.f_sq_w_sq_integrable
import Submission.Work.Coercivity.wip_eq_integral_prod
import Submission.Work.Coercivity.GamDivCSqInt_le_five
import Submission.Work.Coercivity.projCorr_sepIntegral_le_five

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The sharp projector bound -/

/-- **The sharp projector bound.**  With `U = 𝕡(Transport f)·w`, the pointwise identity
`U = (1/(1+z))·(3 D_θf·w - 2(Γ/c) C0 f)` and `(a-2b)² ≤ 2a² + 8b²` give
`U² ≤ 18 (D_θf·w)² + 8 (Γ/c)²(C0 f)²/(1+z)²`; integrating, separating the variables in the
second term and using `∫_z (1+z)^{-2} = 1`, the sharp angular bound
`∫_θ (Γ/c)² ≤ 5` (`GamDivCSqInt_le_five`/`projCorr_sepIntegral_le_five`) and
`(C0 f)² ≤ EDthW f` yields `∫∫ U² ≤ 18 EDthW f + 8·5·EDthW f = 58 EDthW f`.

This is the sharp replacement for `ProjTransport_sq_integral_le` of
`L2CoercivityTransport.lean` (constant `2000`). -/
theorem projTransport_sq_integral_le_sharp (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hint : IntegrableOn
      (Function.uncurry (fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ
        * Spaces.w z ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ))
    (hC0 : (C0 f) ^ 2 ≤ EDthW f)
    (hG : ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2 ≤ 5) :
    IntegrableOn
        (Function.uncurry (fun z θ => (Proj α (Transport f) z θ * Spaces.w z) ^ 2))
        (Spaces.Iz ×ˢ Spaces.Iθ)
      ∧ ∫ p : ℝ × ℝ,
          (Proj α (Transport f) p.1 p.2 * Spaces.w p.1) ^ 2
        ∂((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ))
        ≤ 58 * EDthW f := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)
    with hP
  set U : ℝ × ℝ → ℝ := fun p => Proj α (Transport f) p.1 p.2 * Spaces.w p.1 with hU
  set W : ℝ × ℝ → ℝ := fun p => 18 * (Spaces.Dth f p.1 p.2 * Spaces.w p.1) ^ 2
      + 8 * (Spaces.Gam α p.2 / Spaces.c α) ^ 2 * (C0 f) ^ 2 / (1 + p.1) ^ 2 with hW
  have hEdnn : 0 ≤ EDthW f := by
    rw [EDthW, wip]
    exact integral_nonneg fun z => integral_nonneg fun θ =>
      mul_nonneg (mul_self_nonneg _) (sq_nonneg _)
  have hpt : ∀ᵐ p ∂P, (U p) ^ 2 ≤ W p := by
    filter_upwards [ae_prod_pos, ae_prod_quadrant] with p hp hq
    have hz : 0 < p.1 := hp
    have hid : U p = (1 / (1 + p.1)) *
        (3 * (Spaces.Dth f p.1 p.2 * Spaces.w p.1)
          - 2 * (Spaces.Gam α p.2 / Spaces.c α) * C0 f) := by
      simp only [hU, Proj, Transport, Spaces.w, C0]
      have hz0 : p.1 ≠ 0 := ne_of_gt hz
      have hz1 : 1 + p.1 ≠ 0 := ne_of_gt (by linarith)
      field_simp
    set g : ℝ := Spaces.Gam α p.2 / Spaces.c α with hg
    set Gw : ℝ := Spaces.Dth f p.1 p.2 * Spaces.w p.1 with hGw
    have hquad : (3 * Gw - 2 * g * C0 f) ^ 2 ≤ 18 * Gw ^ 2 + 8 * g ^ 2 * (C0 f) ^ 2 := by
      have h1 : (3 * Gw - 2 * g * C0 f) ^ 2 ≤ 2 * ((3 * Gw) ^ 2 + (2 * g * C0 f) ^ 2) := by
        nlinarith [sq_nonneg (3 * Gw + 2 * g * C0 f)]
      have h2 : 2 * ((3 * Gw) ^ 2 + (2 * g * C0 f) ^ 2) = 18 * Gw ^ 2 + 8 * g ^ 2 * (C0 f) ^ 2 :=
        by ring
      linarith
    calc (U p) ^ 2
        = (1 / (1 + p.1)) ^ 2 * (3 * Gw - 2 * g * C0 f) ^ 2 := by rw [hid]; rw [mul_pow]
      _ ≤ (1 / (1 + p.1)) ^ 2 * (18 * Gw ^ 2 + 8 * g ^ 2 * (C0 f) ^ 2) :=
          mul_le_mul_of_nonneg_left hquad (by positivity)
      _ ≤ 18 * Gw ^ 2 + 8 * g ^ 2 * (C0 f) ^ 2 / (1 + p.1) ^ 2 := by
          have hp1 : (0 : ℝ) < (1 + p.1) ^ 2 := pow_pos (by linarith : (0 : ℝ) < 1 + p.1) 2
          have heq : (1 / (1 + p.1)) ^ 2 * (18 * Gw ^ 2 + 8 * g ^ 2 * (C0 f) ^ 2)
              = 18 * Gw ^ 2 / (1 + p.1) ^ 2 + 8 * g ^ 2 * (C0 f) ^ 2 / (1 + p.1) ^ 2 := by
            field_simp
            try ring
          rw [heq]
          have h2z : 18 * Gw ^ 2 / (1 + p.1) ^ 2 ≤ 18 * Gw ^ 2 := by
            rw [div_le_iff₀ hp1]
            nlinarith [sq_nonneg Gw, sq_nonneg p.1, hz]
          linarith [h2z]
      _ = 18 * (Spaces.Dth f p.1 p.2 * Spaces.w p.1) ^ 2
            + 8 * (Spaces.Gam α p.2 / Spaces.c α) ^ 2 * (C0 f) ^ 2 / (1 + p.1) ^ 2 := by
          rw [hGw, hg]
  -- integrability of the angular factor `(Γ/c)²` on `Iθ`
  have hGamCont : ContinuousOn (fun θ : ℝ => Spaces.Gam α θ) Spaces.Iθ := by
    simp only [Spaces.Gam]
    exact ContinuousOn.rpow_const
      (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
      (fun θ _ => Or.inr (by positivity))
  have hG2int : Integrable (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2)
      (volume.restrict Spaces.Iθ) := by
    have hcont : ContinuousOn (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2) Spaces.Iθ :=
      ((hGamCont.div_const (Spaces.c α)).pow 2)
    exact hcont.integrableOn_Icc
  have hCorrInt : Integrable (fun p : ℝ × ℝ =>
      (Spaces.Gam α p.2 / Spaces.c α) ^ 2 / (1 + p.1) ^ 2) P := by
    have h := integrable_Iz_one_div_sq.mul_prod hG2int
    rw [hP]
    refine h.congr (Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply]
    ring
  have hW1 : Integrable
      (fun p : ℝ × ℝ => 18 * (Spaces.Dth f p.1 p.2 * Spaces.w p.1) ^ 2) P := by
    have h := integrableOn_prod (g := fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ
      * Spaces.w z ^ 2) hint
    exact (h.const_mul 18).congr (Eventually.of_forall fun p => by ring)
  have hW2 : Integrable (fun p : ℝ × ℝ =>
      8 * (Spaces.Gam α p.2 / Spaces.c α) ^ 2 * (C0 f) ^ 2 / (1 + p.1) ^ 2) P := by
    have h := hCorrInt.const_mul (8 * (C0 f) ^ 2)
    refine h.congr (Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply]
    ring
  have hWint : Integrable W P := by
    rw [hW]; exact hW1.add hW2
  have hUaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => (U p) ^ 2) P := by
    have hUA : AEStronglyMeasurable U P := by
      rw [hU]; exact aesm_projTransport_mul_w α f hsm
    refine (hUA.mul hUA).congr (Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply, pow_two]
  have hUint : Integrable (fun p : ℝ × ℝ => (U p) ^ 2) P :=
    hWint.mono' hUaesm (hpt.mono fun p hp => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hp)
  have hunorm : ∫ p, (Spaces.Dth f p.1 p.2 * Spaces.w p.1) ^ 2 ∂P = EDthW f := by
    have h : Integrable (fun p : ℝ × ℝ =>
        Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * Spaces.w p.1 ^ 2) P :=
      integrableOn_prod hint
    have hcongr : (fun p : ℝ × ℝ => (Spaces.Dth f p.1 p.2 * Spaces.w p.1) ^ 2)
        = fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * Spaces.w p.1 ^ 2 := by
      funext p; ring
    rw [hcongr, MeasureTheory.integral_prod _ h, EDthW, wip]
  have hCorrLe : ∫ p, (Spaces.Gam α p.2 / Spaces.c α) ^ 2 / (1 + p.1) ^ 2 ∂P ≤ 5 := by
    rw [hP]
    exact projCorr_sepIntegral_le_five α hα hα1 hG
  have hWexp : ∫ p, W p ∂P
      = 18 * (∫ p, (Spaces.Dth f p.1 p.2 * Spaces.w p.1) ^ 2 ∂P)
        + (8 * (C0 f) ^ 2) * (∫ p, (Spaces.Gam α p.2 / Spaces.c α) ^ 2
            / (1 + p.1) ^ 2 ∂P) := by
    rw [hW, MeasureTheory.integral_add hW1 hW2, MeasureTheory.integral_const_mul]
    congr 1
    rw [show (fun p : ℝ × ℝ =>
        8 * (Spaces.Gam α p.2 / Spaces.c α) ^ 2 * (C0 f) ^ 2 / (1 + p.1) ^ 2)
        = fun p => (8 * (C0 f) ^ 2) * ((Spaces.Gam α p.2 / Spaces.c α) ^ 2
            / (1 + p.1) ^ 2) from by funext p; ring]
    rw [MeasureTheory.integral_const_mul]
  have hWle : ∫ p, W p ∂P ≤ 58 * EDthW f := by
    rw [hWexp, hunorm]
    have hkey : (8 * (C0 f) ^ 2) * (∫ p, (Spaces.Gam α p.2 / Spaces.c α) ^ 2
        / (1 + p.1) ^ 2 ∂P) ≤ 40 * EDthW f := by
      have h3 : (8 * (C0 f) ^ 2) * (∫ p, (Spaces.Gam α p.2 / Spaces.c α) ^ 2
          / (1 + p.1) ^ 2 ∂P) ≤ (8 * (C0 f) ^ 2) * 5 :=
        mul_le_mul_of_nonneg_left hCorrLe (by positivity)
      have h4 : (8 * (C0 f) ^ 2) * 5 ≤ 40 * EDthW f := by nlinarith [hC0]
      linarith
    linarith [hkey, hEdnn]
  constructor
  · rw [IntegrableOn, volume_restrict_prod]
    exact hUint
  · calc ∫ p, (Proj α (Transport f) p.1 p.2 * Spaces.w p.1) ^ 2 ∂P
        = ∫ p, (U p) ^ 2 ∂P := by rw [hU]
      _ ≤ ∫ p, W p ∂P := integral_mono_ae hUint hWint hpt
      _ ≤ 58 * EDthW f := hWle

/-! ## The final numerical inequality -/

/-- `√58 · A · B ≤ A²/20 + 1000 B²` for `A, B ≥ 0`: with `A/√20` and `√290 B` this is
AM–GM, using `√58 = 2√290/√20`. -/
theorem sqrt58_amgm (A B : ℝ) (_hA : 0 ≤ A) (_hB : 0 ≤ B) :
    Real.sqrt 58 * A * B ≤ A ^ 2 / 20 + 1000 * B ^ 2 := by
  have h20 : Real.sqrt 20 ^ 2 = 20 := Real.sq_sqrt (by norm_num)
  have h20pos : 0 < Real.sqrt 20 := Real.sqrt_pos_of_pos (by norm_num)
  have h20ne : Real.sqrt 20 ≠ 0 := ne_of_gt h20pos
  have hsq : (2 * Real.sqrt 290 / Real.sqrt 20) ^ 2 = 58 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 290), h20]
    norm_num
  have hsqrt : Real.sqrt 58 = 2 * Real.sqrt 290 / Real.sqrt 20 := by
    rw [← hsq, Real.sqrt_sq (by positivity)]
  have hkey : 0 ≤ (A / Real.sqrt 20 - Real.sqrt 290 * B) ^ 2 := sq_nonneg _
  have hAM : 2 * (A / Real.sqrt 20) * (Real.sqrt 290 * B)
      ≤ (A / Real.sqrt 20) ^ 2 + (Real.sqrt 290 * B) ^ 2 := by nlinarith [hkey]
  have h1 : (A / Real.sqrt 20) ^ 2 = A ^ 2 / 20 := by rw [div_pow, h20]
  have h2 : (Real.sqrt 290 * B) ^ 2 = 290 * B ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 290)]
  rw [h1, h2] at hAM
  have h3 : 2 * (A / Real.sqrt 20) * (Real.sqrt 290 * B) = Real.sqrt 58 * A * B := by
    rw [hsqrt]
    ring
  rw [h3] at hAM
  nlinarith [hAM, sq_nonneg B]

/-! ## The main theorem -/

/-- The plain `L²` coercivity of `𝓛_Γ^T` with a *sharp* error constant.

The paper (Prop. `prop:L2CoercivityTransport`) proves
`(𝓛_Γ^T f · w, f · w)_{L²} ≥ (1/5)|fw|² - 100|D_θ f · w|²`; the file
`Submission/Work/Coercivity/L2CoercivityTransport.lean` proves the same inequality but
with the much cruder constant `10⁴` on the error, which is not enough for the assembly
of Corollary `FirstDerivativeCoercivity` (the `ℋ¹` inner product `H1IP` has coefficients
`10, 10¹⁰, 10¹⁷, 10²¹`; multiplying this estimate by `10¹⁷` and combining it with the
`D_θ`-estimate, whose `EDth`-gain is `(1/4)·10²¹`, shows that the error constant has to
be at most `2489`).

It is the same proof as the existing one, with one improvement: the projector term is
estimated by bounding the *θ-integral* `∫_θ (Γ/c)²dθ ≤ 5` instead of the pointwise
`(Γ/c)² ≤ 100`.  Indeed, with `U = 𝕡(Transport f)·w`,

* `U = (1/(1+z))·(3·D_θ f·w - 2·(Γ/c)·C0 f)` with `C0 f = L₁₂(Transport f)(0)`;
* `(a-2b)² ≤ 2a² + 8b²` gives `(U)² ≤ 18(D_θ f·w)² + 8(Γ/c)²C0²/(1+z)²`;
* integrating, `∫∫U² ≤ 18·EDthW + 8·(∫_θ(Γ/c)²)·(∫_z (1+z)^{-2})·(C0 f)² ≤ 18·58·… = 58·EDthW`
  (using `(C0 f)² ≤ EDthW`, which is `C0_sq_le_EDthW`, and `∫_z (1+z)^{-2} = 1`);
* `∫_θ(Γ/c)² ≤ 5` follows from `GammaL2Bnd α` (`‖Γ/c - K‖₂ ≤ 7/10`) and
  `∫_θ K² ≤ 9/4` (`integral_Iθ_Ksq_le`) by the triangle inequality in `L²`:
  `(7/10 + 3/2)² = 4.84 ≤ 5`;
* finally the AM–GM step of the existing proof (`(1/5)|fw|² - 5·58·EDthW`) gives the
  constant `290 ≤ 1000`.

In particular the statement is a strict strengthening of `L2CoercivityTransport`
(`1000 < 10000`), so a genuinely new (though similar) proof is required. -/
theorem L2TransportSharp (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : IBP f) (hfH : HardyHyp f) (hΓ : GammaL2Bnd α) (hi : CoerciveData α f) :
    (1 / 5) * Ef f - 1000 * EDthW f
      ≤ wip (fun z _ => Spaces.w z ^ 2) (LGammaT α f) f := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)
    with hP
  have hbase : (1 / 4) * Ef f ≤ wip (fun z _ => Spaces.w z ^ 2) (LGamma α f) f :=
    L2Coercivity α hα hα1 f hf hfH hΓ hi
  have hAeq : wip (fun z _ => Spaces.w z ^ 2) (LGamma α f) f
      = ∫ p, LGamma α f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P := by
    rw [hP]
    exact wip_eq_integral_prod _ _ _ (by simpa using hi.intLG)
  have hT : wip (fun z _ => Spaces.w z ^ 2) (LGammaT α f) f
      = ∫ p, LGammaT α f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P := by
    rw [hP]
    exact wip_eq_integral_prod _ _ _ (by simpa using hi.intLGT)
  have hIntA : Integrable
      (fun p : ℝ × ℝ => LGamma α f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2) P :=
    integrableOn_prod hi.intLG
  have hIntB : Integrable (fun p : ℝ × ℝ =>
      Proj α (Transport f) p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2) P :=
    integrableOn_prod hi.intP
  have hsplit : (∫ p, LGammaT α f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P)
      = (∫ p, LGamma α f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P)
        - (∫ p, Proj α (Transport f) p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P) := by
    rw [← MeasureTheory.integral_sub hIntA hIntB]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [LGammaT]; ring
  have hEfnn : 0 ≤ Ef f := by
    rw [Ef, Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hEdnn : 0 ≤ EDthW f := by
    rw [EDthW, wip]
    exact integral_nonneg fun z => integral_nonneg fun θ =>
      mul_nonneg (mul_self_nonneg _) (sq_nonneg _)
  have hV2int : Integrable (fun p : ℝ × ℝ => (f p.1 p.2 * Spaces.w p.1) ^ 2) P := by
    have h := integrableOn_prod (f_sq_w_sq_integrable α f hi)
    exact h.congr (Eventually.of_forall fun p => by ring)
  have hEfint : (∫ p, (f p.1 p.2 * Spaces.w p.1) ^ 2 ∂P) = Ef f := by
    rw [hP, Ef_eq_wip, wip_eq_integral_prod (fun z _ => Spaces.w z ^ 2) f f
      (by simpa using f_sq_w_sq_integrable α f hi)]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
    ring
  have hC0 : (C0 f) ^ 2 ≤ EDthW f := C0_sq_le_EDthW f hf.smooth hi.intDth
  have hG : ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2 ≤ 5 :=
    GamDivCSqInt_le_five α hα hα1 hΓ
  obtain ⟨hU2intOn, hQle⟩ :=
    projTransport_sq_integral_le_sharp α hα hα1 f hf.smooth hi.intDth hC0 hG
  have hU2int : Integrable
      (fun p : ℝ × ℝ => (Proj α (Transport f) p.1 p.2 * Spaces.w p.1) ^ 2) P := by
    rw [show P = volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)
      from hP.trans volume_restrict_prod.symm]
    exact hU2intOn
  have hUA : MemLp (fun p : ℝ × ℝ => Proj α (Transport f) p.1 p.2 * Spaces.w p.1) 2 P :=
    (memLp_two_iff_integrable_sq (aesm_projTransport_mul_w α f hf.smooth)).2 hU2int
  have hVA : MemLp (fun p : ℝ × ℝ => f p.1 p.2 * Spaces.w p.1) 2 P :=
    (memLp_two_iff_integrable_sq (aesm_f_mul_w hf.smooth)).2 hV2int
  have habsuv : (∫ p, Proj α (Transport f) p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P) ^ 2
      ≤ (∫ p, (Proj α (Transport f) p.1 p.2 * Spaces.w p.1) ^ 2 ∂P) * Ef f := by
    have huv : (∫ p, Proj α (Transport f) p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P)
        = ∫ p, (Proj α (Transport f) p.1 p.2 * Spaces.w p.1)
            * (f p.1 p.2 * Spaces.w p.1) ∂P := by
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_); ring
    rw [huv]
    have := cs_integral_mul hUA hVA
    rwa [hEfint] at this
  have hQnn : 0 ≤ ∫ p, (Proj α (Transport f) p.1 p.2 * Spaces.w p.1) ^ 2 ∂P :=
    integral_nonneg fun p => sq_nonneg _
  have hproj_int_le :
      (∫ p, Proj α (Transport f) p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P)
        ≤ Real.sqrt 58 * Real.sqrt (EDthW f) * Real.sqrt (Ef f) := by
    have h1 : |∫ p, Proj α (Transport f) p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P|
        ≤ Real.sqrt ((∫ p, (Proj α (Transport f) p.1 p.2 * Spaces.w p.1) ^ 2 ∂P) * Ef f) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt habsuv
    have h2 : Real.sqrt ((∫ p, (Proj α (Transport f) p.1 p.2 * Spaces.w p.1) ^ 2 ∂P) * Ef f)
        ≤ Real.sqrt 58 * Real.sqrt (EDthW f) * Real.sqrt (Ef f) := by
      rw [Real.sqrt_mul hQnn]
      have h3 : Real.sqrt (∫ p, (Proj α (Transport f) p.1 p.2 * Spaces.w p.1) ^ 2 ∂P)
          ≤ Real.sqrt 58 * Real.sqrt (EDthW f) := by
        have h := Real.sqrt_le_sqrt hQle
        rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 58)] at h
      have h4 := mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg (Ef f))
      linarith
    calc (∫ p, Proj α (Transport f) p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P)
        ≤ |∫ p, Proj α (Transport f) p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P| :=
          le_abs_self _
      _ ≤ Real.sqrt 58 * Real.sqrt (EDthW f) * Real.sqrt (Ef f) := le_trans h1 h2
  have hnum : (1 / 4) * Ef f - Real.sqrt 58 * Real.sqrt (EDthW f) * Real.sqrt (Ef f)
      ≥ (1 / 5) * Ef f - 1000 * EDthW f := by
    have hcomm : Real.sqrt 58 * Real.sqrt (EDthW f) * Real.sqrt (Ef f)
        = Real.sqrt 58 * Real.sqrt (Ef f) * Real.sqrt (EDthW f) := by ring
    rw [hcomm]
    have h := sqrt58_amgm (Real.sqrt (Ef f)) (Real.sqrt (EDthW f))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt hEfnn, Real.sq_sqrt hEdnn] at h
    linarith
  calc (1 / 5) * Ef f - 1000 * EDthW f
      ≤ (1 / 4) * Ef f - Real.sqrt 58 * Real.sqrt (EDthW f) * Real.sqrt (Ef f) := hnum
    _ ≤ wip (fun z _ => Spaces.w z ^ 2) (LGammaT α f) f := by
        rw [hT, hsplit, ← hAeq]
        linarith [hbase, hproj_int_le]

end Work.Coercivity
