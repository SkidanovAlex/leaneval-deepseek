import Mathlib
import Submission.KernelLimitFamily
import Submission.KernelFun
import Submission.PoleBound
import Submission.ZFourier
import Submission.Commons.Analysis.Schwartz.integral_norm_compl_abs_le
import Submission.Commons.Analysis.Schwartz.integral_norm_compl_mul_rpow_le

open scoped BigOperators Topology FourierTransform SchwartzMap
open Filter MeasureTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# ξ-truncation (P8 Lemma 4.1, step (iii)): the cube comparison

With the kernel realized as a function of the Fourier variables
(`Submission/KernelFun.lean`) and the family-uniform P8 (41)
(`Submission/KernelLimitFamily.lean`), the ξ-truncation compares the kernel `K`
with the inverse pole factor

    pole(ξ, ξ′)⁻¹ = (1 − 2πiξ)(1 − 2πiξ′)·N / ((2 − 2πi(ξ+ξ′))·B(x)·φ(N))

(Mathlib's Fourier normalization, so that the paper's variable is `−2πξ`).
This module proves the *pointwise* comparison on the truncation cube

    |ξ|, |ξ′| ≤ √(log x)/(2π)

(in our variables), in the relative form

    ‖K − pole⁻¹‖ ≤ ε(x)·‖pole⁻¹‖ ,     ε(x) → 0 ,

which is exactly what the integral comparison consumes (the rapid decay of the
Schwartz transforms then makes the error `o(main term)`).

All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The `k = 1` kernel equals the limit of the `Fin 1`-indexed
`coordLocalK`-products (which are the `locK`-products). -/
lemma kernelFun_eq_of_coordK (q : ℕ) {a b : ℂ}
    {L : ℂ} (h : Tendsto (fun n : ℕ =>
      ∏ p ∈ Sfilter q n, coordLocalK p (fun _ : Fin 1 => a) (fun _ : Fin 1 => b))
      atTop (𝓝 L)) : kernelFun q a b = L := by
  refine kernelFun_eq_of_tendsto (h.congr' (Eventually.of_forall (fun n => ?_)))
  exact Finset.prod_congr rfl (fun p hp => coordLocalK_one p
    (Nat.prime_of_mem_primesBelow (Finset.mem_of_mem_filter p hp)).ne_zero a b)

/-- **On-cube comparison of kernel and inverse pole factor.**  For the sieve's
family of moduli and truncation parameters, there is a vanishing error `ε` with

    ‖ K − pole(ξ,ξ′)⁻¹ ‖ ≤ ε(x)·‖pole(ξ,ξ′)⁻¹‖

on the cube `|ξ|, |ξ′| ≤ √(log x)/(2π)`, where `K` is the kernel
`∏_{p ∤ W(x)N(x)} K_p` at the sieve's points. -/
theorem norm_kernelFun_sub_poleInv_le_cube
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0)
    (hcop : ∀ x, (W x).Coprime (N x))
    (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x * N x)
    (hlq : Tendsto (fun x : ℕ =>
        Real.log (((W x) * (N x) : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ x : ℕ, x₀ ≤ x → ∀ ξ ξ' : ℝ,
        |ξ| ≤ Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi) →
        |ξ'| ≤ Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi) →
        ‖kernelFun ((W x) * (N x)) (logZ (-(2 * Real.pi * ξ)) x)
            (logZ (-(2 * Real.pi * ξ')) x) -
          (poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹‖ ≤
        ε x * ‖(poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹‖ := by
  obtain ⟨x₀, ε, hε, hbound⟩ := kernel_pole_asymptotic_family_eps 1 (by norm_num) W N hW hN hcop
    w hw hsmall hlq
  refine ⟨max x₀ 2, ε, hε, fun x hx ξ ξ' hξ hξ' => ?_⟩
  have hx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hpi : 0 < Real.pi := Real.pi_pos
  have hξp : |-(2 * Real.pi * ξ)| ≤ Real.sqrt (Real.log (x : ℝ)) := by
    rw [abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have h2 : 0 < 2 * Real.pi := by positivity
    calc 2 * Real.pi * |ξ| ≤ 2 * Real.pi * (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) := by
          exact mul_le_mul_of_nonneg_left hξ h2.le
      _ = Real.sqrt (Real.log (x : ℝ)) := by field_simp
  have hξ'p : |-(2 * Real.pi * ξ')| ≤ Real.sqrt (Real.log (x : ℝ)) := by
    rw [abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have h2 : 0 < 2 * Real.pi := by positivity
    calc 2 * Real.pi * |ξ'| ≤ 2 * Real.pi * (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) := by
          exact mul_le_mul_of_nonneg_left hξ' h2.le
      _ = Real.sqrt (Real.log (x : ℝ)) := by field_simp
  obtain ⟨L, hL, hb⟩ := hbound x hx₀ (fun _ : Fin 1 => -(2 * Real.pi * ξ))
    (fun _ : Fin 1 => -(2 * Real.pi * ξ')) (fun _ => hξp) (fun _ => hξ'p)
  rw [Fin.prod_univ_one] at hb
  have hKeq : kernelFun ((W x) * (N x)) (logZ (-(2 * Real.pi * ξ)) x)
      (logZ (-(2 * Real.pi * ξ')) x) = L := by
    refine kernelFun_eq_of_coordK _ ?_
    simpa using hL
  have hq : W x * N x ≠ 0 := mul_ne_zero (hW x) (hN x)
  have hpz : poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x ≠ 0 :=
    poleFactor_ne_zero (W x) (N x) (hW x) (hN x) _ _ hlogpos.ne'
  have hsplit : kernelFun ((W x) * (N x)) (logZ (-(2 * Real.pi * ξ)) x)
        (logZ (-(2 * Real.pi * ξ')) x) -
        (poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹ =
      (poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹ *
        (kernelFun ((W x) * (N x)) (logZ (-(2 * Real.pi * ξ)) x)
            (logZ (-(2 * Real.pi * ξ')) x) *
          poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x - 1) := by
    have h1 : (poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹ *
        poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x = 1 :=
      inv_mul_cancel₀ hpz
    exact (calc
      (poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹ *
          (kernelFun ((W x) * (N x)) (logZ (-(2 * Real.pi * ξ)) x)
              (logZ (-(2 * Real.pi * ξ')) x) *
            poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x - 1)
          = (poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹ *
              (kernelFun ((W x) * (N x)) (logZ (-(2 * Real.pi * ξ)) x)
                (logZ (-(2 * Real.pi * ξ')) x) *
              poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x) -
            (poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹ := by
              ring
      _ = ((poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹ *
              poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x) *
              kernelFun ((W x) * (N x)) (logZ (-(2 * Real.pi * ξ)) x)
                (logZ (-(2 * Real.pi * ξ')) x) -
            (poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹ := by
              ring
      _ = kernelFun ((W x) * (N x)) (logZ (-(2 * Real.pi * ξ)) x)
              (logZ (-(2 * Real.pi * ξ')) x) -
            (poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹ := by
              rw [h1, one_mul]).symm
  calc ‖kernelFun ((W x) * (N x)) (logZ (-(2 * Real.pi * ξ)) x)
          (logZ (-(2 * Real.pi * ξ')) x) -
        (poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹‖
      = ‖(poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹ *
          (kernelFun ((W x) * (N x)) (logZ (-(2 * Real.pi * ξ)) x)
              (logZ (-(2 * Real.pi * ξ')) x) *
            poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x - 1)‖ := by
          rw [hsplit]
    _ = ‖(poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹‖ *
          ‖kernelFun ((W x) * (N x)) (logZ (-(2 * Real.pi * ξ)) x)
              (logZ (-(2 * Real.pi * ξ')) x) *
            poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x - 1‖ :=
          norm_mul _ _
    _ ≤ ‖(poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹‖ * ε x := by
          rw [hKeq]
          exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = ε x * ‖(poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹‖ := by
          ring


/-! ## Setup: the Schwartz transforms of the smooth cutoffs -/

/-- The Fourier transform of `expCutoff F` as a Schwartz function. -/
noncomputable def schwartzCut (F : ℝ → ℝ) (hcs : HasCompactSupport F)
    (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) : 𝓢(ℝ, ℂ) :=
  (𝓕 : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)) (expCutoffSchwartz F hcs hsm)

lemma schwartzCut_coe (F : ℝ → ℝ) (hcs : HasCompactSupport F) (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) :
    ⇑(schwartzCut F hcs hsm) = 𝓕 (expCutoff F) := by
  unfold schwartzCut
  convert SchwartzMap.fourier_coe (f := expCutoffSchwartz F hcs hsm) using 1
  ext u
  rfl

/-- **Schwartz tail bound for the Fourier transforms of the cutoffs.** -/
theorem integral_norm_compl_fourierCut_le (F : ℝ → ℝ) (hcs : HasCompactSupport F)
    (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 1 ≤ ρ →
      ∫ x in {x : ℝ | ρ ≤ |x|}, ‖𝓕 (expCutoff F) x‖ ≤ C / ρ ^ m := by
  obtain ⟨C, hC, h⟩ := Commons.Analysis.Schwartz.integral_norm_compl_abs_le
    (schwartzCut F hcs hsm) m
  refine ⟨C, hC, fun ρ hρ => ?_⟩
  simpa [schwartzCut_coe F hcs hsm] using h ρ hρ

/-- Integrability of `(1 + 2π|ξ|) · ‖f ξ‖` for the Schwartz transform `f`
(the polynomial factor is beaten by the rapid decay of `f`). -/
theorem integrable_one_add_abs_mul_norm_fourierCut (F : ℝ → ℝ) (hcs : HasCompactSupport F)
    (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) :
    Integrable (fun ξ : ℝ => (1 + 2 * Real.pi * |ξ|) * ‖𝓕 (expCutoff F) ξ‖) := by
  obtain ⟨C₀, hC₀, hbound₀⟩ := SchwartzMap.decay (schwartzCut F hcs hsm) 0 0
  obtain ⟨C₃, hC₃, hbound₃⟩ := SchwartzMap.decay (schwartzCut F hcs hsm) 3 0
  have hcoe := schwartzCut_coe F hcs hsm
  have hb₀ : ∀ ξ : ℝ, ‖𝓕 (expCutoff F) ξ‖ ≤ C₀ := by
    intro ξ
    have h := hbound₀ ξ
    simpa [hcoe] using h
  have hb₃ : ∀ ξ : ℝ, |ξ| ^ 3 * ‖𝓕 (expCutoff F) ξ‖ ≤ C₃ := by
    intro ξ
    have h := hbound₃ ξ
    simpa [hcoe, Real.norm_eq_abs] using h
  set A : ℝ := 100 * (1 + 2 * Real.pi) * max C₀ C₃ with hA
  have hAmax : 0 < max C₀ C₃ := lt_of_lt_of_le hC₀ (le_max_left _ _)
  have hApos : 0 < A := by rw [hA]; positivity
  have hpi1 : 0 < 1 + 2 * Real.pi := by positivity
  have hdom : ∀ ξ : ℝ, (1 + 2 * Real.pi * |ξ|) * ‖𝓕 (expCutoff F) ξ‖ ≤ A * (1 + ξ ^ 2)⁻¹ := by
    intro ξ
    have h1 : (0 : ℝ) < 1 + ξ ^ 2 := by positivity
    have hxi : (0 : ℝ) ≤ |ξ| := abs_nonneg ξ
    have hfac : (1 + 2 * Real.pi * |ξ|) ≤ (1 + 2 * Real.pi) * (1 + |ξ|) := by
      nlinarith [Real.pi_pos, hxi]
    have hA1 : 2 * (1 + 2 * Real.pi) * C₀ ≤ A * (2 : ℝ)⁻¹ := by
      rw [hA]
      have h5 := mul_le_mul_of_nonneg_left (le_max_left C₀ C₃)
        (by positivity : (0 : ℝ) ≤ 100 * (1 + 2 * Real.pi))
      nlinarith [h5, hC₀, Real.pi_pos]
    have hA2 : 2 * (1 + 2 * Real.pi) * C₃ ≤ A * (2 : ℝ)⁻¹ := by
      rw [hA]
      have h5 := mul_le_mul_of_nonneg_left (le_max_right C₀ C₃)
        (by positivity : (0 : ℝ) ≤ 100 * (1 + 2 * Real.pi))
      nlinarith [h5, hC₃, Real.pi_pos]
    rcases le_total |ξ| 1 with hle | hge
    · have hplus : 1 + |ξ| ≤ 2 := by linarith
      have hstep : (1 + 2 * Real.pi * |ξ|) * ‖𝓕 (expCutoff F) ξ‖ ≤
          2 * (1 + 2 * Real.pi) * C₀ := by
        have hfac2 : (1 + 2 * Real.pi * |ξ|) ≤ 2 * (1 + 2 * Real.pi) := by
          nlinarith [hfac, hplus, Real.pi_pos]
        calc (1 + 2 * Real.pi * |ξ|) * ‖𝓕 (expCutoff F) ξ‖
            ≤ (2 * (1 + 2 * Real.pi)) * C₀ :=
              mul_le_mul hfac2 (hb₀ ξ) (norm_nonneg _) (by positivity)
          _ = 2 * (1 + 2 * Real.pi) * C₀ := by ring
      have hinv : (2 : ℝ)⁻¹ ≤ (1 + ξ ^ 2)⁻¹ :=
        (inv_le_inv₀ (by norm_num) h1).mpr (by nlinarith [hle, sq_abs ξ, hxi])
      calc (1 + 2 * Real.pi * |ξ|) * ‖𝓕 (expCutoff F) ξ‖
          ≤ 2 * (1 + 2 * Real.pi) * C₀ := hstep
        _ ≤ A * (2 : ℝ)⁻¹ := hA1
        _ ≤ A * (1 + ξ ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hinv hApos.le
    · have hxi1 : 1 ≤ |ξ| := hge
      have hplus : 1 + |ξ| ≤ 2 * |ξ| := by linarith
      have hb : ‖𝓕 (expCutoff F) ξ‖ ≤ C₃ / |ξ| ^ 3 := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < |ξ| ^ 3)]
        linarith [hb₃ ξ]
      have hstep : (1 + 2 * Real.pi * |ξ|) * ‖𝓕 (expCutoff F) ξ‖ ≤
          2 * (1 + 2 * Real.pi) * C₃ / |ξ| ^ 2 := by
        have hfac2 : (1 + 2 * Real.pi * |ξ|) ≤ 2 * (1 + 2 * Real.pi) * |ξ| := by
          nlinarith [hfac, hplus, Real.pi_pos]
        have hb' : ‖𝓕 (expCutoff F) ξ‖ ≤ C₃ / |ξ| ^ 3 := hb
        have hxx : (2 * (1 + 2 * Real.pi) * |ξ|) * (C₃ / |ξ| ^ 3) =
            2 * (1 + 2 * Real.pi) * C₃ / |ξ| ^ 2 := by
          field_simp
        have h1' := mul_le_mul hfac2 hb' (norm_nonneg _) (by positivity)
        rwa [hxx] at h1'
      have hhalf : (2 : ℝ)⁻¹ ≤ |ξ| ^ 2 / (1 + ξ ^ 2) := by
        rw [le_div_iff₀ h1]
        nlinarith [hxi1, sq_abs ξ, hxi]
      have hle : 2 * (1 + 2 * Real.pi) * C₃ / |ξ| ^ 2 ≤ A * (1 + ξ ^ 2)⁻¹ := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < |ξ| ^ 2)]
        have heq : A * (1 + ξ ^ 2)⁻¹ * |ξ| ^ 2 = A * (|ξ| ^ 2 / (1 + ξ ^ 2)) := by
          rw [div_eq_mul_inv]; ring
        rw [heq]
        calc 2 * (1 + 2 * Real.pi) * C₃ ≤ A * (2 : ℝ)⁻¹ := hA2
          _ ≤ A * (|ξ| ^ 2 / (1 + ξ ^ 2)) := mul_le_mul_of_nonneg_left hhalf hApos.le
      calc (1 + 2 * Real.pi * |ξ|) * ‖𝓕 (expCutoff F) ξ‖
          ≤ 2 * (1 + 2 * Real.pi) * C₃ / |ξ| ^ 2 := hstep
        _ ≤ A * (1 + ξ ^ 2)⁻¹ := hle
  have hint : Integrable fun ξ : ℝ => A * (1 + ξ ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul A
  have hmeas : AEStronglyMeasurable
      (fun ξ : ℝ => (1 + 2 * Real.pi * |ξ|) * ‖𝓕 (expCutoff F) ξ‖) := by
    have hc₁ : Continuous fun ξ : ℝ => (1 + 2 * Real.pi * |ξ|) := by fun_prop
    have hc₂ : Continuous fun ξ : ℝ => ‖𝓕 (expCutoff F) ξ‖ := by
      rw [← hcoe]; exact (schwartzCut F hcs hsm).continuous.norm
    exact (hc₁.mul hc₂).aestronglyMeasurable
  have hdom' : ∀ ξ : ℝ, ‖(1 + 2 * Real.pi * |ξ|) * ‖𝓕 (expCutoff F) ξ‖‖ ≤ A * (1 + ξ ^ 2)⁻¹ :=
    fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hdom ξ
  exact Integrable.mono' hint hmeas (Filter.Eventually.of_forall hdom')

/-! ## The crude bound on the kernel as a function of the Fourier variables -/

/-- **Crude bound `≪ log³x` for the kernel**, uniform in all Fourier variables:
`CrudeKernelCoord.crudeKernelCoord_eventually` transferred to the limit via
`norm_kernelFun_le`. -/
theorem crude_kernelFun_bound (q : ℕ) (hq : q ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, ∀ ξ ξ' : ℝ,
      ‖kernelFun q (logZ ξ x) (logZ ξ' x)‖ ≤ C * (Real.log (x : ℝ)) ^ 3 := by
  obtain ⟨C, hC, hx⟩ := crudeKernelCoord_eventually q 1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hx, eventually_gt_atTop 1] with x hx1 hx2
  intro ξ ξ'
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx2)
  refine norm_kernelFun_le hq ?_ ?_ (fun n => ?_)
  · rw [logZ_re]; positivity
  · rw [logZ_re]; positivity
  · have h := hx1 n (fun _ : Fin 1 => logZ ξ x) (fun _ : Fin 1 => logZ ξ' x)
      (fun _ => by rw [logZ_re]) (fun _ => by rw [logZ_re])
    have hprod : (∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
        coordLocalK p (fun _ : Fin 1 => logZ ξ x) (fun _ : Fin 1 => logZ ξ' x)) =
        ∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
          locK p (logZ ξ x) (logZ ξ' x) :=
      Finset.prod_congr rfl (fun p hp => coordLocalK_one p
        (Nat.prime_of_mem_primesBelow (Finset.mem_of_mem_filter p hp)).ne_zero _ _)
    rw [hprod] at h
    simpa [Sfilter] using h


/-! ## The truncation cube and the integral comparison -/

/-- The prefactor `(N/φ(N))·(W/φ(W))·(log x)⁻¹` of the pole bound — equal to the
`N/(B(x)φ(N))` of P8 with `B(x) = (φ(W)/W)·log x`. -/
noncomputable def prefactor (W N : ℕ → ℕ) (x : ℕ) : ℝ :=
  ((N x : ℝ) / ((N x).totient : ℝ)) * ((W x : ℝ) / ((W x).totient : ℝ)) *
    (Real.log (x : ℝ))⁻¹

/-- The kernel `∏_{p ∤ WN} K_p` at the sieve's Fourier variables (Mathlib
normalization). -/
noncomputable def kernelP (W N : ℕ → ℕ) (x : ℕ) (p : ℝ × ℝ) : ℂ :=
  kernelFun ((W x) * (N x)) (logZ (-(2 * Real.pi * p.1)) x)
    (logZ (-(2 * Real.pi * p.2)) x)

/-- The inverse pole factor at the sieve's Fourier variables. -/
noncomputable def poleP (W N : ℕ → ℕ) (x : ℕ) (p : ℝ × ℝ) : ℂ :=
  (poleFactor (W x) (N x) (-(2 * Real.pi * p.1)) (-(2 * Real.pi * p.2)) x)⁻¹

/-- The truncation cube `|ξ|, |ξ′| ≤ √(log x)/(2π)`. -/
noncomputable def truncCube (x : ℕ) : Set (ℝ × ℝ) :=
  (Set.Icc (-(Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)))
      (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi))) ×ˢ
    (Set.Icc (-(Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)))
      (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)))

lemma mem_truncCube {x : ℕ} {p : ℝ × ℝ} (hp : p ∈ truncCube x) :
    |p.1| ≤ Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi) ∧
      |p.2| ≤ Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi) := by
  obtain ⟨h1, h2⟩ := hp
  rw [Set.mem_Icc] at h1 h2
  exact ⟨abs_le.mpr ⟨h1.1, h1.2⟩, abs_le.mpr ⟨h2.1, h2.2⟩⟩

/-- **Cube part of the truncation.**  On the cube, the pointwise comparison of
`norm_kernelFun_sub_poleInv_le_cube` together with the growth bound
`norm_poleInv_le` gives the integral bound

    ∫_{cube} ‖K − pole⁻¹‖·‖f‖·‖g‖ ≤ ε(x)·(N/φ(N))(W/φ(W))(1/log x)·C_f·C_g ,

with `C_f = ∫ (1 + 2π|ξ|)‖f ξ‖ dξ` and likewise `C_g` — both fixed constants
(independent of `x`). -/
theorem cube_integral_kernel_sub_pole_le
    (F G : ℝ → ℝ) (hcsF : HasCompactSupport F) (hsmF : ContDiff ℝ (↑(⊤ : ℕ∞)) F)
    (hcsG : HasCompactSupport G) (hsmG : ContDiff ℝ (↑(⊤ : ℕ∞)) G)
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0)
    (hcop : ∀ x, (W x).Coprime (N x))
    (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x * N x)
    (hlq : Tendsto (fun x : ℕ =>
        Real.log (((W x) * (N x) : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ x : ℕ, x₀ ≤ x →
        (∫ p in truncCube x,
            ‖(kernelP W N x p - poleP W N x p) *
              (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖) ≤
          |ε x| * prefactor W N x *
            (∫ ξ : ℝ, (1 + 2 * Real.pi * |ξ|) * ‖𝓕 (expCutoff F) ξ‖) *
            (∫ ξ : ℝ, (1 + 2 * Real.pi * |ξ|) * ‖𝓕 (expCutoff G) ξ‖) := by
  obtain ⟨x₀₁, ε, hε, hcomp⟩ := norm_kernelFun_sub_poleInv_le_cube W N hW hN hcop w hw hsmall hlq
  refine ⟨max x₀₁ 2, ε, hε, fun x hx => ?_⟩
  have hx₁ : x₀₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx₂ : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hmeas : MeasurableSet (truncCube x) :=
    (measurableSet_Icc).prod measurableSet_Icc
  -- the pointwise bound on the cube
  have hpt : ∀ p ∈ truncCube x,
      ‖(kernelP W N x p - poleP W N x p) *
          (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖ ≤
        |ε x| * prefactor W N x *
          ((1 + 2 * Real.pi * |p.1|) * (1 + 2 * Real.pi * |p.2|) *
            ‖𝓕 (expCutoff F) p.1‖ * ‖𝓕 (expCutoff G) p.2‖) := by
    intro p hp
    obtain ⟨h1, h2⟩ := mem_truncCube hp
    have hcmp := hcomp x hx₁ p.1 p.2 h1 h2
    have hgrowth := norm_poleInv_le (W x) (N x) (hW x) (hN x) hL.ne' hL p.1 p.2
    have hpre : 0 ≤ prefactor W N x := by
      rw [prefactor]
      have h1' : (0 : ℝ) < (N x).totient := by
        exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hN x))
      have h2' : (0 : ℝ) < (W x).totient := by
        exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hW x))
      positivity
    have hcmp' : ‖kernelP W N x p - poleP W N x p‖ ≤ |ε x| * ‖poleP W N x p‖ :=
      hcmp.trans (mul_le_mul_of_nonneg_right (le_abs_self (ε x)) (norm_nonneg _))
    have hε0 : (0 : ℝ) ≤ |ε x| := abs_nonneg _
    rw [norm_mul, norm_mul]
    calc ‖kernelP W N x p - poleP W N x p‖ * (‖𝓕 (expCutoff F) p.1‖ *
          ‖𝓕 (expCutoff G) p.2‖)
        ≤ (|ε x| * ‖poleP W N x p‖) * (‖𝓕 (expCutoff F) p.1‖ *
            ‖𝓕 (expCutoff G) p.2‖) :=
          mul_le_mul_of_nonneg_right hcmp' (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ |ε x| * (((N x : ℝ) / ((N x).totient : ℝ)) * ((W x : ℝ) / ((W x).totient : ℝ)) *
            (Real.log (x : ℝ))⁻¹ * (1 + 2 * Real.pi * |p.1|) *
            (1 + 2 * Real.pi * |p.2|)) *
            (‖𝓕 (expCutoff F) p.1‖ * ‖𝓕 (expCutoff G) p.2‖) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgrowth hε0)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = |ε x| * prefactor W N x *
          ((1 + 2 * Real.pi * |p.1|) * (1 + 2 * Real.pi * |p.2|) *
            ‖𝓕 (expCutoff F) p.1‖ * ‖𝓕 (expCutoff G) p.2‖) := by
          rw [prefactor]; ring
  -- the dominating function
  set Φ : ℝ × ℝ → ℝ := fun p =>
    (1 + 2 * Real.pi * |p.1|) * (1 + 2 * Real.pi * |p.2|) *
      ‖𝓕 (expCutoff F) p.1‖ * ‖𝓕 (expCutoff G) p.2‖ with hΦ
  have hΦint : Integrable Φ := by
    rw [hΦ]
    have hthis := (integrable_one_add_abs_mul_norm_fourierCut F hcsF hsmF).mul_prod
      (integrable_one_add_abs_mul_norm_fourierCut G hcsG hsmG)
    have hfun : (fun z : ℝ × ℝ => (1 + 2 * Real.pi * |z.1|) * ‖𝓕 (expCutoff F) z.1‖ *
        ((1 + 2 * Real.pi * |z.2|) * ‖𝓕 (expCutoff G) z.2‖)) =
        fun p : ℝ × ℝ => (1 + 2 * Real.pi * |p.1|) * (1 + 2 * Real.pi * |p.2|) *
          ‖𝓕 (expCutoff F) p.1‖ * ‖𝓕 (expCutoff G) p.2‖ := by
      funext p; ring
    rw [hfun] at hthis
    exact hthis
  have hΦnonneg : ∀ p, 0 ≤ Φ p := fun p => by rw [hΦ]; positivity
  -- measurability of the integrand
  have hmeas_kernel : Measurable (kernelP W N x) := measurable_kernelFun ((W x) * (N x)) x
  have hmeas_pole : Measurable (poleP W N x) := by
    have h := poleInv_eq (W x) (N x) (hW x) (hN x) hL.ne'
    rw [show poleP W N x = fun p : ℝ × ℝ =>
        (((N x : ℂ) / (((W x).totient : ℂ) / (W x : ℂ) * (Real.log (x : ℝ) : ℂ) *
            ((N x).totient : ℂ))) *
          ((1 - 2 * Real.pi * Complex.I * p.1) * (1 - 2 * Real.pi * Complex.I * p.2) /
            (2 - 2 * Real.pi * Complex.I * (p.1 + p.2)))) from by
      funext p; exact h p.1 p.2]
    fun_prop
  have hmeas_fg : Measurable fun p : ℝ × ℝ =>
      𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2 := by
    have h1 : Continuous fun p : ℝ × ℝ => 𝓕 (expCutoff F) p.1 := by
      rw [← schwartzCut_coe F hcsF hsmF]; exact (schwartzCut F hcsF hsmF).continuous.comp continuous_fst
    have h2 : Continuous fun p : ℝ × ℝ => 𝓕 (expCutoff G) p.2 := by
      rw [← schwartzCut_coe G hcsG hsmG]; exact (schwartzCut G hcsG hsmG).continuous.comp continuous_snd
    exact (h1.mul h2).measurable
  have hnormint : IntegrableOn
      (fun p : ℝ × ℝ => ‖(kernelP W N x p - poleP W N x p) *
        (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖) (truncCube x) volume := by
    refine Integrable.mono' ((hΦint.const_mul (|ε x| * prefactor W N x)).restrict) ?_ ?_
    · exact (((hmeas_kernel.sub hmeas_pole).mul hmeas_fg).norm).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hmeas] with p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hpt p hp
  have hgint : IntegrableOn (fun p : ℝ × ℝ => |ε x| * prefactor W N x * Φ p)
      (truncCube x) volume :=
    (hΦint.const_mul (|ε x| * prefactor W N x)).restrict
  have hbound : (∫ p in truncCube x,
        ‖(kernelP W N x p - poleP W N x p) *
          (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖) ≤
      ∫ p in truncCube x, |ε x| * prefactor W N x * Φ p :=
    setIntegral_mono_on hnormint hgint hmeas hpt
  -- the prefactor is nonnegative
  have hpre0 : 0 ≤ prefactor W N x := by
    have h1' : (0 : ℝ) < (N x).totient := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hN x))
    have h2' : (0 : ℝ) < (W x).totient := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hW x))
    rw [prefactor]
    exact mul_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) h1'.le)
      (div_nonneg (Nat.cast_nonneg _) h2'.le)) (inv_nonneg.mpr hL.le)
  have hΦcube0 : 0 ≤ ∫ p in truncCube x, Φ p :=
    setIntegral_nonneg hmeas (fun p _ => hΦnonneg p)
  have hΦcube : (∫ p in truncCube x, Φ p) ≤
      (∫ ξ : ℝ, (1 + 2 * Real.pi * |ξ|) * ‖𝓕 (expCutoff F) ξ‖) *
        (∫ ξ : ℝ, (1 + 2 * Real.pi * |ξ|) * ‖𝓕 (expCutoff G) ξ‖) := by
    calc (∫ p in truncCube x, Φ p) ≤ ∫ p in Set.univ, Φ p :=
          setIntegral_mono_set hΦint.integrableOn
            (Filter.Eventually.of_forall (fun p => hΦnonneg p))
            (Filter.Eventually.of_forall (fun p _ => trivial))
      _ = ∫ p : ℝ × ℝ, Φ p := setIntegral_univ
      _ = _ := by
          rw [hΦ]
          rw [show (fun p : ℝ × ℝ => (1 + 2 * Real.pi * |p.1|) * (1 + 2 * Real.pi * |p.2|) *
                ‖𝓕 (expCutoff F) p.1‖ * ‖𝓕 (expCutoff G) p.2‖) =
              fun p : ℝ × ℝ =>
                ((1 + 2 * Real.pi * |p.1|) * ‖𝓕 (expCutoff F) p.1‖) *
                  ((1 + 2 * Real.pi * |p.2|) * ‖𝓕 (expCutoff G) p.2‖) from by
            funext p; ring]
          exact integral_prod_mul
            (fun ξ : ℝ => (1 + 2 * Real.pi * |ξ|) * ‖𝓕 (expCutoff F) ξ‖)
            (fun ξ : ℝ => (1 + 2 * Real.pi * |ξ|) * ‖𝓕 (expCutoff G) ξ‖)
  set A : ℝ → ℝ := fun ξ : ℝ =>
    (1 + 2 * Real.pi * |ξ|) * ‖(𝓕 (expCutoff F) : ℝ → ℂ) ξ‖ with hAdef
  set B : ℝ → ℝ := fun ξ : ℝ =>
    (1 + 2 * Real.pi * |ξ|) * ‖(𝓕 (expCutoff G) : ℝ → ℂ) ξ‖ with hBdef
  have hAint : Integrable A := by
    rw [hAdef]; exact integrable_one_add_abs_mul_norm_fourierCut F hcsF hsmF
  have hBint : Integrable B := by
    rw [hBdef]; exact integrable_one_add_abs_mul_norm_fourierCut G hcsG hsmG
  have hA0 : ∀ ξ, 0 ≤ A ξ := fun ξ => by rw [hAdef]; positivity
  have hB0 : ∀ ξ, 0 ≤ B ξ := fun ξ => by rw [hBdef]; positivity
  have hpre0' : 0 ≤ |ε x| * prefactor W N x := mul_nonneg (abs_nonneg _) hpre0
  refine hbound.trans ?_
  calc (∫ p in truncCube x, |ε x| * prefactor W N x * Φ p)
      = (|ε x| * prefactor W N x) * (∫ p in truncCube x, A p.1 * B p.2) := by
        rw [show (∫ p in truncCube x, |ε x| * prefactor W N x * Φ p) =
            ∫ p in truncCube x, (|ε x| * prefactor W N x) * (A p.1 * B p.2) from by
          refine setIntegral_congr_fun hmeas (fun p _ => ?_)
          rw [hΦ, hAdef, hBdef]; ring]
        exact integral_const_mul (|ε x| * prefactor W N x)
          (fun p : ℝ × ℝ => A p.1 * B p.2)
    _ ≤ (|ε x| * prefactor W N x) * (∫ p : ℝ × ℝ, A p.1 * B p.2) := by
        refine mul_le_mul_of_nonneg_left ?_ hpre0'
        have hstep : (∫ p in truncCube x, A p.1 * B p.2) ≤
            (∫ p : ℝ × ℝ, A p.1 * B p.2) := by
          rw [show (∫ p : ℝ × ℝ, A p.1 * B p.2) =
              ∫ p in (Set.univ : Set (ℝ × ℝ)), A p.1 * B p.2 from (setIntegral_univ).symm]
          exact setIntegral_mono_set (s := truncCube x) (t := (Set.univ : Set (ℝ × ℝ)))
            (hAint.mul_prod hBint).integrableOn
            (Filter.Eventually.of_forall (fun p => mul_nonneg (hA0 p.1) (hB0 p.2)))
            (Filter.Eventually.of_forall (fun p _ => trivial))
        exact hstep
    _ = (|ε x| * prefactor W N x) * ((∫ ξ : ℝ, A ξ) * (∫ ξ : ℝ, B ξ)) := by
        exact congrArg _ (integral_prod_mul A B)
    _ = |ε x| * prefactor W N x * (∫ ξ : ℝ, (1 + 2 * Real.pi * |ξ|) * ‖𝓕 (expCutoff F) ξ‖) *
          (∫ ξ : ℝ, (1 + 2 * Real.pi * |ξ|) * ‖𝓕 (expCutoff G) ξ‖) := by
        rw [hAdef, hBdef]; ring


/-! ## Weighted Schwartz tails -/

/-- The weight `(1 + 2π|ξ|)·‖𝓕(expCutoff F) ξ‖` whose integral is the constant
`C_F` of the truncation estimates. -/
noncomputable def wCut (F : ℝ → ℝ) : ℝ → ℝ :=
  fun ξ => (1 + 2 * Real.pi * |ξ|) * ‖𝓕 (expCutoff F) ξ‖

lemma integrable_wCut (F : ℝ → ℝ) (hcs : HasCompactSupport F) (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) :
    Integrable (wCut F) :=
  integrable_one_add_abs_mul_norm_fourierCut F hcs hsm

lemma wCut_nonneg (F : ℝ → ℝ) (ξ : ℝ) : 0 ≤ wCut F ξ := by
  rw [wCut]; positivity

/-- The tail of the weighted transform: `∫_{ρ ≤ |ξ|} (1 + 2π|ξ|)‖f ξ‖`. -/
noncomputable def wCutTail (F : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  ∫ ξ in {ξ : ℝ | ρ ≤ |ξ|}, wCut F ξ

/-- **Polynomial decay of the weighted tail.** -/
theorem wCutTail_le (F : ℝ → ℝ) (hcs : HasCompactSupport F) (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F)
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 1 ≤ ρ → wCutTail F ρ ≤ C / ρ ^ m := by
  obtain ⟨C₁, hC₁, h₁⟩ := Commons.Analysis.Schwartz.integral_norm_compl_mul_rpow_le
    (schwartzCut F hcs hsm) 1 m
  have hcoe := schwartzCut_coe F hcs hsm
  refine ⟨(1 + 2 * Real.pi) * C₁, by positivity, fun ρ hρ => ?_⟩
  have hmeasS : MeasurableSet {ξ : ℝ | ρ ≤ |ξ|} := measurableSet_Ici.preimage measurable_abs
  -- integrability of the weighted function
  have hint2 : Integrable
      (fun x : ℝ => (1 + 2 * Real.pi) * ((1 + |x|) ^ 1 * ‖(schwartzCut F hcs hsm) x‖)) := by
    have hbnd : ∀ x : ℝ, ‖(1 + 2 * Real.pi) *
        ((1 + |x|) ^ 1 * ‖(schwartzCut F hcs hsm) x‖)‖
        ≤ (2 * (1 + 2 * Real.pi)) * wCut F x := by
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_one, wCut, hcoe]
      have h2 : 1 + |x| ≤ 2 * (1 + 2 * Real.pi * |x|) := by
        nlinarith [Real.pi_gt_three, abs_nonneg x]
      have h3 : (0 : ℝ) ≤ ‖𝓕 (expCutoff F) x‖ := norm_nonneg _
      have h4 : (1 + 2 * Real.pi) * ((1 + |x|) * ‖𝓕 (expCutoff F) x‖) ≤
          2 * (1 + 2 * Real.pi) * ((1 + 2 * Real.pi * |x|) * ‖𝓕 (expCutoff F) x‖) := by
        have h5 := mul_le_mul_of_nonneg_left h2
          (by positivity : (0 : ℝ) ≤ (1 + 2 * Real.pi) * ‖𝓕 (expCutoff F) x‖)
        nlinarith [h5]
      linarith [h4]
    refine Integrable.mono' ((integrable_wCut F hcs hsm).const_mul (2 * (1 + 2 * Real.pi))) ?_ ?_
    · exact (continuous_const.mul ((continuous_const.add continuous_abs).pow 1 |>.mul
        (schwartzCut F hcs hsm).continuous.norm)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall hbnd
  have hpoint : ∀ ξ ∈ {ξ : ℝ | ρ ≤ |ξ|}, wCut F ξ ≤
      (1 + 2 * Real.pi) * ((1 + |ξ|) ^ 1 * ‖(schwartzCut F hcs hsm) ξ‖) := by
    intro ξ _
    have hfac : (1 + 2 * Real.pi * |ξ|) ≤ (1 + 2 * Real.pi) * (1 + |ξ|) := by
      nlinarith [Real.pi_pos, abs_nonneg ξ]
    rw [wCut, hcoe, pow_one]
    calc (1 + 2 * Real.pi * |ξ|) * ‖𝓕 (expCutoff F) ξ‖
        ≤ ((1 + 2 * Real.pi) * (1 + |ξ|)) * ‖𝓕 (expCutoff F) ξ‖ :=
          mul_le_mul_of_nonneg_right hfac (norm_nonneg _)
      _ = (1 + 2 * Real.pi) * ((1 + |ξ|) * ‖𝓕 (expCutoff F) ξ‖) := by ring
  have hmono := (setIntegral_mono_on ((integrable_wCut F hcs hsm).integrableOn)
    hint2.integrableOn hmeasS hpoint).trans_eq
      (integral_const_mul (1 + 2 * Real.pi)
        (fun x : ℝ => (1 + |x|) ^ 1 * ‖(schwartzCut F hcs hsm) x‖))
  rw [wCutTail]
  calc (∫ ξ in {ξ : ℝ | ρ ≤ |ξ|}, wCut F ξ)
      ≤ (1 + 2 * Real.pi) *
          ∫ x in {x : ℝ | ρ ≤ |x|}, (1 + |x|) ^ 1 * ‖(schwartzCut F hcs hsm) x‖ := hmono
    _ ≤ (1 + 2 * Real.pi) * (C₁ / ρ ^ m) :=
        mul_le_mul_of_nonneg_left (h₁ ρ hρ) (by positivity)
    _ = (1 + 2 * Real.pi) * C₁ / ρ ^ m := by ring


/-! ## Off-cube bounds -/

/-- The `L¹` norm of the Schwartz transform. -/
noncomputable def l1Cut (F : ℝ → ℝ) : ℝ := ∫ ξ : ℝ, ‖𝓕 (expCutoff F) ξ‖

/-- The plain Schwartz tail `∫_{ρ ≤ |ξ|} ‖f ξ‖`. -/
noncomputable def cutTail (F : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  ∫ ξ in {ξ : ℝ | ρ ≤ |ξ|}, ‖𝓕 (expCutoff F) ξ‖

lemma integrable_norm_fourierCut (F : ℝ → ℝ) (hcs : HasCompactSupport F)
    (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) : Integrable (fun ξ : ℝ => ‖𝓕 (expCutoff F) ξ‖) :=
  (fourier_expCutoff_integrable F hcs hsm).norm

/-- Polynomial decay of the plain tail (L30). -/
theorem cutTail_le (F : ℝ → ℝ) (hcs : HasCompactSupport F) (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 1 ≤ ρ → cutTail F ρ ≤ C / ρ ^ m := by
  obtain ⟨C, hC, h⟩ := Commons.Analysis.Schwartz.integral_norm_compl_abs_le
    (schwartzCut F hcs hsm) m
  refine ⟨C, hC, fun ρ hρ => ?_⟩
  have h1 := h ρ hρ
  rw [cutTail]
  simpa [schwartzCut_coe F hcs hsm] using h1

lemma measurableSet_truncCube (x : ℕ) : MeasurableSet (truncCube x) :=
  (measurableSet_Icc).prod measurableSet_Icc

/-- The complement of the cube is contained in the union of the two strips where
one coordinate exceeds the radius. -/
lemma compl_truncCube_subset (x : ℕ) :
    (truncCube x)ᶜ ⊆
      ({p : ℝ × ℝ | Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi) ≤ |p.1|} ∪
        {p : ℝ × ℝ | Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi) ≤ |p.2|}) := by
  intro p hp
  set ρ : ℝ := Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi) with hρ
  by_cases h1 : ρ ≤ |p.1|
  · exact Or.inl h1
  · refine Or.inr ?_
    by_contra h2
    have h2' : |p.2| < ρ := not_le.mp h2
    refine hp ?_
    rw [truncCube, Set.mem_prod]
    exact ⟨⟨by linarith [neg_le_abs p.1, le_of_lt (not_le.mp h1)],
      by linarith [le_abs_self p.1, le_of_lt (not_le.mp h1)]⟩,
      ⟨by linarith [neg_le_abs p.2, le_of_lt h2'],
        by linarith [le_abs_self p.2, le_of_lt h2']⟩⟩

/-! ## Off-cube bounds and the truncation assembly

The following block completes the ξ-truncation (P8 Lemma 4.1 (iii)): the two
off-cube estimates (crude kernel bound resp. polynomial pole bound against the
Schwartz tails) and the assembly of the truncation comparison

    ‖∫_{ℝ²} (K − pole⁻¹)·f⊗g‖ ≤ ε(x)·prefactor ,   ε(x) → 0 .

All kernel-verified, zero `sorry`. -/


lemma setIntegral_le_add_of_subset_union {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {h : X → ℝ} {s t S : Set X} (hS : S ⊆ s ∪ t)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hint : Integrable h μ) (h0 : ∀ x, 0 ≤ h x) :
    ∫ x in S, h x ∂μ ≤ ∫ x in s, h x ∂μ + ∫ x in t, h x ∂μ := by
  have hsub : ∫ x in S, h x ∂μ ≤ ∫ x in s ∪ t, h x ∂μ :=
    setIntegral_mono_set (hint.integrableOn)
      (Filter.Eventually.of_forall h0) (Filter.Eventually.of_forall (fun x hx => hS hx))
  have hmeas' : MeasurableSet (t \ s) := ht.diff hs
  have hdisj : Disjoint s (t \ s) := disjoint_sdiff_self_right
  have hunion : s ∪ (t \ s) = s ∪ t := by
    ext x; simp only [Set.mem_union, Set.mem_sdiff]; tauto
  have hsplit : ∫ x in s ∪ t, h x ∂μ = ∫ x in s, h x ∂μ + ∫ x in t \ s, h x ∂μ := by
    rw [← hunion]
    exact setIntegral_union hdisj hmeas' hint.integrableOn
      (hint.integrableOn.mono_set Set.sdiff_subset)
  have hmono : ∫ x in t \ s, h x ∂μ ≤ ∫ x in t, h x ∂μ :=
    setIntegral_mono_set hint.integrableOn
      (Filter.Eventually.of_forall h0) (Filter.Eventually.of_forall (fun x hx => hx.1))
  linarith

lemma setIntegral_const_mul' {X : Type*} [MeasurableSpace X] {μ : Measure X} (c : ℝ) (f : X → ℝ)
    {s : Set X} (hs : MeasurableSet s) :
    ∫ x in s, c * f x ∂μ = c * ∫ x in s, f x ∂μ := by
  rw [← integral_indicator hs, ← integral_indicator hs,
    show s.indicator (fun x => c * f x) = fun x => c * s.indicator f x from by
      funext x
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; ring]
  exact integral_const_mul c _

lemma setIntegral_mul_const' {X : Type*} [MeasurableSpace X] {μ : Measure X} (c : ℝ) (f : X → ℝ)
    {s : Set X} (hs : MeasurableSet s) :
    ∫ x in s, f x * c ∂μ = (∫ x in s, f x ∂μ) * c := by
  rw [← integral_indicator hs, ← integral_indicator hs,
    show s.indicator (fun x => f x * c) = fun x => s.indicator f x * c from by
      funext x
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; ring]
  exact integral_mul_const c _

lemma measurableSet_sIci (ρ : ℝ) : MeasurableSet {p : ℝ × ℝ | ρ ≤ |p.1|} :=
  measurableSet_Ici.preimage (measurable_abs.comp measurable_fst)
lemma measurableSet_sIci' (ρ : ℝ) : MeasurableSet {p : ℝ × ℝ | ρ ≤ |p.2|} :=
  measurableSet_Ici.preimage (measurable_abs.comp measurable_snd)

lemma integral_prod_strip (A B : ℝ → ℝ) (hA : Integrable A) (hB : Integrable B) (ρ : ℝ) :
    ∫ p in ({ξ : ℝ | ρ ≤ |ξ|} ×ˢ (Set.univ : Set ℝ)), A p.1 * B p.2
      = (∫ ξ in {ξ : ℝ | ρ ≤ |ξ|}, A ξ) * (∫ ξ : ℝ, B ξ) := by
  have hf : IntegrableOn (fun p : ℝ × ℝ => A p.1 * B p.2)
      ({ξ : ℝ | ρ ≤ |ξ|} ×ˢ (Set.univ : Set ℝ)) (volume.prod volume) :=
    (hA.mul_prod hB).integrableOn
  rw [show (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume from rfl]
  rw [setIntegral_prod _ hf]
  simp only [setIntegral_univ]
  simp_rw [integral_const_mul]
  exact setIntegral_mul_const' _ A (measurableSet_Ici.preimage measurable_abs)

lemma integral_prod_strip' (A B : ℝ → ℝ) (hA : Integrable A) (hB : Integrable B) (ρ : ℝ) :
    ∫ p in ((Set.univ : Set ℝ) ×ˢ {ξ : ℝ | ρ ≤ |ξ|}), A p.1 * B p.2
      = (∫ ξ : ℝ, A ξ) * (∫ ξ in {ξ : ℝ | ρ ≤ |ξ|}, B ξ) := by
  have hf : IntegrableOn (fun p : ℝ × ℝ => A p.1 * B p.2)
      ((Set.univ : Set ℝ) ×ˢ {ξ : ℝ | ρ ≤ |ξ|}) (volume.prod volume) :=
    (hA.mul_prod hB).integrableOn
  rw [show (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume from rfl]
  rw [setIntegral_prod _ hf]
  simp only [setIntegral_univ]
  simp_rw [integral_const_mul]
  exact integral_mul_const _ A

theorem crude_kernelFun_bound_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, ∀ (q : ℕ) (_hq : q ≠ 0) (ξ ξ' : ℝ),
      ‖kernelFun q (logZ ξ x) (logZ ξ' x)‖ ≤ C * (Real.log (x : ℝ)) ^ 3 := by
  obtain ⟨C, hC, hx⟩ := crudeKernelCoord_eventually_uniform 1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hx, eventually_gt_atTop 1] with x hx1 hx2
  intro q hq ξ ξ'
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx2)
  refine norm_kernelFun_le hq ?_ ?_ (fun n => ?_)
  · rw [logZ_re]; positivity
  · rw [logZ_re]; positivity
  · have h := hx1 q n (fun _ : Fin 1 => logZ ξ x) (fun _ : Fin 1 => logZ ξ' x)
      (fun _ => by rw [logZ_re]) (fun _ => by rw [logZ_re])
    have hprod : (∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
        coordLocalK p (fun _ : Fin 1 => logZ ξ x) (fun _ : Fin 1 => logZ ξ' x)) =
        ∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
          locK p (logZ ξ x) (logZ ξ' x) :=
      Finset.prod_congr rfl (fun p hp => coordLocalK_one p
        (Nat.prime_of_mem_primesBelow (Finset.mem_of_mem_filter p hp)).ne_zero _ _)
    rw [hprod] at h
    simpa [Sfilter] using h

theorem offCube_kernel_le
    (F G : ℝ → ℝ) (hcsF : HasCompactSupport F) (hsmF : ContDiff ℝ (↑(⊤ : ℕ∞)) F)
    (hcsG : HasCompactSupport G) (hsmG : ContDiff ℝ (↑(⊤ : ℕ∞)) G) :
    ∃ x₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, x₀ ≤ x → ∀ (q : ℕ) (hq : q ≠ 0),
      (∫ p in (truncCube x)ᶜ,
        ‖kernelFun q (logZ (-(2 * Real.pi * p.1)) x) (logZ (-(2 * Real.pi * p.2)) x) *
          (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖) ≤
      C * (Real.log (x : ℝ)) ^ 3 *
        (cutTail F (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) * l1Cut G +
          l1Cut F * cutTail G (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi))) := by
  obtain ⟨Ck, hCk, hxk⟩ := crude_kernelFun_bound_uniform
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hxk
  refine ⟨max X₀ (max 2 (Nat.ceil (Real.exp ((2 * Real.pi) ^ 2 + 2)) + 1)), Ck, hCk, ?_⟩
  intro x hx q hq
  have hX₀x : X₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := le_trans (le_trans (le_max_left 2 _) (le_max_right X₀ _)) hx
  have hxceil : Nat.ceil (Real.exp ((2 * Real.pi) ^ 2 + 2)) + 1 ≤ x :=
    le_trans (le_trans (le_max_right 2 _) (le_max_right X₀ _)) hx
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hxexp : Real.exp ((2 * Real.pi) ^ 2 + 2) < (x : ℝ) := by
    have h1 : Real.exp ((2 * Real.pi) ^ 2 + 2) ≤
        (Nat.ceil (Real.exp ((2 * Real.pi) ^ 2 + 2)) : ℕ) :=
      Nat.le_ceil (Real.exp ((2 * Real.pi) ^ 2 + 2))
    have h2 : ((Nat.ceil (Real.exp ((2 * Real.pi) ^ 2 + 2)) : ℕ) : ℝ) <
        ((Nat.ceil (Real.exp ((2 * Real.pi) ^ 2 + 2)) + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    have h3 : ((Nat.ceil (Real.exp ((2 * Real.pi) ^ 2 + 2)) + 1 : ℕ) : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast hxceil
    linarith
  have hxbig : (2 * Real.pi) ^ 2 + 2 ≤ Real.log (x : ℝ) := by
    have := Real.log_le_log (Real.exp_pos _) hxexp.le
    rwa [Real.log_exp] at this
  have h2π : 0 < 2 * Real.pi := by positivity
  have hrho1 : 1 ≤ Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi) := by
    have hsq : (2 * Real.pi) ^ 2 ≤ Real.log (x : ℝ) := by linarith
    have hle : 2 * Real.pi ≤ Real.sqrt (Real.log (x : ℝ)) := by
      rw [← Real.sqrt_sq h2π.le]; exact Real.sqrt_le_sqrt hsq
    rw [le_div_iff₀ h2π]; linarith
  set ρ : ℝ := Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi) with hρdef
  -- the dominating function
  set hdom : ℝ × ℝ → ℝ :=
    fun p => Ck * (Real.log (x : ℝ)) ^ 3 * (‖𝓕 (expCutoff F) p.1‖ * ‖𝓕 (expCutoff G) p.2‖)
    with hdomdef
  have hdomint : Integrable hdom := by
    rw [hdomdef]
    have hg2 : Integrable (fun p : ℝ × ℝ =>
        ‖𝓕 (expCutoff F) p.1‖ * ‖𝓕 (expCutoff G) p.2‖) := by
      rw [show (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume from rfl]
      exact (integrable_norm_fourierCut F hcsF hsmF).mul_prod
        (integrable_norm_fourierCut G hcsG hsmG)
    exact hg2.const_mul _
  have hdom0 : ∀ p, 0 ≤ hdom p := by
    intro p; rw [hdomdef]; positivity
  -- pointwise bound on the complement
  have hpt : ∀ p ∈ (truncCube x)ᶜ,
      ‖kernelFun q (logZ (-(2 * Real.pi * p.1)) x) (logZ (-(2 * Real.pi * p.2)) x) *
          (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖ ≤ hdom p := by
    intro p _
    have hk := hX₀ x hX₀x q hq (-(2 * Real.pi * p.1)) (-(2 * Real.pi * p.2))
    rw [hdomdef, norm_mul, norm_mul]
    have h1 : ‖kernelFun q (logZ (-(2 * Real.pi * p.1)) x) (logZ (-(2 * Real.pi * p.2)) x)‖ *
        ‖𝓕 (expCutoff F) p.1‖ * ‖𝓕 (expCutoff G) p.2‖ ≤
        Ck * (Real.log (x : ℝ)) ^ 3 * ‖𝓕 (expCutoff F) p.1‖ * ‖𝓕 (expCutoff G) p.2‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hk (norm_nonneg _)) (norm_nonneg _)
    nlinarith [h1]
  -- measurability of the integrand
  have hmeas_fg : Measurable fun p : ℝ × ℝ => 𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2 := by
    have h1 : Continuous fun p : ℝ × ℝ => 𝓕 (expCutoff F) p.1 := by
      rw [← schwartzCut_coe F hcsF hsmF]
      exact (schwartzCut F hcsF hsmF).continuous.comp continuous_fst
    have h2 : Continuous fun p : ℝ × ℝ => 𝓕 (expCutoff G) p.2 := by
      rw [← schwartzCut_coe G hcsG hsmG]
      exact (schwartzCut G hcsG hsmG).continuous.comp continuous_snd
    exact (h1.mul h2).measurable
  have hmeasint : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ‖kernelFun q (logZ (-(2 * Real.pi * p.1)) x) (logZ (-(2 * Real.pi * p.2)) x) *
        (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖) :=
    (((measurable_kernelFun q x).mul hmeas_fg).norm).aestronglyMeasurable
  have hnormint : IntegrableOn (fun p : ℝ × ℝ =>
      ‖kernelFun q (logZ (-(2 * Real.pi * p.1)) x) (logZ (-(2 * Real.pi * p.2)) x) *
        (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖) (truncCube x)ᶜ volume := by
    refine Integrable.mono' hdomint.integrableOn
      (hmeasint.mono_measure Measure.restrict_le_self) ?_
    filter_upwards [ae_restrict_mem (measurableSet_truncCube x).compl] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hpt p hp
  have hmono1 : (∫ p in (truncCube x)ᶜ,
        ‖kernelFun q (logZ (-(2 * Real.pi * p.1)) x) (logZ (-(2 * Real.pi * p.2)) x) *
          (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖) ≤
      ∫ p in (truncCube x)ᶜ, hdom p :=
    setIntegral_mono_on hnormint hdomint.integrableOn (measurableSet_truncCube x).compl hpt
  have hsubl : (truncCube x)ᶜ ⊆
      {p : ℝ × ℝ | ρ ≤ |p.1|} ∪ {p : ℝ × ℝ | ρ ≤ |p.2|} := by
    rw [hρdef]; exact compl_truncCube_subset x
  have hunion : (∫ p in (truncCube x)ᶜ, hdom p) ≤
      (∫ p in {p : ℝ × ℝ | ρ ≤ |p.1|}, hdom p) +
        ∫ p in {p : ℝ × ℝ | ρ ≤ |p.2|}, hdom p :=
    setIntegral_le_add_of_subset_union hsubl (measurableSet_sIci ρ) (measurableSet_sIci' ρ)
      hdomint hdom0
  have hstrip1 : (∫ p in {p : ℝ × ℝ | ρ ≤ |p.1|}, hdom p) =
      Ck * (Real.log (x : ℝ)) ^ 3 *
        (cutTail F ρ * l1Cut G) := by
    have hset : {p : ℝ × ℝ | ρ ≤ |p.1|} =
        {ξ : ℝ | ρ ≤ |ξ|} ×ˢ (Set.univ : Set ℝ) := by
      ext p; simp [Set.mem_prod]
    rw [hset, hdomdef]
    have hfun : (fun p : ℝ × ℝ => Ck * (Real.log (x : ℝ)) ^ 3 *
        (‖𝓕 (expCutoff F) p.1‖ * ‖𝓕 (expCutoff G) p.2‖)) =
        fun p : ℝ × ℝ => (Ck * (Real.log (x : ℝ)) ^ 3 * ‖𝓕 (expCutoff F) p.1‖) *
          ‖𝓕 (expCutoff G) p.2‖ := by funext p; ring
    rw [hfun]
    rw [integral_prod_strip (fun ξ => Ck * (Real.log (x : ℝ)) ^ 3 * ‖𝓕 (expCutoff F) ξ‖)
      (fun ξ => ‖𝓕 (expCutoff G) ξ‖) ((integrable_norm_fourierCut F hcsF hsmF).const_mul _)
      (integrable_norm_fourierCut G hcsG hsmG) ρ]
    rw [show (∫ ξ in {ξ : ℝ | ρ ≤ |ξ|},
          Ck * (Real.log (x : ℝ)) ^ 3 * ‖𝓕 (expCutoff F) ξ‖) =
        Ck * (Real.log (x : ℝ)) ^ 3 * cutTail F ρ from by
      rw [cutTail]
      exact setIntegral_const_mul' (s := {ξ : ℝ | ρ ≤ |ξ|}) _ _
        (measurableSet_Ici.preimage measurable_abs)]
    rw [l1Cut]
    ring
  have hstrip2 : (∫ p in {p : ℝ × ℝ | ρ ≤ |p.2|}, hdom p) =
      Ck * (Real.log (x : ℝ)) ^ 3 *
        (l1Cut F * cutTail G ρ) := by
    have hset : {p : ℝ × ℝ | ρ ≤ |p.2|} =
        (Set.univ : Set ℝ) ×ˢ {ξ : ℝ | ρ ≤ |ξ|} := by
      ext p; simp [Set.mem_prod]
    rw [hset, hdomdef]
    have hfun : (fun p : ℝ × ℝ => Ck * (Real.log (x : ℝ)) ^ 3 *
        (‖𝓕 (expCutoff F) p.1‖ * ‖𝓕 (expCutoff G) p.2‖)) =
        fun p : ℝ × ℝ => ‖𝓕 (expCutoff F) p.1‖ *
          (Ck * (Real.log (x : ℝ)) ^ 3 * ‖𝓕 (expCutoff G) p.2‖) := by funext p; ring
    rw [hfun]
    rw [integral_prod_strip' (fun ξ => ‖𝓕 (expCutoff F) ξ‖)
      (fun ξ => Ck * (Real.log (x : ℝ)) ^ 3 * ‖𝓕 (expCutoff G) ξ‖)
      (integrable_norm_fourierCut F hcsF hsmF) ((integrable_norm_fourierCut G hcsG hsmG).const_mul _) ρ]
    rw [show (∫ ξ in {ξ : ℝ | ρ ≤ |ξ|},
          Ck * (Real.log (x : ℝ)) ^ 3 * ‖𝓕 (expCutoff G) ξ‖) =
        Ck * (Real.log (x : ℝ)) ^ 3 * cutTail G ρ from by
      rw [cutTail]
      exact setIntegral_const_mul' (s := {ξ : ℝ | ρ ≤ |ξ|}) _ _
        (measurableSet_Ici.preimage measurable_abs)]
    rw [l1Cut]
    ring
  calc (∫ p in (truncCube x)ᶜ, ‖kernelFun q (logZ (-(2 * Real.pi * p.1)) x)
          (logZ (-(2 * Real.pi * p.2)) x) *
          (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖)
      ≤ ∫ p in (truncCube x)ᶜ, hdom p := hmono1
    _ ≤ (∫ p in {p : ℝ × ℝ | ρ ≤ |p.1|}, hdom p) +
        ∫ p in {p : ℝ × ℝ | ρ ≤ |p.2|}, hdom p := hunion
    _ = Ck * (Real.log (x : ℝ)) ^ 3 * (cutTail F ρ * l1Cut G) +
        Ck * (Real.log (x : ℝ)) ^ 3 * (l1Cut F * cutTail G ρ) := by rw [hstrip1, hstrip2]
    _ = Ck * (Real.log (x : ℝ)) ^ 3 *
        (cutTail F ρ * l1Cut G + l1Cut F * cutTail G ρ) := by ring

theorem offCube_pole_le
    (F G : ℝ → ℝ) (hcsF : HasCompactSupport F) (hsmF : ContDiff ℝ (↑(⊤ : ℕ∞)) F)
    (hcsG : HasCompactSupport G) (hsmG : ContDiff ℝ (↑(⊤ : ℕ∞)) G)
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0) :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      (∫ p in (truncCube x)ᶜ,
        ‖poleP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖) ≤
      prefactor W N x *
        (wCutTail F (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) * (∫ ξ : ℝ, wCut G ξ) +
          (∫ ξ : ℝ, wCut F ξ) * wCutTail G (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi))) := by
  refine ⟨2, fun x hx => ?_⟩
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  set ρ : ℝ := Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi) with hρdef
  have hpre0 : 0 ≤ prefactor W N x := by
    have h1' : (0 : ℝ) < (N x).totient := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hN x))
    have h2' : (0 : ℝ) < (W x).totient := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hW x))
    rw [prefactor]
    exact mul_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) h1'.le)
      (div_nonneg (Nat.cast_nonneg _) h2'.le)) (inv_nonneg.mpr hL.le)
  -- the dominating function
  set hdom : ℝ × ℝ → ℝ := fun p => prefactor W N x * (wCut F p.1 * wCut G p.2) with hdomdef
  have hdomint : Integrable hdom := by
    rw [hdomdef]
    have hg2 : Integrable (fun p : ℝ × ℝ => wCut F p.1 * wCut G p.2) := by
      rw [show (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume from rfl]
      exact (integrable_wCut F hcsF hsmF).mul_prod (integrable_wCut G hcsG hsmG)
    exact hg2.const_mul _
  have hdom0 : ∀ p, 0 ≤ hdom p := by
    intro p; rw [hdomdef]
    exact mul_nonneg hpre0 (mul_nonneg (wCut_nonneg F p.1) (wCut_nonneg G p.2))
  -- pointwise bound on the complement
  have hpt : ∀ p ∈ (truncCube x)ᶜ,
      ‖poleP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖ ≤ hdom p := by
    intro p _
    have hgrowth := norm_poleInv_le (W x) (N x) (hW x) (hN x) hL.ne' hL p.1 p.2
    have hpole : poleP W N x p = poleInv (W x) (N x) x p.1 p.2 := rfl
    have hpre_eq : ((N x : ℝ) / ((N x).totient : ℝ)) * ((W x : ℝ) / ((W x).totient : ℝ)) *
        (Real.log (x : ℝ))⁻¹ * (1 + 2 * Real.pi * |p.1|) * (1 + 2 * Real.pi * |p.2|) =
        prefactor W N x * (1 + 2 * Real.pi * |p.1|) * (1 + 2 * Real.pi * |p.2|) := by
      rw [prefactor]
    rw [hpre_eq] at hgrowth
    have hwF : wCut F p.1 = (1 + 2 * Real.pi * |p.1|) * ‖𝓕 (expCutoff F) p.1‖ := by
      simp only [wCut]
    have hwG : wCut G p.2 = (1 + 2 * Real.pi * |p.2|) * ‖𝓕 (expCutoff G) p.2‖ := by
      simp only [wCut]
    have hb : (0 : ℝ) ≤ ‖𝓕 (expCutoff F) p.1‖ := norm_nonneg _
    have hc : (0 : ℝ) ≤ ‖𝓕 (expCutoff G) p.2‖ := norm_nonneg _
    show ‖poleP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖ ≤
      prefactor W N x * (wCut F p.1 * wCut G p.2)
    have htarget : prefactor W N x * (wCut F p.1 * wCut G p.2) =
        (prefactor W N x * (1 + 2 * Real.pi * |p.1|) * (1 + 2 * Real.pi * |p.2|)) *
          (‖𝓕 (expCutoff F) p.1‖ * ‖𝓕 (expCutoff G) p.2‖) := by
      rw [hwF, hwG]; ring
    rw [htarget, hpole, norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right hgrowth (mul_nonneg hb hc)
  -- measurability
  have hmeas_fg : Measurable fun p : ℝ × ℝ => 𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2 := by
    have h1 : Continuous fun p : ℝ × ℝ => 𝓕 (expCutoff F) p.1 := by
      rw [← schwartzCut_coe F hcsF hsmF]
      exact (schwartzCut F hcsF hsmF).continuous.comp continuous_fst
    have h2 : Continuous fun p : ℝ × ℝ => 𝓕 (expCutoff G) p.2 := by
      rw [← schwartzCut_coe G hcsG hsmG]
      exact (schwartzCut G hcsG hsmG).continuous.comp continuous_snd
    exact (h1.mul h2).measurable
  have hmeas_pole : Measurable (poleP W N x) := by
    have h := poleInv_eq (W x) (N x) (hW x) (hN x) hL.ne'
    rw [show poleP W N x = fun p : ℝ × ℝ =>
        (((N x : ℂ) / (((W x).totient : ℂ) / (W x : ℂ) * (Real.log (x : ℝ) : ℂ) *
            ((N x).totient : ℂ))) *
          ((1 - 2 * Real.pi * Complex.I * p.1) * (1 - 2 * Real.pi * Complex.I * p.2) /
            (2 - 2 * Real.pi * Complex.I * (p.1 + p.2)))) from by
      funext p; exact h p.1 p.2]
    fun_prop
  have hmeasint : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ‖poleP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖) :=
    (((hmeas_pole.mul hmeas_fg).norm)).aestronglyMeasurable
  have hnormint : IntegrableOn (fun p : ℝ × ℝ =>
      ‖poleP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖) (truncCube x)ᶜ volume := by
    refine Integrable.mono' hdomint.integrableOn
      (hmeasint.mono_measure Measure.restrict_le_self) ?_
    filter_upwards [ae_restrict_mem (measurableSet_truncCube x).compl] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hpt p hp
  have hmono1 : (∫ p in (truncCube x)ᶜ,
        ‖poleP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖) ≤
      ∫ p in (truncCube x)ᶜ, hdom p :=
    setIntegral_mono_on hnormint hdomint.integrableOn (measurableSet_truncCube x).compl hpt
  have hsubl : (truncCube x)ᶜ ⊆
      {p : ℝ × ℝ | ρ ≤ |p.1|} ∪ {p : ℝ × ℝ | ρ ≤ |p.2|} := by
    rw [hρdef]; exact compl_truncCube_subset x
  have hunion : (∫ p in (truncCube x)ᶜ, hdom p) ≤
      (∫ p in {p : ℝ × ℝ | ρ ≤ |p.1|}, hdom p) +
        ∫ p in {p : ℝ × ℝ | ρ ≤ |p.2|}, hdom p :=
    setIntegral_le_add_of_subset_union hsubl (measurableSet_sIci ρ) (measurableSet_sIci' ρ)
      hdomint hdom0
  have hstrip1 : (∫ p in {p : ℝ × ℝ | ρ ≤ |p.1|}, hdom p) =
      prefactor W N x * (wCutTail F ρ * (∫ ξ : ℝ, wCut G ξ)) := by
    have hset : {p : ℝ × ℝ | ρ ≤ |p.1|} =
        {ξ : ℝ | ρ ≤ |ξ|} ×ˢ (Set.univ : Set ℝ) := by
      ext p; simp [Set.mem_prod]
    rw [hset, hdomdef]
    have hfun : (fun p : ℝ × ℝ => prefactor W N x * (wCut F p.1 * wCut G p.2)) =
        fun p : ℝ × ℝ => (prefactor W N x * wCut F p.1) * wCut G p.2 := by
      funext p; ring
    rw [hfun]
    rw [integral_prod_strip (fun ξ => prefactor W N x * wCut F ξ) (fun ξ => wCut G ξ)
      ((integrable_wCut F hcsF hsmF).const_mul _) (integrable_wCut G hcsG hsmG) ρ]
    rw [show (∫ ξ in {ξ : ℝ | ρ ≤ |ξ|}, prefactor W N x * wCut F ξ) =
        prefactor W N x * wCutTail F ρ from by
      rw [wCutTail]
      exact setIntegral_const_mul' (s := {ξ : ℝ | ρ ≤ |ξ|}) _ _
        (measurableSet_Ici.preimage measurable_abs)]
    ring
  have hstrip2 : (∫ p in {p : ℝ × ℝ | ρ ≤ |p.2|}, hdom p) =
      prefactor W N x * ((∫ ξ : ℝ, wCut F ξ) * wCutTail G ρ) := by
    have hset : {p : ℝ × ℝ | ρ ≤ |p.2|} =
        (Set.univ : Set ℝ) ×ˢ {ξ : ℝ | ρ ≤ |ξ|} := by
      ext p; simp [Set.mem_prod]
    rw [hset, hdomdef]
    have hfun : (fun p : ℝ × ℝ => prefactor W N x * (wCut F p.1 * wCut G p.2)) =
        fun p : ℝ × ℝ => wCut F p.1 * (prefactor W N x * wCut G p.2) := by
      funext p; ring
    rw [hfun]
    rw [integral_prod_strip' (fun ξ => wCut F ξ) (fun ξ => prefactor W N x * wCut G ξ)
      (integrable_wCut F hcsF hsmF) ((integrable_wCut G hcsG hsmG).const_mul _) ρ]
    rw [show (∫ ξ in {ξ : ℝ | ρ ≤ |ξ|}, prefactor W N x * wCut G ξ) =
        prefactor W N x * wCutTail G ρ from by
      rw [wCutTail]
      exact setIntegral_const_mul' (s := {ξ : ℝ | ρ ≤ |ξ|}) _ _
        (measurableSet_Ici.preimage measurable_abs)]
    ring
  calc (∫ p in (truncCube x)ᶜ,
        ‖poleP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖)
      ≤ ∫ p in (truncCube x)ᶜ, hdom p := hmono1
    _ ≤ (∫ p in {p : ℝ × ℝ | ρ ≤ |p.1|}, hdom p) +
        ∫ p in {p : ℝ × ℝ | ρ ≤ |p.2|}, hdom p := hunion
    _ = prefactor W N x * (wCutTail F ρ * (∫ ξ : ℝ, wCut G ξ)) +
        prefactor W N x * ((∫ ξ : ℝ, wCut F ξ) * wCutTail G ρ) := by rw [hstrip1, hstrip2]
    _ = prefactor W N x *
        (wCutTail F ρ * (∫ ξ : ℝ, wCut G ξ) + (∫ ξ : ℝ, wCut F ξ) * wCutTail G ρ) := by ring

lemma norm_kernelP_le (W N : ℕ → ℕ) {x : ℕ} {Ck L : ℝ}
    (h : ∀ ξ ξ' : ℝ, ‖kernelFun ((W x) * (N x)) (logZ ξ x) (logZ ξ' x)‖ ≤ Ck * L)
    (p : ℝ × ℝ) : ‖kernelP W N x p‖ ≤ Ck * L := h _ _

lemma norm_poleP_mul_le (F G : ℝ → ℝ) (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0)
    {x : ℕ} (hlog : 0 < Real.log (x : ℝ)) (p : ℝ × ℝ) :
    ‖poleP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖ ≤
      prefactor W N x * (wCut F p.1 * wCut G p.2) := by
  have hgrowth := norm_poleInv_le (W x) (N x) (hW x) (hN x) hlog.ne' hlog p.1 p.2
  have hpole : poleP W N x p = poleInv (W x) (N x) x p.1 p.2 := rfl
  have hpre_eq : ((N x : ℝ) / ((N x).totient : ℝ)) * ((W x : ℝ) / ((W x).totient : ℝ)) *
      (Real.log (x : ℝ))⁻¹ * (1 + 2 * Real.pi * |p.1|) * (1 + 2 * Real.pi * |p.2|) =
      prefactor W N x * (1 + 2 * Real.pi * |p.1|) * (1 + 2 * Real.pi * |p.2|) := by
    rw [prefactor]
  rw [hpre_eq] at hgrowth
  rw [hpole]
  have hwF : wCut F p.1 = (1 + 2 * Real.pi * |p.1|) * ‖𝓕 (expCutoff F) p.1‖ := by
    simp only [wCut]
  have hwG : wCut G p.2 = (1 + 2 * Real.pi * |p.2|) * ‖𝓕 (expCutoff G) p.2‖ := by
    simp only [wCut]
  have hb : (0 : ℝ) ≤ ‖𝓕 (expCutoff F) p.1‖ := norm_nonneg _
  have hc : (0 : ℝ) ≤ ‖𝓕 (expCutoff G) p.2‖ := norm_nonneg _
  rw [norm_mul, norm_mul]
  have htarget : prefactor W N x * (wCut F p.1 * wCut G p.2) =
      (prefactor W N x * (1 + 2 * Real.pi * |p.1|) * (1 + 2 * Real.pi * |p.2|)) *
        (‖𝓕 (expCutoff F) p.1‖ * ‖𝓕 (expCutoff G) p.2‖) := by
    rw [hwF, hwG]; ring
  rw [htarget]
  exact mul_le_mul_of_nonneg_right hgrowth (mul_nonneg hb hc)

lemma kernelFun_bound_uniform_pointwise :
    ∃ x₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, x₀ ≤ x → ∀ (q : ℕ) (_hq : q ≠ 0) (ξ ξ' : ℝ),
      ‖kernelFun q (logZ ξ x) (logZ ξ' x)‖ ≤ C * (Real.log (x : ℝ)) ^ 3 := by
  obtain ⟨C, hC, hx⟩ := crude_kernelFun_bound_uniform
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hx
  exact ⟨X₀, C, hC, fun x hx' q hq ξ ξ' => hX₀ x hx' q hq ξ ξ'⟩

theorem kernel_sub_pole_integral_le
    (F G : ℝ → ℝ) (hcsF : HasCompactSupport F) (hsmF : ContDiff ℝ (↑(⊤ : ℕ∞)) F)
    (hcsG : HasCompactSupport G) (hsmG : ContDiff ℝ (↑(⊤ : ℕ∞)) G)
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0)
    (hcop : ∀ x, (W x).Coprime (N x))
    (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x * N x)
    (hlq : Tendsto (fun x : ℕ =>
        Real.log (((W x) * (N x) : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ x : ℕ, x₀ ≤ x →
        ‖∫ p : ℝ × ℝ, (kernelP W N x p - poleP W N x p) *
            (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖ ≤
        ε x * prefactor W N x := by
  classical
  obtain ⟨x₀c, εc, hεc, hcube⟩ :=
    cube_integral_kernel_sub_pole_le F G hcsF hsmF hcsG hsmG W N hW hN hcop w hw hsmall hlq
  obtain ⟨x₀k, Ck, hCk, hkern⟩ := offCube_kernel_le F G hcsF hsmF hcsG hsmG
  obtain ⟨x₀p, hpole⟩ := offCube_pole_le F G hcsF hsmF hcsG hsmG W N hW hN
  obtain ⟨x₀K, Ck2, _hCk2, hKbound⟩ := kernelFun_bound_uniform_pointwise
  obtain ⟨CcutF, hCcutF, hcutF⟩ := cutTail_le F hcsF hsmF 10
  obtain ⟨CcutG, hCcutG, hcutG⟩ := cutTail_le G hcsG hsmG 10
  obtain ⟨CwF, hCwF, htwF⟩ := wCutTail_le F hcsF hsmF 10
  obtain ⟨CwG, hCwG, htwG⟩ := wCutTail_le G hcsG hsmG 10
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hL_nat : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim1 : Tendsto (fun x : ℕ => |εc x| * ((∫ ξ : ℝ, wCut F ξ) * (∫ ξ : ℝ, wCut G ξ)))
      atTop (𝓝 0) := by
    simpa using hεc.abs.mul tendsto_const_nhds
  have hlim2 : Tendsto (fun x : ℕ => Ck * (2 * Real.pi) ^ 10 *
      (CcutF * l1Cut G + l1Cut F * CcutG) * (Real.log (x : ℝ))⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp hL_nat).const_mul
      (Ck * (2 * Real.pi) ^ 10 * (CcutF * l1Cut G + l1Cut F * CcutG))
    simpa [mul_assoc] using h
  have hρatTop : Tendsto (fun x : ℕ => Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) atTop atTop := by
    have hsqrt : Tendsto (fun x : ℕ => Real.sqrt (Real.log (x : ℝ))) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp hL_nat
    have h2 := hsqrt.const_mul_atTop (show (0 : ℝ) < 1 / (2 * Real.pi) by positivity)
    have hfun : (fun x : ℕ => (1 / (2 * Real.pi)) * Real.sqrt (Real.log (x : ℝ))) =
        fun x : ℕ => Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi) := by
      funext y; ring
    rwa [hfun] at h2
  have hlim3 : Tendsto (fun x : ℕ =>
      (CwF * (∫ ξ : ℝ, wCut G ξ) + (∫ ξ : ℝ, wCut F ξ) * CwG) *
        ((Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi))⁻¹) ^ 10) atTop (𝓝 0) := by
    have hinv : Tendsto (fun x : ℕ => (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi))⁻¹)
        atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hρatTop
    have h := (hinv.pow 10).const_mul (CwF * (∫ ξ : ℝ, wCut G ξ) + (∫ ξ : ℝ, wCut F ξ) * CwG)
    simpa [mul_assoc] using h
  refine ⟨max (max x₀c (max x₀k (max x₀p x₀K)))
      (max (Nat.ceil (Real.exp ((2 * Real.pi) ^ 2 + 2)) + 1) 2),
    fun x => |εc x| * ((∫ ξ : ℝ, wCut F ξ) * (∫ ξ : ℝ, wCut G ξ)) +
      Ck * (2 * Real.pi) ^ 10 * (CcutF * l1Cut G + l1Cut F * CcutG) * (Real.log (x : ℝ))⁻¹ +
      (CwF * (∫ ξ : ℝ, wCut G ξ) + (∫ ξ : ℝ, wCut F ξ) * CwG) *
        ((Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi))⁻¹) ^ 10, ?_, ?_⟩
  · simpa only [add_assoc, mul_assoc, add_zero, zero_add] using hlim1.add (hlim2.add hlim3)
  · intro x hx
    change ‖∫ p : ℝ × ℝ, (kernelP W N x p - poleP W N x p) *
        (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖ ≤
      (|εc x| * ((∫ ξ : ℝ, wCut F ξ) * (∫ ξ : ℝ, wCut G ξ)) +
        Ck * (2 * Real.pi) ^ 10 * (CcutF * l1Cut G + l1Cut F * CcutG) * (Real.log (x : ℝ))⁻¹ +
        (CwF * (∫ ξ : ℝ, wCut G ξ) + (∫ ξ : ℝ, wCut F ξ) * CwG) *
          ((Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi))⁻¹) ^ 10) * prefactor W N x
    have hstep1 : max (max x₀c (max x₀k (max x₀p x₀K)))
        (max (Nat.ceil (Real.exp ((2 * Real.pi) ^ 2 + 2)) + 1) 2) ≤ x := hx
    have h12 : max x₀c (max x₀k (max x₀p x₀K)) ≤ x := le_trans (le_max_left _ _) hstep1
    have hxc : x₀c ≤ x := le_trans (le_max_left _ _) h12
    have hkpk : max x₀k (max x₀p x₀K) ≤ x := le_trans (le_max_right _ _) h12
    have hxk : x₀k ≤ x := le_trans (le_max_left _ _) hkpk
    have hpk : max x₀p x₀K ≤ x := le_trans (le_max_right _ _) hkpk
    have hxp : x₀p ≤ x := le_trans (le_max_left _ _) hpk
    have hxk2 : x₀K ≤ x := le_trans (le_max_right _ _) hpk
    have hB2 : max (Nat.ceil (Real.exp ((2 * Real.pi) ^ 2 + 2)) + 1) 2 ≤ x :=
      le_trans (le_max_right _ _) hstep1
    have hB : Nat.ceil (Real.exp ((2 * Real.pi) ^ 2 + 2)) + 1 ≤ x :=
      le_trans (le_max_left _ _) hB2
    have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hB2
    have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    have hxexp : Real.exp ((2 * Real.pi) ^ 2 + 2) < (x : ℝ) := by
      have h1 : Real.exp ((2 * Real.pi) ^ 2 + 2) ≤
          (Nat.ceil (Real.exp ((2 * Real.pi) ^ 2 + 2)) : ℕ) := Nat.le_ceil _
      have h2 : ((Nat.ceil (Real.exp ((2 * Real.pi) ^ 2 + 2)) : ℕ) : ℝ) <
          ((Nat.ceil (Real.exp ((2 * Real.pi) ^ 2 + 2)) + 1 : ℕ) : ℝ) := by push_cast; linarith
      have h3 : ((Nat.ceil (Real.exp ((2 * Real.pi) ^ 2 + 2)) + 1 : ℕ) : ℝ) ≤ (x : ℝ) := by
        exact_mod_cast hB
      linarith
    have hxbig : (2 * Real.pi) ^ 2 + 2 ≤ Real.log (x : ℝ) := by
      have h := Real.log_le_log (Real.exp_pos _) hxexp.le
      rwa [Real.log_exp] at h
    have hρ1 : 1 ≤ Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi) := by
      have hsq : (2 * Real.pi) ^ 2 ≤ Real.log (x : ℝ) := by linarith
      have hle : 2 * Real.pi ≤ Real.sqrt (Real.log (x : ℝ)) := by
        rw [← Real.sqrt_sq h2pi.le]; exact Real.sqrt_le_sqrt hsq
      rw [le_div_iff₀ h2pi]; linarith
    -- the prefactor: nonnegativity and the reciprocal-forces-log bound
    have hφN : 0 < (N x).totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hN x))
    have hφW : 0 < (W x).totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hW x))
    have hNratio : 1 ≤ (N x : ℝ) / ((N x).totient : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hφN)]
      simpa using (Nat.cast_le (α := ℝ)).mpr (Nat.totient_le (N x))
    have hWratio : 1 ≤ (W x : ℝ) / ((W x).totient : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hφW)]
      simpa using (Nat.cast_le (α := ℝ)).mpr (Nat.totient_le (W x))
    have hpre0 : 0 ≤ prefactor W N x := by
      rw [prefactor]
      exact mul_nonneg (mul_nonneg (le_trans zero_le_one hNratio) (le_trans zero_le_one hWratio))
        (inv_nonneg.mpr hL.le)
    have hpre_ge : (Real.log (x : ℝ))⁻¹ ≤ prefactor W N x := by
      rw [prefactor]
      calc (Real.log (x : ℝ))⁻¹ = 1 * 1 * (Real.log (x : ℝ))⁻¹ := by ring
        _ ≤ ((N x : ℝ) / ((N x).totient : ℝ)) * ((W x : ℝ) / ((W x).totient : ℝ)) *
              (Real.log (x : ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul hNratio hWratio zero_le_one (le_trans zero_le_one hNratio))
              (inv_nonneg.mpr hL.le)
    have hpre_mul : 1 ≤ prefactor W N x * Real.log (x : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hpre_ge hL.le
      rwa [inv_mul_cancel₀ hL.ne'] at h
    -- integrand and its dominating estimate
    set f : ℝ × ℝ → ℂ := fun p => (kernelP W N x p - poleP W N x p) *
      (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2) with hfdef
    set ρ : ℝ := Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi) with hρdef
    have hρ1' : 1 ≤ ρ := by rw [hρdef]; exact hρ1
    have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ1'
    have htop : 0 ≤ (2 * Real.pi) ^ 10 := by positivity
    have hWCF0 : 0 ≤ ∫ ξ : ℝ, wCut F ξ := integral_nonneg (fun ξ => wCut_nonneg F ξ)
    have hWCG0 : 0 ≤ ∫ ξ : ℝ, wCut G ξ := integral_nonneg (fun ξ => wCut_nonneg G ξ)
    have hL1F0 : 0 ≤ l1Cut F := integral_nonneg (fun ξ => norm_nonneg _)
    have hL1G0 : 0 ≤ l1Cut G := integral_nonneg (fun ξ => norm_nonneg _)
    have hKbd : ∀ p : ℝ × ℝ, ‖kernelP W N x p‖ ≤ Ck2 * (Real.log (x : ℝ)) ^ 3 := fun p =>
      norm_kernelP_le W N (hKbound x hxk2 (W x * N x) (mul_ne_zero (hW x) (hN x))) p
    have hPbd : ∀ p : ℝ × ℝ, ‖poleP W N x p *
        (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖ ≤
        prefactor W N x * (wCut F p.1 * wCut G p.2) := fun p =>
      norm_poleP_mul_le F G W N hW hN hL p
    have hfg_meas : Measurable fun p : ℝ × ℝ =>
        𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2 := by
      have h1 : Continuous fun p : ℝ × ℝ => 𝓕 (expCutoff F) p.1 := by
        rw [← schwartzCut_coe F hcsF hsmF]
        exact (schwartzCut F hcsF hsmF).continuous.comp continuous_fst
      have h2 : Continuous fun p : ℝ × ℝ => 𝓕 (expCutoff G) p.2 := by
        rw [← schwartzCut_coe G hcsG hsmG]
        exact (schwartzCut G hcsG hsmG).continuous.comp continuous_snd
      exact (h1.mul h2).measurable
    have hKmeas : Measurable (kernelP W N x) := measurable_kernelFun ((W x) * (N x)) x
    have hPmeas : Measurable (poleP W N x) := by
      have h := poleInv_eq (W x) (N x) (hW x) (hN x) hL.ne'
      rw [show poleP W N x = fun p : ℝ × ℝ =>
          (((N x : ℂ) / (((W x).totient : ℂ) / (W x : ℂ) * (Real.log (x : ℝ) : ℂ) *
              ((N x).totient : ℂ))) *
            ((1 - 2 * Real.pi * Complex.I * p.1) * (1 - 2 * Real.pi * Complex.I * p.2) /
              (2 - 2 * Real.pi * Complex.I * (p.1 + p.2)))) from by
        funext p; exact h p.1 p.2]
      fun_prop
    have hKprod_int : Integrable (fun p : ℝ × ℝ => kernelP W N x p *
        (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)) := by
      have hbase : Integrable (fun p : ℝ × ℝ =>
          ‖𝓕 (expCutoff F) p.1‖ * ‖𝓕 (expCutoff G) p.2‖) := by
        rw [show (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume from rfl]
        exact (integrable_norm_fourierCut F hcsF hsmF).mul_prod
          (integrable_norm_fourierCut G hcsG hsmG)
      have hd : Integrable (fun p : ℝ × ℝ => Ck2 * (Real.log (x : ℝ)) ^ 3 *
          (‖𝓕 (expCutoff F) p.1‖ * ‖𝓕 (expCutoff G) p.2‖)) := hbase.const_mul _
      refine Integrable.mono' hd ((hKmeas.mul hfg_meas).aestronglyMeasurable) ?_
      filter_upwards with p
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (hKbd p) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have hPprod_int : Integrable (fun p : ℝ × ℝ => poleP W N x p *
        (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)) := by
      have hbase : Integrable (fun p : ℝ × ℝ => wCut F p.1 * wCut G p.2) := by
        rw [show (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume from rfl]
        exact (integrable_wCut F hcsF hsmF).mul_prod (integrable_wCut G hcsG hsmG)
      have hd : Integrable (fun p : ℝ × ℝ => prefactor W N x * (wCut F p.1 * wCut G p.2)) :=
        hbase.const_mul _
      refine Integrable.mono' hd ((hPmeas.mul hfg_meas).aestronglyMeasurable) ?_
      filter_upwards with p
      exact hPbd p
    have hfint : Integrable f := by
      rw [hfdef]
      have heq : (fun p : ℝ × ℝ => (kernelP W N x p - poleP W N x p) *
          (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)) =
          fun p : ℝ × ℝ => kernelP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2) -
            poleP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2) := by
        funext p; ring
      rw [heq]
      exact hKprod_int.sub hPprod_int
    have hsplit : ∫ p : ℝ × ℝ, ‖f p‖ =
        (∫ p in truncCube x, ‖f p‖) + ∫ p in (truncCube x)ᶜ, ‖f p‖ := by
      have h := setIntegral_union (s := truncCube x) (t := (truncCube x)ᶜ) disjoint_compl_right
        (measurableSet_truncCube x).compl hfint.norm.integrableOn hfint.norm.integrableOn
      rw [Set.union_compl_self, setIntegral_univ] at h
      exact h
    have hcube' : (∫ p in truncCube x, ‖f p‖) ≤
        |εc x| * prefactor W N x * (∫ ξ : ℝ, wCut F ξ) * (∫ ξ : ℝ, wCut G ξ) := by
      rw [hfdef]
      simpa [wCut] using hcube x hxc
    have hoff : (∫ p in (truncCube x)ᶜ, ‖f p‖) ≤
        Ck * (Real.log (x : ℝ)) ^ 3 * (cutTail F ρ * l1Cut G + l1Cut F * cutTail G ρ) +
        prefactor W N x * (wCutTail F ρ * (∫ ξ : ℝ, wCut G ξ) +
          (∫ ξ : ℝ, wCut F ξ) * wCutTail G ρ) := by
      have hk := hkern x hxk (W x * N x) (mul_ne_zero (hW x) (hN x))
      have hp := hpole x hxp
      have hpt : ∀ p ∈ (truncCube x)ᶜ, ‖f p‖ ≤
          ‖kernelP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖ +
            ‖poleP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖ := by
        intro p _
        have h1 : f p = kernelP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2) -
            poleP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2) := by
          rw [hfdef]; ring
        rw [h1]
        exact norm_sub_le _ _
      have hABint : IntegrableOn (fun p : ℝ × ℝ =>
          ‖kernelP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖ +
            ‖poleP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖)
          (truncCube x)ᶜ volume := (hKprod_int.norm.add hPprod_int.norm).integrableOn
      have hmono := setIntegral_mono_on hfint.norm.integrableOn hABint
        (measurableSet_truncCube x).compl hpt
      have hsum : (∫ p in (truncCube x)ᶜ,
          (‖kernelP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖ +
            ‖poleP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖)) =
          (∫ p in (truncCube x)ᶜ,
            ‖kernelP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖) +
          (∫ p in (truncCube x)ᶜ,
            ‖poleP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖) :=
        integral_add hKprod_int.norm.integrableOn hPprod_int.norm.integrableOn
      rw [hsum] at hmono
      have hk'' : (∫ p in (truncCube x)ᶜ,
            ‖kernelP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖) ≤
          Ck * (Real.log (x : ℝ)) ^ 3 * (cutTail F ρ * l1Cut G + l1Cut F * cutTail G ρ) := by
        rw [hρdef]
        exact hk
      have hp'' : (∫ p in (truncCube x)ᶜ,
            ‖poleP W N x p * (𝓕 (expCutoff F) p.1 * 𝓕 (expCutoff G) p.2)‖) ≤
          prefactor W N x * (wCutTail F ρ * (∫ ξ : ℝ, wCut G ξ) +
            (∫ ξ : ℝ, wCut F ξ) * wCutTail G ρ) := by
        rw [hρdef]
        exact hp
      linarith [hmono, hk'', hp'']
    have hmain : ‖∫ p : ℝ × ℝ, f p‖ ≤
        |εc x| * prefactor W N x * (∫ ξ : ℝ, wCut F ξ) * (∫ ξ : ℝ, wCut G ξ) +
        (Ck * (Real.log (x : ℝ)) ^ 3 * (cutTail F ρ * l1Cut G + l1Cut F * cutTail G ρ) +
          prefactor W N x * (wCutTail F ρ * (∫ ξ : ℝ, wCut G ξ) +
            (∫ ξ : ℝ, wCut F ξ) * wCutTail G ρ)) := by
      have h1 : ‖∫ p : ℝ × ℝ, f p‖ ≤ ∫ p : ℝ × ℝ, ‖f p‖ :=
        norm_integral_le_integral_norm f
      calc ‖∫ p : ℝ × ℝ, f p‖ ≤ ∫ p : ℝ × ℝ, ‖f p‖ := h1
        _ = (∫ p in truncCube x, ‖f p‖) + ∫ p in (truncCube x)ᶜ, ‖f p‖ := hsplit
        _ ≤ |εc x| * prefactor W N x * (∫ ξ : ℝ, wCut F ξ) * (∫ ξ : ℝ, wCut G ξ) +
            (Ck * (Real.log (x : ℝ)) ^ 3 * (cutTail F ρ * l1Cut G + l1Cut F * cutTail G ρ) +
              prefactor W N x * (wCutTail F ρ * (∫ ξ : ℝ, wCut G ξ) +
                (∫ ξ : ℝ, wCut F ξ) * wCutTail G ρ)) := add_le_add hcube' hoff
    rw [hfdef] at hmain
    refine hmain.trans ?_
    -- abbreviations
    set A1 : ℝ := |εc x| * ((∫ ξ : ℝ, wCut F ξ) * (∫ ξ : ℝ, wCut G ξ)) with hA1def
    set A2 : ℝ := Ck * (2 * Real.pi) ^ 10 * (CcutF * l1Cut G + l1Cut F * CcutG) *
      (Real.log (x : ℝ))⁻¹ with hA2def
    set A3 : ℝ := (CwF * (∫ ξ : ℝ, wCut G ξ) + (∫ ξ : ℝ, wCut F ξ) * CwG) *
      (ρ⁻¹) ^ 10 with hA3def
    have hratio : (Real.log (x : ℝ)) ^ 4 * (ρ ^ 10)⁻¹ =
        (2 * Real.pi) ^ 10 * (Real.log (x : ℝ))⁻¹ := by
      have hρpow : ρ ^ 10 = (Real.log (x : ℝ)) ^ 5 / (2 * Real.pi) ^ 10 := by
        rw [hρdef, div_pow]
        have hsq : (Real.sqrt (Real.log (x : ℝ))) ^ 10 = (Real.log (x : ℝ)) ^ 5 := by
          rw [show (10 : ℕ) = 2 * 5 from rfl, pow_mul, Real.sq_sqrt hL.le]
        rw [hsq]
      rw [hρpow, inv_div]
      field_simp
    have hcf : cutTail F ρ ≤ CcutF / ρ ^ 10 := hcutF ρ hρ1'
    have hcg : cutTail G ρ ≤ CcutG / ρ ^ 10 := hcutG ρ hρ1'
    have hCcut0 : 0 ≤ CcutF * l1Cut G + l1Cut F * CcutG :=
      add_nonneg (mul_nonneg hCcutF.le hL1G0) (mul_nonneg hL1F0 hCcutG.le)
    have hTL : Ck * (Real.log (x : ℝ)) ^ 3 * (cutTail F ρ * l1Cut G + l1Cut F * cutTail G ρ) *
        Real.log (x : ℝ) ≤
        Ck * (2 * Real.pi) ^ 10 * (CcutF * l1Cut G + l1Cut F * CcutG) *
          (Real.log (x : ℝ))⁻¹ := by
      have hinner : cutTail F ρ * l1Cut G + l1Cut F * cutTail G ρ ≤
          CcutF / ρ ^ 10 * l1Cut G + l1Cut F * (CcutG / ρ ^ 10) :=
        add_le_add (mul_le_mul_of_nonneg_right hcf hL1G0) (mul_le_mul_of_nonneg_left hcg hL1F0)
      have hL4 : (0 : ℝ) ≤ Ck * (Real.log (x : ℝ)) ^ 4 := by positivity
      calc Ck * (Real.log (x : ℝ)) ^ 3 * (cutTail F ρ * l1Cut G + l1Cut F * cutTail G ρ) *
            Real.log (x : ℝ)
          = Ck * (Real.log (x : ℝ)) ^ 4 * (cutTail F ρ * l1Cut G + l1Cut F * cutTail G ρ) := by ring
        _ ≤ Ck * (Real.log (x : ℝ)) ^ 4 *
              (CcutF / ρ ^ 10 * l1Cut G + l1Cut F * (CcutG / ρ ^ 10)) :=
            mul_le_mul_of_nonneg_left hinner hL4
        _ = Ck * ((Real.log (x : ℝ)) ^ 4 * (ρ ^ 10)⁻¹) *
              (CcutF * l1Cut G + l1Cut F * CcutG) := by ring
        _ = Ck * (2 * Real.pi) ^ 10 * (CcutF * l1Cut G + l1Cut F * CcutG) *
              (Real.log (x : ℝ))⁻¹ := by
            rw [hratio]
            ring
    have hT2 : Ck * (Real.log (x : ℝ)) ^ 3 * (cutTail F ρ * l1Cut G + l1Cut F * cutTail G ρ) ≤
        A2 * prefactor W N x := by
      rw [hA2def]
      have hcutF0 : 0 ≤ cutTail F ρ := integral_nonneg (fun ξ => norm_nonneg _)
      have hcutG0 : 0 ≤ cutTail G ρ := integral_nonneg (fun ξ => norm_nonneg _)
      have h0 : (0 : ℝ) ≤ Ck * (Real.log (x : ℝ)) ^ 3 *
          (cutTail F ρ * l1Cut G + l1Cut F * cutTail G ρ) :=
        mul_nonneg (mul_nonneg hCk.le (pow_nonneg hL.le 3))
          (add_nonneg (mul_nonneg hcutF0 hL1G0) (mul_nonneg hL1F0 hcutG0))
      calc Ck * (Real.log (x : ℝ)) ^ 3 * (cutTail F ρ * l1Cut G + l1Cut F * cutTail G ρ)
          = Ck * (Real.log (x : ℝ)) ^ 3 * (cutTail F ρ * l1Cut G + l1Cut F * cutTail G ρ) * 1 := by
            ring
        _ ≤ Ck * (Real.log (x : ℝ)) ^ 3 * (cutTail F ρ * l1Cut G + l1Cut F * cutTail G ρ) *
              (prefactor W N x * Real.log (x : ℝ)) := mul_le_mul_of_nonneg_left hpre_mul h0
        _ = Ck * (Real.log (x : ℝ)) ^ 3 * (cutTail F ρ * l1Cut G + l1Cut F * cutTail G ρ) *
              Real.log (x : ℝ) * prefactor W N x := by ring
        _ ≤ Ck * (2 * Real.pi) ^ 10 * (CcutF * l1Cut G + l1Cut F * CcutG) *
              (Real.log (x : ℝ))⁻¹ * prefactor W N x :=
            mul_le_mul_of_nonneg_right hTL hpre0
    have htwF' : wCutTail F ρ ≤ CwF / ρ ^ 10 := htwF ρ hρ1'
    have htwG' : wCutTail G ρ ≤ CwG / ρ ^ 10 := htwG ρ hρ1'
    have hT3 : prefactor W N x * (wCutTail F ρ * (∫ ξ : ℝ, wCut G ξ) +
        (∫ ξ : ℝ, wCut F ξ) * wCutTail G ρ) ≤ A3 * prefactor W N x := by
      rw [hA3def]
      have hinner : wCutTail F ρ * (∫ ξ : ℝ, wCut G ξ) + (∫ ξ : ℝ, wCut F ξ) * wCutTail G ρ ≤
          (CwF * (∫ ξ : ℝ, wCut G ξ) + (∫ ξ : ℝ, wCut F ξ) * CwG) * (ρ⁻¹) ^ 10 := by
        have h1 : wCutTail F ρ * (∫ ξ : ℝ, wCut G ξ) ≤ (CwF / ρ ^ 10) * (∫ ξ : ℝ, wCut G ξ) :=
          mul_le_mul_of_nonneg_right htwF' hWCG0
        have h2 : (∫ ξ : ℝ, wCut F ξ) * wCutTail G ρ ≤ (∫ ξ : ℝ, wCut F ξ) * (CwG / ρ ^ 10) :=
          mul_le_mul_of_nonneg_left htwG' hWCF0
        have h3 : (CwF / ρ ^ 10) * (∫ ξ : ℝ, wCut G ξ) + (∫ ξ : ℝ, wCut F ξ) * (CwG / ρ ^ 10) =
            (CwF * (∫ ξ : ℝ, wCut G ξ) + (∫ ξ : ℝ, wCut F ξ) * CwG) * (ρ⁻¹) ^ 10 := by
          rw [div_eq_mul_inv, div_eq_mul_inv, inv_pow]
          ring
        linarith [h1, h2, h3.le, h3.ge]
      calc prefactor W N x * (wCutTail F ρ * (∫ ξ : ℝ, wCut G ξ) +
            (∫ ξ : ℝ, wCut F ξ) * wCutTail G ρ)
          ≤ prefactor W N x * ((CwF * (∫ ξ : ℝ, wCut G ξ) +
              (∫ ξ : ℝ, wCut F ξ) * CwG) * (ρ⁻¹) ^ 10) :=
            mul_le_mul_of_nonneg_left hinner hpre0
        _ = (CwF * (∫ ξ : ℝ, wCut G ξ) + (∫ ξ : ℝ, wCut F ξ) * CwG) *
              (ρ⁻¹) ^ 10 * prefactor W N x := by ring
    have hT1 : |εc x| * prefactor W N x * (∫ ξ : ℝ, wCut F ξ) * (∫ ξ : ℝ, wCut G ξ) ≤
        A1 * prefactor W N x := by
      rw [hA1def]
      exact le_of_eq (by ring)
    have hexp : (A1 + A2 + A3) * prefactor W N x =
        A1 * prefactor W N x + A2 * prefactor W N x + A3 * prefactor W N x := by ring
    linarith [hT1, hT2, hT3, hexp]

end Commons.NumberTheory.MaynardSieve
