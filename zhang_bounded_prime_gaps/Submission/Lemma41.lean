import Mathlib
import Submission.DivisorKernel
import Submission.MainTerm

open scoped BigOperators Topology FourierTransform SchwartzMap
open Filter MeasureTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# Polymath8a Lemma 4.1 for one coordinate pair (the `k = 1` case)

Combining the three verified ingredients

* `Submission.DivisorKernel.divisorSum_eq_kernelIntegral` — the divisor sum equals
  the kernel integral (the Fubini step),
* `Submission.Truncation.kernel_sub_pole_integral_le` — the kernel is the inverse
  pole factor up to `o(prefactor)`,
* `Submission.MainTerm.poleFactor_mainTerm` — the pole-factor integral evaluates
  to `prefactor·∫₀^∞ F′G′`,

we obtain the `k = 1` instance of P8 (36):

    Σ_{d,d′} μ(d)μ(d′)/[d,d′]·F(log_x d)·G(log_x d′)  (([d,d′], WN) = 1)
      = (1 + o(1))·(N/φ(N))·(W/φ(W))·(1/log x)·∫₀^∞ F′(t)G′(t) dt .

All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The function-level Fourier transform of `expCutoff F` is the coefficient
function of the Schwartz-level Fourier transform of `expCutoffSchwartz F`. -/
lemma fourierCut_eq_fourierTransformCLM {F : ℝ → ℝ} (hcs : HasCompactSupport F)
    (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) (ξ : ℝ) :
    fourierCut F ξ =
      (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) (expCutoffSchwartz F hcs hsm)) ξ := by
  rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe]
  rfl

/-- The `prefactor` is the pole-factor constant of `poleFactor_mainTerm`. -/
lemma prefactor_eq_poleConstant (W N : ℕ → ℕ) {x : ℕ} (hW : W x ≠ 0) (hN : N x ≠ 0)
    (hlog : Real.log (x : ℝ) ≠ 0) :
    ((N x : ℂ) / ((((W x).totient : ℂ) / (W x : ℂ)) * (Real.log (x : ℝ) : ℂ) *
        ((N x).totient : ℂ))) = ((prefactor W N x : ℝ) : ℂ) := by
  have hWc : ((W x : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hW
  have hNc : ((N x : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN
  have hφW : ((W x).totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hW)).ne'
  have hφN : ((N x).totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN)).ne'
  have hlogC : (Real.log (x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog
  rw [prefactor]
  push_cast
  field_simp

/-- The derivative of `expCutoff F` at a differentiability point. -/
lemma deriv_expCutoff {F : ℝ → ℝ} (hcs : HasCompactSupport F) (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F)
    (t : ℝ) :
    deriv (⇑(expCutoffSchwartz F hcs hsm)) t =
      ((Real.exp t * (F t + deriv F t) : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ F t := (hsm.differentiable (by simp) t)
  have h1 : HasDerivAt (fun u : ℝ => Real.exp u * F u)
      (Real.exp t * F t + Real.exp t * deriv F t) t :=
    (Real.hasDerivAt_exp t).mul hd.hasDerivAt
  have h2 : HasDerivAt (fun u : ℝ => ((Real.exp u * F u : ℝ) : ℂ))
      (((Real.exp t * F t + Real.exp t * deriv F t : ℝ)) : ℂ) t := h1.ofReal_comp
  have h3 : deriv (fun u : ℝ => ((Real.exp u * F u : ℝ) : ℂ)) t =
      ((Real.exp t * F t + Real.exp t * deriv F t : ℝ) : ℂ) := h2.deriv
  have hfun : ⇑(expCutoffSchwartz F hcs hsm) = fun u : ℝ => ((Real.exp u * F u : ℝ) : ℂ) := rfl
  rw [hfun, h3]
  congr 1
  ring

/-- `e^{−t}(A′ − A) = F′` for `A = eᵗF`. -/
lemma exp_neg_mul_deriv_sub {F : ℝ → ℝ} (hcs : HasCompactSupport F)
    (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) (t : ℝ) :
    Complex.exp (-t) * (deriv (⇑(expCutoffSchwartz F hcs hsm)) t -
        ⇑(expCutoffSchwartz F hcs hsm) t) = ((deriv F t : ℝ) : ℂ) := by
  have hA : ⇑(expCutoffSchwartz F hcs hsm) t = ((Real.exp t * F t : ℝ) : ℂ) := rfl
  have key : Real.exp (-t) * (Real.exp t * (F t + deriv F t) - Real.exp t * F t) = deriv F t := by
    have h1 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp (-t) * (Real.exp t * (F t + deriv F t) - Real.exp t * F t)
        = (Real.exp (-t) * Real.exp t) * deriv F t := by ring
      _ = deriv F t := by rw [h1, one_mul]
  rw [deriv_expCutoff hcs hsm t, hA]
  have hstep0 : Complex.exp (-(t : ℂ)) = ((Real.exp (-t) : ℝ) : ℂ) := by
    rw [show (-(t : ℂ)) = ((-t : ℝ) : ℂ) from by push_cast; ring, ← Complex.ofReal_exp]
  rw [hstep0]
  have hstep : ((Real.exp (-t) : ℝ) : ℂ) * (((Real.exp t * (F t + deriv F t) : ℝ) : ℂ) -
      ((Real.exp t * F t : ℝ) : ℂ)) =
      ((Real.exp (-t) * (Real.exp t * (F t + deriv F t) - Real.exp t * F t) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sub, ← Complex.ofReal_mul]
  rw [hstep, key]


/-- **P8 Lemma 4.1, `k = 1` case.**  For a family of moduli `W, N` with
`(W x, N x) = 1`, `w x → ∞` with all primes `≤ w x` dividing `W x·N x`, and
`log(W x·N x)/√(log x) → 0`, the divisor sum

    Σ_{d,d′} μ(d)μ(d′)/[d,d′]·F(log_x d)·G(log_x d′)   (([d,d′], W(x)N(x)) = 1)

agrees with `(N/φ(N))·(W/φ(W))·(1/log x)·∫₀^∞ F′(t)G′(t) dt` up to a relative
error `o(1)`, for smooth compactly supported `F, G`. -/
theorem lemma41
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
        ‖(∑' d : ℕ × ℕ, mobiusLcmWeight (W x * N x) d.1 d.2 *
              (F (logR d.1 x) : ℂ) * (G (logR d.2 x) : ℂ)) -
            (prefactor W N x : ℂ) *
              (∫ t : ℝ in Set.Ioi 0, ((deriv F t : ℝ) : ℂ) * ((deriv G t : ℝ) : ℂ))‖ ≤
          ε x * prefactor W N x := by
  classical
  obtain ⟨x₀t, εt, hεt, ht⟩ :=
    kernel_sub_pole_integral_le F G hcsF hsmF hcsG hsmG W N hW hN hcop w hw hsmall hlq
  obtain ⟨x₀K, Ck, hCk, hKbound⟩ := kernelFun_bound_uniform_pointwise
  refine ⟨max x₀t (max x₀K 2), εt, hεt, fun x hx => ?_⟩
  have hxt : x₀t ≤ x := le_trans (le_max_left _ _) hx
  have hxK : x₀K ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx1 : 1 < x := by omega
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx1)
  have hq : W x * N x ≠ 0 := mul_ne_zero (hW x) (hN x)
  have hKbd : ∀ p : ℝ × ℝ, ‖kernelP W N x p‖ ≤ Ck * (Real.log (x : ℝ)) ^ 3 := fun p =>
    norm_kernelP_le W N (hKbound x hxK (W x * N x) hq) p
  -- integrability of the two pieces
  have hFi : Integrable (fun ξ : ℝ => ‖fourierCut F ξ‖) := by
    simpa only [fourierCut] using integrable_norm_fourierCut F hcsF hsmF
  have hGi : Integrable (fun ξ : ℝ => ‖fourierCut G ξ‖) := by
    simpa only [fourierCut] using integrable_norm_fourierCut G hcsG hsmG
  have hbaseF : Integrable (fun p : ℝ × ℝ => ‖fourierCut F p.1‖ * ‖fourierCut G p.2‖) := by
    rw [show (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume from rfl]
    exact hFi.mul_prod hGi
  have hfg_meas : Measurable fun p : ℝ × ℝ =>
      fourierCut F p.1 * fourierCut G p.2 := by
    have h1 : Continuous fun p : ℝ × ℝ => fourierCut F p.1 := by
      have h := (schwartzCut F hcsF hsmF).continuous
      rw [schwartzCut_coe F hcsF hsmF] at h
      exact h.comp continuous_fst
    have h2 : Continuous fun p : ℝ × ℝ => fourierCut G p.2 := by
      have h := (schwartzCut G hcsG hsmG).continuous
      rw [schwartzCut_coe G hcsG hsmG] at h
      exact h.comp continuous_snd
    exact (h1.mul h2).measurable
  have hIntK : Integrable (fun p : ℝ × ℝ =>
      kernelP W N x p * (fourierCut F p.1 * fourierCut G p.2)) := by
    refine Integrable.mono' (hbaseF.const_mul (Ck * (Real.log (x : ℝ)) ^ 3)) ?_ ?_
    · exact ((measurable_kernelFun ((W x) * (N x)) x).mul hfg_meas).aestronglyMeasurable
    · filter_upwards with p
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (hKbd p) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hIntP : Integrable (fun p : ℝ × ℝ =>
      poleP W N x p * (fourierCut F p.1 * fourierCut G p.2)) := by
    have hbase : Integrable (fun p : ℝ × ℝ => wCut F p.1 * wCut G p.2) := by
      rw [show (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume from rfl]
      exact (integrable_wCut F hcsF hsmF).mul_prod (integrable_wCut G hcsG hsmG)
    have hPmeas : Measurable (poleP W N x) := by
      have h := poleInv_eq (W x) (N x) (hW x) (hN x) hL.ne'
      rw [show poleP W N x = fun p : ℝ × ℝ =>
          (((N x : ℂ) / (((W x).totient : ℂ) / (W x : ℂ) * (Real.log (x : ℝ) : ℂ) *
              ((N x).totient : ℂ))) *
            ((1 - 2 * Real.pi * Complex.I * p.1) * (1 - 2 * Real.pi * Complex.I * p.2) /
              (2 - 2 * Real.pi * Complex.I * (p.1 + p.2)))) from by
        funext p; exact h p.1 p.2]
      fun_prop
    refine Integrable.mono' (hbase.const_mul (prefactor W N x)) ?_ ?_
    · exact ((hPmeas.mul hfg_meas)).aestronglyMeasurable
    · filter_upwards with p
      exact norm_poleP_mul_le F G W N hW hN hL p
  -- the pole integral
  have hpole : (∫ p : ℝ × ℝ, poleP W N x p * (fourierCut F p.1 * fourierCut G p.2)) =
      (prefactor W N x : ℂ) *
        ∫ t : ℝ in Set.Ioi 0, ((deriv F t : ℝ) : ℂ) * ((deriv G t : ℝ) : ℂ) := by
    have h1 : (∫ p : ℝ × ℝ, poleP W N x p * (fourierCut F p.1 * fourierCut G p.2)) =
        ∫ ξ : ℝ, ∫ ξ' : ℝ, poleP W N x (ξ, ξ') * (fourierCut F ξ * fourierCut G ξ') := by
      rw [show (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume from rfl]
      exact integral_prod _ hIntP
    rw [h1]
    have h2 : (∫ ξ : ℝ, ∫ ξ' : ℝ, poleP W N x (ξ, ξ') * (fourierCut F ξ * fourierCut G ξ')) =
        ∫ ξ : ℝ, ∫ ξ' : ℝ,
          (poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹ *
            (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) (expCutoffSchwartz F hcsF hsmF)) ξ *
            (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) (expCutoffSchwartz G hcsG hsmG)) ξ' := by
      have key : ∀ ξ ξ' : ℝ, poleP W N x (ξ, ξ') * (fourierCut F ξ * fourierCut G ξ') =
          (poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹ *
            (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) (expCutoffSchwartz F hcsF hsmF)) ξ *
            (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) (expCutoffSchwartz G hcsG hsmG)) ξ' := by
        intro ξ ξ'
        rw [fourierCut_eq_fourierTransformCLM hcsF hsmF ξ,
          fourierCut_eq_fourierTransformCLM hcsG hsmG ξ',
          show poleP W N x (ξ, ξ') =
            (poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹ from rfl]
        ring
      exact integral_congr_ae (Filter.Eventually.of_forall (fun ξ =>
        integral_congr_ae (Filter.Eventually.of_forall (key ξ))))
    rw [h2]
    rw [poleFactor_mainTerm (W x) (N x) (hW x) (hN x) x hL.ne'
      (expCutoffSchwartz F hcsF hsmF) (expCutoffSchwartz G hcsG hsmG)]
    rw [prefactor_eq_poleConstant W N (hW x) (hN x) hL.ne']
    congr 1
    have key2 : ∀ t : ℝ, Complex.exp (-t) * (deriv (⇑(expCutoffSchwartz F hcsF hsmF)) t -
        ⇑(expCutoffSchwartz F hcsF hsmF) t) * (Complex.exp (-t) *
        (deriv (⇑(expCutoffSchwartz G hcsG hsmG)) t - ⇑(expCutoffSchwartz G hcsG hsmG) t)) =
        ((deriv F t : ℝ) : ℂ) * ((deriv G t : ℝ) : ℂ) := by
      intro t
      rw [exp_neg_mul_deriv_sub hcsF hsmF t, exp_neg_mul_deriv_sub hcsG hsmG t]
    exact integral_congr_ae (Filter.Eventually.of_forall key2)
  -- the Fubini step
  have hdiff := divisorSum_eq_kernelIntegral F G hcsF hsmF hcsG hsmG (W x * N x) x hq hx1
  -- assemble
  have hsplit : (∫ p : ℝ × ℝ, kernelP W N x p * (fourierCut F p.1 * fourierCut G p.2)) -
        (∫ p : ℝ × ℝ, poleP W N x p * (fourierCut F p.1 * fourierCut G p.2)) =
      ∫ p : ℝ × ℝ,
        (kernelP W N x p - poleP W N x p) * (fourierCut F p.1 * fourierCut G p.2) := by
    rw [← integral_sub hIntK hIntP]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    ring
  rw [hdiff]
  calc ‖(∫ p : ℝ × ℝ, kernelP W N x p * (fourierCut F p.1 * fourierCut G p.2)) -
        (prefactor W N x : ℂ) *
          ∫ t : ℝ in Set.Ioi 0, ((deriv F t : ℝ) : ℂ) * ((deriv G t : ℝ) : ℂ)‖
      = ‖(∫ p : ℝ × ℝ, kernelP W N x p * (fourierCut F p.1 * fourierCut G p.2)) -
          (∫ p : ℝ × ℝ, poleP W N x p * (fourierCut F p.1 * fourierCut G p.2))‖ := by
        rw [hpole]
    _ = ‖∫ p : ℝ × ℝ,
          (kernelP W N x p - poleP W N x p) * (fourierCut F p.1 * fourierCut G p.2)‖ := by
        rw [hsplit]
    _ ≤ εt x * prefactor W N x := ht x hxt

end Commons.NumberTheory.MaynardSieve
