import Mathlib
import Submission.Commons.Analysis.Fourier.cos_inv_one_add_sq_Ioi
import Submission.Commons.Analysis.Fourier.dirichlet_integral

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Truncated Perron-kernel deviation (commons)

`Commons.Analysis.Fourier.perron_kernel_bound`: for `T ≥ 1` and `α ≠ 0`,

`‖∫_{-T}^{T} e^{iαt}/(1+it) dt − (if 0 < α then 2πe^{−α} else 0)‖ ≤ C·min(1, 1/(T|α|))`.

The Perron integrand splits into an even real part and an odd imaginary part, so
`kern(T,α) = 2·∫_0^T (cos(αt) + t·sin(αt))/(1+t²) dt`.  On the small-`|α|T`
region (`T|α| ≤ 1`) the kernel is bounded by an absolute constant
(`kern_region_bound`); for `|α|T > 1` an integration-by-parts oscillation bound
(`osc_tail_bound`) shows `‖kern(R,α) − kern(T,α)‖ ≤ 6/(|α|T)` uniformly in `R ≥ T`.
`kern(R,α)` converges as `R → ∞` to the closed form `2π·e^{−α}` for `α > 0` and `0`
for `α ≤ 0` (`kern_tendsto_value`), via the half-line cosine integral
`cos_inv_one_add_sq_Ioi` and the Dirichlet integral `dirichlet_integral` (already in
`Submission.Commons.Analysis.Fourier`), which give the limiting values
`A∞ = (π/2)·e^{−|α|}`, `B∞ = (π/2)·sign(α)·e^{−|α|}`.  The two bounds (split on
`T|α| ≤ 1`) combine into the final statement.
-/


/-!
# Uniform bound on the truncated Perron kernel on the small-`T|α|` region (child task)

Prove `PerronKernel.kern_region_bound` below:

    ‖∫_{-T}^{T} e^{iαt}/(1+it) dt‖ ≤ π + 2        whenever  1 ≤ T  and  T·|α| ≤ 1

(all integrals are Mathlib interval integrals over the real variable `t`;
`α ≠ 0` is *not* needed).
-/

noncomputable section

open Real Set Complex Filter intervalIntegral MeasureTheory
open scoped Topology Real

namespace Commons.Analysis.Fourier

namespace PerronKernel

/-! ## Complex identities for the Perron integrand -/

/-- `(1 + i·t)⁻¹ = (1 - i·t)/(1 + t²)`. -/
lemma one_add_I_mul_inv (t : ℝ) :
    (1 + I * (t : ℂ))⁻¹ = (1 - I * (t : ℂ)) * (((1 + t ^ 2 : ℝ) : ℂ)⁻¹) := by
  have hprod : (1 + I * (t : ℂ)) * ((1 : ℂ) - I * (t : ℂ)) = (((1 + t ^ 2 : ℝ) : ℂ)) := by
    have hi : (I : ℂ) ^ 2 = -1 := by simp
    calc
      (1 + I * (t : ℂ)) * (1 - I * (t : ℂ)) = (1 : ℂ) - (I * (t : ℂ)) ^ 2 := by ring
      _ = (1 : ℂ) - (I : ℂ) ^ 2 * (t : ℂ) ^ 2 := by ring
      _ = ((1 + t ^ 2 : ℝ) : ℂ) := by
        rw [hi]
        simp
  have hnnz : (((1 + t ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (show (1 + t ^ 2 : ℝ) ≠ 0 by nlinarith)
  have hnnz2 : (1 + I * (t : ℂ)) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hprod
    exact hnnz hprod.symm
  have hnnz3 : (1 - I * (t : ℂ)) ≠ 0 := by
    intro hz
    apply hnnz2
    have hc : (starRingEnd ℂ) (1 - I * (t : ℂ)) = 1 + I * (t : ℂ) := by simp
    rw [← hc]
    rw [hz]
    simp
  field_simp [hprod, hnnz2, hnnz3]
  exact hprod.symm

/-- `e^{iαt} (1 - it) = (cos(αt) + t·sin(αt)) + i·(sin(αt) - t·cos(αt))`. -/
lemma exp_times_conj (α t : ℝ) :
    cexp (I * (α * t : ℂ)) * (1 - I * (t : ℂ))
      = ((Real.cos (α * t) + t * Real.sin (α * t) : ℝ) : ℂ)
          + I * ((Real.sin (α * t) - t * Real.cos (α * t) : ℝ) : ℂ) := by
  rw [mul_comm I (α * t : ℂ), Complex.exp_mul_I]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_cos (α * t), ← Complex.ofReal_sin (α * t)]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im]
    ring_nf
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im]
    ring_nf

lemma ofReal_mul_inv_eq (x y : ℝ) :
    ((x : ℂ) * ((y : ℂ)⁻¹)) = ((x / y : ℝ) : ℂ) := by
  by_cases hy : y = 0
  · simp [hy]
  · rw [← Complex.ofReal_inv]
    rw [← Complex.ofReal_mul]
    congr 1

/-- Real and imaginary parts of the Perron integrand. -/
lemma integrand_decomp (α t : ℝ) :
    cexp (I * (α * t : ℂ)) / (1 + I * (t : ℂ))
      = (((Real.cos (α * t) + t * Real.sin (α * t)) / (1 + t ^ 2) : ℝ) : ℂ)
          + I * (((Real.sin (α * t) - t * Real.cos (α * t)) / (1 + t ^ 2) : ℝ) : ℂ) := by
  rw [div_eq_mul_inv]
  rw [one_add_I_mul_inv]
  rw [← mul_assoc]
  rw [exp_times_conj α t]
  rw [add_mul]
  congr 1
  · rw [ofReal_mul_inv_eq]
  · rw [mul_assoc]
    rw [ofReal_mul_inv_eq]

/-! ## Definitions and continuity facts -/

noncomputable def pfun (α t : ℝ) : ℝ := (Real.cos (α * t) + t * Real.sin (α * t)) / (1 + t ^ 2)
noncomputable def qfun (α t : ℝ) : ℝ := (Real.sin (α * t) - t * Real.cos (α * t)) / (1 + t ^ 2)

noncomputable def kern (T α : ℝ) : ℂ :=
  ∫ t in -T..T, cexp (I * (α * t)) / (1 + I * t)

noncomputable def kernA (T α : ℝ) : ℝ := ∫ t in (0 : ℝ)..T, Real.cos (α * t) / (1 + t ^ 2)
noncomputable def kernB (T α : ℝ) : ℝ := ∫ t in (0 : ℝ)..T, t * Real.sin (α * t) / (1 + t ^ 2)

lemma continuous_pfun (α : ℝ) : Continuous (pfun α) := by
  unfold pfun
  have hnum : Continuous fun t : ℝ => Real.cos (α * t) + t * Real.sin (α * t) := by fun_prop
  have hden : Continuous fun t : ℝ => (1 : ℝ) + t ^ 2 := by fun_prop
  have hdenz : ∀ t : ℝ, (1 : ℝ) + t ^ 2 ≠ 0 := by intro t; nlinarith [sq_nonneg t]
  exact Continuous.div₀ hnum hden hdenz

lemma continuous_qfun (α : ℝ) : Continuous (qfun α) := by
  unfold qfun
  have hnum : Continuous fun t : ℝ => Real.sin (α * t) - t * Real.cos (α * t) := by fun_prop
  have hden : Continuous fun t : ℝ => (1 : ℝ) + t ^ 2 := by fun_prop
  have hdenz : ∀ t : ℝ, (1 : ℝ) + t ^ 2 ≠ 0 := by intro t; nlinarith [sq_nonneg t]
  exact Continuous.div₀ hnum hden hdenz

lemma pfun_even (α : ℝ) : ∀ t : ℝ, pfun α (-t) = pfun α t := by
  intro t; unfold pfun
  have h1 : α * (-t) = -(α * t) := by ring
  have hd : (1 + (-t) ^ 2 : ℝ) = 1 + t ^ 2 := by ring
  rw [h1, Real.cos_neg, Real.sin_neg, hd]; ring

lemma qfun_odd (α : ℝ) : ∀ t : ℝ, qfun α (-t) = -qfun α t := by
  intro t; unfold qfun
  have h1 : α * (-t) = -(α * t) := by ring
  have hd : (1 + (-t) ^ 2 : ℝ) = 1 + t ^ 2 := by ring
  rw [h1, Real.cos_neg, Real.sin_neg, hd]; ring

/-- The integral of an odd continuous function over `[-T,T]` vanishes. -/
lemma integral_real_odd_zero (f : ℝ → ℝ) (_hf : Continuous f) (ho : ∀ x, f (-x) = - f x) (T : ℝ) :
    (∫ x in -T..T, f x) = 0 := by
  have h1 : (∫ x in -T..T, f x) = (∫ x in -T..T, f (-x)) := by
    rw [intervalIntegral.integral_comp_neg]
    congr 1
    ring
  have h2 : (∫ x in -T..T, f x) = - (∫ x in -T..T, f x) := by
    calc
      (∫ x in -T..T, f x) = (∫ x in -T..T, f (-x)) := h1
      _ = (∫ x in -T..T, - f x) := by
        refine intervalIntegral.integral_congr (μ := volume) ?_
        intro x hx; exact ho x
      _ = - (∫ x in -T..T, f x) := intervalIntegral.integral_neg (f := f)
  linarith

/-- The integral of an even continuous function over `[-T,T]` is twice the half integral. -/
lemma integral_real_even_two (f : ℝ → ℝ) (hf : Continuous f) (he : ∀ x, f (-x) = f x) (T : ℝ) :
    (∫ x in -T..T, f x) = 2 * (∫ x in 0..T, f x) := by
  have hadj : (∫ x in -T..0, f x) + ∫ x in 0..T, f x = ∫ x in -T..T, f x := by
    exact intervalIntegral.integral_add_adjacent_intervals (μ := volume) (f := f) (a := -T)
      (b := (0:ℝ)) (c := T) (hf.intervalIntegrable (-T) 0) (hf.intervalIntegrable 0 T)
  rw [← hadj]
  have hneg : (∫ x in -T..0, f x) = (∫ x in 0..T, f (-x)) := by
    have h := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := T) f
    rw [neg_zero] at h
    exact h.symm
  rw [hneg]
  have hc : (∫ x in 0..T, f (-x)) = (∫ x in 0..T, f x) := by
    apply intervalIntegral.integral_congr (μ := volume)
    intro x hx; exact he x
  rw [hc]
  ring

lemma continuous_kernA (α : ℝ) : Continuous fun t => Real.cos (α * t) / (1 + t ^ 2) := by
  have hnum : Continuous fun t : ℝ => Real.cos (α * t) := by fun_prop
  have hden : Continuous fun t : ℝ => (1 : ℝ) + t ^ 2 := by fun_prop
  have hdenz : ∀ t : ℝ, (1 : ℝ) + t ^ 2 ≠ 0 := by intro t; nlinarith [sq_nonneg t]
  exact Continuous.div₀ hnum hden hdenz

lemma continuous_kernB (α : ℝ) : Continuous fun t => t * Real.sin (α * t) / (1 + t ^ 2) := by
  have hnum : Continuous fun t : ℝ => t * Real.sin (α * t) := by fun_prop
  have hden : Continuous fun t : ℝ => (1 : ℝ) + t ^ 2 := by fun_prop
  have hdenz : ∀ t : ℝ, (1 : ℝ) + t ^ 2 ≠ 0 := by intro t; nlinarith [sq_nonneg t]
  exact Continuous.div₀ hnum hden hdenz

/-! ## Real-part reduction of the truncated Perron kernel -/

lemma integrand_decomp_pq (α : ℝ) : ∀ t : ℝ,
    cexp (I * (α * t : ℂ)) / (1 + I * (t : ℂ)) = ((pfun α t : ℝ) : ℂ) + I * ((qfun α t : ℝ) : ℂ) := by
  intro t
  unfold pfun qfun
  exact integrand_decomp α t

/-- The integral of the real part of the integrand over `[0,T]`. -/
lemma pfun_integral_eq (T α : ℝ) : (∫ t in 0..T, pfun α t) = kernA T α + kernB T α := by
  unfold kernA kernB pfun
  have hsplit : (fun t : ℝ => (Real.cos (α * t) + t * Real.sin (α * t)) / (1 + t ^ 2))
      = (fun t : ℝ => Real.cos (α * t) / (1 + t ^ 2) + t * Real.sin (α * t) / (1 + t ^ 2)) := by
    funext t
    rw [add_div]
  rw [hsplit]
  have hfi : IntervalIntegrable (fun t : ℝ => Real.cos (α * t) / (1 + t ^ 2)) volume 0 T :=
    (continuous_kernA α).intervalIntegrable _ _
  have hgi : IntervalIntegrable (fun t : ℝ => t * Real.sin (α * t) / (1 + t ^ 2)) volume 0 T :=
    (continuous_kernB α).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (μ := volume) (a := (0 : ℝ)) (b := T) hfi hgi]

/-- `K(T,α) = 2·(∫_0^T cos(αt)/(1+t²) dt + ∫_0^T t·sin(αt)/(1+t²) dt)`, as a real number. -/
lemma kern_eq_two_A_B (T α : ℝ) : kern T α = ((2 * (kernA T α + kernB T α) : ℝ) : ℂ) := by
  unfold kern
  have hint : (fun t : ℝ => cexp (I * (α * t : ℂ)) / (1 + I * (t : ℂ))) =
      (fun t : ℝ => ((pfun α t : ℝ) : ℂ) + I * ((qfun α t : ℝ) : ℂ)) := by
    funext t
    exact integrand_decomp_pq α t
  rw [hint]
  have hcf : IntervalIntegrable (fun t => (((pfun α t : ℝ) : ℂ))) volume (-T) T :=
    (continuous_ofReal.comp (continuous_pfun α)).intervalIntegrable _ _
  have hcg : IntervalIntegrable (fun t => (I * (((qfun α t : ℝ) : ℂ)))) volume (-T) T := by
    exact ((continuous_const.mul (continuous_ofReal.comp (continuous_qfun α)))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (μ := volume) (a := -T) (b := T) hcf hcg]
  have hq0 : (∫ t in -T..T, qfun α t) = 0 := integral_real_odd_zero (qfun α) (continuous_qfun α) (qfun_odd α) T
  rw [intervalIntegral.integral_const_mul]
  simp_rw [intervalIntegral.integral_ofReal]
  rw [hq0]
  simp
  have hp : (∫ t in -T..T, pfun α t) = 2 * (∫ t in 0..T, pfun α t) :=
    integral_real_even_two (pfun α) (continuous_pfun α) (pfun_even α) T
  rw [hp]
  rw [pfun_integral_eq]
  simp

/-! ## Uniform (small-|α|T) bounds -/

/-- `|∫_0^T cos(αt)/(1+t²) dt| ≤ π/2` for `T ≥ 0`. -/
lemma abs_kernA_le (α T : ℝ) (hT : 0 ≤ T) : |kernA T α| ≤ Real.pi / 2 := by
  -- |∫_0^T cos/(1+t²)| ≤ ∫_0^T |cos|/(1+t²) ≤ ∫_0^T 1/(1+t²) = arctan T ≤ π/2
  have h1 : ‖∫ t in (0 : ℝ)..T, Real.cos (α * t) / (1 + t ^ 2)‖ ≤
      ∫ t in (0 : ℝ)..T, ‖Real.cos (α * t) / (1 + t ^ 2)‖ :=
    intervalIntegral.norm_integral_le_integral_norm (a := (0:ℝ)) (b := T) hT
  have hmono : (∫ t in (0 : ℝ)..T, ‖Real.cos (α * t) / (1 + t ^ 2)‖) ≤
      ∫ t in (0 : ℝ)..T, (1 : ℝ) / (1 + t ^ 2) := by
    apply intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := T) hT
    · exact ((continuous_kernA α).norm.intervalIntegrable (0:ℝ) T)
    · exact ((continuous_const.div (by fun_prop : Continuous fun t : ℝ => 1 + t ^ 2)
        (by intro t; nlinarith [sq_nonneg t])).intervalIntegrable (0:ℝ) T)
    · intro x hx
      have hb : |Real.cos (α * x)| ≤ 1 := Real.abs_cos_le_one _
      have hden : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
      rw [Real.norm_eq_abs]
      calc
        |Real.cos (α * x) / (1 + x ^ 2)| = |Real.cos (α * x)| / (1 + x ^ 2) := by
          rw [abs_div]; simp [abs_of_nonneg hden.le]
        _ ≤ 1 / (1 + x ^ 2) := by
          gcongr
  have hval : (∫ t in (0 : ℝ)..T, (1 : ℝ) / (1 + t ^ 2)) = Real.arctan T := by
    rw [integral_one_div_one_add_sq]
    simp
  have h2 : |kernA T α| ≤ Real.arctan T := by
    calc
      |kernA T α| = ‖∫ t in (0 : ℝ)..T, Real.cos (α * t) / (1 + t ^ 2)‖ := by
        rw [Real.norm_eq_abs]
        rfl
      _ ≤ ∫ t in (0 : ℝ)..T, ‖Real.cos (α * t) / (1 + t ^ 2)‖ := h1
      _ ≤ ∫ t in (0 : ℝ)..T, (1 : ℝ) / (1 + t ^ 2) := hmono
      _ = Real.arctan T := hval
  exact le_trans h2 (Real.arctan_lt_pi_div_two T).le

/-- `|∫_0^T t·sin(αt)/(1+t²) dt| ≤ |α|·T` for `T ≥ 0`. -/
lemma abs_kernB_le (α T : ℝ) (hT : 0 ≤ T) : |kernB T α| ≤ |α| * T := by
  -- pointwise |t sin(αt)|/(1+t²) ≤ |α| on [0,T]
  have hpt : ∀ x ∈ Set.uIoc (0 : ℝ) T, ‖x * Real.sin (α * x) / (1 + x ^ 2)‖ ≤ |α| := by
    intro x hx
    have hx0 : 0 ≤ x := by
      rcases (Set.mem_uIoc.mp hx) with h | h
      · exact le_of_lt h.1
      · exfalso
        nlinarith [hT, h.1, h.2]
    have hden : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
    rw [Real.norm_eq_abs]
    calc
      |x * Real.sin (α * x) / (1 + x ^ 2)| = |x * Real.sin (α * x)| / (1 + x ^ 2) := by
        rw [abs_div]
        simp [abs_of_nonneg hden.le]
      _ = (x * |Real.sin (α * x)|) / (1 + x ^ 2) := by
        rw [abs_mul, abs_of_nonneg hx0]
      _ ≤ (x * |α * x|) / (1 + x ^ 2) := by
        have hs : |Real.sin (α * x)| ≤ |α * x| := Real.abs_sin_le_abs
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hx0) hden.le
      _ = (|α| * x ^ 2) / (1 + x ^ 2) := by
        have hnum : x * |α * x| = |α| * x ^ 2 := by
          rw [abs_mul, abs_of_nonneg hx0]
          ring
        rw [hnum]
      _ ≤ |α| := by
        rw [div_le_iff₀ hden]
        exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg x]) (abs_nonneg α)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := T)
    (f := fun x : ℝ => x * Real.sin (α * x) / (1 + x ^ 2)) (C := |α|) hpt
  calc
    |kernB T α| = ‖∫ x in (0 : ℝ)..T, x * Real.sin (α * x) / (1 + x ^ 2)‖ := by
      rw [Real.norm_eq_abs]
      rfl
    _ ≤ |α| * |T - 0| := hbound
    _ = |α| * T := by
      rw [sub_zero, abs_of_nonneg hT]

/-- The kernel is bounded by `π + 2·|α|T`; in particular by `π + 2` when `|α|T ≤ 1`. -/
lemma abs_kern_le (T α : ℝ) (hT : 0 ≤ T) : ‖kern T α‖ ≤ Real.pi + 2 * |α| * T := by
  rw [kern_eq_two_A_B]
  have hnorm : ‖((2 * (kernA T α + kernB T α) : ℝ) : ℂ)‖ = |2 * (kernA T α + kernB T α)| := by
    simpa using (RCLike.norm_ofReal (K := ℂ) (2 * (kernA T α + kernB T α)))
  rw [hnorm]
  have hmain : |2 * (kernA T α + kernB T α)| ≤ 2 * (|kernA T α| + |kernB T α|) := by
    calc
      |2 * (kernA T α + kernB T α)| = 2 * |kernA T α + kernB T α| := by
        rw [abs_mul, abs_of_nonneg]; norm_num
      _ ≤ 2 * (|kernA T α| + |kernB T α|) := by
        exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
  exact le_trans hmain (by
    nlinarith [abs_kernA_le α T hT, abs_kernB_le α T hT])

/-- Uniform bound: `‖K(T,α)‖ ≤ π + 2` for `1 ≤ T`, `T·|α| ≤ 1`. -/
theorem kern_region_bound (T α : ℝ) (hT : 1 ≤ T) (hreg : T * |α| ≤ 1) :
    ‖kern T α‖ ≤ Real.pi + 2 := by
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hb := abs_kern_le T α hT0
  have hbt : 2 * |α| * T ≤ 2 := by
    nlinarith [hreg]
  linarith

end PerronKernel

end Commons.Analysis.Fourier


/-!
# Oscillatory tail bound (child task)

Prove `PerronKernel.osc_tail_bound` below:

    ‖∫_T^R e^{iαt} / (1 + i t) dt‖ ≤ 3 / (|α| · T)

for real `α ≠ 0`, `1 ≤ T ≤ R` (all integrals are Mathlib interval integrals over
the real variable `t`, integrands complex).  Do **not** weaken the statement.
You may add helper lemmas **above** the theorem and change imports.

Integration-by-parts route (all derivative facts below are machine-verified in
this file already and can be reused):

  1. Write the integrand as `u'(t)·v(t)` with
        u(t) = cexp (I * (α : ℂ) * (t : ℂ)) / (I * (α : ℂ))     (u' = cexp …)
        v(t) = (1 + I * (t : ℂ))⁻¹                               (v' = -I·v(t)^2)
     (derivatives supplied below: `deriv_cexp_div`, `deriv_one_add_I_inv`).
  2. Integrate by parts on `[T, R]` (Mathlib:
     `intervalIntegral.integral_deriv_mul_eq_sub` or
     `intervalIntegral.integral_mul_deriv_eq_deriv_mul` with `A = ℂ`) to get
        ∫_T^R u'·v  =  (u(R)v(R) − u(T)v(T)) − ∫_T^R u·v'
     (equivalently apply the FTC to `F = u·v`, whose derivative is `u'v + uv'`).
  3. Bound pointwise, for `t ≥ T ≥ 1`:
        ‖u(t)v(t)‖ = ‖cexp‖/(‖Iα‖·‖1 + i t‖) ≤ 1/(|α|·t) ≤ 1/(|α|T)
        ‖u(t)·v'(t)‖ ≤ 1/(|α|·(1+t²))          (since |v(t)|² = 1/(1+t²))
     whence ‖boundary‖ ≤ 2/(|α|T) and ‖∫_T^R u·v'‖ ≤ (1/|α|)∫_T^R 1/(1+t²)dt
     ≤ (1/|α|)(1/T − 1/R) ≤ 1/(|α|T)  (use `1/(1+t²) ≤ 1/t²` for `t ≥ 1`).
     Use the triangle inequality and `norm_integral_le_integral_norm` /
     `intervalIntegral.integral_mono_on`-style bounds.
  4. Since `e^{iαt}/(1+it) = cexp (I*(α:ℂ)*(t:ℂ)) · (1 + I*(t:ℂ))⁻¹` pointwise
     (and `cexp (I*(α:ℂ)*(t:ℂ)) = cexp (I*(α*t : ℂ))`), rewrite the integrand
     accordingly.  Note `‖α‖ = |α|` for real `α` lifted to ℂ
     (`RCLike.norm_ofReal`).
-/

noncomputable section

open Real Set Complex Filter intervalIntegral MeasureTheory
open scoped Topology Real

namespace Commons.Analysis.Fourier

namespace PerronKernel

/-- derivative of `s ↦ e^{I·α·s}/(I·α)`, equal to `e^{I·α·s}`. -/
lemma deriv_cexp_div (α : ℝ) (hα : α ≠ 0) : ∀ t : ℝ,
    HasDerivAt (fun s : ℝ => cexp (I * (α : ℂ) * (s : ℂ)) / (I * (α : ℂ)))
      (cexp (I * (α : ℂ) * (t : ℂ))) t := by
  intro t
  have hlin : HasDerivAt (fun w : ℂ => (I * (α : ℂ)) * w) (I * (α : ℂ)) (t : ℂ) := by
    simpa using (hasDerivAt_id (t : ℂ)).const_mul (I * (α : ℂ))
  have hcomp : HasDerivAt (fun s : ℝ => (I * (α : ℂ)) * (s : ℂ)) (I * (α : ℂ)) t :=
    hlin.comp_ofReal
  have hcexp := HasDerivAt.cexp hcomp
  have h2 := hcexp.div_const (I * (α : ℂ))
  refine h2.congr_deriv ?_
  have hnz : (I * (α : ℂ)) ≠ 0 := by
    intro hz
    apply hα
    have hz' := congrArg Complex.im hz
    simpa using hz'
  have hα' : ((α : ℂ)) ≠ 0 := by exact_mod_cast hα
  field_simp [hnz, hα']

/-- derivative of `s ↦ (1 + I·s)⁻¹`. -/
lemma deriv_one_add_I_inv : ∀ t : ℝ,
    HasDerivAt (fun s : ℝ => (1 + I * (s : ℂ))⁻¹) (-(I : ℂ) * ((1 + I * (t : ℂ))⁻¹) ^ 2) t := by
  intro t
  have hg : HasDerivAt (fun s : ℝ => (1 + I * (s : ℂ) : ℂ)) I t := by
    have hlin : HasDerivAt (fun w : ℂ => I * w) I (t : ℂ) := by
      simpa using (hasDerivAt_id (t : ℂ)).const_mul I
    have hcomp : HasDerivAt (fun s : ℝ => I * (s : ℂ)) I t := hlin.comp_ofReal
    simpa using hcomp.const_add 1
  have hne : (1 + I * (t : ℂ) : ℂ) ≠ 0 := by
    intro hz
    have : Complex.normSq (1 + I * (t : ℂ)) = 0 := by simp [hz]
    rw [Complex.normSq_apply] at this
    have hre : (1 + I * (t : ℂ) : ℂ).re = 1 := by simp
    have him : (1 + I * (t : ℂ) : ℂ).im = t := by simp
    rw [hre, him] at this
    nlinarith
  have hinv := hasDerivAt_inv hne
  have h := hinv.comp t hg
  refine h.congr_deriv ?_
  have hx2 : ((1 + I * (t : ℂ)) ^ 2)⁻¹ = ((1 + I * (t : ℂ))⁻¹) ^ 2 := by
    exact (inv_pow (a := (1 + I * (t : ℂ))) 2).symm
  calc
    (-((1 + I * (t : ℂ)) ^ 2)⁻¹) * I = -(I * ((1 + I * (t : ℂ)) ^ 2)⁻¹) := by ring
    _ = -I * ((1 + I * (t : ℂ)) ^ 2)⁻¹ := by ring
    _ = -(I : ℂ) * ((1 + I * (t : ℂ))⁻¹) ^ 2 := by rw [hx2]

private def oscUp (α : ℝ) (s : ℝ) : ℂ := cexp (I * (α : ℂ) * (s : ℂ))
private def oscU (α : ℝ) (s : ℝ) : ℂ := oscUp α s / (I * (α : ℂ))
private def oscV (s : ℝ) : ℂ := (1 + I * (s : ℂ))⁻¹
private def oscW (α : ℝ) (s : ℝ) : ℂ := oscU α s * oscV s
private def oscR (α : ℝ) (s : ℝ) : ℂ := oscU α s * (-(I : ℂ) * (oscV s) ^ 2)
private def oscG (α : ℝ) (s : ℝ) : ℂ := cexp (I * ((α * s : ℝ) : ℂ)) / (1 + I * (s : ℂ))

lemma phase_arg (α t : ℝ) : I * (α : ℂ) * (t : ℂ) = I * ((α * t : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul]; ring
lemma integrand_eq_oscG (α t : ℝ) :
    cexp (I * (α * t : ℂ)) / (1 + I * (t : ℂ)) = oscG α t := by
  unfold oscG
  rw [Complex.ofReal_mul]
lemma oscG_eq (α x : ℝ) : oscG α x = oscUp α x * oscV x := by
  unfold oscG oscUp oscV
  rw [← phase_arg]
  rw [div_eq_mul_inv]
lemma norm_phase_exp (α t : ℝ) : ‖cexp (I * (α : ℂ) * (t : ℂ))‖ = 1 := by
  rw [phase_arg]
  simpa [mul_comm, mul_left_comm, mul_assoc] using Complex.norm_exp_ofReal_mul_I (α * t)
lemma norm_I_mul_ofReal (α : ℝ) : ‖I * (α : ℂ)‖ = |α| := by simp
lemma one_add_I_ne_zero (t : ℝ) : (1 + I * (t : ℂ) : ℂ) ≠ 0 := by
  intro h; have hre := congrArg Complex.re h; simp at hre
lemma one_add_I_norm_sq (t : ℝ) : ‖(1 + I * (t : ℂ) : ℂ)‖ ^ 2 = 1 + t ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [sq]
lemma one_add_I_norm_ge (t : ℝ) (ht : 0 ≤ t) : t ≤ ‖(1 + I * (t : ℂ) : ℂ)‖ := by
  have hsq : t ^ 2 ≤ ‖(1 + I * (t : ℂ) : ℂ)‖ ^ 2 := by
    rw [one_add_I_norm_sq]; nlinarith
  have hs := (sq_le_sq.mp hsq)
  simpa [abs_of_nonneg ht, abs_of_nonneg (norm_nonneg _)] using hs
lemma oscV_norm_le (t : ℝ) (ht : 1 ≤ t) : ‖oscV t‖ ≤ t⁻¹ := by
  unfold oscV
  rw [norm_inv]
  have ht0 : 0 < t := by linarith
  have hz0 : 0 < ‖(1 + I * (t : ℂ) : ℂ)‖ := norm_pos_iff.mpr (one_add_I_ne_zero t)
  exact (inv_le_inv₀ hz0 ht0).mpr (one_add_I_norm_ge t (by linarith))
lemma oscV_norm_sq (t : ℝ) : ‖oscV t‖ ^ 2 = (1 + t ^ 2)⁻¹ := by
  unfold oscV
  rw [norm_inv, inv_pow, one_add_I_norm_sq]
lemma oscU_norm (α t : ℝ) : ‖oscU α t‖ = (|α|)⁻¹ := by
  unfold oscU oscUp
  calc
    ‖cexp (I * (α : ℂ) * (t : ℂ)) / (I * (α : ℂ))‖ = ‖cexp (I * (α : ℂ) * (t : ℂ))‖ / ‖I * (α : ℂ)‖ := by rw [norm_div]
    _ = 1 / |α| := by
      rw [norm_phase_exp, norm_I_mul_ofReal]
    _ = (|α|)⁻¹ := by simp
lemma oscR_norm_le (α t : ℝ) : ‖oscR α t‖ ≤ (|α|)⁻¹ * (1 + t ^ 2)⁻¹ := by
  unfold oscR
  calc
    ‖oscU α t * (-(I : ℂ) * (oscV t) ^ 2)‖ ≤ ‖oscU α t‖ * ‖-(I : ℂ) * (oscV t) ^ 2‖ := norm_mul_le _ _
    _ = (|α|)⁻¹ * ‖(oscV t) ^ 2‖ := by
      have hnorm : ‖-(I : ℂ) * (oscV t) ^ 2‖ = ‖(oscV t) ^ 2‖ := by
        rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
      rw [oscU_norm, hnorm]
    _ = (|α|)⁻¹ * ((1 + t ^ 2)⁻¹) := by rw [norm_pow, oscV_norm_sq]
lemma oscW_norm_le (α t : ℝ) (ht : 1 ≤ t) : ‖oscW α t‖ ≤ (|α| * t)⁻¹ := by
  unfold oscW
  calc
    ‖oscU α t * oscV t‖ ≤ ‖oscU α t‖ * ‖oscV t‖ := norm_mul_le _ _
    _ = (|α|)⁻¹ * ‖oscV t‖ := by rw [oscU_norm]
    _ ≤ (|α|)⁻¹ * t⁻¹ := mul_le_mul_of_nonneg_left (oscV_norm_le t ht) (inv_nonneg.mpr (abs_nonneg α))
    _ = (|α| * t)⁻¹ := by rw [← mul_inv]
lemma oscW_norm_bound (α t T : ℝ) (hα : α ≠ 0) (htT : T ≤ t) (hT : 1 ≤ T) :
    ‖oscW α t‖ ≤ (|α| * T)⁻¹ := by
  have h1 := oscW_norm_le α t (le_trans hT htT)
  refine le_trans h1 ?_
  have hle : |α| * T ≤ |α| * t := mul_le_mul_of_nonneg_left htT (abs_nonneg α)
  have hbpos : 0 < |α| * t := mul_pos (abs_pos.mpr hα) (lt_of_lt_of_le zero_lt_one (le_trans hT htT))
  have hapos : 0 < |α| * T := mul_pos (abs_pos.mpr hα) (lt_of_lt_of_le zero_lt_one hT)
  exact (inv_le_inv₀ hbpos hapos).mpr hle

lemma cont_oscUp (α : ℝ) : Continuous (oscUp α) := by unfold oscUp; fun_prop
lemma cont_oscV : Continuous oscV := by
  unfold oscV
  exact (by fun_prop : Continuous fun s : ℝ => (1 + I * (s : ℂ) : ℂ)).inv₀ (fun s => one_add_I_ne_zero s)
lemma cont_oscU (α : ℝ) : Continuous (oscU α) := by unfold oscU; exact (cont_oscUp α).div_const (I * (α : ℂ))
lemma cont_oscR (α : ℝ) : Continuous (oscR α) := by
  unfold oscR
  exact (cont_oscU α).mul ((continuous_const.mul (cont_oscV.pow 2)))
lemma hasDerivAt_oscU (α : ℝ) (hα : α ≠ 0) : ∀ t, HasDerivAt (oscU α) (oscUp α t) t := by
  intro t; unfold oscU oscUp; simpa using deriv_cexp_div α hα t
lemma hasDerivAt_oscV : ∀ t, HasDerivAt oscV (-(I : ℂ) * (oscV t) ^ 2) t := by
  intro t; unfold oscV; simpa using deriv_one_add_I_inv t
lemma hasDerivAt_oscW (α : ℝ) (hα : α ≠ 0) : ∀ t,
    HasDerivAt (oscU α * oscV) (oscUp α t * oscV t + oscU α t * (-(I : ℂ) * (oscV t) ^ 2)) t := by
  intro t
  exact (hasDerivAt_oscU α hα t).mul (hasDerivAt_oscV t)
lemma integral_osc_main (α T R : ℝ) (hα : α ≠ 0) :
    (∫ t in T..R, (oscUp α t * oscV t + oscU α t * (-(I : ℂ) * (oscV t) ^ 2)))
      = (oscU α * oscV) R - (oscU α * oscV) T := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := oscU α * oscV)
    (f' := fun t => oscUp α t * oscV t + oscU α t * (-(I : ℂ) * (oscV t) ^ 2))
  · intro x hx
    exact hasDerivAt_oscW α hα x
  · exact (((cont_oscUp α).mul cont_oscV).add (cont_oscR α)).intervalIntegrable T R
lemma osc_integral_identity (α T R : ℝ) (hα : α ≠ 0) :
    (∫ t in T..R, oscG α t) = (oscW α R - oscW α T) - ∫ t in T..R, oscR α t := by
  have hFTC := integral_osc_main α T R hα
  have hsplit :
      (∫ t in T..R, (oscUp α t * oscV t + oscU α t * (-(I : ℂ) * (oscV t) ^ 2)))
        = (∫ t in T..R, oscUp α t * oscV t) + ∫ t in T..R, oscU α t * (-(I : ℂ) * (oscV t) ^ 2) := by
    exact intervalIntegral.integral_add (μ := volume)
      (((cont_oscUp α).mul cont_oscV).intervalIntegrable T R)
      ((cont_oscR α).intervalIntegrable T R)
  have hrewrite : (∫ t in T..R, oscUp α t * oscV t) = ∫ t in T..R, oscG α t := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact (oscG_eq α x).symm
  rw [hsplit, hrewrite] at hFTC
  change (∫ t in T..R, oscG α t) + ∫ t in T..R, oscR α t = oscW α R - oscW α T at hFTC
  rw [eq_sub_iff_add_eq]
  exact hFTC

lemma inv_one_add_sq_le_inv_sq (t : ℝ) (ht : 1 ≤ t) : (1 + t ^ 2)⁻¹ ≤ (t ^ 2)⁻¹ := by
  have ht0 : 0 < t := by linarith
  have hle : t ^ 2 ≤ 1 + t ^ 2 := by nlinarith
  have hpos1 : 0 < 1 + t ^ 2 := by positivity
  have hpos2 : 0 < t ^ 2 := sq_pos_of_pos ht0
  exact (inv_le_inv₀ hpos1 hpos2).mpr hle
lemma continuous_inv_one_add_sq : Continuous fun t : ℝ => (1 + t ^ 2)⁻¹ := by
  refine Continuous.inv₀ ?hf ?h0
  · fun_prop
  · intro t; positivity

lemma integral_inv_sq_of_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t in a..b, (t ^ 2)⁻¹) = a⁻¹ - b⁻¹ := by
  have hint : IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ ?hf ?h0
    · exact (by fun_prop : Continuous fun t : ℝ => (t : ℝ) ^ 2).continuousOn
    · intro x hx
      have hmin : min a b ≤ x := hx.1
      have hpos : 0 < min a b := lt_min ha hb
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hpos hmin))
  have hintN : IntervalIntegrable (fun t : ℝ => -(t ^ 2)⁻¹) volume a b := by
    exact IntervalIntegrable.neg hint
  have hFTC : (∫ t in a..b, -(t ^ 2)⁻¹) = (fun x : ℝ => x⁻¹) b - (fun x : ℝ => x⁻¹) a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => x⁻¹)
      (f' := fun t : ℝ => -(t ^ 2)⁻¹)
      (by
        intro x hx
        have hx0 : x ≠ 0 := by
          have hmin : min a b ≤ x := hx.1
          have hpos : 0 < min a b := lt_min ha hb
          exact ne_of_gt (lt_of_lt_of_le hpos hmin)
        exact hasDerivAt_inv hx0)
      hintN
  have hneg : (∫ t in a..b, -(t ^ 2)⁻¹) = -(∫ t in a..b, (t ^ 2)⁻¹) := by
    rw [intervalIntegral.integral_neg]
  rw [hneg] at hFTC
  linarith

lemma integrable_inv_sq_Icc (T R : ℝ) (hT : 0 < T) (hTR : T ≤ R) :
    IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹) volume T R := by
  refine ContinuousOn.intervalIntegrable_of_Icc hTR ?_
  refine ContinuousOn.inv₀ ?hf ?h0
  · exact (by fun_prop : Continuous fun t : ℝ => (t : ℝ) ^ 2).continuousOn
  · intro x hx
    have hT0 : 0 < x := lt_of_lt_of_le hT hx.1
    exact pow_ne_zero 2 (ne_of_gt hT0)

lemma integral_inv_one_add_sq_le (T R : ℝ) (hT : 1 ≤ T) (hTR : T ≤ R) :
    (∫ t in T..R, (1 + t ^ 2)⁻¹) ≤ T⁻¹ := by
  have hmono : (∫ t in T..R, (1 + t ^ 2)⁻¹) ≤ ∫ t in T..R, (t ^ 2)⁻¹ := by
    refine intervalIntegral.integral_mono_on hTR ?hf ?hg ?h
    · exact continuous_inv_one_add_sq.intervalIntegrable T R
    · exact integrable_inv_sq_Icc T R (by linarith) hTR
    · intro x hx
      exact inv_one_add_sq_le_inv_sq x (le_trans hT hx.1)
  have hval : (∫ t in T..R, (t ^ 2)⁻¹) = T⁻¹ - R⁻¹ :=
    integral_inv_sq_of_pos T R (by linarith) (by linarith)
  rw [hval] at hmono
  have hRinv : 0 ≤ R⁻¹ := inv_nonneg.mpr (by linarith)
  linarith

lemma oscR_integral_norm_le (α T R : ℝ) (hT : 1 ≤ T) (hTR : T ≤ R) :
    ‖∫ t in T..R, oscR α t‖ ≤ (|α|)⁻¹ * T⁻¹ := by
  calc
    ‖∫ t in T..R, oscR α t‖ ≤ ∫ t in T..R, ‖oscR α t‖ := intervalIntegral.norm_integral_le_integral_norm hTR
    _ ≤ ∫ t in T..R, (|α|)⁻¹ * (1 + t ^ 2)⁻¹ := by
      exact intervalIntegral.integral_mono_on hTR
        (((cont_oscR α).norm).intervalIntegrable T R)
        (((continuous_const.mul continuous_inv_one_add_sq)).intervalIntegrable T R)
        (fun x hx => oscR_norm_le α x)
    _ = (|α|)⁻¹ * (∫ t in T..R, (1 + t ^ 2)⁻¹) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (|α|)⁻¹ * T⁻¹ := mul_le_mul_of_nonneg_left (integral_inv_one_add_sq_le T R hT hTR)
        (inv_nonneg.mpr (abs_nonneg α))


theorem osc_tail_bound (α T R : ℝ) (hα : α ≠ 0) (hT : 1 ≤ T) (hTR : T ≤ R) :
    ‖∫ t in T..R, cexp (I * (α * t : ℂ)) / (1 + I * (t : ℂ))‖ ≤ 3 / (|α| * T) := by
  have hconv : (∫ t in T..R, cexp (I * (α * t : ℂ)) / (1 + I * (t : ℂ))) = ∫ t in T..R, oscG α t := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact integrand_eq_oscG α x
  rw [hconv]
  have hbound : ‖oscW α R - oscW α T‖ ≤ 2 * (|α| * T)⁻¹ := by
    calc
      ‖oscW α R - oscW α T‖ ≤ ‖oscW α R‖ + ‖oscW α T‖ := norm_sub_le _ _
      _ ≤ 2 * (|α| * T)⁻¹ := by
        have h1 := oscW_norm_bound α R T hα hTR hT
        have h2 := oscW_norm_bound α T T hα le_rfl hT
        nlinarith
  have hint : ‖∫ t in T..R, oscR α t‖ ≤ (|α| * T)⁻¹ := by
    have h := oscR_integral_norm_le α T R hT hTR
    rwa [← mul_inv] at h
  have hmain : ‖∫ t in T..R, oscG α t‖ ≤ 3 * (|α| * T)⁻¹ := by
    calc
      ‖∫ t in T..R, oscG α t‖ = ‖(oscW α R - oscW α T) - ∫ t in T..R, oscR α t‖ := by
          rw [osc_integral_identity α T R hα]
      _ ≤ ‖oscW α R - oscW α T‖ + ‖∫ t in T..R, oscR α t‖ := norm_sub_le _ _
      _ ≤ 2 * (|α| * T)⁻¹ + (|α| * T)⁻¹ := add_le_add hbound hint
      _ = 3 * (|α| * T)⁻¹ := by ring
  rw [div_eq_mul_inv]
  exact hmain

end PerronKernel

end Commons.Analysis.Fourier


/-!
# Fourier (sine) value of the Cauchy-moment density (child task)

Prove `PerronKernel.sin_mul_one_add_sq_tendsto` below:

    lim_{T→∞} ∫_0^T x·sin(a·x)/(1+x²) dx = (π/2)·sign(a)·e^{−|a|}          (a ≠ 0)

where the integral is the Mathlib interval integral `∫ x in (0 : ℝ)..T` and the
limit is `Tendsto ... atTop (𝓝 ...)`.  Do **not** weaken the statement.  You
may add helper lemmas **above** the theorem and change the imports.

The cosine value is already available (import `Submission.CosValue`):

    cos_inv_one_add_sq_Ioi (a : ℝ) :
      (∫ x : ℝ in Set.Ioi (0 : ℝ), Real.cos (a*x)/(1+x²)) = (π/2)·exp(−|a|)

and the Dirichlet value (import `Submission.DirichletValue`):

    PerronKernel.dirichlet_integral :
      Tendsto (fun T : ℝ => ∫ x in (0:ℝ)..T, Real.sin x / x) atTop (𝓝 (π/2))

Suggested route (real analysis only):
  1. Algebraic decomposition for `x > 0`:
        x·sin(a·x)/(1+x²) = sin(a·x)/x − sin(a·x)/(x·(1+x²))
     so for every finite T,
        ∫_0^T x·sin(ax)/(1+x²) dx = ∫_0^T sin(ax)/x dx − ∫_0^T sin(ax)/(x(1+x²)) dx .
  2. First term: for `a > 0`, substitute `u = a·x` and use `dirichlet_integral`
     (plus a change of variables); for `a < 0` use oddness of `sin`.
  3. Second term: the function `x ↦ sin(a·x)/(x·(1+x²))` is *absolutely*
     integrable on `(0,∞)` (near 0 it is bounded by `|a|`; at infinity by
     `1/x³`), so the finite integrals tend to the Lebesgue integral
     `D(a) := ∫ x in Ioi 0, sin(a·x)/(x·(1+x²))`.
     Show `D(a) = (π/2)·(1 − e^{−|a|})·sign a` by differentiating in `a`
     (`∂/∂a` of `sin(a·x)/(x(1+x²))` is `cos(a·x)/(1+x²)`, bounded by the
     integrable function `1/(1+x²)`, so differentiation under the integral is
     legitimate — use Mathlib's `hasDerivAt`-under-`∫`/dominated-convergence
     theorems or differentiate finite integrals and pass to the limit), with
     `D(0) = 0` and `cos_inv_one_add_sq_Ioi` giving `D'(a) = (π/2)e^{−|a|}`.
     Alternatively integrate over the finite range `[0,M]` first and then let
     `M → ∞` uniformly on compact `a`-intervals.
  4. Combine and take limits: `(π/2)sign a − D(a) = (π/2)·sign(a)·e^{−|a|}`.
-/

noncomputable section

open Real Set Filter MeasureTheory
open scoped Topology Real

namespace Commons.Analysis.Fourier

namespace PerronKernel

/-! ### Change of variables `u = b·x` for the Dirichlet-type integrals -/

/-- For `b ≠ 0`, `sin(b·x)/x = sinc(b·x)·b` almost everywhere. -/
lemma sinc_integral_eq (b : ℝ) (hb : b ≠ 0) (T : ℝ) :
    (∫ x in (0 : ℝ)..T, Real.sin (b * x) / x) = ∫ x in (0 : ℝ)..T, Real.sinc (b * x) * b := by
  refine intervalIntegral.integral_congr_ae ?_
  have hfull : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hfull] with x hx
  intro hxmem
  have hbx : b * x ≠ 0 := mul_ne_zero hb hx
  have hsinc : Real.sinc (b * x) = Real.sin (b * x) / (b * x) := Real.sinc_of_ne_zero hbx
  rw [hsinc]
  field_simp [hx]

/-- Substitution `u = b·x` in an interval integral of `sinc`. -/
lemma sinc_integral_subst (b : ℝ) (T : ℝ) :
    (∫ x in (0 : ℝ)..T, Real.sinc (b * x) * b) = ∫ u in (0 : ℝ)..(b * T), Real.sinc u := by
  let F : ℝ → ℝ := fun t => b * t
  have hderiv : ∀ x ∈ Set.uIcc 0 T, HasDerivAt F b x := by
    intro x hx
    dsimp [F]
    simpa using (hasDerivAt_id x).const_mul b
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := T)
    (f := F) (f' := fun _ => b) (g := Real.sinc) hderiv continuousOn_const Real.continuous_sinc
  simpa [F] using hsub

/-- `lim_{T→∞} ∫_0^T sin(b·x)/x dx = π/2` for `b > 0` (rescaling of `dirichlet_integral`). -/
lemma sin_scaled_tendsto (b : ℝ) (hb : 0 < b) :
    Tendsto (fun T : ℝ => ∫ x in (0 : ℝ)..T, Real.sin (b * x) / x) atTop (𝓝 (Real.pi / 2)) := by
  have hsubst : ∀ T : ℝ,
      (∫ x in (0 : ℝ)..T, Real.sin (b * x) / x) = ∫ u in (0 : ℝ)..(b * T), Real.sin u / u := by
    intro T
    calc
      (∫ x in (0 : ℝ)..T, Real.sin (b * x) / x) = ∫ x in (0 : ℝ)..T, Real.sinc (b * x) * b := sinc_integral_eq b hb.ne' T
      _ = ∫ u in (0 : ℝ)..(b * T), Real.sinc u := sinc_integral_subst b T
      _ = ∫ u in (0 : ℝ)..(b * T), Real.sin u / u := by
        refine intervalIntegral.integral_congr_ae ?_
        have hfull : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 0 := by
          rw [MeasureTheory.ae_iff]
          simp
        filter_upwards [hfull] with u hu
        intro humem
        rw [Real.sinc_of_ne_zero hu]
  have hT : Tendsto (fun T : ℝ => b * T) atTop atTop := by
    simpa [mul_comm] using (Filter.Tendsto.atTop_mul_const (r := b) hb tendsto_id)
  have hdir := dirichlet_integral.comp hT
  exact hdir.congr' (Eventually.of_forall (fun T => (hsubst T).symm))

/-- `lim_{T→∞} ∫_0^T sin(b·x)/x dx = −π/2` for `b < 0` (oddness). -/
lemma sin_scaled_tendsto_neg (b : ℝ) (hb : b < 0) :
    Tendsto (fun T : ℝ => ∫ x in (0 : ℝ)..T, Real.sin (b * x) / x) atTop (𝓝 (-(Real.pi / 2))) := by
  have hb' : 0 < -b := neg_pos.mpr hb
  have hpos := sin_scaled_tendsto (-b) hb'
  have hodd : (fun T : ℝ => ∫ x in (0 : ℝ)..T, Real.sin (b * x) / x) =ᶠ[atTop]
      fun T : ℝ => -∫ x in (0 : ℝ)..T, Real.sin ((-b) * x) / x := by
    refine Eventually.of_forall (fun T => ?_)
    have hpt : (fun x : ℝ => Real.sin (b * x) / x) = fun x : ℝ => -(Real.sin ((-b) * x) / x) := by
      funext x
      congr 1
      have hs : Real.sin (b * x) = -Real.sin (-(b * x)) := by simp
      have harg : -(b * x) = (-b) * x := by ring
      rw [hs, harg]
      ring
    calc
      (∫ x in (0 : ℝ)..T, Real.sin (b * x) / x) = ∫ x in (0 : ℝ)..T, -(Real.sin ((-b) * x) / x) := by
        rw [hpt]
      _ = -∫ x in (0 : ℝ)..T, Real.sin ((-b) * x) / x := intervalIntegral.integral_neg
  have htend : Tendsto (fun T : ℝ => -∫ x in (0 : ℝ)..T, Real.sin ((-b) * x) / x) atTop
      (𝓝 (-(Real.pi / 2))) := hpos.neg
  exact htend.congr' hodd.symm
/-! ### The second term: absolutely integrable on `(0, ∞)` -/

/-- The function `x ↦ sin(a·x)/(x·(1+x²))` is integrable on `(0,∞)`. -/
lemma sin_x_mul_inv_integrableOn (a : ℝ) :
    IntegrableOn (fun x : ℝ => Real.sin (a * x) / (x * (1 + x ^ 2))) (Ioi (0 : ℝ)) volume := by
  rw [IntegrableOn]
  have hg0 : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) (volume.restrict (Ioi (0 : ℝ))) := by
    exact integrable_inv_one_add_sq.integrableOn
  have hg : Integrable (fun x : ℝ => |a| * (1 + x ^ 2)⁻¹) (volume.restrict (Ioi (0 : ℝ))) := by
    simpa using hg0.const_mul (|a|)
  have hcontOn : ContinuousOn (fun x : ℝ => Real.sin (a * x) / (x * (1 + x ^ 2))) (Ioi (0 : ℝ)) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (mem_Ioi.mp hx)
    have hc_sin : ContinuousAt (fun t : ℝ => Real.sin (a * t)) x := by fun_prop
    have hc_den : ContinuousAt (fun t : ℝ => t * (1 + t ^ 2)) x := by fun_prop
    have hden : (x * (1 + x ^ 2)) ≠ 0 := mul_ne_zero hx0 (by nlinarith [sq_nonneg x])
    exact (hc_sin.div hc_den hden).continuousWithinAt
  have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.sin (a * x) / (x * (1 + x ^ 2)))
      (volume.restrict (Ioi (0 : ℝ))) := hcontOn.aestronglyMeasurable measurableSet_Ioi
  refine Integrable.mono' (g := fun x : ℝ => |a| * (1 + x ^ 2)⁻¹) hg hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : 0 < x := (mem_Ioi.mp hx)
  have hdenpos : 0 < x * (1 + x ^ 2) := mul_pos hxpos (by nlinarith [sq_nonneg x])
  have hsin : |Real.sin (a * x)| ≤ |a| * x := by
    calc
      |Real.sin (a * x)| ≤ |a * x| := Real.abs_sin_le_abs (x := a * x)
      _ = |a| * x := by rw [abs_mul, abs_of_nonneg hxpos.le]
  calc
    ‖Real.sin (a * x) / (x * (1 + x ^ 2))‖ = |Real.sin (a * x)| / (x * (1 + x ^ 2)) := by
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hdenpos.le]
    _ ≤ (|a| * x) / (x * (1 + x ^ 2)) := by
      exact div_le_div_of_nonneg_right hsin hdenpos.le
    _ = |a| * (1 + x ^ 2)⁻¹ := by
      field_simp [ne_of_gt hxpos]

/-- The function `x ↦ cos(a·x)/(1+x²)` is integrable on `(0,∞)`. -/
lemma cos_one_add_sq_integrableOn (a : ℝ) :
    IntegrableOn (fun x : ℝ => Real.cos (a * x) / (1 + x ^ 2)) (Ioi (0 : ℝ)) volume := by
  rw [IntegrableOn]
  have hg : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) (volume.restrict (Ioi (0 : ℝ))) := by
    exact integrable_inv_one_add_sq.integrableOn
  have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.cos (a * x) / (1 + x ^ 2))
      (volume.restrict (Ioi (0 : ℝ))) := by
    have hcont : Continuous fun x : ℝ => Real.cos (a * x) / (1 + x ^ 2) := by
      refine Continuous.div (by fun_prop) (by fun_prop) ?_
      intro x
      nlinarith [sq_nonneg x]
    exact hcont.aestronglyMeasurable
  refine Integrable.mono' (g := fun x : ℝ => (1 + x ^ 2)⁻¹) hg hmeas ?_
  filter_upwards with x
  have h1 : |Real.cos (a * x)| ≤ 1 := Real.abs_cos_le_one (a * x)
  have hpos : 0 ≤ (1 + x ^ 2)⁻¹ := inv_nonneg.mpr (by nlinarith [sq_nonneg x])
  calc
    ‖Real.cos (a * x) / (1 + x ^ 2)‖ = |Real.cos (a * x)| * (1 + x ^ 2)⁻¹ := by
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (show 0 ≤ (1 + x ^ 2 : ℝ) by nlinarith [sq_nonneg x])]
      ring
    _ ≤ 1 * (1 + x ^ 2)⁻¹ := mul_le_mul_of_nonneg_right h1 hpos
    _ = (1 + x ^ 2)⁻¹ := by rw [one_mul]

/-- Finite integrals of the absolutely-integrable second term tend to its Lebesgue integral. -/
lemma sin_x_mul_inv_tendsto_Ioi (a : ℝ) :
    Tendsto (fun T : ℝ => ∫ x in (0 : ℝ)..T, Real.sin (a * x) / (x * (1 + x ^ 2)))
      atTop (𝓝 (∫ x in Ioi (0 : ℝ), Real.sin (a * x) / (x * (1 + x ^ 2)))) := by
  simpa using (MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ))
    (f := fun x : ℝ => Real.sin (a * x) / (x * (1 + x ^ 2))) (μ := volume)
    (sin_x_mul_inv_integrableOn a) tendsto_id)

/-- Finite integrals of `cos(a·x)/(1+x²)` tend to their Lebesgue integral `(π/2)e^{−|a|}`. -/
lemma cos_one_add_sq_tendsto_Ioi (a : ℝ) :
    Tendsto (fun T : ℝ => ∫ x in (0 : ℝ)..T, Real.cos (a * x) / (1 + x ^ 2))
      atTop (𝓝 ((Real.pi / 2) * Real.exp (-|a|))) := by
  have h := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ))
    (f := fun x : ℝ => Real.cos (a * x) / (1 + x ^ 2)) (μ := volume)
    (cos_one_add_sq_integrableOn a) tendsto_id
  rw [cos_inv_one_add_sq_Ioi] at h
  exact h

/-! ### Differentiation (in the scale) of the finite-range sine integrals -/

/-- `x ↦ (1+x²)⁻¹` is continuous. -/
lemma cont_one_add_sq_inv : Continuous (fun t : ℝ => (1 + t ^ 2)⁻¹) := by
  refine Continuous.inv₀ (by fun_prop) ?_
  intro t
  nlinarith [sq_nonneg t]

/-- `|cos(a·x)/(1+x²)| ≤ (1+x²)⁻¹`. -/
lemma abs_cos_div_le_inv (s x : ℝ) : |Real.cos (s * x) / (1 + x ^ 2)| ≤ (1 + x ^ 2)⁻¹ := by
  have h1 : |Real.cos (s * x)| ≤ 1 := Real.abs_cos_le_one (s * x)
  have hpos : 0 ≤ (1 + x ^ 2)⁻¹ := inv_nonneg.mpr (by nlinarith [sq_nonneg x])
  calc
    |Real.cos (s * x) / (1 + x ^ 2)| = |Real.cos (s * x)| * (1 + x ^ 2)⁻¹ := by
      rw [abs_div, abs_of_nonneg (show 0 ≤ (1 + x ^ 2 : ℝ) by nlinarith [sq_nonneg x])]
      ring
    _ ≤ 1 * (1 + x ^ 2)⁻¹ := mul_le_mul_of_nonneg_right h1 hpos
    _ = (1 + x ^ 2)⁻¹ := by rw [one_mul]

/-- `x ↦ cos(a·x)/(1+x²)` is continuous. -/
lemma cos_div_cont (a : ℝ) : Continuous (fun x : ℝ => Real.cos (a * x) / (1 + x ^ 2)) := by
  refine Continuous.div (by fun_prop) (by fun_prop) ?_
  intro x
  nlinarith [sq_nonneg x]

/-- `‖cos(a·x)/(1+x²)‖ ≤ (1+x²)⁻¹`. -/
lemma norm_cos_div_le (a x : ℝ) : ‖Real.cos (a * x) / (1 + x ^ 2)‖ ≤ (1 + x ^ 2)⁻¹ := by
  rw [Real.norm_eq_abs]
  exact abs_cos_div_le_inv a x

/-- `d/da ∫_0^M sin(a·x)/(x(1+x²)) dx = ∫_0^M cos(a·x)/(1+x²) dx`, `M ≥ 0`. -/
lemma deriv_finite_sin_mul (M : ℝ) (hM : 0 ≤ M) (a : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ x in (0 : ℝ)..M, Real.sin (s * x) / (x * (1 + x ^ 2)))
      (∫ x in (0 : ℝ)..M, Real.cos (a * x) / (1 + x ^ 2)) a := by
  by_cases hM0 : M = 0
  · subst M
    have hfun : (fun s : ℝ => ∫ x in (0 : ℝ)..0, Real.sin (s * x) / (x * (1 + x ^ 2))) =
        fun _ : ℝ => 0 := by
      funext s
      simp
    have hval : (∫ x in (0 : ℝ)..0, Real.cos (a * x) / (1 + x ^ 2)) = 0 := by simp
    rw [hfun, hval]
    exact hasDerivAt_const a (0 : ℝ)
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    let F : ℝ → ℝ → ℝ := fun x t => Real.sin (x * t) / (t * (1 + t ^ 2))
    let F' : ℝ → ℝ → ℝ := fun x t => Real.cos (x * t) / (1 + t ^ 2)
    let bound : ℝ → ℝ := fun t => (1 + t ^ 2)⁻¹
    have huIoc : Set.uIoc (0 : ℝ) M = Set.Ioc (0 : ℝ) M := Set.uIoc_of_le hM
    have hF_meas_all : ∀ x : ℝ, AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc 0 M)) := by
      intro x
      refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc)
      intro t ht
      have ht0 : t ≠ 0 := by
        have ht' : t ∈ Set.Ioc (0 : ℝ) M := by simpa [huIoc] using ht
        exact ne_of_gt (Set.mem_Ioc.mp ht').1
      have hc_sin : ContinuousAt (fun u : ℝ => Real.sin (x * u)) t := by fun_prop
      have hc_den : ContinuousAt (fun u : ℝ => u * (1 + u ^ 2)) t := by fun_prop
      have hden : (t * (1 + t ^ 2)) ≠ 0 := mul_ne_zero ht0 (by nlinarith [sq_nonneg t])
      dsimp [F]
      exact (hc_sin.div hc_den hden).continuousWithinAt
    have hF_meas : ∀ᶠ x in 𝓝 a, AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc 0 M)) :=
      Eventually.of_forall hF_meas_all
    have hF_int : IntervalIntegrable (F a) volume 0 M := by
      rw [intervalIntegrable_iff]
      rw [huIoc]
      have hsub : Set.Ioc (0 : ℝ) M ⊆ Ioi (0 : ℝ) := by
        intro t ht
        exact Set.mem_Ioi.mpr (Set.mem_Ioc.mp ht).1
      exact (sin_x_mul_inv_integrableOn a).mono_set hsub
    have hF'_meas : AEStronglyMeasurable (F' a) (volume.restrict (Set.uIoc 0 M)) := by
      dsimp [F']
      exact (cos_div_cont a).aestronglyMeasurable
    have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 M → ∀ x ∈ Set.univ, ‖F' x t‖ ≤ bound t := by
      filter_upwards with t
      intro htmem x hxuniv
      dsimp [F', bound]
      exact norm_cos_div_le x t
    have bound_int : IntervalIntegrable bound volume 0 M :=
      (cont_one_add_sq_inv).intervalIntegrable (μ := volume) 0 M
    have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 M → ∀ x ∈ Set.univ, HasDerivAt (fun y => F y t) (F' x t) x := by
      filter_upwards with t
      intro htmem x hxuniv
      have ht0 : t ≠ 0 := by
        have ht' : t ∈ Set.Ioc (0 : ℝ) M := by simpa [huIoc] using htmem
        exact ne_of_gt (Set.mem_Ioc.mp ht').1
      have hlin0 : HasDerivAt (fun u : ℝ => t * u) t x := by
        simpa using (hasDerivAt_id x).const_mul t
      have hlin : HasDerivAt (fun u : ℝ => u * t) t x := by
        convert hlin0 using 1
        ext u
        ring
      have hnum : HasDerivAt (Real.sin ∘ (fun u : ℝ => u * t)) (Real.cos (x * t) * t) x := by
        exact HasDerivAt.comp x (Real.hasDerivAt_sin (x * t)) hlin
      have hdiv : HasDerivAt (fun u : ℝ => Real.sin (u * t) / (t * (1 + t ^ 2)))
          (Real.cos (x * t) * t / (t * (1 + t ^ 2))) x := by
        simpa using hnum.div_const (t * (1 + t ^ 2))
      dsimp [F, F']
      convert hdiv using 1
      field_simp [ht0]
    have hres := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (𝕜 := ℝ) (E := ℝ) (μ := volume) (x₀ := a) (s := Set.univ) (a := 0) (b := M)
      (F := F) (F' := F') (bound := bound)
      (by simp : Set.univ ∈ 𝓝 a) hF_meas hF_int hF'_meas h_bound bound_int h_diff
    simpa [F, F'] using hres.2

/-- `a ↦ ∫_0^M cos(a·x)/(1+x²) dx` is continuous, for `M ≥ 0`. -/
lemma continuous_finite_cos (M : ℝ) (hM : 0 ≤ M) :
    Continuous (fun s : ℝ => ∫ x in (0 : ℝ)..M, Real.cos (s * x) / (1 + x ^ 2)) := by
  rw [continuous_iff_continuousAt]
  intro a
  let F : ℝ → ℝ → ℝ := fun s x => Real.cos (s * x) / (1 + x ^ 2)
  have hF_meas : ∀ᶠ s in 𝓝 a, AEStronglyMeasurable (F s) (volume.restrict (Set.uIoc 0 M)) := by
    refine Eventually.of_forall (fun s => ?_)
    dsimp [F]
    exact (cos_div_cont s).aestronglyMeasurable
  have h_bound : ∀ᶠ s in 𝓝 a, ∀ᵐ x ∂volume, x ∈ Set.uIoc 0 M → ‖F s x‖ ≤ (1 + x ^ 2)⁻¹ := by
    refine Eventually.of_forall (fun s => ?_)
    filter_upwards with x
    intro hxmem
    dsimp [F]
    exact norm_cos_div_le s x
  have bound_int : IntervalIntegrable (fun x : ℝ => (1 + x ^ 2)⁻¹) volume 0 M :=
    (cont_one_add_sq_inv).intervalIntegrable (μ := volume) 0 M
  have h_lim : ∀ᵐ x ∂volume, x ∈ Set.uIoc 0 M → Tendsto (fun s => F s x) (𝓝 a) (𝓝 (F a x)) := by
    filter_upwards with x
    intro hxmem
    dsimp [F]
    have hc : Continuous (fun s : ℝ => Real.cos (s * x) / (1 + x ^ 2)) := by
      refine Continuous.div (by fun_prop) (by fun_prop) ?_
      intro s
      nlinarith [sq_nonneg x]
    exact hc.continuousAt.tendsto
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (a := 0) (b := M) (l := 𝓝 a) (μ := volume)
    (bound := fun x : ℝ => (1 + x ^ 2)⁻¹) (F := F) (f := F a)
    hF_meas h_bound bound_int h_lim
  change Tendsto (fun s : ℝ => ∫ x in (0 : ℝ)..M, Real.cos (s * x) / (1 + x ^ 2)) (𝓝 a)
    (𝓝 (∫ x in (0 : ℝ)..M, Real.cos (a * x) / (1 + x ^ 2)))
  simpa [F] using h

/-- Bound on the absolute value of the finite `cos`-integral: `≤ π/2` for `M ≥ 0`. -/
lemma cosFin_abs_le (M : ℝ) (hM : 0 ≤ M) (s : ℝ) :
    |(∫ x in (0 : ℝ)..M, Real.cos (s * x) / (1 + x ^ 2))| ≤ Real.pi / 2 := by
  have h1 : |∫ x in (0 : ℝ)..M, Real.cos (s * x) / (1 + x ^ 2)| ≤
      ∫ x in (0 : ℝ)..M, |Real.cos (s * x) / (1 + x ^ 2)| :=
    intervalIntegral.abs_integral_le_integral_abs hM
  have hfi : IntervalIntegrable (fun x : ℝ => |Real.cos (s * x) / (1 + x ^ 2)|) volume (0 : ℝ) M := by
    exact ((cos_div_cont s).abs).intervalIntegrable (μ := volume) (0 : ℝ) M
  have hgi : IntervalIntegrable (fun x : ℝ => (1 + x ^ 2)⁻¹) volume (0 : ℝ) M := by
    exact (cont_one_add_sq_inv).intervalIntegrable (μ := volume) (0 : ℝ) M
  have h2 : (∫ x in (0 : ℝ)..M, |Real.cos (s * x) / (1 + x ^ 2)|) ≤
      ∫ x in (0 : ℝ)..M, (1 + x ^ 2)⁻¹ := by
    refine intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := M) hM hfi hgi ?_
    intro x hx
    exact abs_cos_div_le_inv s x
  have h3 : (∫ x in (0 : ℝ)..M, (1 + x ^ 2)⁻¹) = Real.arctan M := by
    simpa using (integral_inv_one_add_sq (a := (0 : ℝ)) (b := M))
  calc
    |∫ x in (0 : ℝ)..M, Real.cos (s * x) / (1 + x ^ 2)| ≤
        ∫ x in (0 : ℝ)..M, |Real.cos (s * x) / (1 + x ^ 2)| := h1
    _ ≤ ∫ x in (0 : ℝ)..M, (1 + x ^ 2)⁻¹ := h2
    _ = Real.arctan M := h3
    _ ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two M).le

/-- Fundamental identity: for `M ≥ 0`, `a ≥ 0`,
    ∫_0^M sin(a·x)/(x(1+x²)) dx = ∫_0^a [∫_0^M cos(s·x)/(1+x²) dx] ds . -/
lemma finite_sin_eq_integral_cos (M : ℝ) (hM : 0 ≤ M) (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in (0 : ℝ)..M, Real.sin (a * x) / (x * (1 + x ^ 2))) =
      ∫ s in (0 : ℝ)..a, (∫ x in (0 : ℝ)..M, Real.cos (s * x) / (1 + x ^ 2)) := by
  let f : ℝ → ℝ := fun s => ∫ x in (0 : ℝ)..M, Real.sin (s * x) / (x * (1 + x ^ 2))
  let f' : ℝ → ℝ := fun s => ∫ x in (0 : ℝ)..M, Real.cos (s * x) / (1 + x ^ 2)
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) a, HasDerivAt f (f' s) s := by
    intro s hs
    dsimp [f, f']
    exact deriv_finite_sin_mul M hM s
  have hint : IntervalIntegrable f' volume (0 : ℝ) a := by
    apply Continuous.intervalIntegrable (μ := volume)
    dsimp [f']
    exact continuous_finite_cos M hM
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := a)
    (f := f) (f' := f') hderiv hint
  have hf0 : f (0 : ℝ) = 0 := by
    dsimp [f]
    have hfun : (fun x : ℝ => Real.sin ((0 : ℝ) * x) / (x * (1 + x ^ 2))) = fun _ : ℝ => 0 := by
      funext x
      simp
    rw [hfun]
    simp
  calc
    (∫ x in (0 : ℝ)..M, Real.sin (a * x) / (x * (1 + x ^ 2))) = f a := by
      simp [f]
    _ = f a - f (0 : ℝ) := by rw [hf0, sub_zero]
    _ = ∫ s in (0 : ℝ)..a, f' s := hftc.symm
    _ = ∫ s in (0 : ℝ)..a, (∫ x in (0 : ℝ)..M, Real.cos (s * x) / (1 + x ^ 2)) := by
      simp [f']

/-- `∫_0^c e^{−s} ds = 1 − e^{−c}`. -/
lemma exp_neg_interval (c : ℝ) :
    (∫ s in (0 : ℝ)..c, Real.exp (-s)) = 1 - Real.exp (-c) := by
  calc
    (∫ s in (0 : ℝ)..c, Real.exp (-s)) = ∫ s in (-c)..(0 : ℝ), Real.exp s := by
      simpa using (intervalIntegral.integral_comp_neg (f := Real.exp) (a := (0 : ℝ)) (b := c))
    _ = Real.exp (0 : ℝ) - Real.exp (-c) := by simp
    _ = 1 - Real.exp (-c) := by rw [Real.exp_zero]


/-! ### Value of the full second term: `∫_{Ioi 0} sin(a·x)/(x(1+x²)) = (π/2)·sign a·(1−e^{−|a|})` -/

/-- For `c > 0`, `∫_{Ioi 0} sin(c·x)/(x(1+x²)) dx = (π/2)(1 − e^{−c})`. -/
lemma sin_x_mul_inv_Ioi_pos (c : ℝ) (hc : 0 < c) :
    (∫ x : ℝ in Ioi (0 : ℝ), Real.sin (c * x) / (x * (1 + x ^ 2))) =
      (Real.pi / 2) * (1 - Real.exp (-c)) := by
  let F : ℝ → ℝ → ℝ := fun M s => ∫ x in (0 : ℝ)..M, Real.cos (s * x) / (1 + x ^ 2)
  have hF_meas : ∀ᶠ M in atTop, AEStronglyMeasurable (fun s : ℝ => F M s) (volume.restrict (Set.uIoc 0 c)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
    apply Continuous.aestronglyMeasurable
    dsimp [F]
    exact continuous_finite_cos M hM
  have h_bound : ∀ᶠ M in atTop, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 c → ‖F M s‖ ≤ Real.pi / 2 := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
    filter_upwards with s
    intro hs
    dsimp [F]
    exact cosFin_abs_le M hM s
  have bound_int : IntervalIntegrable (fun s : ℝ => Real.pi / 2) volume (0 : ℝ) c := by
    exact intervalIntegrable_const
  have h_lim : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 c →
      Tendsto (fun M => F M s) atTop (𝓝 ((Real.pi / 2) * Real.exp (-|s|))) := by
    filter_upwards with s
    intro hs
    dsimp [F]
    exact cos_one_add_sq_tendsto_Ioi s
  have hdct := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (a := (0 : ℝ)) (b := c) (l := atTop) (μ := volume)
    (F := F) (f := fun s : ℝ => (Real.pi / 2) * Real.exp (-|s|))
    (bound := fun s : ℝ => Real.pi / 2)
    hF_meas h_bound bound_int h_lim
  have heq : (fun M : ℝ => ∫ x in (0 : ℝ)..M, Real.sin (c * x) / (x * (1 + x ^ 2))) =ᶠ[atTop]
      fun M : ℝ => ∫ s in (0 : ℝ)..c, F M s := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
    dsimp [F]
    exact finite_sin_eq_integral_cos M hM c hc.le
  have hE1 := (sin_x_mul_inv_tendsto_Ioi c).congr' heq
  have hdct' : Tendsto (fun M : ℝ => ∫ s in (0 : ℝ)..c, F M s) atTop
      (𝓝 (∫ s in (0 : ℝ)..c, (Real.pi / 2) * Real.exp (-|s|))) := by
    simpa using hdct
  have hval0 : (∫ s in (0 : ℝ)..c, (Real.pi / 2) * Real.exp (-|s|)) =
      ∫ x : ℝ in Ioi (0 : ℝ), Real.sin (c * x) / (x * (1 + x ^ 2)) := by
    exact tendsto_nhds_unique (f := fun M : ℝ => ∫ s in (0 : ℝ)..c, F M s) (l := atTop) hdct' hE1
  have hval : (∫ x : ℝ in Ioi (0 : ℝ), Real.sin (c * x) / (x * (1 + x ^ 2))) =
      ∫ s in (0 : ℝ)..c, (Real.pi / 2) * Real.exp (-|s|) := hval0.symm
  have hrew : (∫ s in (0 : ℝ)..c, (Real.pi / 2) * Real.exp (-|s|)) =
      (∫ s in (0 : ℝ)..c, (Real.pi / 2) * Real.exp (-s)) := by
    refine intervalIntegral.integral_congr ?_
    intro s hs
    have hs0 : 0 ≤ s := by
      have h : s ∈ Set.uIcc (0 : ℝ) c := hs
      rw [Set.uIcc_of_le hc.le] at h
      exact (Set.mem_Icc.mp h).1
    dsimp
    congr 1
    congr 1
    rw [abs_of_nonneg hs0]
  have hconst : (∫ s in (0 : ℝ)..c, (Real.pi / 2) * Real.exp (-s)) =
      (Real.pi / 2) * (∫ s in (0 : ℝ)..c, Real.exp (-s)) := by
    exact intervalIntegral.integral_const_mul (Real.pi / 2) (fun s : ℝ => Real.exp (-s))
  calc
    (∫ x : ℝ in Ioi (0 : ℝ), Real.sin (c * x) / (x * (1 + x ^ 2)))
        = ∫ s in (0 : ℝ)..c, (Real.pi / 2) * Real.exp (-|s|) := hval
    _ = (∫ s in (0 : ℝ)..c, (Real.pi / 2) * Real.exp (-s)) := hrew
    _ = (Real.pi / 2) * (∫ s in (0 : ℝ)..c, Real.exp (-s)) := hconst
    _ = (Real.pi / 2) * (1 - Real.exp (-c)) := by rw [exp_neg_interval]

/-- Oddness of the second term: `∫_{Ioi 0} sin(a·x)/(x(1+x²)) = −∫_{Ioi 0} sin((−a)·x)/(x(1+x²))`. -/
lemma sin_x_mul_inv_Ioi_odd (a : ℝ) :
    (∫ x : ℝ in Ioi (0 : ℝ), Real.sin (a * x) / (x * (1 + x ^ 2))) =
      - (∫ x : ℝ in Ioi (0 : ℝ), Real.sin ((-a) * x) / (x * (1 + x ^ 2))) := by
  calc
    (∫ x : ℝ in Ioi (0 : ℝ), Real.sin (a * x) / (x * (1 + x ^ 2)))
        = ∫ x : ℝ in Ioi (0 : ℝ), -(Real.sin ((-a) * x) / (x * (1 + x ^ 2))) := by
          refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
          congr 1
          have harg : a * x = -((-a) * x) := by ring
          rw [harg, Real.sin_neg]
          ring
    _ = - (∫ x : ℝ in Ioi (0 : ℝ), Real.sin ((-a) * x) / (x * (1 + x ^ 2))) := by
          simpa using (MeasureTheory.integral_neg (μ := volume.restrict (Ioi (0 : ℝ)))
            (f := fun x : ℝ => Real.sin ((-a) * x) / (x * (1 + x ^ 2))))

/-- `∫_{Ioi 0} sin(a·x)/(x(1+x²)) dx = (π/2)·sign a·(1 − e^{−|a|})` for `a ≠ 0`. -/
lemma sin_x_mul_inv_Ioi (a : ℝ) (ha : a ≠ 0) :
    (∫ x : ℝ in Ioi (0 : ℝ), Real.sin (a * x) / (x * (1 + x ^ 2))) =
      (Real.pi / 2) * Real.sign a * (1 - Real.exp (-|a|)) := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hc : 0 < -a := neg_pos.mpr hneg
    have hD := sin_x_mul_inv_Ioi_pos (-a) hc
    rw [sin_x_mul_inv_Ioi_odd a, hD]
    simp [Real.sign_of_neg hneg, abs_of_neg hneg]
  · have hD := sin_x_mul_inv_Ioi_pos a hpos
    rw [hD]
    simp [Real.sign_of_pos hpos, abs_of_pos hpos]

/-! ### Pointwise decomposition of the integrand (via the continuous `sinc`-functions) -/

/-- `x·sin(ax)/(1+x²) = a·sinc(ax) − a·sinc(ax)/(1+x²)` for `a ≠ 0`. -/
lemma sin_mul_one_add_sq_eq_sinc (a : ℝ) (ha : a ≠ 0) (x : ℝ) :
    x * Real.sin (a * x) / (1 + x ^ 2) =
      a * Real.sinc (a * x) - a * Real.sinc (a * x) / (1 + x ^ 2) := by
  by_cases hx : x = 0
  · subst x
    simp
  · have hbx : a * x ≠ 0 := mul_ne_zero ha hx
    have hs1 := Real.sinc_of_ne_zero hbx
    rw [hs1]
    field_simp [hbx]
    ring

/-- `x ↦ a·sinc(a·x)` is continuous. -/
lemma continuous_sinc_a (a : ℝ) : Continuous (fun x : ℝ => a * Real.sinc (a * x)) := by
  have hc : Continuous (fun x : ℝ => Real.sinc (a * x)) := Real.continuous_sinc.comp (by fun_prop)
  exact hc.const_mul a

/-- For `a ≠ 0`, `x ↦ a·sinc(a·x)/(1+x²)` is continuous. -/
lemma continuous_sinc_div (a : ℝ) : Continuous (fun x : ℝ => a * Real.sinc (a * x) / (1 + x ^ 2)) := by
  refine Continuous.div (continuous_sinc_a a) (by fun_prop) ?_
  intro x
  nlinarith [sq_nonneg x]

/-- Interval-integral replacement of `a·sinc(a·x)` by `sin(a·x)/x`. -/
lemma interval_sinc_sin (a : ℝ) (ha : a ≠ 0) (T : ℝ) :
    (∫ x in (0 : ℝ)..T, a * Real.sinc (a * x)) = ∫ x in (0 : ℝ)..T, Real.sin (a * x) / x := by
  refine intervalIntegral.integral_congr_ae ?_
  have hfull : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hfull] with x hx
  intro hmem
  have hbx : a * x ≠ 0 := mul_ne_zero ha hx
  have hs1 := Real.sinc_of_ne_zero hbx
  rw [hs1]
  field_simp [hx]

/-- Interval-integral replacement of `a·sinc(a·x)/(1+x²)` by `sin(a·x)/(x(1+x²))`. -/
lemma interval_sinc_sin_mul_inv (a : ℝ) (ha : a ≠ 0) (T : ℝ) :
    (∫ x in (0 : ℝ)..T, a * Real.sinc (a * x) / (1 + x ^ 2)) =
      ∫ x in (0 : ℝ)..T, Real.sin (a * x) / (x * (1 + x ^ 2)) := by
  refine intervalIntegral.integral_congr_ae ?_
  have hfull : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hfull] with x hx
  intro hmem
  have hbx : a * x ≠ 0 := mul_ne_zero ha hx
  have hs1 := Real.sinc_of_ne_zero hbx
  rw [hs1]
  field_simp [hx]

/-- The decomposition identity at the level of finite interval integrals:
    ∫_0^T x·sin(ax)/(1+x²) dx = ∫_0^T sin(ax)/x dx − ∫_0^T sin(ax)/(x(1+x²)) dx . -/
lemma sin_mul_one_add_sq_eq_sub (a : ℝ) (ha : a ≠ 0) (T : ℝ) :
    (∫ x in (0 : ℝ)..T, x * Real.sin (a * x) / (1 + x ^ 2)) =
      (∫ x in (0 : ℝ)..T, Real.sin (a * x) / x) -
        (∫ x in (0 : ℝ)..T, Real.sin (a * x) / (x * (1 + x ^ 2))) := by
  let g : ℝ → ℝ := fun x => a * Real.sinc (a * x)
  let h : ℝ → ℝ := fun x => a * Real.sinc (a * x) / (1 + x ^ 2)
  have hg_int : IntervalIntegrable g volume (0 : ℝ) T := by
    apply Continuous.intervalIntegrable (μ := volume)
    dsimp [g]
    exact continuous_sinc_a a
  have hh_int : IntervalIntegrable h volume (0 : ℝ) T := by
    apply Continuous.intervalIntegrable (μ := volume)
    dsimp [h]
    exact continuous_sinc_div a
  calc
    (∫ x in (0 : ℝ)..T, x * Real.sin (a * x) / (1 + x ^ 2))
        = ∫ x in (0 : ℝ)..T, (g x - h x) := by
          refine intervalIntegral.integral_congr ?_
          intro x hx
          dsimp [g, h]
          exact sin_mul_one_add_sq_eq_sinc a ha x
    _ = (∫ x in (0 : ℝ)..T, g x) - ∫ x in (0 : ℝ)..T, h x := by
          exact intervalIntegral.integral_sub hg_int hh_int
    _ = (∫ x in (0 : ℝ)..T, Real.sin (a * x) / x) -
          ∫ x in (0 : ℝ)..T, Real.sin (a * x) / (x * (1 + x ^ 2)) := by
          rw [interval_sinc_sin a ha T, interval_sinc_sin_mul_inv a ha T]

/-! ### Assembling the two convergent pieces -/

/-- Limit of the full integral (positive `a`). -/
lemma sin_mul_one_add_sq_tendsto_pos (a : ℝ) (ha : 0 < a) :
    Tendsto (fun T : ℝ => ∫ x in (0 : ℝ)..T, x * Real.sin (a * x) / (1 + x ^ 2))
      atTop (𝓝 ((Real.pi / 2) * Real.exp (-a))) := by
  have hsplit : (fun T : ℝ => ∫ x in (0 : ℝ)..T, x * Real.sin (a * x) / (1 + x ^ 2)) =ᶠ[atTop]
      fun T : ℝ => (∫ x in (0 : ℝ)..T, Real.sin (a * x) / x) -
        (∫ x in (0 : ℝ)..T, Real.sin (a * x) / (x * (1 + x ^ 2))) := by
    exact Eventually.of_forall (fun T => sin_mul_one_add_sq_eq_sub a ha.ne' T)
  have h1 : Tendsto (fun T : ℝ => ∫ x in (0 : ℝ)..T, Real.sin (a * x) / x) atTop (𝓝 (Real.pi / 2)) := sin_scaled_tendsto a ha
  have h2conv := sin_x_mul_inv_tendsto_Ioi a
  have h2 : Tendsto (fun T : ℝ => ∫ x in (0 : ℝ)..T, Real.sin (a * x) / (x * (1 + x ^ 2)))
      atTop (𝓝 ((Real.pi / 2) * Real.sign a * (1 - Real.exp (-|a|)))) := by
    simpa [sin_x_mul_inv_Ioi a ha.ne'] using h2conv
  have hsub := h1.sub h2
  have hval : Real.pi / 2 - (Real.pi / 2) * Real.sign a * (1 - Real.exp (-|a|)) =
      (Real.pi / 2) * Real.exp (-a) := by
    rw [Real.sign_of_pos ha, abs_of_pos ha]
    ring
  have hsub' : Tendsto (fun T : ℝ => (∫ x in (0 : ℝ)..T, Real.sin (a * x) / x) -
        (∫ x in (0 : ℝ)..T, Real.sin (a * x) / (x * (1 + x ^ 2)))) atTop
      (𝓝 ((Real.pi / 2) * Real.exp (-a))) := by
    simpa [hval] using hsub
  exact hsub'.congr' hsplit.symm

/-- Limit of the full integral (negative `a`). -/
lemma sin_mul_one_add_sq_tendsto_neg (a : ℝ) (ha : a < 0) :
    Tendsto (fun T : ℝ => ∫ x in (0 : ℝ)..T, x * Real.sin (a * x) / (1 + x ^ 2))
      atTop (𝓝 (-((Real.pi / 2) * Real.exp a))) := by
  have hsplit : (fun T : ℝ => ∫ x in (0 : ℝ)..T, x * Real.sin (a * x) / (1 + x ^ 2)) =ᶠ[atTop]
      fun T : ℝ => (∫ x in (0 : ℝ)..T, Real.sin (a * x) / x) -
        (∫ x in (0 : ℝ)..T, Real.sin (a * x) / (x * (1 + x ^ 2))) := by
    exact Eventually.of_forall (fun T => sin_mul_one_add_sq_eq_sub a (ne_of_lt ha) T)
  have h1 : Tendsto (fun T : ℝ => ∫ x in (0 : ℝ)..T, Real.sin (a * x) / x) atTop (𝓝 (-(Real.pi / 2))) := sin_scaled_tendsto_neg a ha
  have h2conv := sin_x_mul_inv_tendsto_Ioi a
  have h2 : Tendsto (fun T : ℝ => ∫ x in (0 : ℝ)..T, Real.sin (a * x) / (x * (1 + x ^ 2)))
      atTop (𝓝 ((Real.pi / 2) * Real.sign a * (1 - Real.exp (-|a|)))) := by
    simpa [sin_x_mul_inv_Ioi a (ne_of_lt ha)] using h2conv
  have hsub := h1.sub h2
  have hval : -(Real.pi / 2) - (Real.pi / 2) * Real.sign a * (1 - Real.exp (-|a|)) =
      -((Real.pi / 2) * Real.exp a) := by
    rw [Real.sign_of_neg ha, abs_of_neg ha]
    ring
  have hsub' : Tendsto (fun T : ℝ => (∫ x in (0 : ℝ)..T, Real.sin (a * x) / x) -
        (∫ x in (0 : ℝ)..T, Real.sin (a * x) / (x * (1 + x ^ 2)))) atTop
      (𝓝 (-((Real.pi / 2) * Real.exp a))) := by
    simpa [hval] using hsub
  exact hsub'.congr' hsplit.symm

/-- `lim_{T→∞} ∫_0^T x·sin(a·x)/(1+x²) dx = (π/2)·sign(a)·e^{−|a|}` for `a ≠ 0`. -/
theorem sin_mul_one_add_sq_tendsto (a : ℝ) (ha : a ≠ 0) :
    Tendsto (fun T : ℝ => ∫ x in (0 : ℝ)..T, x * Real.sin (a * x) / (1 + x ^ 2))
      atTop (𝓝 ((Real.pi / 2) * Real.sign a * Real.exp (-|a|))) := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have h := sin_mul_one_add_sq_tendsto_neg a hneg
    have hval : -((Real.pi / 2) * Real.exp a) = (Real.pi / 2) * Real.sign a * Real.exp (-|a|) := by
      rw [Real.sign_of_neg hneg, abs_of_neg hneg]
      ring
    simpa [hval] using h
  · have h := sin_mul_one_add_sq_tendsto_pos a hpos
    have hval : (Real.pi / 2) * Real.exp (-a) = (Real.pi / 2) * Real.sign a * Real.exp (-|a|) := by
      rw [Real.sign_of_pos hpos, abs_of_pos hpos]
      ring
    simpa [hval] using h

end PerronKernel

end Commons.Analysis.Fourier


/-!
# Truncated Perron kernel bound (child task)

Task: prove `perron_kernel_bound` below.  Do **not** weaken the statement.
-/

open Polynomial Finset Real Complex Filter ArithmeticFunction MeasureTheory
open scoped ComplexConjugate Topology Real

namespace Commons.Analysis.Fourier
noncomputable section

/-! ## Complex identities for the Perron integrand -/

/-- `(1 + i·t)⁻¹ = (1 - i·t)/(1 + t²)`. -/
lemma one_add_I_mul_inv (t : ℝ) :
    (1 + I * (t : ℂ))⁻¹ = (1 - I * (t : ℂ)) * (((1 + t ^ 2 : ℝ) : ℂ)⁻¹) := by
  have hprod : (1 + I * (t : ℂ)) * ((1 : ℂ) - I * (t : ℂ)) = (((1 + t ^ 2 : ℝ) : ℂ)) := by
    have hi : (I : ℂ) ^ 2 = -1 := by simp
    calc
      (1 + I * (t : ℂ)) * (1 - I * (t : ℂ)) = (1 : ℂ) - (I * (t : ℂ)) ^ 2 := by ring
      _ = (1 : ℂ) - (I : ℂ) ^ 2 * (t : ℂ) ^ 2 := by ring
      _ = ((1 + t ^ 2 : ℝ) : ℂ) := by
        rw [hi]
        simp
  have hnnz : (((1 + t ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (show (1 + t ^ 2 : ℝ) ≠ 0 by nlinarith)
  have hnnz2 : (1 + I * (t : ℂ)) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hprod
    exact hnnz hprod.symm
  have hnnz3 : (1 - I * (t : ℂ)) ≠ 0 := by
    intro hz
    apply hnnz2
    have hc : (starRingEnd ℂ) (1 - I * (t : ℂ)) = 1 + I * (t : ℂ) := by simp
    rw [← hc]
    rw [hz]
    simp
  field_simp [hprod, hnnz2, hnnz3]
  exact hprod.symm

/-- `e^{iαt} (1 - it) = (cos(αt) + t·sin(αt)) + i·(sin(αt) - t·cos(αt))`. -/
lemma exp_times_conj (α t : ℝ) :
    cexp (I * (α * t : ℂ)) * (1 - I * (t : ℂ))
      = ((Real.cos (α * t) + t * Real.sin (α * t) : ℝ) : ℂ)
          + I * ((Real.sin (α * t) - t * Real.cos (α * t) : ℝ) : ℂ) := by
  rw [mul_comm I (α * t : ℂ), Complex.exp_mul_I]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_cos (α * t), ← Complex.ofReal_sin (α * t)]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im]
    ring_nf
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im]
    ring_nf

lemma ofReal_mul_inv_eq (x y : ℝ) :
    ((x : ℂ) * ((y : ℂ)⁻¹)) = ((x / y : ℝ) : ℂ) := by
  by_cases hy : y = 0
  · simp [hy]
  · rw [← Complex.ofReal_inv]
    rw [← Complex.ofReal_mul]
    congr 1

/-- Real and imaginary parts of the Perron integrand. -/
lemma integrand_decomp (α t : ℝ) :
    cexp (I * (α * t : ℂ)) / (1 + I * (t : ℂ))
      = (((Real.cos (α * t) + t * Real.sin (α * t)) / (1 + t ^ 2) : ℝ) : ℂ)
          + I * (((Real.sin (α * t) - t * Real.cos (α * t)) / (1 + t ^ 2) : ℝ) : ℂ) := by
  rw [div_eq_mul_inv]
  rw [one_add_I_mul_inv]
  rw [← mul_assoc]
  rw [exp_times_conj α t]
  rw [add_mul]
  congr 1
  · rw [ofReal_mul_inv_eq]
  · rw [mul_assoc]
    rw [ofReal_mul_inv_eq]

/-! ## Real-part reduction of the truncated Perron kernel -/

/-- Even/odd decomposition of the real part of the integrand. -/
noncomputable def pfun (α t : ℝ) : ℝ := (Real.cos (α * t) + t * Real.sin (α * t)) / (1 + t ^ 2)
/-- Even/odd decomposition of the imaginary part of the integrand. -/
noncomputable def qfun (α t : ℝ) : ℝ := (Real.sin (α * t) - t * Real.cos (α * t)) / (1 + t ^ 2)

lemma continuous_pfun (α : ℝ) : Continuous (pfun α) := by
  unfold pfun
  have hnum : Continuous fun t : ℝ => Real.cos (α * t) + t * Real.sin (α * t) := by fun_prop
  have hden : Continuous fun t : ℝ => (1 : ℝ) + t ^ 2 := by fun_prop
  have hdenz : ∀ t : ℝ, (1 : ℝ) + t ^ 2 ≠ 0 := by intro t; nlinarith [sq_nonneg t]
  exact Continuous.div₀ hnum hden hdenz

lemma continuous_qfun (α : ℝ) : Continuous (qfun α) := by
  unfold qfun
  have hnum : Continuous fun t : ℝ => Real.sin (α * t) - t * Real.cos (α * t) := by fun_prop
  have hden : Continuous fun t : ℝ => (1 : ℝ) + t ^ 2 := by fun_prop
  have hdenz : ∀ t : ℝ, (1 : ℝ) + t ^ 2 ≠ 0 := by intro t; nlinarith [sq_nonneg t]
  exact Continuous.div₀ hnum hden hdenz

lemma pfun_even (α : ℝ) : ∀ t : ℝ, pfun α (-t) = pfun α t := by
  intro t; unfold pfun
  have h1 : α * (-t) = -(α * t) := by ring
  have hd : (1 + (-t) ^ 2 : ℝ) = 1 + t ^ 2 := by ring
  rw [h1, Real.cos_neg, Real.sin_neg, hd]; ring

lemma qfun_odd (α : ℝ) : ∀ t : ℝ, qfun α (-t) = -qfun α t := by
  intro t; unfold qfun
  have h1 : α * (-t) = -(α * t) := by ring
  have hd : (1 + (-t) ^ 2 : ℝ) = 1 + t ^ 2 := by ring
  rw [h1, Real.cos_neg, Real.sin_neg, hd]; ring

/-- The integral of an odd continuous function over `[-T,T]` vanishes. -/
lemma integral_real_odd_zero (f : ℝ → ℝ) (hf : Continuous f) (ho : ∀ x, f (-x) = - f x) (T : ℝ) :
    (∫ x in -T..T, f x) = 0 := by
  have h1 : (∫ x in -T..T, f x) = (∫ x in -T..T, f (-x)) := by
    rw [intervalIntegral.integral_comp_neg]
    congr 2 <;> ring
  have h2 : (∫ x in -T..T, f x) = - (∫ x in -T..T, f x) := by
    calc
      (∫ x in -T..T, f x) = (∫ x in -T..T, f (-x)) := h1
      _ = (∫ x in -T..T, - f x) := by
        refine intervalIntegral.integral_congr (μ := volume) ?_
        intro x hx; exact ho x
      _ = - (∫ x in -T..T, f x) := intervalIntegral.integral_neg (f := f)
  linarith

/-- The integral of an even continuous function over `[-T,T]` is twice the half integral. -/
lemma integral_real_even_two (f : ℝ → ℝ) (hf : Continuous f) (he : ∀ x, f (-x) = f x) (T : ℝ) :
    (∫ x in -T..T, f x) = 2 * (∫ x in 0..T, f x) := by
  have hadj : (∫ x in -T..0, f x) + ∫ x in 0..T, f x = ∫ x in -T..T, f x := by
    exact intervalIntegral.integral_add_adjacent_intervals (μ := volume) (f := f) (a := -T)
      (b := (0:ℝ)) (c := T) (hf.intervalIntegrable (-T) 0) (hf.intervalIntegrable 0 T)
  rw [← hadj]
  congr 1
  have hneg : (∫ x in -T..0, f x) = (∫ x in 0..T, f (-x)) := by
    have h := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := T) f
    rw [neg_zero] at h
    exact h.symm
  rw [hneg]
  have hc : (∫ x in 0..T, f (-x)) = (∫ x in 0..T, f x) := by
    apply intervalIntegral.integral_congr (μ := volume)
    intro x hx; exact he x
  rw [hc]
  ring

lemma continuous_kernA (α : ℝ) : Continuous fun t => Real.cos (α * t) / (1 + t ^ 2) := by
  have hnum : Continuous fun t : ℝ => Real.cos (α * t) := by fun_prop
  have hden : Continuous fun t : ℝ => (1 : ℝ) + t ^ 2 := by fun_prop
  have hdenz : ∀ t : ℝ, (1 : ℝ) + t ^ 2 ≠ 0 := by intro t; nlinarith [sq_nonneg t]
  exact Continuous.div₀ hnum hden hdenz

lemma continuous_kernB (α : ℝ) : Continuous fun t => t * Real.sin (α * t) / (1 + t ^ 2) := by
  have hnum : Continuous fun t : ℝ => t * Real.sin (α * t) := by fun_prop
  have hden : Continuous fun t : ℝ => (1 : ℝ) + t ^ 2 := by fun_prop
  have hdenz : ∀ t : ℝ, (1 : ℝ) + t ^ 2 ≠ 0 := by intro t; nlinarith [sq_nonneg t]
  exact Continuous.div₀ hnum hden hdenz

/-- The truncated Perron kernel. -/
noncomputable def kern (T α : ℝ) : ℂ :=
  ∫ t in -T..T, cexp (I * (α * t)) / (1 + I * t)

/-- Cosine part of the kernel, `∫_0^T cos(αt)/(1+t²) dt`. -/
noncomputable def kernA (T α : ℝ) : ℝ := ∫ t in (0 : ℝ)..T, Real.cos (α * t) / (1 + t ^ 2)
/-- Sine part of the kernel, `∫_0^T t·sin(αt)/(1+t²) dt`. -/
noncomputable def kernB (T α : ℝ) : ℝ := ∫ t in (0 : ℝ)..T, t * Real.sin (α * t) / (1 + t ^ 2)

lemma integrand_decomp_pq (α : ℝ) : ∀ t : ℝ,
    cexp (I * (α * t : ℂ)) / (1 + I * (t : ℂ)) = ((pfun α t : ℝ) : ℂ) + I * ((qfun α t : ℝ) : ℂ) := by
  intro t
  unfold pfun qfun
  exact integrand_decomp α t

lemma pfun_integral_eq (T α : ℝ) : (∫ t in 0..T, pfun α t) = kernA T α + kernB T α := by
  unfold kernA kernB pfun
  have hsplit : (fun t : ℝ => (Real.cos (α * t) + t * Real.sin (α * t)) / (1 + t ^ 2))
      = (fun t : ℝ => Real.cos (α * t) / (1 + t ^ 2) + t * Real.sin (α * t) / (1 + t ^ 2)) := by
    funext t
    rw [add_div]
  rw [hsplit]
  have hfi : IntervalIntegrable (fun t : ℝ => Real.cos (α * t) / (1 + t ^ 2)) volume 0 T :=
    (continuous_kernA α).intervalIntegrable _ _
  have hgi : IntervalIntegrable (fun t : ℝ => t * Real.sin (α * t) / (1 + t ^ 2)) volume 0 T :=
    (continuous_kernB α).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (μ := volume) (a := (0 : ℝ)) (b := T) hfi hgi]

/-- `K(T,α) = 2·(∫_0^T cos(αt)/(1+t²) dt + ∫_0^T t·sin(αt)/(1+t²) dt)`, as a real number. -/
lemma kern_eq_two_A_B (T α : ℝ) : kern T α = ((2 * (kernA T α + kernB T α) : ℝ) : ℂ) := by
  unfold kern
  have hint : (fun t : ℝ => cexp (I * (α * t : ℂ)) / (1 + I * (t : ℂ))) =
      (fun t : ℝ => ((pfun α t : ℝ) : ℂ) + I * ((qfun α t : ℝ) : ℂ)) := by
    funext t
    exact integrand_decomp_pq α t
  rw [hint]
  have hcf : IntervalIntegrable (fun t => (((pfun α t : ℝ) : ℂ))) volume (-T) T :=
    (continuous_ofReal.comp (continuous_pfun α)).intervalIntegrable _ _
  have hcg : IntervalIntegrable (fun t => (I * (((qfun α t : ℝ) : ℂ)))) volume (-T) T := by
    exact ((continuous_const.mul (continuous_ofReal.comp (continuous_qfun α)))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (μ := volume) (a := -T) (b := T) hcf hcg]
  have hq0 : (∫ t in -T..T, qfun α t) = 0 := integral_real_odd_zero (qfun α) (continuous_qfun α) (qfun_odd α) T
  rw [intervalIntegral.integral_const_mul]
  simp_rw [intervalIntegral.integral_ofReal]
  rw [hq0]
  simp
  have hp : (∫ t in -T..T, pfun α t) = 2 * (∫ t in 0..T, pfun α t) :=
    integral_real_even_two (pfun α) (continuous_pfun α) (pfun_even α) T
  rw [hp]
  rw [pfun_integral_eq]
  simp

/-! Uniform bounds on the small-`|α|T` region are imported from
`Submission.RegionBound` (`PerronKernel.kern_region_bound`, `PerronKernel.abs_kernA_le`, `PerronKernel.abs_kernB_le`). -/

/-! ## The limiting value as a real number -/

/-- Real value of the limiting kernel: `2π·e^{−α}` for `α > 0` and `0` for `α ≤ 0`. -/
noncomputable def kernVal (α : ℝ) : ℝ := if 0 < α then 2 * Real.pi * Real.exp (-α) else 0

lemma kernVal_of_pos {α : ℝ} (hα : 0 < α) : kernVal α = 2 * Real.pi * Real.exp (-α) := by
  simp [kernVal, hα]

lemma kernVal_of_nonpos {α : ℝ} (hα : α ≤ 0) : kernVal α = 0 := by
  simp [kernVal, hα]

lemma kernVal_abs_le (α : ℝ) : |kernVal α| ≤ 2 * Real.pi := by
  by_cases hα : 0 < α
  · rw [kernVal_of_pos hα]
    have he1 : Real.exp (-α) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    calc
      |2 * Real.pi * Real.exp (-α)| = 2 * Real.pi * Real.exp (-α) := by
        rw [abs_mul, abs_mul]
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        rw [abs_of_nonneg Real.pi_pos.le]
        rw [abs_of_nonneg (Real.exp_pos (-α)).le]
      _ ≤ 2 * Real.pi * 1 := by gcongr
      _ = 2 * Real.pi := by ring
  · rw [kernVal_of_nonpos (le_of_not_gt hα)]
    simp
    nlinarith [Real.pi_pos]

/-- The complex `if`-value equals the real value lifted to `ℂ`. -/
lemma value_eq_ofReal (α : ℝ) :
    (if 0 < α then (2 * π) * cexp (-α) else 0) = ((kernVal α : ℝ) : ℂ) := by
  by_cases hα : 0 < α
  · rw [if_pos hα, kernVal_of_pos hα]
    have hx : (2 * π : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by norm_num
    rw [hx]
    have he : cexp (-(α : ℂ)) = ((Real.exp (-α) : ℝ) : ℂ) := by
      rw [show -(α : ℂ) = (↑(-α) : ℂ) by simp]
      rw [Complex.ofReal_exp]
    rw [he]
    norm_num
  · rw [if_neg hα, kernVal_of_nonpos (le_of_not_gt hα)]
    simp

/-- Norm of the difference of two real lifts. -/
lemma norm_ofReal_sub (x y : ℝ) : ‖(x : ℂ) - (y : ℂ)‖ = |x - y| := by
  rw [← Complex.ofReal_sub]
  exact RCLike.norm_ofReal (x - y)

/-! ## Kernel difference tail -/

/-- `∫_T^R cos(αt)/(1+t²) = kernA R − kernA T` and similar splittings. -/
lemma kernA_sub (T R α : ℝ) : kernA R α - kernA T α =
    ∫ t in T..R, Real.cos (α * t) / (1 + t ^ 2) := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (f := fun t : ℝ => Real.cos (α * t) / (1 + t ^ 2)) (a := (0 : ℝ)) (b := T) (c := R)
    ((continuous_kernA α).intervalIntegrable 0 T) ((continuous_kernA α).intervalIntegrable T R)
  have h_eq : kernA T α + (∫ t in T..R, Real.cos (α * t) / (1 + t ^ 2)) = kernA R α := by
    simpa [kernA] using h1
  linarith

lemma kernB_sub (T R α : ℝ) : kernB R α - kernB T α =
    ∫ t in T..R, t * Real.sin (α * t) / (1 + t ^ 2) := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (f := fun t : ℝ => t * Real.sin (α * t) / (1 + t ^ 2)) (a := (0 : ℝ)) (b := T) (c := R)
    ((continuous_kernB α).intervalIntegrable 0 T) ((continuous_kernB α).intervalIntegrable T R)
  have h_eq : kernB T α + (∫ t in T..R, t * Real.sin (α * t) / (1 + t ^ 2)) = kernB R α := by
    simpa [kernB] using h1
  linarith

/-- `∫_T^R pfun = (kernA R − kernA T) + (kernB R − kernB T)`. -/
lemma pfun_integral_tail (T R α : ℝ) :
    (∫ t in T..R, pfun α t) = (kernA R α - kernA T α) + (kernB R α - kernB T α) := by
  have hsplit : (fun t : ℝ => pfun α t) =
      (fun t : ℝ => Real.cos (α * t) / (1 + t ^ 2) + t * Real.sin (α * t) / (1 + t ^ 2)) := by
    funext t
    unfold pfun
    rw [add_div]
  rw [hsplit]
  have hfi : IntervalIntegrable (fun t : ℝ => Real.cos (α * t) / (1 + t ^ 2)) volume T R :=
    (continuous_kernA α).intervalIntegrable T R
  have hgi : IntervalIntegrable (fun t : ℝ => t * Real.sin (α * t) / (1 + t ^ 2)) volume T R :=
    (continuous_kernB α).intervalIntegrable T R
  rw [intervalIntegral.integral_add (μ := volume) (a := T) (b := R) hfi hgi]
  rw [kernA_sub, kernB_sub]

/-- `K(R,α) − K(T,α) = 2·∫_T^R pfun(α,t)`, real lift. -/
lemma kern_sub_eq_ofReal (T R α : ℝ) :
    kern R α - kern T α = ((2 * (∫ t in T..R, pfun α t) : ℝ) : ℂ) := by
  rw [kern_eq_two_A_B R α, kern_eq_two_A_B T α]
  rw [pfun_integral_tail T R α]
  -- push ofReal arithmetic
  simp
  ring

/-- Real part of the complex integrand equals `pfun`. -/
lemma scale_cast (t a b : ℝ) :
    (a + I * (b : ℂ)) * (((1 + t ^ 2 : ℝ) : ℂ)⁻¹) =
      ((a * ((1 + t ^ 2 : ℝ)⁻¹) : ℝ) : ℂ) + I * ((b * ((1 + t ^ 2 : ℝ)⁻¹) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_mul_re, Complex.I_mul_im]
    rw [show (((1 + t ^ 2 : ℝ) : ℂ)⁻¹) = (↑(((1 + t ^ 2 : ℝ)⁻¹)) : ℂ) by rw [Complex.ofReal_inv]]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_mul_re, Complex.I_mul_im,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
    ring
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_mul_re, Complex.I_mul_im]
    rw [show (((1 + t ^ 2 : ℝ) : ℂ)⁻¹) = (↑(((1 + t ^ 2 : ℝ)⁻¹)) : ℂ) by rw [Complex.ofReal_inv]]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_mul_re, Complex.I_mul_im,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
    ring

lemma re_integrand_eq_pfun (α t : ℝ) :
    (cexp (I * (α * t : ℂ)) / (1 + I * (t : ℂ))).re = pfun α t := by
  unfold pfun
  rw [div_eq_mul_inv, one_add_I_mul_inv, ← mul_assoc, exp_times_conj α t]
  rw [scale_cast t (Real.cos (α * t) + t * Real.sin (α * t)) (Real.sin (α * t) - t * Real.cos (α * t))]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_mul_re]
  ring

/-- Real part commutes with interval integrals. -/
lemma integral_re_interval (f : ℝ → ℂ) (a b : ℝ) (hfi : IntervalIntegrable f MeasureTheory.volume a b) :
    (∫ t in a..b, (f t).re) = ((∫ t in a..b, f t).re) := by
  have hc := ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ) (E := ℂ) (F := ℝ)
    Complex.reCLM hfi
  simpa using hc

/-- The complex Perron integrand is continuous. -/
lemma continuous_cexp_div (α : ℝ) : Continuous fun t : ℝ => cexp (I * (α * t : ℂ)) / (1 + I * (t : ℂ)) := by
  have hnum : Continuous fun t : ℝ => cexp (I * (α * t : ℂ)) := by fun_prop
  have hden : Continuous fun t : ℝ => (1 + I * (t : ℂ) : ℂ) := by fun_prop
  have hz : ∀ t : ℝ, (1 + I * (t : ℂ) : ℂ) ≠ 0 := by
    intro t
    have hsq : (0 : ℝ) < Complex.normSq (1 + I * (t : ℂ)) := by
      rw [Complex.normSq_apply]
      -- re (1 + I t) = 1, im = t
      have hre : (1 + I * (t : ℂ) : ℂ).re = 1 := by simp
      have him : (1 + I * (t : ℂ) : ℂ).im = t := by simp
      rw [hre, him]
      nlinarith [sq_nonneg t]
    intro hz'
    have : Complex.normSq (1 + I * (t : ℂ)) = 0 := by simp [hz']
    linarith
  exact Continuous.div₀ hnum hden hz

/-- Difference of two truncations is bounded by the tail:
    `‖K(R,α) − K(T,α)‖ ≤ 6/(|α|T)` for `1 ≤ T ≤ R`, `α ≠ 0`. -/
lemma kern_tail_bound (T R α : ℝ) (hα : α ≠ 0) (hT : 1 ≤ T) (hTR : T ≤ R) :
    ‖kern R α - kern T α‖ ≤ 6 / (|α| * T) := by
  rw [kern_sub_eq_ofReal T R α]
  let F : ℂ := ∫ t in T..R, cexp (I * (α * t : ℂ)) / (1 + I * (t : ℂ))
  have hz : (∫ t in T..R, pfun α t) = F.re := by
    have hpt : ∀ t, pfun α t = (cexp (I * (α * t : ℂ)) / (1 + I * (t : ℂ))).re := fun t => (re_integrand_eq_pfun α t).symm
    have hfi : IntervalIntegrable (fun t : ℝ => cexp (I * (α * t : ℂ)) / (1 + I * (t : ℂ))) volume T R :=
      (continuous_cexp_div α).intervalIntegrable T R
    calc
      (∫ t in T..R, pfun α t) = ∫ t in T..R, (cexp (I * (α * t : ℂ)) / (1 + I * (t : ℂ))).re := by
        apply intervalIntegral.integral_congr (μ := volume)
        intro t ht
        exact hpt t
      _ = F.re := by
        dsimp [F]
        exact integral_re_interval (fun t : ℝ => cexp (I * (α * t : ℂ)) / (1 + I * (t : ℂ))) T R hfi
  have hfi' : IntervalIntegrable (fun t : ℝ => cexp (I * (α * t : ℂ)) / (1 + I * (t : ℂ))) volume T R :=
    (continuous_cexp_div α).intervalIntegrable T R
  have habs : |F.re| ≤ ‖F‖ := by
    dsimp [F]
    exact Complex.abs_re_le_norm _
  have hosc : ‖F‖ ≤ 3 / (|α| * T) := by
    dsimp [F]
    exact PerronKernel.osc_tail_bound α T R hα hT hTR
  have hx : (|α| * T) ≠ 0 := by
    exact mul_ne_zero (abs_ne_zero.mpr hα) (ne_of_gt (lt_of_lt_of_le zero_lt_one hT))
  have hnr : ‖((2 * (∫ t in T..R, pfun α t) : ℝ) : ℂ)‖ = |2 * (∫ t in T..R, pfun α t)| := by
    exact RCLike.norm_ofReal (2 * (∫ t in T..R, pfun α t))
  rw [hnr]
  calc
    |2 * (∫ t in T..R, pfun α t)| = |2 * F.re| := by rw [hz]
    _ = 2 * |F.re| := by
      rw [abs_mul]
      have h2 : |(2 : ℝ)| = 2 := by norm_num
      rw [h2]
    _ ≤ 2 * ‖F‖ := mul_le_mul_of_nonneg_left habs (by norm_num)
    _ ≤ 2 * (3 / (|α| * T)) := mul_le_mul_of_nonneg_left hosc (by norm_num)
    _ = 6 / (|α| * T) := by field_simp [hx]; norm_num

end

--/-! ## Convergence of the truncated kernel -/

/-- Limiting cosine value: `(π/2)·e^{−|α|}`. -/
noncomputable def kernAinf (α : ℝ) : ℝ := Real.pi / 2 * Real.exp (-|α|)
/-- Limiting sine value: `(π/2)·sign(α)·e^{−|α|}`. -/
noncomputable def kernBinf (α : ℝ) : ℝ := Real.pi / 2 * Real.sign α * Real.exp (-|α|)

/-- `A_R(α) → (π/2)e^{−|α|}` as `R → ∞`. -/
lemma kernA_tendsto (α : ℝ) : Tendsto (fun R : ℝ => kernA R α) atTop (𝓝 (kernAinf α)) := by
  have hcont : Continuous fun x : ℝ => Real.cos (α * x) / (1 + x ^ 2) := continuous_kernA α
  have hb : ∀ x : ℝ, ‖Real.cos (α * x) / (1 + x ^ 2)‖ ≤ (1 + x ^ 2)⁻¹ := by
    intro x
    have hb' : |Real.cos (α * x)| ≤ 1 := abs_cos_le_one _
    have hden : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
    rw [Real.norm_eq_abs]
    rw [abs_div]
    rw [abs_of_pos hden]
    calc
      |Real.cos (α * x)| / (1 + x ^ 2) ≤ 1 / (1 + x ^ 2) := by gcongr
      _ = (1 + x ^ 2)⁻¹ := by rw [one_div]
  have hgi : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) volume := integrable_inv_one_add_sq
  have hfi : Integrable (fun x : ℝ => Real.cos (α * x) / (1 + x ^ 2)) volume := by
    refine MeasureTheory.Integrable.mono' hgi hcont.aestronglyMeasurable ?_
    exact (Eventually.of_forall hb)
  have h1 := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ)) hfi.integrableOn tendsto_id
  have hval : (∫ x : ℝ in Set.Ioi (0 : ℝ), Real.cos (α * x) / (1 + x ^ 2)) = kernAinf α := by
    unfold kernAinf
    exact cos_inv_one_add_sq_Ioi α
  rw [hval] at h1
  simpa [kernA] using h1

/-- `B_R(α) → (π/2)·sign(α)·e^{−|α|}` as `R → ∞` (for `α ≠ 0`). -/
lemma kernB_tendsto (α : ℝ) (hα : α ≠ 0) : Tendsto (fun R : ℝ => kernB R α) atTop (𝓝 (kernBinf α)) := by
  have h1 := PerronKernel.sin_mul_one_add_sq_tendsto α hα
  unfold kernBinf kernB
  simpa [mul_assoc, mul_comm, mul_left_comm] using h1

/-- `2·A_R → 2·A∞`. -/
lemma two_kernA_tendsto (α : ℝ) : Tendsto (fun R : ℝ => 2 * kernA R α) atTop (𝓝 (2 * kernAinf α)) := by
  exact (kernA_tendsto α).const_mul 2

/-- `2·B_R → 2·B∞` (for `α ≠ 0`). -/
lemma two_kernB_tendsto (α : ℝ) (hα : α ≠ 0) : Tendsto (fun R : ℝ => 2 * kernB R α) atTop (𝓝 (2 * kernBinf α)) := by
  exact (kernB_tendsto α hα).const_mul 2

/-- `2·(A∞+B∞) = kernVal` (the limiting value; for `α ≠ 0`). -/
lemma two_inf_eq_kernVal (α : ℝ) (hα : α ≠ 0) : 2 * (kernAinf α + kernBinf α) = kernVal α := by
  by_cases hα0 : 0 < α
  · have hs : Real.sign α = 1 := Real.sign_of_pos hα0
    have hAbs : |α| = α := abs_of_pos hα0
    rw [kernVal_of_pos hα0, kernAinf, kernBinf, hs, hAbs]
    ring
  · have hαle : α ≤ 0 := le_of_not_gt hα0
    have hneg : α < 0 := lt_of_le_of_ne hαle hα
    have hs : Real.sign α = -1 := Real.sign_of_neg hneg
    have hAbs : |α| = -α := abs_of_neg hneg
    rw [kernVal_of_nonpos hαle, kernAinf, kernBinf, hs, hAbs]
    ring

/-- `K(R,α)` tends to the closed-form limiting value. -/
lemma kern_tendsto_value (α : ℝ) (hα : α ≠ 0) :
    Tendsto (fun R : ℝ => kern R α)
      atTop (𝓝 (if 0 < α then (2 * π) * cexp (-α) else 0)) := by
  have hsum : Tendsto (fun R : ℝ => 2 * (kernA R α + kernB R α)) atTop (𝓝 (2 * (kernAinf α + kernBinf α))) := by
    have h1 := (two_kernA_tendsto α).add (two_kernB_tendsto α hα)
    have hd : (fun R : ℝ => 2 * (kernA R α + kernB R α)) = fun R : ℝ => 2 * kernA R α + 2 * kernB R α := by
      funext R; ring
    have hlim : 2 * (kernAinf α + kernBinf α) = 2 * kernAinf α + 2 * kernBinf α := by ring
    simpa [hd, hlim] using h1
  have hconv : Tendsto (fun R : ℝ => kern R α) atTop (𝓝 ((kernVal α : ℝ) : ℂ)) := by
    have ht : Tendsto (fun R : ℝ => ((2 * (kernA R α + kernB R α) : ℝ) : ℂ)) atTop (𝓝 ((2 * (kernAinf α + kernBinf α) : ℝ) : ℂ)) :=
      continuous_ofReal.continuousAt.tendsto.comp hsum
    rw [two_inf_eq_kernVal α hα] at ht
    simpa [kern_eq_two_A_B] using ht
  rw [← value_eq_ofReal α] at hconv
  exact hconv

/-- Truncated Perron kernel deviation bound. -/
theorem perron_kernel_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T α : ℝ), (1 ≤ T) → (α ≠ 0) →
        ‖(∫ t in -T..T, cexp (I * (α * t)) / (1 + I * t))
            - (if 0 < α then (2 * π) * cexp (-α) else 0)‖
          ≤ C * min 1 (1 / (T * |α|)) := by
  refine ⟨32, by norm_num, ?_⟩
  intro T α hT hα
  change ‖kern T α - (if 0 < α then (2 * π) * cexp (-α) else 0)‖ ≤ 32 * min 1 (1 / (T * |α|))
  let V : ℂ := if 0 < α then (2 * π) * cexp (-α) else 0
  have hconv : Tendsto (fun R : ℝ => kern R α) atTop (𝓝 V) := by
    simpa [V] using kern_tendsto_value α hα
  have hδpos : 0 < T * |α| := mul_pos (lt_of_lt_of_le zero_lt_one hT) (abs_pos.mpr hα)
  by_cases hδle : T * |α| ≤ 1
  · have hmin : min 1 (1 / (T * |α|)) = 1 := by
      rw [min_eq_left]
      rw [one_le_div₀ hδpos]
      exact hδle
    rw [hmin]
    have hreg : ‖kern T α‖ ≤ Real.pi + 2 := by
      simpa [kern, PerronKernel.kern] using PerronKernel.kern_region_bound T α hT hδle
    have hVnorm : ‖V‖ ≤ 2 * Real.pi := by
      dsimp [V]
      rw [value_eq_ofReal α]
      simpa [RCLike.norm_ofReal] using (kernVal_abs_le α)
    have hmain : ‖kern T α - V‖ ≤ 32 := by
      calc
        ‖kern T α - V‖ ≤ ‖kern T α‖ + ‖V‖ := norm_sub_le _ _
        _ ≤ (Real.pi + 2) + 2 * Real.pi := add_le_add hreg hVnorm
        _ ≤ 32 := by nlinarith [Real.pi_lt_four]
    simpa using hmain
  · have hδgt1 : 1 < T * |α| := lt_of_not_ge hδle
    have hmin : min 1 (1 / (T * |α|)) = 1 / (T * |α|) := by
      rw [min_eq_right]
      rw [div_le_one₀ hδpos]
      exact le_of_lt hδgt1
    rw [hmin]
    have htail : ∀ R : ℝ, T ≤ R → ‖kern R α - kern T α‖ ≤ 6 / (|α| * T) := by
      intro R hR
      exact kern_tail_bound T R α hα hT hR
    have hmain : ‖kern T α - V‖ ≤ 6 / (|α| * T) := by
      apply le_of_forall_pos_le_add
      intro ε hε
      have hconvε : ∀ᶠ R in atTop, ‖kern R α - V‖ < ε := by
        have hh := (Metric.tendsto_nhds.mp hconv) ε hε
        simpa [dist_eq_norm] using hh
      rcases eventually_atTop.1 hconvε with ⟨R0, hR0⟩
      let R1 := max T R0
      have hTR1 : T ≤ R1 := le_max_left _ _
      have hR0R1 : R0 ≤ R1 := le_max_right _ _
      have hεR : ‖kern R1 α - V‖ ≤ ε := (hR0 R1 hR0R1).le
      have htri : ‖kern T α - V‖ ≤ ‖kern T α - kern R1 α‖ + ‖kern R1 α - V‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
        exact dist_triangle (kern T α) (kern R1 α) V
      calc
        ‖kern T α - V‖ ≤ ‖kern T α - kern R1 α‖ + ‖kern R1 α - V‖ := htri
        _ ≤ 6 / (|α| * T) + ε := add_le_add
            (by rw [norm_sub_rev]; exact kern_tail_bound T R1 α hα hT hTR1) hεR
    have hmain' : ‖kern T α - V‖ ≤ 6 / (T * |α|) := by
      simpa [mul_comm] using hmain
    have hcmp : 6 / (T * |α|) ≤ 32 * (1 / (T * |α|)) := by
      rw [div_eq_mul_inv]
      rw [one_div]
      exact mul_le_mul_of_nonneg_right (by norm_num : (6 : ℝ) ≤ 32)
        (by positivity : 0 ≤ (T * |α|)⁻¹)
    exact hmain'.trans hcmp
end Commons.Analysis.Fourier
