import Mathlib
import Submission.Work.FunctionalEquations.Basic

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology MeasureTheory
open scoped FourierTransform SchwartzMap

noncomputable section

/-!
# Fourier (Dirichlet) expansion of a periodic holomorphic function on the upper half plane

The main result of this file, `Work.FunctionalEquations.DirichletExpansion`, is the
classical statement that a holomorphic function on the upper half plane which is periodic
of period `1` and of at most polynomial decay at `i∞` has a (pointwise, absolutely
convergent) Dirichlet series expansion

`h τ = ∑_{m ≥ 0} c_m e^{2 π i (m+1) τ}`,

with the coefficients given by contour integrals

`c_m = ∫_0^1 h (t + i y) e^{-2 π i (m+1) (t + i y)} dt`

along any horizontal line `Im = y`, `y > 0` (independence of `y` is part of the statement).

The proof goes through the standard `q`-parameter: `h` is `g (e^{2π i τ})` for a function
`g` on the punctured unit disc; the growth hypothesis makes the singularity at `0`
removable, so `g` is holomorphic on the unit disc and is the sum of its Taylor series
there (`Periodic.cuspFunction`, `hasSum_taylorSeries_on_ball`).  Reading the Taylor
coefficients back along the line `Im = y` by orthogonality (`CoeffIntegral`) produces the
integral formula for the coefficients.

## Main statements

* `CoeffIntegral`: the `k`-th coefficient of a convergent Dirichlet series
  `∑_m c_m e^{2π i (m+1) (t + i y)}` is the integral of the function against
  `e^{-2π i (k+1) (t + i y)}` over `t ∈ (0,1)`.
* `ExpansionReindex`: a convergent power series `∑_n a_n q^n` at `q = e^{2π i τ}` with
  `a 0 = 0` gives a Dirichlet series in the variable `τ`.
* `DirichletExpansion`: the theorem above.
-/

/-! ### Elementary exponential and integral identities -/

/-- The modulus of `e^{2π i (m+1) (t + i y)}`. -/
lemma norm_exp_two_pi_I_nat (m : ℕ) (t y : ℝ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) + 1) * ((t : ℂ) + (y : ℂ) * Complex.I))‖
      = Real.exp (-(2 * Real.pi * ((m : ℝ) + 1) * y)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- The modulus of `e^{-2π i (m+1) (t + i y)}`. -/
lemma norm_exp_neg_two_pi_I_nat (m : ℕ) (t y : ℝ) :
    ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) + 1) * ((t : ℂ) + (y : ℂ) * Complex.I)))‖
      = Real.exp (2 * Real.pi * ((m : ℝ) + 1) * y) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- The product of two characters is the character of the difference. -/
lemma exp_mul_exp_shift (u v : ℂ) (t y : ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u * ((t : ℂ) + (y : ℂ) * Complex.I)) *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * v * ((t : ℂ) + (y : ℂ) * Complex.I)))
    = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (u - v) * ((t : ℂ) + (y : ℂ) * Complex.I)) := by
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Orthogonality of the characters `t ↦ e^{2π i n t}` on `(0,1)`. -/
lemma integral_char_int (n : ℤ) :
    ∫ t in (0:ℝ)..1, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ))
      = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg hn]
    have hc : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ≠ 0 := by
      apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · exact two_ne_zero
          · exact_mod_cast Real.pi_ne_zero
        · exact Complex.I_ne_zero
      · exact_mod_cast hn
    rw [show (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)))
        = (fun t : ℝ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * (t : ℂ))) from by
          funext t; ring]
    rw [integral_exp_mul_complex hc]
    simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [show (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))
        = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by ring]
    rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
    simp

/-- Integral of a single character `t ↦ b e^{2π i n (t + i y)}` over `(0,1)`. -/
lemma integral_exp_shift (b : ℂ) (n : ℤ) (y : ℝ) :
    ∫ t in (0 : ℝ)..1,
        b * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((t : ℂ) + (y : ℂ) * Complex.I))
      = b * (if n = 0 then 1 else 0) := by
  have hsplit : ∀ t : ℝ,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((t : ℂ) + (y : ℂ) * Complex.I))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((y : ℂ) * Complex.I)) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)) := by
    intro t
    rw [← Complex.exp_add]
    congr 1
    ring
  have h1 : (fun t : ℝ => b * Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((t : ℂ) + (y : ℂ) * Complex.I)))
      = (fun t : ℝ => (b * Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((y : ℂ) * Complex.I))) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ))) := by
    funext t
    rw [hsplit t]
    ring
  rw [h1, intervalIntegral.integral_const_mul]
  rw [show (∫ t in (0:ℝ)..1, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)))
      = (if n = 0 then 1 else 0) by simpa using integral_char_int n]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg hn, mul_zero, mul_zero]

/-- **Coefficients of a Dirichlet series by integration.**  If `φ t = ∑_{m ≥ 0} c_m
e^{2π i (m+1) (t + i y)}` for all real `t`, with `y > 0`, and the coefficient norms are
summable as in the hypothesis `hs`, then each `c_k` is the `k`-th Fourier coefficient of `φ`
on the line `Im = y`. -/
theorem CoeffIntegral {c : ℕ → ℂ} {φ : ℝ → ℂ} {y : ℝ} (_hy : 0 < y)
    (hφ : ∀ t : ℝ, HasSum (fun m : ℕ =>
      c m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) + 1)
        * ((t : ℂ) + (y : ℂ) * Complex.I))) (φ t))
    (hs : Summable fun m : ℕ => ‖c m‖ * Real.exp (-(2 * Real.pi * ((m : ℝ) + 1) * y))) :
    ∀ k : ℕ, c k = ∫ t in (0 : ℝ)..1, φ t * Complex.exp
      (-(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1)
        * ((t : ℂ) + (y : ℂ) * Complex.I))) := by
  intro k
  set B : ℝ → ℂ := fun t => Complex.exp
    (-(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1) * ((t : ℂ) + (y : ℂ) * Complex.I)))
    with hB
  set F : ℕ → ℝ → ℂ := fun m t =>
    (c m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) + 1)
      * ((t : ℂ) + (y : ℂ) * Complex.I))) * B t with hF
  have hFint : ∀ m : ℕ, Integrable (F m) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro m
    have hcont : Continuous (F m) := by rw [hF]; fun_prop
    exact (hcont.continuousOn.integrableOn_Icc (a := (0:ℝ)) (b := 1)).mono_set
      (fun x hx => ⟨hx.1.le, hx.2⟩)
  have hFsum : Summable fun m : ℕ => ∫ t, ‖F m t‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have hpt : ∀ m : ℕ, ∫ t, ‖F m t‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))
        = (‖c m‖ * Real.exp (-(2 * Real.pi * ((m : ℝ) + 1) * y))) *
            Real.exp (2 * Real.pi * ((k : ℝ) + 1) * y) := by
      intro m
      have hpt2 : ∀ t : ℝ, ‖F m t‖
          = (‖c m‖ * Real.exp (-(2 * Real.pi * ((m : ℝ) + 1) * y))) *
            Real.exp (2 * Real.pi * ((k : ℝ) + 1) * y) := by
        intro t
        simp only [hF, hB]
        rw [norm_mul, norm_mul, norm_exp_two_pi_I_nat, norm_exp_neg_two_pi_I_nat]
        try ring
      rw [show (fun t : ℝ => ‖F m t‖) = (fun _ : ℝ =>
            (‖c m‖ * Real.exp (-(2 * Real.pi * ((m : ℝ) + 1) * y))) *
            Real.exp (2 * Real.pi * ((k : ℝ) + 1) * y)) from funext hpt2]
      rw [MeasureTheory.integral_const]
      simp [MeasureTheory.Measure.real]
    refine (hs.mul_right (Real.exp (2 * Real.pi * ((k : ℝ) + 1) * y))).congr ?_
    intro m
    exact (hpt m).symm
  have htsum : ∀ t : ℝ, ∑' m : ℕ, F m t = φ t * B t := by
    intro t
    have h := ((hφ t).mul_right (B t)).tsum_eq
    simp only [hF]
    exact h
  have hval : HasSum (fun m : ℕ => ∫ t, F m t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
      (∫ t, φ t * B t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    have hfun : (fun t : ℝ => ∑' m : ℕ, F m t) = (fun t : ℝ => φ t * B t) := funext htsum
    rw [← hfun]
    exact MeasureTheory.hasSum_integral_of_summable_integral_norm hFint hFsum
  have hterm : ∀ m : ℕ, ∫ t, F m t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))
      = c m * (if m = k then 1 else 0) := by
    intro m
    rw [← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
    have hcongr : (fun t : ℝ => F m t) = (fun t : ℝ => c m * Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (((m : ℤ) - (k : ℤ) : ℤ) : ℂ)
          * ((t : ℂ) + (y : ℂ) * Complex.I))) := by
      funext t
      simp only [hF, hB]
      rw [mul_assoc (c m), exp_mul_exp_shift]
      congr 2
      push_cast
      ring
    rw [hcongr, integral_exp_shift]
    congr 1
    by_cases hmk : m = k
    · subst hmk; simp
    · have hne : ((m:ℤ) - (k:ℤ)) ≠ 0 := by
        intro hh; exact hmk (by exact_mod_cast (sub_eq_zero.mp hh))
      rw [if_neg hne, if_neg hmk]
  have hcongr2 : (fun m : ℕ => ∫ t, F m t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
      = (fun m : ℕ => c m * (if m = k then 1 else 0)) := funext hterm
  rw [hcongr2] at hval
  have hck : ∫ t, φ t * B t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = c k := by
    rw [← hval.tsum_eq, tsum_eq_single k (fun m hm => by rw [if_neg hm, mul_zero])]
    simp
  rw [← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)] at hck
  exact hck.symm

/-- **From a power series in `q = e^{2π i τ}` to a Dirichlet series.** -/
theorem ExpansionReindex {H h : ℂ → ℂ} {a : ℕ → ℂ} (ha0 : a 0 = 0)
    (hTaylor : ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun n : ℕ => a n * q ^ n) (H q))
    (hlink : ∀ τ : ℂ, 0 < τ.im → H (Function.Periodic.qParam 1 τ) = h τ) :
    ∀ τ : ℂ, 0 < τ.im → HasSum (fun m : ℕ =>
      a (m + 1) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) + 1) * τ)) (h τ) := by
  intro τ hτ
  have hq : ‖Function.Periodic.qParam 1 τ‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos hτ
  have h1 : HasSum (fun n : ℕ => a n * Function.Periodic.qParam 1 τ ^ n) (h τ) := by
    rw [← hlink τ hτ]
    exact hTaylor _ hq
  have hterm : ∀ m : ℕ, a (m + 1) * Function.Periodic.qParam 1 τ ^ (m + 1)
      = a (m + 1) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) + 1) * τ) := by
    intro m
    congr 1
    rw [Function.Periodic.qParam]
    simp only [Complex.ofReal_one, div_one]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hcongr : (fun m : ℕ => a (m + 1) * Function.Periodic.qParam 1 τ ^ (m + 1))
      = (fun m : ℕ => a (m + 1) * Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) + 1) * τ)) := funext hterm
  have h2 : HasSum (fun m : ℕ => a (m + 1) * Function.Periodic.qParam 1 τ ^ (m + 1))
      (h τ) := by
    refine (hasSum_nat_add_iff
      (f := fun n : ℕ => a n * Function.Periodic.qParam 1 τ ^ n) 1).mpr ?_
    simpa [ha0] using h1
  rw [hcongr] at h2
  exact h2

/-! ### The main theorem -/

/-- **Dirichlet expansion of a periodic holomorphic function.**  Let `h` be holomorphic
on the upper half plane, periodic of period `1`, and bounded in terms of a weight `M`
obeying `M y ≤ A y^{-β}` and `M y e^{-2 π m y} → 0` as `y → ∞` for every `m`.  Then `h`
has an absolutely convergent Dirichlet series expansion with frequencies `1, 2, 3, …`
and the coefficients are the contour integrals along any horizontal line in the upper
half plane. -/
theorem DirichletExpansion (h : ℂ → ℂ)
    (hper : ∀ τ : ℂ, 0 < τ.im → h (τ + 1) = h τ)
    (hhol : DifferentiableOn ℂ h {τ : ℂ | 0 < τ.im})
    (M : ℝ → ℝ) (hM : ∀ τ : ℂ, 0 < τ.im → ‖h τ‖ ≤ M τ.im)
    (hMbound : ∃ A β : ℝ, 0 ≤ A ∧ 0 ≤ β ∧ ∀ y : ℝ, 0 < y → M y ≤ A * y ^ (-β))
    (hMdecay : ∀ m : ℕ, Tendsto (fun y : ℝ => M y * Real.exp (-(2 * Real.pi) * y) ^ m)
      atTop (𝓝 0)) :
    ∃ c : ℕ → ℂ,
      (∀ τ : ℂ, 0 < τ.im → HasSum (fun m : ℕ =>
        c m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) + 1) * τ)) (h τ)) ∧
      (∀ (m : ℕ) (y : ℝ), 0 < y → c m = ∫ t in (0 : ℝ)..1,
        h ((t : ℂ) + (y : ℂ) * Complex.I) * Complex.exp
          (-(2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) + 1) * ((t : ℂ) + (y : ℂ) * Complex.I)))) := by
  obtain ⟨A, β, hA0, hβ0, hAb⟩ := hMbound
  -- Step 1: extend `h` to a globally `1`-periodic function `G`, agreeing with `h` on the
  -- upper half plane.
  set G : ℂ → ℂ := fun z => if 0 < z.im then h z else 0 with hGdef
  have hGper : Function.Periodic G 1 := by
    intro z
    by_cases hz : 0 < z.im
    · have hz' : 0 < (z + 1).im := by simpa using hz
      rw [hGdef]
      simp only [hz, hz', if_true]
      exact hper z hz
    · have hz' : ¬ 0 < (z + 1).im := by simpa using hz
      rw [hGdef]
      simp only [hz, hz', if_false]
  have hGeq : ∀ z, 0 < z.im → G z = h z := by
    intro z hz; rw [hGdef]; simp [hz]
  have hGdiff_at : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ G z := by
    intro z hz
    have hnhds : {w : ℂ | 0 < w.im} ∈ 𝓝 z :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz
    exact (hhol.differentiableAt hnhds).congr_of_eventuallyEq
      (by filter_upwards [hnhds] with w hw; exact hGeq w hw)
  have hGdiff : ∀ᶠ z : ℂ in comap Complex.im atTop, DifferentiableAt ℂ G z := by
    filter_upwards [preimage_mem_comap (Ioi_mem_atTop (0:ℝ))] with z hz
    exact hGdiff_at z hz
  have hGbd : (comap Complex.im atTop).BoundedAtFilter G := by
    refine Asymptotics.isBigO_iff.mpr ⟨A, ?_⟩
    filter_upwards [preimage_mem_comap (Ici_mem_atTop (1 : ℝ))] with z hz
    have hz0 : 0 < z.im := lt_of_lt_of_le one_pos hz
    rw [hGeq z hz0, Pi.one_apply, norm_one, mul_one]
    calc ‖h z‖ ≤ M z.im := hM z hz0
      _ ≤ A * z.im ^ (-β) := hAb z.im hz0
      _ ≤ A * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hA0
          exact Real.rpow_le_one_of_one_le_of_nonpos hz (by linarith)
      _ = A := mul_one A
  have hGzero : (comap Complex.im atTop).ZeroAtFilter G := by
    have hM0 : Tendsto (fun y : ℝ => M y) atTop (𝓝 0) := by
      simpa using hMdecay 0
    rw [ZeroAtFilter, tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' ?_ ?_ (hM0.comp Filter.tendsto_comap)
    · filter_upwards with z using norm_nonneg _
    · filter_upwards [preimage_mem_comap (Ioi_mem_atTop (0:ℝ))] with z hz
      rw [hGeq z hz]
      exact hM z hz
  -- Step 2: the `q`-function of `h` is holomorphic on the unit disc.
  set H : ℂ → ℂ := Function.Periodic.cuspFunction 1 G with hHdef
  have hHdiff : DifferentiableOn ℂ H (Metric.ball 0 1) := by
    intro q hq
    rw [Metric.mem_ball, dist_zero_right] at hq
    rcases eq_or_ne q 0 with rfl | hq'
    · exact (Function.Periodic.differentiableAt_cuspFunction_zero one_pos hGper hGdiff
        hGbd).differentiableWithinAt
    · have hz : 0 < (Function.Periodic.invQParam 1 q).im := by
        rw [Function.Periodic.im_invQParam]
        have hlog : Real.log ‖q‖ < 0 := Real.log_neg (norm_pos_iff.mpr hq') hq
        have hpi : (0:ℝ) < 2 * Real.pi := by positivity
        rw [show -1 / (2 * Real.pi) * Real.log ‖q‖
            = (2 * Real.pi)⁻¹ * (-(Real.log ‖q‖)) by ring]
        exact mul_pos (inv_pos.mpr hpi) (neg_pos.mpr hlog)
      rw [← Function.Periodic.qParam_right_inv (h := 1) one_ne_zero hq']
      exact (Function.Periodic.differentiableAt_cuspFunction (h := 1)
        (by norm_num : (1:ℝ) ≠ 0) hGper (hGdiff_at _ hz)).differentiableWithinAt
  have hH0 : H 0 = 0 := Function.Periodic.cuspFunction_zero_of_zero_at_inf one_pos hGzero
  -- Step 3: Taylor coefficients of `H` at `0`.
  set a : ℕ → ℂ := fun n => (n.factorial : ℂ)⁻¹ * iteratedDeriv n H 0 with hadef
  have hTaylor : ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun n : ℕ => a n * q ^ n) (H q) := by
    intro q hq
    have hcongr : (fun n : ℕ => (n.factorial : ℂ)⁻¹ • (q - 0) ^ n • iteratedDeriv n H 0)
        = (fun n : ℕ => a n * q ^ n) := by
      funext n
      simp only [hadef, sub_zero, smul_eq_mul]
      ring_nf
    have hh := Complex.hasSum_taylorSeries_on_ball hHdiff (by rwa [Metric.mem_ball, dist_zero_right])
    rw [hcongr] at hh
    exact hh
  have ha0 : a 0 = 0 := by
    simp only [hadef, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul]
    simpa using hH0
  have hlink : ∀ τ : ℂ, 0 < τ.im → H (Function.Periodic.qParam 1 τ) = h τ := by
    intro τ hτ
    rw [hHdef, Function.Periodic.eq_cuspFunction (h := 1) (f := G) (by norm_num) hGper τ]
    exact hGeq τ hτ
  have hmain := ExpansionReindex ha0 hTaylor hlink
  refine ⟨fun m => a (m + 1), hmain, ?_⟩
  -- Step 4: identify the coefficients by integration.
  intro m y hy
  have hφ : ∀ t : ℝ, HasSum (fun k : ℕ =>
      a (k + 1) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1)
        * ((t : ℂ) + (y : ℂ) * Complex.I))) (h ((t : ℂ) + (y : ℂ) * Complex.I)) :=
    fun t => hmain _ (by simp; exact hy)
  have hs : Summable fun k : ℕ =>
      ‖a (k + 1)‖ * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * y)) := by
    have hsum := (hφ 0).summable
    refine hsum.norm.congr (fun k => ?_)
    rw [norm_mul, Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
  exact CoeffIntegral hy hφ hs m

end

end Work.FunctionalEquations
