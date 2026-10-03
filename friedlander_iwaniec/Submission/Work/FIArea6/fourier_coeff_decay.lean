import Mathlib

namespace Work.FIArea6

open MeasureTheory intervalIntegral
open scoped Topology

/-- `iteratedDeriv 2 q = deriv (deriv q)`. -/
lemma iteratedDeriv_two_eq (q : ℝ → ℝ) : iteratedDeriv 2 q = deriv (deriv q) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- The Fourier exponential factor has norm one. -/
lemma norm_exp_int (ℓ : ℤ) (α : ℝ) :
    ‖Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖ = 1 := by
  rw [show -(ℓ : ℂ) * Complex.I * α = ((-((ℓ : ℝ) * α) : ℝ) : ℂ) * Complex.I from by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **Support vanishing.**  A `C²` function supported in `[0, 2πθ]` vanishes, together with
its first two derivatives, on the two closed tails `(-∞,0]` and `[2πθ,∞)`. -/
lemma q_vanish_support (q : ℝ → ℝ) (θ : ℝ) (hqC : ContDiff ℝ 2 q)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ) :
    (∀ x, x ≤ 0 → q x = 0) ∧ (∀ x, 2 * Real.pi * θ ≤ x → q x = 0) ∧
    (∀ x, x ≤ 0 → deriv q x = 0) ∧ (∀ x, 2 * Real.pi * θ ≤ x → deriv q x = 0) ∧
    (∀ x, x ≤ 0 → deriv (deriv q) x = 0) ∧ (∀ x, 2 * Real.pi * θ ≤ x → deriv (deriv q) x = 0) := by
  have hcont : Continuous q := hqC.continuous
  have hdcont : Continuous (deriv q) := hqC.continuous_deriv (by norm_num)
  have h_id2 : iteratedDeriv 2 q = deriv (deriv q) := iteratedDeriv_two_eq q
  have hddcont : Continuous (deriv (deriv q)) := h_id2 ▸ hqC.continuous_iteratedDeriv' 2
  have key : ∀ (f : ℝ → ℝ), Continuous f → (∀ x, x < 0 → f x = 0) →
      (∀ x, 2 * Real.pi * θ < x → f x = 0) →
      (∀ x, x ≤ 0 → f x = 0) ∧ (∀ x, 2 * Real.pi * θ ≤ x → f x = 0) := by
    intro f hf hneg hpos
    have hcl : IsClosed {x : ℝ | f x = 0} := isClosed_singleton.preimage hf
    constructor
    · intro x hx
      have hxc : x ∈ closure (Set.Iio (0:ℝ)) := by rw [closure_Iio]; exact hx
      exact hcl.closure_subset (closure_mono (fun y hy => hneg y hy) hxc)
    · intro x hx
      have hxc : x ∈ closure (Set.Ioi (2 * Real.pi * θ)) := by rw [closure_Ioi]; exact hx
      exact hcl.closure_subset (closure_mono (fun y hy => hpos y hy) hxc)
  have hq := key q hcont
    (fun x hx => by by_contra h; exact absurd (hqsupp x h).1 (not_le.mpr hx))
    (fun x hx => by by_contra h; exact absurd (hqsupp x h).2 (not_le.mpr hx))
  have hdq := key (deriv q) hdcont
    (fun x hx => by
      have hev : q =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
        filter_upwards [isOpen_Iio.mem_nhds hx] with y hy using hq.1 y (le_of_lt hy)
      rw [Filter.EventuallyEq.deriv_eq hev]; simp)
    (fun x hx => by
      have hev : q =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy using hq.2 y (le_of_lt hy)
      rw [Filter.EventuallyEq.deriv_eq hev]; simp)
  have hddq := key (deriv (deriv q)) hddcont
    (fun x hx => by
      have hev : deriv q =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
        filter_upwards [isOpen_Iio.mem_nhds hx] with y hy using hdq.1 y (le_of_lt hy)
      rw [Filter.EventuallyEq.deriv_eq hev]; simp)
    (fun x hx => by
      have hev : deriv q =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy using hdq.2 y (le_of_lt hy)
      rw [Filter.EventuallyEq.deriv_eq hev]; simp)
  exact ⟨hq.1, hq.2, hdq.1, hdq.2, hddq.1, hddq.2⟩

/-- Trivial (support) bound on the integral of `q`. -/
lemma integral_q_le_decay (q : ℝ → ℝ) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hqC : ContDiff ℝ 2 q) (hq1 : ∀ α, q α ≤ 1)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ) :
    ∫ α in (0:ℝ)..(2 * Real.pi), q α ≤ 2 * Real.pi * θ := by
  have hle : 2 * Real.pi * θ ≤ 2 * Real.pi := by
    have : (0:ℝ) < 2 * Real.pi := by positivity
    nlinarith
  have hqθ : 0 ≤ 2 * Real.pi * θ := by positivity
  have hq0 : ∀ x, 2 * Real.pi * θ ≤ x → q x = 0 := (q_vanish_support q θ hqC hqsupp).2.1
  have hcont : Continuous q := hqC.continuous
  have hsplit : (∫ x in (0:ℝ)..(2 * Real.pi * θ), q x)
        + (∫ x in (2 * Real.pi * θ)..(2 * Real.pi), q x)
      = ∫ x in (0:ℝ)..(2 * Real.pi), q x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (0:ℝ) (2 * Real.pi * θ))
      (hcont.intervalIntegrable (2 * Real.pi * θ) (2 * Real.pi))
  rw [← hsplit]
  have hz : ∫ x in (2 * Real.pi * θ)..(2 * Real.pi), q x = 0 := by
    have h : ∫ x in (2 * Real.pi * θ)..(2 * Real.pi), q x
        = ∫ x in (2 * Real.pi * θ)..(2 * Real.pi), (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hle] at hx
      exact hq0 x hx.1
    rw [h, intervalIntegral.integral_zero]
  rw [hz, add_zero]
  have hmono : ∫ x in (0:ℝ)..(2 * Real.pi * θ), q x
      ≤ ∫ x in (0:ℝ)..(2 * Real.pi * θ), (1:ℝ) :=
    intervalIntegral.integral_mono_on hqθ (hcont.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) (fun x _ => hq1 x)
  have hone : ∫ x in (0:ℝ)..(2 * Real.pi * θ), (1:ℝ) = 2 * Real.pi * θ := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  linarith [hmono, hone]

/-- Support bound on the integral of `|q''|`. -/
lemma integral_abs_dd_le_decay (q : ℝ → ℝ) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hqC : ContDiff ℝ 2 q) (hd2 : ∀ α, |deriv (deriv q) α| ≤ 1000 / θ ^ 2)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ) :
    ∫ α in (0:ℝ)..(2 * Real.pi), |deriv (deriv q) α| ≤ 2 * Real.pi * θ * (1000 / θ ^ 2) := by
  have hle : 2 * Real.pi * θ ≤ 2 * Real.pi := by
    have : (0:ℝ) < 2 * Real.pi := by positivity
    nlinarith
  have hqθ : 0 ≤ 2 * Real.pi * θ := by positivity
  have hd0 : ∀ x, 2 * Real.pi * θ ≤ x → deriv (deriv q) x = 0 :=
    (q_vanish_support q θ hqC hqsupp).2.2.2.2.2
  have hcont : Continuous (fun α : ℝ => |deriv (deriv q) α|) := by
    have h : Continuous (deriv (deriv q)) :=
      (iteratedDeriv_two_eq q) ▸ hqC.continuous_iteratedDeriv' 2
    exact h.abs
  have hsplit : (∫ x in (0:ℝ)..(2 * Real.pi * θ), |deriv (deriv q) x|)
        + (∫ x in (2 * Real.pi * θ)..(2 * Real.pi), |deriv (deriv q) x|)
      = ∫ x in (0:ℝ)..(2 * Real.pi), |deriv (deriv q) x| :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (0:ℝ) (2 * Real.pi * θ))
      (hcont.intervalIntegrable (2 * Real.pi * θ) (2 * Real.pi))
  rw [← hsplit]
  have hz : ∫ x in (2 * Real.pi * θ)..(2 * Real.pi), |deriv (deriv q) x| = 0 := by
    have h : ∫ x in (2 * Real.pi * θ)..(2 * Real.pi), |deriv (deriv q) x|
        = ∫ x in (2 * Real.pi * θ)..(2 * Real.pi), (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hle] at hx
      show |deriv (deriv q) x| = (0:ℝ)
      rw [hd0 x hx.1, abs_zero]
    rw [h, intervalIntegral.integral_zero]
  rw [hz, add_zero]
  have hmono : ∫ x in (0:ℝ)..(2 * Real.pi * θ), |deriv (deriv q) x|
      ≤ ∫ x in (0:ℝ)..(2 * Real.pi * θ), (1000 / θ ^ 2 : ℝ) :=
    intervalIntegral.integral_mono_on hqθ (hcont.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) (fun x _ => hd2 x)
  have hone : ∫ x in (0:ℝ)..(2 * Real.pi * θ), (1000 / θ ^ 2 : ℝ)
      = 2 * Real.pi * θ * (1000 / θ ^ 2) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  linarith [hmono, hone]

/-- One integration by parts against an exponential `e` with `e' = e·c`. -/
lemma ibp_step (q q' : ℝ → ℝ) (e : ℝ → ℂ) (c : ℂ)
    (hq : ∀ x ∈ Set.uIcc (0:ℝ) (2 * Real.pi), HasDerivAt (fun y => (q y : ℂ)) ((q' x : ℂ)) x)
    (he : ∀ x ∈ Set.uIcc (0:ℝ) (2 * Real.pi), HasDerivAt e (e x * c) x)
    (hqi : IntervalIntegrable (fun y => (q' y : ℂ)) volume (0:ℝ) (2 * Real.pi))
    (hei : IntervalIntegrable (fun y => e y * c) volume (0:ℝ) (2 * Real.pi)) :
    (∫ x in (0:ℝ)..(2 * Real.pi), (q x : ℂ) * e x) * c
      = (q (2 * Real.pi) : ℂ) * e (2 * Real.pi) - (q 0 : ℂ) * e 0
        - ∫ x in (0:ℝ)..(2 * Real.pi), (q' x : ℂ) * e x := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := fun y => (q y : ℂ))
      (v := e) (u' := fun y => (q' y : ℂ)) (v' := fun y => e y * c) hq he hqi hei
  have hcongr : ∫ x in (0:ℝ)..(2 * Real.pi), (q x : ℂ) * (e x * c)
      = (∫ x in (0:ℝ)..(2 * Real.pi), (q x : ℂ) * e x) * c := by
    rw [show (fun x => (q x : ℂ) * (e x * c)) = (fun x => ((q x : ℂ) * e x) * c) from by
      funext x; ring,
      intervalIntegral.integral_mul_const]
  rw [hcongr] at h
  exact h

/-- **Two integrations by parts**, against the exponential `α ↦ exp (c·α)`. -/
lemma ibp_twice_exp (q : ℝ → ℝ) (c : ℂ) (hqC : ContDiff ℝ 2 q)
    (h0 : q 0 = 0) (h2π : q (2 * Real.pi) = 0)
    (hd0 : deriv q 0 = 0) (hd2π : deriv q (2 * Real.pi) = 0) :
    (∫ α in (0:ℝ)..(2 * Real.pi), (q α : ℂ) * Complex.exp (c * (α : ℂ))) * c ^ 2
      = ∫ α in (0:ℝ)..(2 * Real.pi),
          ((deriv (deriv q) α : ℝ) : ℂ) * Complex.exp (c * (α : ℂ)) := by
  have he_deriv : ∀ x : ℝ,
      HasDerivAt (fun α : ℝ => Complex.exp (c * (α : ℂ))) (Complex.exp (c * (x : ℂ)) * c) x := by
    intro x
    have hlin : HasDerivAt (fun α : ℝ => c * (α : ℂ)) c x := by
      have h : HasDerivAt (fun α : ℝ => (α : ℂ)) (1 : ℂ) x := (hasDerivAt_id x).ofReal_comp
      simpa using h.const_mul c
    exact (Complex.hasDerivAt_exp (c * (x : ℂ))).comp x hlin
  have he_cont : Continuous (fun α : ℝ => Complex.exp (c * (α : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hq_deriv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (q y : ℂ)) ((deriv q x : ℝ) : ℂ) x := fun x =>
    (hqC.differentiable (by norm_num)).differentiableAt.hasDerivAt.ofReal_comp
  have hdq_deriv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => ((deriv q y : ℝ) : ℂ)) ((deriv (deriv q) x : ℝ) : ℂ) x := fun x =>
    (hqC.differentiable_deriv_two.differentiableAt).hasDerivAt.ofReal_comp
  have hdq_cont : Continuous (fun y : ℝ => ((deriv q y : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hqC.continuous_deriv (by norm_num))
  have hddq_cont : Continuous (fun y : ℝ => ((deriv (deriv q) y : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((iteratedDeriv_two_eq q) ▸ hqC.continuous_iteratedDeriv' 2)
  have step1 := ibp_step q (deriv q) (fun α : ℝ => Complex.exp (c * (α : ℂ))) c
      (fun x _ => hq_deriv x) (fun x _ => he_deriv x)
      (hdq_cont.intervalIntegrable _ _)
      ((he_cont.mul continuous_const).intervalIntegrable _ _)
  have hK : (∫ x in (0:ℝ)..(2 * Real.pi), (q x : ℂ) * Complex.exp (c * (x : ℂ))) * c
      = - ∫ x in (0:ℝ)..(2 * Real.pi), ((deriv q x : ℝ) : ℂ) * Complex.exp (c * (x : ℂ)) := by
    have := step1
    rw [h2π, h0] at this
    simpa using this
  have step2 := ibp_step (deriv q) (deriv (deriv q)) (fun α : ℝ => Complex.exp (c * (α : ℂ))) c
      (fun x _ => hdq_deriv x) (fun x _ => he_deriv x)
      (hddq_cont.intervalIntegrable _ _)
      ((he_cont.mul continuous_const).intervalIntegrable _ _)
  have hL : (∫ x in (0:ℝ)..(2 * Real.pi), ((deriv q x : ℝ) : ℂ) * Complex.exp (c * (x : ℂ))) * c
      = - ∫ x in (0:ℝ)..(2 * Real.pi),
            ((deriv (deriv q) x : ℝ) : ℂ) * Complex.exp (c * (x : ℂ)) := by
    have := step2
    rw [hd2π, hd0] at this
    simpa using this
  rw [pow_two, ← mul_assoc, hK, neg_mul, hL, neg_neg]

/-- **Two integrations by parts.**  For a `C²` function `q` with `q(0)=q(2π)=0` and
`q'(0)=q'(2π)=0`, the Fourier coefficient is `c^{-2}` times the coefficient of `q''`. -/
lemma ibp_twice (q : ℝ → ℝ) (ℓ : ℤ) (hqC : ContDiff ℝ 2 q)
    (h0 : q 0 = 0) (h2π : q (2 * Real.pi) = 0)
    (hd0 : deriv q 0 = 0) (hd2π : deriv q (2 * Real.pi) = 0) :
    (∫ α in (0:ℝ)..(2 * Real.pi), (q α : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α))
        * (-(ℓ : ℂ) * Complex.I) ^ 2
      = ∫ α in (0:ℝ)..(2 * Real.pi),
          ((deriv (deriv q) α : ℝ) : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α) :=
  ibp_twice_exp q (-(ℓ : ℂ) * Complex.I) hqC h0 h2π hd0 hd2π

/-- Numeric comparison, small regime. -/
lemma decay_numeric_small (θ l : ℝ) (hθ : 0 < θ) (hl : (θ * l) ^ 2 ≤ 4) :
    2 * Real.pi * θ ≤ 10000 * θ * (1 + (θ * l) ^ 2)⁻¹ := by
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have ht0 : (0:ℝ) < 1 + (θ * l) ^ 2 := by positivity
  have hle : 1 + (θ * l) ^ 2 ≤ 5 := by nlinarith
  have hinv : (1:ℝ)/5 ≤ (1 + (θ * l) ^ 2)⁻¹ := by
    rw [one_div]
    exact (inv_le_inv₀ (show (0:ℝ) < 5 by norm_num) ht0).mpr hle
  calc 2 * Real.pi * θ ≤ 2000 * θ := by nlinarith [hpi, hθ]
    _ = 10000 * θ * (1/5) := by ring
    _ ≤ 10000 * θ * (1 + (θ * l) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)

/-- Numeric comparison, large regime. -/
lemma decay_numeric_large (θ l : ℝ) (hθ : 0 < θ) (hl : 4 < (θ * l) ^ 2) :
    (l ^ 2)⁻¹ * (2 * Real.pi * θ * (1000 / θ ^ 2)) ≤ 10000 * θ * (1 + (θ * l) ^ 2)⁻¹ := by
  set t : ℝ := (θ * l) ^ 2 with ht
  have ht0 : 0 < t := by rw [ht]; nlinarith
  have h1t : (0:ℝ) < 1 + t := by linarith
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hl2 : l ^ 2 = t / θ ^ 2 := by
    rw [ht, eq_div_iff (pow_ne_zero 2 (ne_of_gt hθ))]; ring
  have hkey : 2000 * Real.pi * θ * (1 + t) ≤ 10000 * θ * t := by
    have h1 : 1 + t ≤ (5/4) * t := by linarith
    have h2 : 2000 * Real.pi * (1 + t) ≤ 2000 * Real.pi * ((5/4) * t) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 2000 * Real.pi * ((5/4) * t) ≤ 10000 * t := by nlinarith [hpi, ht0]
    nlinarith [h2, h3, hθ]
  have hstep : (θ ^ 2 / t) * (2 * Real.pi * θ * (1000 / θ ^ 2)) = 2000 * Real.pi * θ / t := by
    field_simp; ring
  rw [hl2, inv_div, hstep]
  show 2000 * Real.pi * θ / t ≤ 10000 * θ / (1 + t)
  rw [div_le_div_iff₀ ht0 h1t]
  exact hkey

/-- **(16.26)**: an angular mollifier supported in the sector `[0, 2πθ]`, `C²` (so that the
boundary terms in two integrations by parts vanish at `0` and `2πθ`), and satisfying the
*genuine* derivative bounds `|q^{(j)}| ≤ C θ^{-j}` (`j ≤ 2`) has Fourier coefficients
`≪ θ(1+θ²ℓ²)^{-1}`.  This is the single smoothness input that §16 consumes from `q`; it is
stated with real derivatives and an explicit `ContDiff` hypothesis so that it transfers to the
round-4 coefficient predicate. -/
theorem fourier_coeff_decay (q : ℝ → ℝ) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hqC : ContDiff ℝ 2 q)
    (hq0 : ∀ α, 0 ≤ q α) (hq1 : ∀ α, q α ≤ 1)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ)
    (hd1 : ∀ α, |iteratedDeriv 1 q α| ≤ 1000 / θ)
    (hd2 : ∀ α, |iteratedDeriv 2 q α| ≤ 1000 / θ ^ 2)
    (ℓ : ℤ) :
    ‖∫ α in (0 : ℝ)..(2 * Real.pi), (q α : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖
      ≤ 10000 * θ * (1 + (θ * ℓ) ^ 2)⁻¹ := by
  have h2πpos : (0:ℝ) < 2 * Real.pi := by positivity
  have h2πθ_le : 2 * Real.pi * θ ≤ 2 * Real.pi := by nlinarith [hθ, hθ1, Real.pi_pos]
  have hnormint : ∀ α : ℝ, ‖(q α : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖ = q α := by
    intro α
    rw [norm_mul, norm_exp_int ℓ α, mul_one,
      show ‖(q α : ℂ)‖ = |q α| from by simp, abs_of_nonneg (hq0 α)]
  have htriv : ‖∫ α in (0 : ℝ)..(2 * Real.pi), (q α : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖
      ≤ 2 * Real.pi * θ := by
    calc ‖∫ α in (0 : ℝ)..(2 * Real.pi), (q α : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖
        ≤ ∫ α in (0 : ℝ)..(2 * Real.pi),
            ‖(q α : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (le_of_lt h2πpos)
      _ = ∫ α in (0 : ℝ)..(2 * Real.pi), q α := by
          apply intervalIntegral.integral_congr
          intro α _
          exact hnormint α
      _ ≤ 2 * Real.pi * θ := integral_q_le_decay q θ hθ hθ1 hqC hq1 hqsupp
  by_cases hsmall : ((θ * (ℓ:ℝ))^2) ≤ 4
  · exact le_trans htriv (decay_numeric_small θ (ℓ:ℝ) hθ hsmall)
  · rw [not_le] at hsmall
    have hl_ne : (ℓ:ℝ) ≠ 0 := by
      intro h
      rw [h, mul_zero] at hsmall
      norm_num at hsmall
    obtain ⟨hv1, hv2, hv3, hv4, hv5, hv6⟩ := q_vanish_support q θ hqC hqsupp
    have hq0' : q 0 = 0 := hv1 0 le_rfl
    have hq2π : q (2 * Real.pi) = 0 := hv2 (2 * Real.pi) h2πθ_le
    have hdq0 : deriv q 0 = 0 := hv3 0 le_rfl
    have hdq2π : deriv q (2 * Real.pi) = 0 := hv4 (2 * Real.pi) h2πθ_le
    have hibp := ibp_twice q ℓ hqC hq0' hq2π hdq0 hdq2π
    have hd2' : ∀ α, |deriv (deriv q) α| ≤ 1000 / θ ^ 2 := by
      intro α; rw [← iteratedDeriv_two_eq q]; exact hd2 α
    have hC : (-(ℓ : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have h2 : (ℓ : ℂ) = 0 := by
        rcases mul_eq_zero.mp h with h3 | h3
        · exact neg_eq_zero.mp h3
        · exact absurd h3 Complex.I_ne_zero
      exact hl_ne (by simpa using congrArg Complex.re h2)
    have hC2 : (-(ℓ : ℂ) * Complex.I)^2 ≠ 0 := pow_ne_zero 2 hC
    have hJeq : (∫ α in (0:ℝ)..(2 * Real.pi), (q α : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α))
        = ((-(ℓ : ℂ) * Complex.I)^2)⁻¹
          * ∫ α in (0:ℝ)..(2 * Real.pi),
              ((deriv (deriv q) α : ℝ) : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α) := by
      rw [eq_inv_mul_iff_mul_eq₀ hC2, mul_comm]
      exact hibp
    have hnormC : ‖((- (ℓ : ℂ) * Complex.I)^2)⁻¹‖ = ((ℓ:ℝ)^2)⁻¹ := by
      rw [norm_inv, norm_pow]
      have hc : ‖(-(ℓ : ℂ) * Complex.I)‖ = |(ℓ:ℝ)| := by
        rw [norm_mul, norm_neg, Complex.norm_intCast, Complex.norm_I, mul_one]
      rw [hc, sq_abs]
    have hL : ‖∫ α in (0:ℝ)..(2 * Real.pi),
          ((deriv (deriv q) α : ℝ) : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖
        ≤ 2 * Real.pi * θ * (1000 / θ ^ 2) := by
      calc ‖∫ α in (0:ℝ)..(2 * Real.pi),
              ((deriv (deriv q) α : ℝ) : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖
          ≤ ∫ α in (0:ℝ)..(2 * Real.pi),
              ‖((deriv (deriv q) α : ℝ) : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖ :=
            intervalIntegral.norm_integral_le_integral_norm (le_of_lt h2πpos)
        _ = ∫ α in (0:ℝ)..(2 * Real.pi), |deriv (deriv q) α| := by
            apply intervalIntegral.integral_congr
            intro α _
            show ‖((deriv (deriv q) α : ℝ) : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖
                = |deriv (deriv q) α|
            rw [norm_mul, norm_exp_int ℓ α, mul_one]
            simp
        _ ≤ 2 * Real.pi * θ * (1000 / θ ^ 2) := integral_abs_dd_le_decay q θ hθ hθ1 hqC hd2' hqsupp
    calc ‖∫ α in (0 : ℝ)..(2 * Real.pi), (q α : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖
        = ‖((- (ℓ : ℂ) * Complex.I)^2)⁻¹
            * ∫ α in (0:ℝ)..(2 * Real.pi),
                ((deriv (deriv q) α : ℝ) : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖ := by
          rw [hJeq]
      _ ≤ ‖((- (ℓ : ℂ) * Complex.I)^2)⁻¹‖
            * ‖∫ α in (0:ℝ)..(2 * Real.pi),
                ((deriv (deriv q) α : ℝ) : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖ :=
          norm_mul_le _ _
      _ = ((ℓ:ℝ)^2)⁻¹
            * ‖∫ α in (0:ℝ)..(2 * Real.pi),
                ((deriv (deriv q) α : ℝ) : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖ := by
          rw [hnormC]
      _ ≤ ((ℓ:ℝ)^2)⁻¹ * (2 * Real.pi * θ * (1000 / θ ^ 2)) :=
          mul_le_mul_of_nonneg_left hL (inv_nonneg.mpr (sq_nonneg _))
      _ ≤ 10000 * θ * (1 + (θ * (ℓ:ℝ)) ^ 2)⁻¹ :=
          decay_numeric_large θ (ℓ:ℝ) hθ hsmall

end Work.FIArea6
