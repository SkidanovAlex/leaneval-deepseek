import Mathlib
import Submission.Work.RPB1a.Defs

/-!
# `Work.RPB1a.exists_trigPoly_C1_approx`

Node N1 of the analytic (conformal-map) route to B1: a smooth `2π`-periodic loop
`u : ℝ → ℂ` is `ε`-approximated, in value and in derivative, uniformly on `ℝ`
by a trigonometric polynomial `trigPoly N a`.

The argument is self-contained (Mathlib only).

* `trigPoly_dense` (Stone–Weierstrass, via density of the Fourier monomials on
  `AddCircle (2π)`) approximates the continuous periodic `deriv u` uniformly by a
  trigonometric polynomial `q = trigPoly N b`.
* `integral_trigPoly` identifies the mean of a trigonometric polynomial with its
  constant coefficient, and the fundamental theorem of calculus gives
  `∫₀^{2π} deriv u = u (2π) - u 0 = 0`; together these bound the constant
  coefficient: `‖b 0‖ ≤ ε`.
* `exists_trigPoly_deriv` produces a trigonometric polynomial `p = trigPoly N a`
  whose derivative is `q - b 0` (an antiderivative in the trigonometric world,
  which always has zero mean) and which is normalised so that `p 0 = u 0`.
* `deriv p - deriv u = (q - deriv u) - b 0` is then small, and `p - u` is small
  by the fundamental theorem of calculus applied to `p - u` on a period, using
  `periodic_reduce` to pass from `[0, 2π]` to all of `ℝ`.
-/

namespace Work.RPB1a

open Complex Set Metric MeasureTheory
open scoped ContDiff Real BigOperators
open Work.RPB1a
open intervalIntegral

set_option linter.style.haveILetI false

/-! ## Elementary facts about `trigPoly` -/

/-- A trigonometric polynomial is `2π`-periodic. -/
private lemma trigPoly_periodic (N : ℕ) (a : ℤ → ℂ) :
    ∀ t, trigPoly N a (t + 2 * π) = trigPoly N a t := by
  intro t
  simp only [trigPoly]
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  rw [show ((n : ℂ) * ((t + 2 * π : ℝ) : ℂ) * I)
        = (n : ℂ) * (t : ℂ) * I + (n : ℂ) * ((2 * π : ℝ) : ℂ) * I by push_cast; ring]
  rw [Complex.exp_add]
  rw [show (n : ℂ) * ((2 * π : ℝ) : ℂ) * I = (n : ℂ) * (2 * (π : ℂ) * I) by push_cast; ring]
  rw [Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- A trigonometric polynomial is continuous. -/
lemma trigPoly_continuous (N : ℕ) (a : ℤ → ℂ) : Continuous (trigPoly N a) := by
  rw [show trigPoly N a
      = fun t : ℝ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          a n * Complex.exp ((n : ℂ) * (t : ℂ) * I) from rfl]
  fun_prop

/-- A trigonometric polynomial is differentiable. -/
lemma trigPoly_differentiable (N : ℕ) (a : ℤ → ℂ) : Differentiable ℝ (trigPoly N a) := by
  rw [show trigPoly N a
      = fun t : ℝ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          a n * Complex.exp ((n : ℂ) * (t : ℂ) * I) from rfl]
  fun_prop

/-- The derivative of a trigonometric polynomial, term by term. -/
lemma deriv_trigPoly (N : ℕ) (a : ℤ → ℂ) (t : ℝ) :
    deriv (trigPoly N a) t = ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
      a n * ((n : ℂ) * I) * Complex.exp ((n : ℂ) * (t : ℂ) * I) := by
  have hderiv : ∀ n ∈ Finset.Icc (-(N : ℤ)) N,
      HasDerivAt (fun s : ℝ => a n * Complex.exp ((n : ℂ) * (s : ℂ) * I))
        (a n * ((n : ℂ) * I) * Complex.exp ((n : ℂ) * (t : ℂ) * I)) t := by
    intro n _
    have hinner : HasDerivAt (fun s : ℝ => (n : ℂ) * (s : ℂ) * I) ((n : ℂ) * I) t := by
      have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
      have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) * I) I t := by simpa using h1.mul_const I
      have h3 : HasDerivAt (fun y : ℝ => (n : ℂ) * ((y : ℂ) * I)) ((n : ℂ) * I) t := by
        simpa using h2.const_mul (n : ℂ)
      simpa [mul_assoc] using h3
    have h' := hinner.cexp.const_mul (a n)
    convert h' using 1
    ring
  rw [show trigPoly N a = (fun s : ℝ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
        a n * Complex.exp ((n : ℂ) * (s : ℂ) * I)) from rfl]
  rw [deriv_fun_sum (u := Finset.Icc (-(N : ℤ)) N)
    (A := fun n (s : ℝ) => a n * Complex.exp ((n : ℂ) * (s : ℂ) * I)) (x := t)
    (fun n hn => (hderiv n hn).differentiableAt)]
  exact Finset.sum_congr rfl (fun n hn => (hderiv n hn).deriv)

/-! ## The mean of a trigonometric polynomial -/

/-- `∫₀^{2π} e^{int} dt` equals `2π` when `n = 0` (the integrand is the constant `1`) and `0`
otherwise, since the primitive `e^{int}/(i n)` takes the same value at the two endpoints. -/
theorem integral_exp_int_mul_I (n : ℤ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp ((n : ℂ) * (t : ℂ) * Complex.I)
      = if n = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  by_cases hn : n = 0
  · subst hn; simp
  · simp only [hn, ↓reduceIte]
    have hc : (n : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero
    have hrew : ∀ t : ℝ,
        (n : ℂ) * (t : ℂ) * Complex.I = ((n : ℂ) * Complex.I) * (t : ℂ) := fun t => by ring
    simp_rw [hrew]
    rw [integral_exp_mul_complex hc]
    have hexp : Complex.exp (((n : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show ((n : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)
            = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [hexp]
    simp

/-- `∫₀^{2π} trigPoly N b = 2π · b 0`: the mean of a trigonometric polynomial over a period is
its constant coefficient. -/
theorem integral_trigPoly (N : ℕ) (b : ℤ → ℂ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), trigPoly N b t = ((2 : ℝ) * Real.pi : ℂ) * b 0 := by
  simp only [trigPoly]
  rw [intervalIntegral.integral_finsetSum
    (fun n _ => Continuous.intervalIntegrable (by fun_prop) 0 (2 * Real.pi))]
  simp_rw [intervalIntegral.integral_const_mul]
  simp_rw [integral_exp_int_mul_I]
  rw [Finset.sum_eq_single 0]
  · simp [mul_comm]
  · intro n _ hn0; simp [hn0]
  · intro h0
    exact absurd (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) h0

/-! ## Density of trigonometric polynomials on the circle -/

/-- The `Ico`-lift of a periodic function to the additive circle is that function, at every real
point (the lift is independent of the chosen representative). -/
theorem liftIco_zero_coe_periodic {T : ℝ} [Fact (0 < T)] {g : ℝ → ℂ}
    (hg : Function.Periodic g T) (t : ℝ) :
    AddCircle.liftIco T 0 g (t : AddCircle T) = g t := by
  set x : ℝ := (AddCircle.equivIco T 0 (t : AddCircle T) : ℝ)
  have hxmem : x ∈ Set.Ico 0 (0 + T) := by
    simpa [x] using (AddCircle.equivIco T 0 (t : AddCircle T)).coe_prop
  have hcoe : (x : AddCircle T) = (t : AddCircle T) := by
    simpa [x] using AddCircle.coe_equivIco (p := T) (a := 0) (y := (t : AddCircle T))
  have hxeq : AddCircle.liftIco T 0 g (x : AddCircle T) = g x :=
    AddCircle.liftIco_coe_apply hxmem
  rw [← hcoe, hxeq]
  have h0 : ((x - t : ℝ) : AddCircle T) = 0 := by
    rw [AddCircle.coe_sub, hcoe, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := T)).mp h0
  have hx_t : x - n • T = t := by
    rw [hn, sub_sub_cancel]
  rw [← hx_t]
  exact (hg.sub_zsmul_eq n).symm

/-- The Fourier character on `AddCircle (2π)` evaluated at the class of a real number is the
plain exponential `exp (i n t)`. -/
lemma fourier_two_pi_coe_apply (n : ℤ) (t : ℝ) :
    fourier (T := 2 * Real.pi) n (t : AddCircle (2 * Real.pi)) =
      Complex.exp ((n : ℂ) * (t : ℂ) * Complex.I) := by
  have hT : ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by push_cast; ring
  rw [fourier_coe_apply, hT]
  congr 1
  field_simp

/-- Evaluating a `Finsupp.sum` of Fourier characters at a point gives the corresponding
`Finset.sum`. -/
lemma finsupp_sum_fourier_apply (c : ℤ →₀ ℂ) (t : ℝ) :
    (c.sum fun i a => a • fourier (T := 2 * Real.pi) i) (t : AddCircle (2 * Real.pi)) =
      ∑ i ∈ c.support, c i * fourier (T := 2 * Real.pi) i (t : AddCircle (2 * Real.pi)) := by
  simp [Finsupp.sum, smul_eq_mul]

/-- `trigPoly N (fun n => c n) t` equals the value at `(t : AddCircle (2π))` of the finite
Fourier sum `∑ i ∈ c.support, c i • fourier i`. -/
theorem trigPoly_eq_sum_fourier (c : ℤ →₀ ℂ) (t : ℝ) :
    trigPoly (c.support.sup fun i => i.natAbs) (fun n => c n) t =
      (c.sum fun i a => a • fourier (T := 2 * Real.pi) i) (t : AddCircle (2 * Real.pi)) := by
  set N : ℕ := c.support.sup fun i => i.natAbs with hN
  have hsupp : c.support ⊆ Finset.Icc (-(N : ℤ)) N := by
    intro i hi
    have h : i.natAbs ≤ N := by rw [hN]; exact Finset.le_sup hi
    simp only [Finset.mem_Icc]
    omega
  have hzero : ∀ x ∈ Finset.Icc (-(N : ℤ)) N, x ∉ c.support →
      c x * fourier (T := 2 * Real.pi) x (t : AddCircle (2 * Real.pi)) = 0 := by
    intro x _ hx
    rw [Finsupp.notMem_support_iff] at hx
    rw [hx, zero_mul]
  rw [finsupp_sum_fourier_apply, trigPoly, Finset.sum_subset hsupp hzero]
  exact Finset.sum_congr rfl fun n _ => by rw [fourier_two_pi_coe_apply]

/-- Weierstrass approximation of a continuous `2π`-periodic function by trigonometric
polynomials, uniformly on `ℝ`. -/
theorem trigPoly_dense (g : ℝ → ℂ) (hg : Continuous g)
    (hper : ∀ t, g (t + 2 * Real.pi) = g t) (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (b : ℤ → ℂ), ∀ t : ℝ, ‖trigPoly N b t - g t‖ < ε := by
  have hTpos : 0 < 2 * Real.pi := by positivity
  haveI : Fact (0 < 2 * Real.pi) := ⟨hTpos⟩
  have hgper : Function.Periodic g (2 * Real.pi) := hper
  have hcont : Continuous (AddCircle.liftIco (2 * Real.pi) 0 g) :=
    AddCircle.liftIco_zero_continuous (by simpa using (hper 0).symm)
      (hg.continuousOn (s := Set.Icc 0 (2 * Real.pi)))
  let G : C(AddCircle (2 * Real.pi), ℂ) := ⟨AddCircle.liftIco (2 * Real.pi) 0 g, hcont⟩
  have hG_coe : ∀ t : ℝ, G (t : AddCircle (2 * Real.pi)) = g t :=
    fun t => liftIco_zero_coe_periodic hgper t
  have hdense :
      G ∈ (Submodule.span ℂ (Set.range (fourier (T := 2 * Real.pi)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    exact Submodule.mem_top
  have hcl : G ∈ closure
      (↑(Submodule.span ℂ (Set.range (fourier (T := 2 * Real.pi)))) :
        Set C(AddCircle (2 * Real.pi), ℂ)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hdense
  obtain ⟨F, hFspan, hFdist⟩ := Metric.mem_closure_iff.mp hcl ε hε
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hFspan
  refine ⟨c.support.sup (fun i => i.natAbs), (fun n => c n), fun t => ?_⟩
  have key : trigPoly (c.support.sup (fun i => i.natAbs)) (fun n => c n) t
      = F (t : AddCircle (2 * Real.pi)) := by
    rw [trigPoly_eq_sum_fourier, ← hc]
  rw [key, ← hG_coe t]
  calc ‖F (t : AddCircle (2 * Real.pi)) - G (t : AddCircle (2 * Real.pi))‖
      = ‖(F - G) (t : AddCircle (2 * Real.pi))‖ := by rw [ContinuousMap.sub_apply]
    _ ≤ ‖F - G‖ := ContinuousMap.norm_coe_le_norm (F - G) (t : AddCircle (2 * Real.pi))
    _ = dist F G := (dist_eq_norm F G).symm
    _ < ε := by rw [dist_comm]; exact hFdist

/-! ## Derivatives and means of periodic functions -/

/-- The derivative of a `2π`-periodic function is `2π`-periodic. -/
theorem deriv_periodic_of_periodic (u : ℝ → ℂ) (hper : ∀ t, u (t + 2 * Real.pi) = u t) :
    ∀ t, deriv u (t + 2 * Real.pi) = deriv u t := by
  intro t
  have hfun : (fun s : ℝ => u (s + 2 * Real.pi)) = u := funext hper
  calc deriv u (t + 2 * Real.pi)
      = deriv (fun s : ℝ => u (s + 2 * Real.pi)) t :=
        (deriv_comp_add_const u (2 * Real.pi) t).symm
    _ = deriv u t := by rw [hfun]

/-- A smooth `2π`-periodic function has zero mean over a period. -/
theorem mean_deriv (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : ∀ t, u (t + 2 * Real.pi) = u t) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), deriv u t = 0 := by
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hFTC := intervalIntegral.integral_deriv_of_contDiffOn_Icc (a := 0) (b := 2 * Real.pi)
      (f := u) ((hu.of_le (by simp)).contDiffOn) h2pi
  have hu2pi : u (2 * Real.pi) = u 0 := by simpa using hper 0
  rw [hFTC, hu2pi, sub_self]

/-! ## An antiderivative inside the trigonometric polynomials -/

lemma sum_eq_erase_add (s : Finset ℤ) (h0 : 0 ∈ s) (f : ℤ → ℂ) :
    (∑ n ∈ s, f n) = (∑ n ∈ s.erase 0, f n) + f 0 := by
  conv_lhs => rw [← Finset.sum_erase_add s f h0]

lemma sum_ite_eq_erase (s : Finset ℤ) (h0 : 0 ∈ s) (c : ℂ) (f : ℤ → ℂ) :
    (∑ n ∈ s, (if n = 0 then c else f n)) = (∑ n ∈ s.erase 0, f n) + c := by
  rw [sum_eq_erase_add s h0 (fun n => if n = 0 then c else f n), if_pos rfl]
  congr 1
  exact Finset.sum_congr rfl (fun n hn => by rw [if_neg (Finset.mem_erase.mp hn).1])

lemma sum_ite_zero_erase (s : Finset ℤ) (h0 : 0 ∈ s) (f : ℤ → ℂ) :
    (∑ n ∈ s, (if n = 0 then (0 : ℂ) else f n)) = ∑ n ∈ s.erase 0, f n := by
  rw [sum_ite_eq_erase s h0 0 f, add_zero]

/-- Given any trigonometric polynomial `trigPoly N b` and any complex number `u0` there is a
trigonometric polynomial `trigPoly N a` with the same index range whose derivative is
`trigPoly N b - b 0` (the zero-mean part of `trigPoly N b`) and whose value at `0` is `u0`. -/
theorem exists_trigPoly_deriv (N : ℕ) (b : ℤ → ℂ) (u0 : ℂ) :
    ∃ a : ℤ → ℂ, (∀ t, deriv (trigPoly N a) t = trigPoly N b t - b 0) ∧ trigPoly N a 0 = u0 := by
  classical
  set V : ℂ := ∑ m ∈ (Finset.Icc (-(N : ℤ)) N).erase 0, b m / ((m : ℂ) * I) with hV
  refine ⟨fun n => if n = 0 then u0 - V else b n / ((n : ℂ) * I), ?_, ?_⟩
  · intro t
    rw [deriv_trigPoly]
    have h0mem : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) N := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have key : ∀ n ∈ Finset.Icc (-(N : ℤ)) N,
        (if n = 0 then u0 - V else b n / ((n : ℂ) * I)) * ((n : ℂ) * I)
            * Complex.exp ((n : ℂ) * (t : ℂ) * I)
        = (if n = 0 then (0 : ℂ) else b n * Complex.exp ((n : ℂ) * (t : ℂ) * I)) := by
      intro n _
      by_cases h : n = 0
      · subst h; simp
      · rw [if_neg h, if_neg h,
          div_mul_cancel₀ _ (mul_ne_zero (Int.cast_ne_zero.mpr h) Complex.I_ne_zero)]
    rw [Finset.sum_congr rfl key,
      sum_ite_zero_erase _ h0mem (fun n => b n * Complex.exp ((n : ℂ) * (t : ℂ) * I))]
    have htrig : trigPoly N b t
        = ∑ n ∈ Finset.Icc (-(N : ℤ)) N, b n * Complex.exp ((n : ℂ) * (t : ℂ) * I) := rfl
    rw [htrig, sum_eq_erase_add _ h0mem (fun n => b n * Complex.exp ((n : ℂ) * (t : ℂ) * I))]
    simp only [Int.cast_zero, zero_mul, Complex.exp_zero, mul_one]
    ring
  · simp only [trigPoly, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
    have h0mem : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) N := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [sum_ite_eq_erase _ h0mem (u0 - V) (fun n => b n / ((n : ℂ) * I)), hV]
    ring

/-! ## Reducing a periodic bound to `[0, 2π]` -/

/-- A `2π`-periodic function whose norm is `< ε` on `[0, 2π]` is `< ε` everywhere. -/
private lemma periodic_reduce {f : ℝ → ℂ} (hf : ∀ t, f (t + 2 * Real.pi) = f t) {ε : ℝ}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖f t‖ < ε) : ∀ t, ‖f t‖ < ε := by
  intro t
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  set k : ℤ := ⌊t / (2 * Real.pi)⌋ with hk
  have hk1 : (k : ℝ) * (2 * Real.pi) ≤ t := by
    have hp := Int.floor_le (t / (2 * Real.pi)); rw [← hk] at hp
    rwa [le_div_iff₀ h2pi_pos] at hp
  have hk2 : t < (k : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
    have hp := Int.lt_floor_add_one (t / (2 * Real.pi)); rw [← hk] at hp
    have hp' := (div_lt_iff₀ h2pi_pos).mp hp
    nlinarith [hp']
  have hks : k • (2 * Real.pi) = (k : ℝ) * (2 * Real.pi) := zsmul_eq_mul (2 * Real.pi) k
  have hfper : Function.Periodic f (2 * Real.pi) := hf
  have hFt : f (t - k • (2 * Real.pi)) = f t := hfper.sub_zsmul_eq k
  have hmem : t - k • (2 * Real.pi) ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    rw [hks]; exact ⟨by linarith, by linarith⟩
  have := h (t - k • (2 * Real.pi)) hmem
  rwa [hFt] at this

/-! ## Main statement -/

/-- A smooth `2π`-periodic loop is `ε`-approximated in value and derivative, uniformly, by a
trigonometric polynomial. -/
theorem exists_trigPoly_C1_approx (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : ∀ t, u (t + 2 * π) = u t) (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (a : ℤ → ℂ), ∀ t : ℝ,
      ‖trigPoly N a t - u t‖ < ε ∧ ‖deriv (trigPoly N a) t - deriv u t‖ < ε := by
  -- Tolerances: the factors `2`, `2π` are absorbed into `η`.
  set η : ℝ := ε / (4 * Real.pi + 2) with hη
  have hden : (0 : ℝ) < 4 * Real.pi + 2 := by positivity
  have hηpos : 0 < η := by rw [hη]; positivity
  have h2η : 2 * η < ε := by
    rw [hη, ← mul_div_assoc, div_lt_iff₀ hden]; nlinarith [Real.pi_pos, hε]
  have h4πη : 4 * Real.pi * η < ε := by
    rw [hη, ← mul_div_assoc, div_lt_iff₀ hden]; nlinarith [Real.pi_pos, hε]
  -- Uniform approximation of the derivative.
  have hdc : Continuous (deriv u) := hu.continuous_deriv (by simp)
  have hdp : ∀ t, deriv u (t + 2 * Real.pi) = deriv u t := deriv_periodic_of_periodic u hper
  have hmean : ∫ t in (0 : ℝ)..(2 * Real.pi), deriv u t = 0 := mean_deriv u hu hper
  obtain ⟨N, b, hb⟩ := trigPoly_dense (deriv u) hdc hdp η hηpos
  have htrigb : Continuous (trigPoly N b) := trigPoly_continuous N b
  have hnorm2pi : ‖((2 : ℝ) * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [show ((2 : ℝ) * Real.pi : ℂ) = ((2 : ℝ) : ℂ) * ((Real.pi : ℝ) : ℂ) from by
      push_cast; ring]
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
  -- The constant Fourier coefficient of the approximant is small, because both it and `deriv u`
  -- have computable means and `deriv u` has mean `0`.
  have hb0 : ‖b 0‖ ≤ η := by
    have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
    have hI1 : IntervalIntegrable (trigPoly N b) volume 0 (2 * Real.pi) :=
      htrigb.intervalIntegrable _ _
    have hI2 : IntervalIntegrable (deriv u) volume 0 (2 * Real.pi) :=
      hdc.intervalIntegrable _ _
    have hint : ∫ t in (0 : ℝ)..(2 * Real.pi), (trigPoly N b t - deriv u t)
        = ((2 : ℝ) * Real.pi : ℂ) * b 0 := by
      rw [intervalIntegral.integral_sub hI1 hI2, integral_trigPoly N b, hmean, sub_zero]
    have hbnd : ‖∫ t in (0 : ℝ)..(2 * Real.pi), (trigPoly N b t - deriv u t)‖
        ≤ η * (2 * Real.pi) := by
      have h0 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ))
        (b := 2 * Real.pi) (C := η) (f := fun t => trigPoly N b t - deriv u t)
        (fun x _ => le_of_lt (hb x))
      rwa [sub_zero, abs_of_pos h2pi_pos] at h0
    rw [hint, norm_mul, hnorm2pi] at hbnd
    rw [mul_comm η] at hbnd
    exact le_of_mul_le_mul_left hbnd h2pi_pos
  -- The trigonometric antiderivative `p = trigPoly N a` of `q - b 0`, normalised at `0`.
  obtain ⟨a, hderivp, hpa0⟩ := exists_trigPoly_deriv N b (u 0)
  have hdu : Differentiable ℝ u := hu.differentiable (by simp)
  have hda : Differentiable ℝ (trigPoly N a) := trigPoly_differentiable N a
  set F : ℝ → ℂ := fun s => trigPoly N a s - u s with hFdef
  have hdiffF : Differentiable ℝ F := by rw [hFdef]; exact hda.sub hdu
  have hderivF : ∀ s, deriv F s = deriv (trigPoly N a) s - deriv u s := by
    intro s
    rw [hFdef]
    exact deriv_sub hda.differentiableAt hdu.differentiableAt
  have hbound' : ∀ s, ‖(trigPoly N b s - b 0) - deriv u s‖ ≤ 2 * η := by
    intro s
    have heq : (trigPoly N b s - b 0) - deriv u s = (trigPoly N b s - deriv u s) - b 0 := by
      ring
    rw [heq]
    calc ‖(trigPoly N b s - deriv u s) - b 0‖
          ≤ ‖trigPoly N b s - deriv u s‖ + ‖b 0‖ := norm_sub_le _ _
      _ ≤ 2 * η := by have h1 := hb s; have h2 := hb0; linarith
  have hdF : Continuous (deriv F) := by
    rw [show deriv F = fun s => (trigPoly N b s - b 0) - deriv u s from
      funext (fun s => by rw [hderivF s, hderivp s])]
    exact (htrigb.sub continuous_const).sub hdc
  have hFper : ∀ t, F (t + 2 * Real.pi) = F t := by
    intro t
    simp only [hFdef]
    rw [trigPoly_periodic N a t, hper t]
  have hF0 : F 0 = 0 := by rw [hFdef]; simp [hpa0]
  -- On one period the value error is at most `2π · (2η)`, by the fundamental theorem of calculus.
  have hval_Icc : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖F t‖ < ε := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht.1
    have ht2 : t ≤ 2 * Real.pi := ht.2
    have hFTC : ∫ s in (0 : ℝ)..t, deriv F s = F t - F 0 :=
      intervalIntegral.integral_deriv_eq_sub (fun x _ => hdiffF.differentiableAt)
        (hdF.intervalIntegrable 0 t)
    have hthis : ∫ s in (0 : ℝ)..t, deriv F s = F t := by rw [hFTC, hF0, sub_zero]
    rw [← hthis]
    have hbnd : ‖∫ s in (0 : ℝ)..t, deriv F s‖ ≤ (2 * η) * |t - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => by
        rw [hderivF x, hderivp x]; exact hbound' x)
    calc ‖∫ s in (0 : ℝ)..t, deriv F s‖ ≤ (2 * η) * |t - 0| := hbnd
      _ = (2 * η) * t := by rw [sub_zero, abs_of_nonneg ht0]
      _ ≤ (2 * η) * (2 * Real.pi) := by
          apply mul_le_mul_of_nonneg_left ht2; positivity
      _ = 4 * Real.pi * η := by ring
      _ < ε := h4πη
  have hval_all : ∀ t, ‖F t‖ < ε := periodic_reduce hFper hval_Icc
  refine ⟨N, a, ?_⟩
  intro t
  exact ⟨by simpa only [hFdef] using hval_all t,
    by rw [hderivp t]; exact lt_of_le_of_lt (hbound' t) h2η⟩

end Work.RPB1a
