import Mathlib
import Submission.Work.RHContract.Corpus

namespace Work.RHContract.A

open Complex MeasureTheory Filter
open scoped Real Topology BigOperators

/-!
# The trivial zeros of `ζ₁ = (s-1)·ζ` are simple

`Commons.NumberTheory.Zeta.zeta1Order ρ` is the multiplicity of `ρ` as a zero of
`riemannZeta₁`, as extracted from `Commons.NumberTheory.Zeta.zeta1_logDeriv_pole_removal`
(or `0` if `ρ` is not a zero).  The trivial zeros of `ζ` are the negative even integers
`-2 (k+1)`; they are simple, so `zeta1Order` equals `1` there.

The proof goes through the standard reflection formula
`ζ(s) = 2^s π^(s-1) sin(πs/2) Γ(1-s) ζ(1-s)`
near `s = -2(k+1)`: the sine factor has a simple zero there while every other factor is
analytic and non-zero, so `deriv riemannZeta (-2(k+1)) ≠ 0`.  Since `riemannZeta₁ s = (s-1)·ζ s`
near the point, also `deriv riemannZeta₁ (-2(k+1)) ≠ 0`, and at a simple zero the `m`
produced by the pole removal of the logarithmic derivative must equal `1`.
-/

/-- If `f` is analytic at `x` with a simple zero there and `F` is analytic at `x` with
`F = logDeriv f - m / (· - x)` on a punctured neighbourhood, then `m = 1`.  This is the
uniqueness of the order of the pole of the logarithmic derivative at a simple zero. -/
private lemma order_eq_one_of_logDeriv_sub_pole {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hfx : f x = 0) (hfd : deriv f x ≠ 0)
    (m : ℕ) {F : ℂ → ℂ} (hF : AnalyticAt ℂ F x)
    (hEv : ∀ᶠ s in 𝓝[≠] x, F s = logDeriv f s - m / (s - x)) : m = 1 := by
  have h1 : Tendsto (fun s => (s - x) * logDeriv f s) (𝓝[≠] x) (𝓝 1) :=
    AnalyticAt.tendsto_mul_logDeriv_simple_zero hf hfx hfd
  have hcont : Tendsto F (𝓝[≠] x) (𝓝 (F x)) :=
    Filter.Tendsto.mono_left hF.continuousAt.tendsto (nhdsWithin_le_nhds (a := x) (s := {x}ᶜ))
  have hsub : Tendsto (fun s : ℂ => s - x) (𝓝[≠] x) (𝓝 (0 : ℂ)) := by
    have hc : ContinuousAt (fun s : ℂ => s - x) x :=
      (continuousAt_id (x := x)).sub (continuousAt_const (y := x) (x := x))
    simpa using Filter.Tendsto.mono_left hc.tendsto (nhdsWithin_le_nhds (a := x) (s := {x}ᶜ))
  have hmul : Tendsto (fun s => (s - x) * F s) (𝓝[≠] x) (𝓝 ((0 : ℂ) * F x)) := hsub.mul hcont
  have hzero1 : (0 : ℂ) * F x = 0 := by ring
  rw [hzero1] at hmul
  have hadd : Tendsto (fun s => (s - x) * F s + (m : ℂ)) (𝓝[≠] x) (𝓝 ((m : ℂ))) := by
    simpa using hmul.add (tendsto_const_nhds (x := (m : ℂ)) (f := 𝓝[≠] x))
  have h2 : Tendsto (fun s => (s - x) * logDeriv f s) (𝓝[≠] x) (𝓝 (m : ℂ)) := by
    refine hadd.congr' ?_
    filter_upwards [hEv, self_mem_nhdsWithin] with s hs hsx
    rw [hs]
    have : s - x ≠ 0 := sub_ne_zero.mpr hsx
    field_simp
    ring
  have hfin : (1 : ℂ) = (m : ℂ) := tendsto_nhds_unique h1 h2
  exact_mod_cast hfin.symm

/-- The real cosine of `(2n+3)π/2` vanishes. -/
private lemma real_cos_odd_pi_half (n : ℕ) :
    Real.cos ((2 * n + 3 : ℝ) * Real.pi / 2) = 0 := by
  have h : (2 * n + 3 : ℝ) * Real.pi / 2 = Real.pi * 3 / 2 + (n : ℝ) * Real.pi := by ring
  rw [h, Real.cos_add]
  have h1 : Real.cos (Real.pi * 3 / 2) = 0 := by
    rw [show Real.pi * 3 / 2 = 3 * Real.pi / 2 by ring,
      show (3:ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 by ring, Real.cos_add]
    simp [Real.cos_pi, Real.sin_pi]
  have h2 : Real.sin (Real.pi * 3 / 2) = -1 := by
    rw [show Real.pi * 3 / 2 = 3 * Real.pi / 2 by ring,
      show (3:ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 by ring, Real.sin_add]
    simp [Real.cos_pi, Real.sin_pi]
  rw [h1, h2, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
  ring

/-- The real sine of `(2n+3)π/2` does not vanish. -/
private lemma real_sin_odd_pi_half_ne_zero (n : ℕ) :
    Real.sin ((2 * n + 3 : ℝ) * Real.pi / 2) ≠ 0 := by
  have h : (2 * n + 3 : ℝ) * Real.pi / 2 = Real.pi * 3 / 2 + (n : ℝ) * Real.pi := by ring
  rw [h, Real.sin_add]
  have h1 : Real.cos (Real.pi * 3 / 2) = 0 := by
    rw [show Real.pi * 3 / 2 = 3 * Real.pi / 2 by ring,
      show (3:ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 by ring, Real.cos_add]
    simp [Real.cos_pi, Real.sin_pi]
  have h2 : Real.sin (Real.pi * 3 / 2) = -1 := by
    rw [show Real.pi * 3 / 2 = 3 * Real.pi / 2 by ring,
      show (3:ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 by ring, Real.sin_add]
    simp [Real.cos_pi, Real.sin_pi]
  rw [h1, h2, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
  simp

private lemma one_sub_neg_two_mul_nat_add_one (n : ℕ) :
    (1 : ℂ) - (-2 * ((n : ℂ) + 1)) = ((2 * n + 3 : ℕ) : ℂ) := by
  push_cast; ring

private lemma one_sub_rho_re (n : ℕ) :
    ((1 : ℂ) - (-2 * ((n : ℂ) + 1))).re = (2 * n + 3 : ℝ) := by
  rw [one_sub_neg_two_mul_nat_add_one]; simp

/-- The product `zPhiP w * zPhiQ w` rewriting of the reflection formula: the factors
other than the sine. -/
private noncomputable def zPhiP (w : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-(1 - w)) * Gamma (1 - w) * riemannZeta (1 - w)

/-- The vanishing sine factor of the reflection formula. -/
private noncomputable def zPhiQ (w : ℂ) : ℂ :=
  Complex.cos ((Real.pi : ℂ) * (1 - w) / 2)

private lemma zPhiQ_arg (n : ℕ) :
    (Real.pi : ℂ) * (1 - (-2 * ((n : ℂ) + 1))) / 2
      = (((2 * n + 3 : ℝ) * Real.pi / 2 : ℝ) : ℂ) := by
  rw [one_sub_neg_two_mul_nat_add_one]
  push_cast
  ring

private lemma zPhiQ_zero (n : ℕ) : zPhiQ (-2 * ((n : ℂ) + 1)) = 0 := by
  simp only [zPhiQ, zPhiQ_arg n, ← Complex.ofReal_cos, real_cos_odd_pi_half]
  simp

private lemma zPhiQ_sin_ne_zero (n : ℕ) :
    Complex.sin ((Real.pi : ℂ) * (1 - (-2 * ((n : ℂ) + 1))) / 2) ≠ 0 := by
  rw [zPhiQ_arg n, ← Complex.ofReal_sin]
  exact_mod_cast real_sin_odd_pi_half_ne_zero n

private lemma pi_complex_ne_zero : (Real.pi : ℂ) ≠ 0 := by
  exact_mod_cast Real.pi_ne_zero

private lemma base_ne_zero : (2 * (Real.pi : ℂ)) ≠ 0 :=
  mul_ne_zero two_ne_zero pi_complex_ne_zero

private lemma zPhiP_differentiable (n : ℕ) :
    DifferentiableAt ℂ zPhiP (-2 * ((n : ℂ) + 1)) := by
  have hne : ∀ m : ℕ, (1 : ℂ) - (-2 * ((n : ℂ) + 1)) ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    rw [one_sub_rho_re] at this
    simp only [Complex.neg_re, Complex.natCast_re] at this
    have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have hne1 : (1 : ℂ) - (-2 * ((n : ℂ) + 1)) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [one_sub_rho_re] at this
    simp at this
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hcpow : DifferentiableAt ℂ
      (fun w : ℂ => (2 * (Real.pi : ℂ)) ^ (-(1 - w))) (-2 * ((n : ℂ) + 1)) :=
    DifferentiableAt.const_cpow (f := fun w : ℂ => -(1 - w)) (by fun_prop) (Or.inl base_ne_zero)
  have hA : DifferentiableAt ℂ
      (fun w : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-(1 - w))) (-2 * ((n : ℂ) + 1)) :=
    hcpow.const_mul 2
  have hG : DifferentiableAt ℂ (fun w : ℂ => Gamma (1 - w)) (-2 * ((n : ℂ) + 1)) :=
    (differentiableAt_Gamma (1 - (-2 * ((n : ℂ) + 1))) hne).comp _ (by fun_prop)
  have hZ : DifferentiableAt ℂ (fun w : ℂ => riemannZeta (1 - w)) (-2 * ((n : ℂ) + 1)) :=
    (differentiableAt_riemannZeta (s := 1 - (-2 * ((n : ℂ) + 1))) hne1).comp _ (by fun_prop)
  unfold zPhiP
  exact (hA.mul hG).mul hZ

private lemma zPhiQ_differentiable (n : ℕ) :
    DifferentiableAt ℂ zPhiQ (-2 * ((n : ℂ) + 1)) := by
  unfold zPhiQ
  exact Complex.differentiableAt_cos.comp _ (by fun_prop)

private lemma zPhiP_ne_zero (n : ℕ) : zPhiP (-2 * ((n : ℂ) + 1)) ≠ 0 := by
  have hts : (1 : ℂ) - (-2 * ((n : ℂ) + 1)) ≠ 0 := by
    rw [one_sub_neg_two_mul_nat_add_one]
    exact_mod_cast (by omega : (2 * n + 3 : ℕ) ≠ 0)
  have hexp : (-(1 - (-2 * ((n : ℂ) + 1)))) ≠ 0 := neg_ne_zero.mpr hts
  have hcpow0 : (2 * (Real.pi : ℂ)) ^ (-(1 - (-2 * ((n : ℂ) + 1)))) ≠ 0 :=
    (Complex.cpow_ne_zero_iff_of_exponent_ne_zero hexp).mpr base_ne_zero
  have hGam0 : Gamma (1 - (-2 * ((n : ℂ) + 1))) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [one_sub_rho_re]; positivity)
  have hzeta0 : riemannZeta (1 - (-2 * ((n : ℂ) + 1))) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    rw [one_sub_rho_re]
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  unfold zPhiP
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hcpow0) hGam0) hzeta0

private lemma zPhiQ_deriv (n : ℕ) :
    deriv zPhiQ (-2 * ((n : ℂ) + 1))
      = Complex.sin ((Real.pi : ℂ) * (1 - (-2 * ((n : ℂ) + 1))) / 2) * ((Real.pi : ℂ) / 2) := by
  unfold zPhiQ
  have hu : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * (1 - w) / 2) (-((Real.pi : ℂ)/2))
      (-2 * ((n : ℂ) + 1)) := by
    have h1 : HasDerivAt (fun w : ℂ => (1:ℂ) - w) (-1) (-2 * ((n : ℂ) + 1)) := by
      simpa using (hasDerivAt_id (-2 * ((n : ℂ) + 1))).const_sub (1:ℂ)
    have h2 : HasDerivAt (fun w : ℂ => ((Real.pi:ℂ)/2) * (1 - w)) (((Real.pi:ℂ)/2) * (-1))
        (-2 * ((n : ℂ) + 1)) :=
      h1.const_mul ((Real.pi:ℂ)/2)
    convert h2 using 1
    · ext w; ring
    · ring
  have h := (Complex.hasDerivAt_cos ((Real.pi : ℂ) * (1 - (-2 * ((n : ℂ) + 1))) / 2)).comp
      (-2 * ((n : ℂ) + 1)) hu
  rw [show deriv (fun w : ℂ => Complex.cos ((Real.pi : ℂ) * (1 - w) / 2)) (-2 * ((n : ℂ) + 1))
        = deriv (Complex.cos ∘ fun w : ℂ => (Real.pi : ℂ) * (1 - w) / 2) (-2 * ((n : ℂ) + 1))
        from rfl,
      h.deriv]
  ring

private lemma zPhiQ_deriv_ne_zero (n : ℕ) : deriv zPhiQ (-2 * ((n : ℂ) + 1)) ≠ 0 := by
  rw [zPhiQ_deriv]
  exact mul_ne_zero (zPhiQ_sin_ne_zero n) (div_ne_zero pi_complex_ne_zero two_ne_zero)

private lemma rho_re_neg (n : ℕ) : (-2 * ((n : ℂ) + 1)).re < 0 := by
  have h : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
  rw [h]
  have hp : (0:ℝ) < (n:ℝ) + 1 := by positivity
  linarith

private lemma eventually_re_neg (n : ℕ) : ∀ᶠ w in 𝓝 (-2 * ((n : ℂ) + 1)), w.re < 0 :=
  (continuous_re.continuousAt (x := -2 * ((n : ℂ) + 1))).eventually
    (eventually_lt_nhds (rho_re_neg n))

/-- Near `-2 (n+1)` the reflection formula rewrites `ζ` as `zPhiP * zPhiQ`. -/
private lemma riemannZeta_eventuallyEq_zPhi (n : ℕ) :
    riemannZeta =ᶠ[𝓝 (-2 * ((n : ℂ) + 1))] (fun w => zPhiP w * zPhiQ w) := by
  filter_upwards [eventually_re_neg n] with w hw
  have h1 : ∀ m : ℕ, (1 : ℂ) - w ≠ -(m : ℂ) := by
    intro m hm
    have := congrArg Complex.re hm
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at this
    have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have h2 : (1 : ℂ) - w ≠ 1 := by
    intro hm
    have := congrArg Complex.re hm
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith
  have h := riemannZeta_one_sub h1 h2
  simp only [zPhiP, zPhiQ]
  rw [show riemannZeta w = 2 * (2 * (Real.pi : ℂ)) ^ (-(1 - w)) * Gamma (1 - w)
        * Complex.cos ((Real.pi : ℂ) * (1 - w) / 2) * riemannZeta (1 - w) by
      simpa using h]
  ring

/-- `ζ` has a non-vanishing derivative at the trivial zero `-2 (n+1)`. -/
private theorem deriv_riemannZeta_neg_two_mul_nat_add_one_ne_zero (n : ℕ) :
    deriv riemannZeta (-2 * ((n : ℂ) + 1)) ≠ 0 := by
  have hfe := riemannZeta_eventuallyEq_zPhi n
  have hderiv : deriv riemannZeta (-2 * ((n : ℂ) + 1))
      = deriv (fun w => zPhiP w * zPhiQ w) (-2 * ((n : ℂ) + 1)) := hfe.deriv_eq
  have hPd := zPhiP_differentiable n
  have hQd := zPhiQ_differentiable n
  have hprod : deriv (fun w => zPhiP w * zPhiQ w) (-2 * ((n : ℂ) + 1))
      = deriv zPhiP (-2 * ((n : ℂ) + 1)) * zPhiQ (-2 * ((n : ℂ) + 1))
        + zPhiP (-2 * ((n : ℂ) + 1)) * deriv zPhiQ (-2 * ((n : ℂ) + 1)) :=
    deriv_mul hPd hQd
  rw [hderiv, hprod, zPhiQ_zero n]
  simp only [mul_zero, zero_add]
  exact mul_ne_zero (zPhiP_ne_zero n) (zPhiQ_deriv_ne_zero n)

private lemma rho_ne_one (n : ℕ) : (-2 * ((n : ℂ) + 1)) ≠ 1 := by
  intro h
  have := rho_re_neg n
  rw [h] at this
  norm_num at this

/-- Near `-2 (n+1)` the completed zeta function `ζ₁` equals `(s-1) ζ s`. -/
private lemma riemannZeta_one_eq (n : ℕ) :
    riemannZeta₁ =ᶠ[𝓝 (-2 * ((n : ℂ) + 1))]
      (fun s => (s - 1) * riemannZeta s) := by
  filter_upwards [eventually_ne_nhds (rho_ne_one n)] with s hs
  have h := riemannZeta_eq_inv_sub_mul (s := s) hs
  rw [h]
  have : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp

/-- `ζ₁` has a non-vanishing derivative at the trivial zero `-2 (n+1)`. -/
private theorem deriv_riemannZeta_one_neg_two_mul_nat_add_one_ne_zero (n : ℕ) :
    deriv riemannZeta₁ (-2 * ((n : ℂ) + 1)) ≠ 0 := by
  have hfe := riemannZeta_one_eq n
  have hderiv : deriv riemannZeta₁ (-2 * ((n : ℂ) + 1))
      = deriv (fun s => (s - 1) * riemannZeta s) (-2 * ((n : ℂ) + 1)) := hfe.deriv_eq
  have hd1 : DifferentiableAt ℂ (fun s : ℂ => s - 1) (-2 * ((n : ℂ) + 1)) := by fun_prop
  have hd2 : DifferentiableAt ℂ riemannZeta (-2 * ((n : ℂ) + 1)) :=
    differentiableAt_riemannZeta (s := -2 * ((n : ℂ) + 1)) (rho_ne_one n)
  have hprod : deriv (fun s => (s - 1) * riemannZeta s) (-2 * ((n : ℂ) + 1))
      = deriv (fun s : ℂ => s - 1) (-2 * ((n : ℂ) + 1))
          * riemannZeta (-2 * ((n : ℂ) + 1))
        + (( -2 * ((n : ℂ) + 1)) - 1) * deriv riemannZeta (-2 * ((n : ℂ) + 1)) := by
    rw [show deriv (fun s : ℂ => (s - 1) * riemannZeta s) (-2 * ((n : ℂ) + 1))
          = deriv ((fun s : ℂ => s - 1) * riemannZeta) (-2 * ((n : ℂ) + 1)) from rfl,
        deriv_mul hd1 hd2]
  have hdsub : deriv (fun s : ℂ => s - 1) (-2 * ((n : ℂ) + 1)) = 1 :=
    ((hasDerivAt_id (-2 * ((n : ℂ) + 1))).sub_const (1:ℂ)).deriv
  rw [hderiv, hprod, hdsub, riemannZeta_neg_two_mul_nat_add_one n]
  simp only [mul_zero, zero_add]
  exact mul_ne_zero (by
    intro h; have hr := rho_re_neg n; rw [sub_eq_zero] at h; rw [h] at hr; norm_num at hr)
    (deriv_riemannZeta_neg_two_mul_nat_add_one_ne_zero n)

-- The trivial zeros of `ζ₁ = (s-1)·ζ`, i.e. the points `-2(k+1)`, are simple.
theorem zeta1Order_triv (k : ℕ) :
    Commons.NumberTheory.Zeta.zeta1Order (-2 * ((k : ℂ) + 1)) = 1 := by
  set ρ : ℂ := -2 * ((k : ℂ) + 1) with hρ
  have hzero : riemannZeta₁ ρ = 0 := by
    rw [hρ]
    have h := riemannZeta_eq_inv_sub_mul (s := -2 * ((k : ℂ) + 1)) (rho_ne_one k)
    rw [riemannZeta_neg_two_mul_nat_add_one k] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (inv_ne_zero (sub_ne_zero.mpr (rho_ne_one k)))
  have hana : AnalyticAt ℂ riemannZeta₁ ρ := differentiable_riemannZeta₁.analyticAt ρ
  have hderiv : deriv riemannZeta₁ ρ ≠ 0 := by
    rw [hρ]; exact deriv_riemannZeta_one_neg_two_mul_nat_add_one_ne_zero k
  rw [Commons.NumberTheory.Zeta.zeta1Order, dif_pos hzero]
  have hspec := Classical.choose_spec (Commons.NumberTheory.Zeta.zeta1_logDeriv_pole_removal ρ hzero)
  obtain ⟨hm1, F, hFana, hFev⟩ := hspec
  exact order_eq_one_of_logDeriv_sub_pole hana hzero hderiv
    (Classical.choose (Commons.NumberTheory.Zeta.zeta1_logDeriv_pole_removal ρ hzero)) hFana hFev

end Work.RHContract.A
