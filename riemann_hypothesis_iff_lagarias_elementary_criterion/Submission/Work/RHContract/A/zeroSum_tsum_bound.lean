import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.A.zeroSum_finset_multiplicity_le

/-!
# `Work.RHContract.A.zeroSum_tsum_bound`

Under the Riemann hypothesis, for `x ≥ 2`,

`‖∑'_ρ m_ρ x^{ρ+1}/(ρ(ρ+1))‖ ≤ (2 + γ − log 4π) · x√x + 1/x`,

where the sum runs over all zeros `ρ` of the completed zeta function `ζ₁ = (s−1)·ζ`
(counted with multiplicity `m_ρ = zeta1Order ρ`).

## The argument

Every zero of `ζ₁` is either a *trivial* zero `-2(k+1)` (simple, hence `m = 1`) or a
non-trivial zero of `ζ`, which under RH has real part `1/2`.  We bound the sum of norms
(which dominates the norm of the sum) by splitting it into these two families.

* *Non-trivial part.*  On the critical line `‖ρ + 1‖² = ‖ρ‖² + 2 ≥ ‖ρ‖²`, so
  `‖m_ρ x^{ρ+1}/(ρ(ρ+1))‖ ≤ x^{3/2} · m_ρ/‖ρ‖²`, and the finite multiplicity sum
  `∑_{ρ∈S} m_ρ/‖ρ‖² ≤ 2 + γ − log 4π` (the sharp Hadamard bound, `zeroSum_finset_le_beta`
  transported to `zeta1Order` by `zeroSum_finset_multiplicity_le`).
* *Trivial part.*  `-2(k+1)` contributes exactly `x^{-(2k+1)}/((2k+2)(2k+1))`, which is at most
  `1/(x(k+1)(k+2))` since `x ≥ 2`; the injection `k ↦ -2(k+1)` turns this into a sub-sum of the
  telescoping series `∑_k 1/((k+1)(k+2)) = 1`, giving at most `1/x` in total.

Since every finite sub-sum of the norm sum is bounded by `(2 + γ − log 4π)·x√x + 1/x`, the
family is summable with the same bound on its `tsum`, and `‖∑'‖ ≤ ∑' ‖·‖` finishes the proof.
-/

namespace Work.RHContract.A

open scoped BigOperators

noncomputable section

/-! ## Elementary facts about `zeta1Order` and the tilted summand -/

/-- `zeta1Order` vanishes away from the zeros of `ζ₁`. -/
private lemma zst_zeta1Order_eq_zero_of_ne_zero {ρ : ℂ} (h : riemannZeta₁ ρ ≠ 0) :
    Commons.NumberTheory.Zeta.zeta1Order ρ = 0 := by
  unfold Commons.NumberTheory.Zeta.zeta1Order
  rw [dif_neg h]

/-- On the critical line, `‖ρ + 1‖² = ‖ρ‖² + 2`. -/
private lemma zst_norm_add_one_sq_of_re_half {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ‖ρ + 1‖ ^ 2 = ‖ρ‖ ^ 2 + 2 := by
  have hh := Complex.normSq_add ρ 1
  have h1 : Complex.normSq (ρ + 1) = Complex.normSq ρ + 1 + 2 * ρ.re := by
    rw [hh]
    simp
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hre] at h1
  linarith

/-- **Pointwise bound on the critical line.**  For `y ≥ 1` and `Re ρ = 1/2`, the tilted summand
at `ρ` is at most `y^{3/2}·m_ρ/‖ρ‖²`. -/
private lemma zst_norm_tilt_le {y : ℝ} (hy : 1 ≤ y) {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ‖(Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ) * (y : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖
      ≤ y ^ (3 / 2 : ℝ) * ((Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2) := by
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    norm_num at hre
  have hρ1 : ρ + 1 ≠ 0 := by
    intro h
    have h2 : ρ = -1 := by linear_combination h
    rw [h2] at hre
    norm_num at hre
  have hle : ‖ρ‖ ≤ ‖ρ + 1‖ := by
    have h := zst_norm_add_one_sq_of_re_half hre
    nlinarith [norm_nonneg ρ, norm_nonneg (ρ + 1)]
  have hm : (0 : ℝ) ≤ (Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) := Nat.cast_nonneg _
  have hyle : (0 : ℝ) ≤ y ^ (3 / 2 : ℝ) := Real.rpow_nonneg hypos.le _
  have hρn : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  rw [norm_div, norm_mul, norm_mul, Complex.norm_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hypos, Complex.add_re, Complex.one_re, hre]
  have h32 : (1 / 2 : ℝ) + 1 = 3 / 2 := by norm_num
  rw [h32]
  have hstep : (Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖)
      ≤ (Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2 := by
    apply div_le_div_of_nonneg_left hm (by positivity)
    nlinarith [hle, hρn]
  calc (Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) * y ^ (3 / 2 : ℝ) / (‖ρ‖ * ‖ρ + 1‖)
      = y ^ (3 / 2 : ℝ) * ((Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) /
          (‖ρ‖ * ‖ρ + 1‖)) := by ring
    _ ≤ y ^ (3 / 2 : ℝ) * ((Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hstep hyle

section

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
private theorem zst_zeta1Order_triv (k : ℕ) :
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

end

/-! ## The contribution of the trivial zeros -/

/-- The trivial zero `-2(k+1)` contributes at most `1/(y·(k+1)(k+2))`. -/
private lemma zst_norm_triv_term_le {y : ℝ} (hy : 1 ≤ y) (k : ℕ) :
    ‖(Commons.NumberTheory.Zeta.zeta1Order (-2 * ((k : ℂ) + 1)) : ℂ)
        * (y : ℂ) ^ ((-2 * ((k : ℂ) + 1)) + 1)
          / ((-2 * ((k : ℂ) + 1)) * ((-2 * ((k : ℂ) + 1)) + 1))‖
      ≤ 1 / (y * ((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hρ1 : ((-2 : ℂ) * ((k : ℂ) + 1)) + 1 = -(((2 * k + 1 : ℕ)) : ℂ) := by
    push_cast; ring
  have hre1 : (((-2 : ℂ) * ((k : ℂ) + 1)) + 1).re = -(2 * (k : ℝ) + 1) := by
    rw [hρ1, Complex.neg_re, Complex.natCast_re]
    push_cast
    ring
  have hρ : (-2 : ℂ) * ((k : ℂ) + 1) = -(((2 * (k + 1) : ℕ)) : ℂ) := by push_cast; ring
  have hN1 : ‖(-2 : ℂ) * ((k : ℂ) + 1)‖ = 2 * (k : ℝ) + 2 := by
    rw [hρ, norm_neg, Complex.norm_natCast]
    push_cast
    ring
  have hN2 : ‖((-2 : ℂ) * ((k : ℂ) + 1)) + 1‖ = 2 * (k : ℝ) + 1 := by
    rw [hρ1, norm_neg, Complex.norm_natCast]
    push_cast
    ring
  have hden : ‖((-2 : ℂ) * ((k : ℂ) + 1)) * ((-2 : ℂ) * ((k : ℂ) + 1) + 1)‖
      = (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) := by
    rw [norm_mul, hN1, hN2]
  have hnum : ‖(Commons.NumberTheory.Zeta.zeta1Order (-2 * ((k : ℂ) + 1)) : ℂ)
        * (y : ℂ) ^ ((-2 * ((k : ℂ) + 1)) + 1)‖ = 1 * y ^ (-(2 * (k : ℝ) + 1)) := by
    rw [norm_mul, zst_zeta1Order_triv k, Complex.norm_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hypos, hre1]
    norm_num
  rw [norm_div, hnum, hden]
  have hdenpos : 0 < (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) := by positivity
  have hpos1 : 0 < y * ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
  rw [div_le_div_iff₀ hdenpos hpos1]
  have hp : y ^ (-(2 * (k : ℝ) + 1)) * y = y ^ (-(2 * (k : ℝ))) := by
    nth_rewrite 2 [← Real.rpow_one y]
    rw [← Real.rpow_add hypos]
    congr 1
    ring
  have hle1 : y ^ (-(2 * (k : ℝ))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have hkle : ((k : ℝ) + 1) * ((k : ℝ) + 2) ≤ (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hb : y ^ (-(2 * (k : ℝ))) * (((k : ℝ) + 1) * ((k : ℝ) + 2))
      ≤ (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) := by
    have h1 : y ^ (-(2 * (k : ℝ))) * (((k : ℝ) + 1) * ((k : ℝ) + 2))
        ≤ 1 * (((k : ℝ) + 1) * ((k : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_right hle1 (by positivity)
    linarith [h1, hkle]
  have hexp : 1 * y ^ (-(2 * (k : ℝ) + 1)) * (y * ((k : ℝ) + 1) * ((k : ℝ) + 2))
      = y ^ (-(2 * (k : ℝ))) * (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    rw [← hp]
    ring
  linarith [hb, hexp]

/-- `Σ_k 1/((k+1)(k+2)) ≤ 1` over any finite set of indices (telescoping series). -/
private lemma zst_sum_one_div_mul_succ_le_one (s : Finset ℕ) :
    s.sum (fun k => 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) ≤ 1 := by
  classical
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range s
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hN (fun i _ _ => by positivity)) ?_
  have htel : ∀ i : ℕ,
      (1 : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 2)) = 1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2) := by
    intro i
    have h1 : ((i : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((i : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun i _ => htel i)]
  have htel2 : ∀ M : ℕ,
      (∑ i ∈ Finset.range M, (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)))
        = 1 - 1 / ((M : ℝ) + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
        have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
        field_simp
        ring
  rw [htel2]
  have hpos : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  linarith

/-- The total contribution of a finite set all of whose elements are trivial zeros. -/
private lemma zst_triv_sum_le {y : ℝ} (hy : 1 ≤ y) (T : Finset ℂ)
    (hT : ∀ ρ ∈ T, ∃ k : ℕ, ρ = -2 * ((k : ℂ) + 1)) :
    T.sum (fun ρ => ‖(Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ) * (y : ℂ) ^ (ρ + 1)
        / (ρ * (ρ + 1))‖) ≤ 1 / y := by
  classical
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  set nn : ℂ → ℕ := fun ρ =>
    if h : ∃ k : ℕ, ρ = -2 * ((k : ℂ) + 1) then Classical.choose h else 0 with hnn
  have hnn_spec : ∀ ρ ∈ T, ρ = -2 * ((nn ρ : ℂ) + 1) := by
    intro ρ hρ
    have h : ∃ k : ℕ, ρ = -2 * ((k : ℂ) + 1) := hT ρ hρ
    have hc : nn ρ = Classical.choose h := by rw [hnn]; exact dif_pos h
    rw [hc]
    exact Classical.choose_spec h
  have hinj : Set.InjOn nn ↑T := by
    intro a ha b hb hab
    have ha' := hnn_spec a (by simpa using ha)
    have hb' := hnn_spec b (by simpa using hb)
    rw [ha', hb', hab]
  have hle : T.sum (fun ρ => ‖(Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ) * (y : ℂ) ^ (ρ + 1)
        / (ρ * (ρ + 1))‖)
      ≤ T.sum (fun ρ => 1 / (y * ((nn ρ : ℝ) + 1) * ((nn ρ : ℝ) + 2))) := by
    refine Finset.sum_le_sum (fun ρ hρ => ?_)
    have hb := zst_norm_triv_term_le hy (nn ρ)
    conv_lhs => rw [hnn_spec ρ hρ]
    exact hb
  refine le_trans hle ?_
  rw [← Finset.sum_image (s := T) (g := nn)
    (f := fun k : ℕ => 1 / (y * ((k : ℝ) + 1) * ((k : ℝ) + 2))) hinj]
  have h2 : (T.image nn).sum (fun k => 1 / (y * ((k : ℝ) + 1) * ((k : ℝ) + 2)))
      = (1 / y) * (T.image nn).sum (fun k => 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    field_simp
  rw [h2]
  have h3 := zst_sum_one_div_mul_succ_le_one (T.image nn)
  have h4 : (0 : ℝ) ≤ 1 / y := by positivity
  calc (1 / y) * (T.image nn).sum (fun k => 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)))
      ≤ (1 / y) * 1 := mul_le_mul_of_nonneg_left h3 h4
    _ = 1 / y := by ring

/-! ## The finite-set bound and summability -/

/-- **Finite-set bound.**  For every finite set `T` of complex numbers and `y ≥ 1`, the sum of
the norms of the tilted summands is at most `(2 + γ − log 4π)·y^{3/2} + 1/y`. -/
private lemma zst_finset_norm_sum_le (h : RiemannHypothesis) {y : ℝ} (hy : 1 ≤ y)
    (T : Finset ℂ) :
    T.sum (fun ρ => ‖(Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ) * (y : ℂ) ^ (ρ + 1)
        / (ρ * (ρ + 1))‖) ≤
      (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) * y ^ (3 / 2 : ℝ) + 1 / y := by
  classical
  set P : ℂ → Prop := fun ρ => ∃ k : ℕ, ρ = -2 * ((k : ℂ) + 1) with hP
  have hsplit : T.sum (fun ρ => ‖(Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ)
        * (y : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖)
      = (T.filter P).sum
          (fun ρ => ‖(Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ)
            * (y : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖)
        + (T.filter (fun ρ => ¬ P ρ)).sum
          (fun ρ => ‖(Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ)
            * (y : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖) :=
    (Finset.sum_filter_add_sum_filter_not T P (fun ρ =>
      ‖(Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ)
        * (y : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖)).symm
  rw [hsplit]
  have htriv : (T.filter P).sum
      (fun ρ => ‖(Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ)
        * (y : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖) ≤ 1 / y :=
    zst_triv_sum_le hy _ (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
  have hnon : (T.filter (fun ρ => ¬ P ρ)).sum
      (fun ρ => ‖(Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ)
        * (y : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖)
      ≤ (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) * y ^ (3 / 2 : ℝ) := by
    set S : Finset ℂ := (T.filter (fun ρ => ¬ P ρ)).filter
      (fun ρ => riemannZeta₁ ρ = 0) with hS
    have hpt : (T.filter (fun ρ => ¬ P ρ)).sum
        (fun ρ => ‖(Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ)
          * (y : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖)
        ≤ (T.filter (fun ρ => ¬ P ρ)).sum (fun ρ =>
            y ^ (3 / 2 : ℝ) * ((Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2)) := by
      refine Finset.sum_le_sum (fun ρ hρ => ?_)
      by_cases hz : riemannZeta₁ ρ = 0
      · exact zst_norm_tilt_le hy
          (re_eq_half_of_riemannZeta1_eq_zero h hz (Finset.mem_filter.mp hρ).2)
      · rw [zst_zeta1Order_eq_zero_of_ne_zero hz]
        simp
    refine le_trans hpt ?_
    rw [← Finset.mul_sum]
    have hSS : (T.filter (fun ρ => ¬ P ρ)).sum
        (fun ρ => (Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2)
        = S.sum (fun ρ => (Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2) := by
      rw [hS]
      refine (Finset.sum_subset (Finset.filter_subset _ _) (fun ρ hρ hρS => ?_)).symm
      have hz : riemannZeta₁ ρ ≠ 0 := fun h =>
        hρS (Finset.mem_filter.mpr ⟨hρ, h⟩)
      rw [zst_zeta1Order_eq_zero_of_ne_zero hz]
      simp
    rw [hSS]
    have hSbound : S.sum (fun ρ => (Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2)
        ≤ 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by
      set R : ℝ := S.sum (fun ρ => ‖ρ‖) + 1 with hRdef
      have hR0 : 0 ≤ R := by
        have h0 : 0 ≤ S.sum (fun i => ‖i‖) := Finset.sum_nonneg (fun i _ => norm_nonneg i)
        rw [hRdef]; linarith
      refine zeroSum_finset_multiplicity_le h R hR0 S ?_
      intro ρ hρ
      obtain ⟨hρT, hz⟩ := Finset.mem_filter.mp hρ
      have hnt : ¬ ∃ k : ℕ, ρ = -2 * ((k : ℂ) + 1) := (Finset.mem_filter.mp hρT).2
      have hhalf := re_eq_half_of_riemannZeta1_eq_zero h hz hnt
      refine ⟨hz, ?_, ?_, ?_⟩
      · have hle : ‖ρ‖ ≤ S.sum (fun i => ‖i‖) :=
          Finset.single_le_sum (fun i _ => norm_nonneg i) hρ
        rw [hRdef]; linarith
      · rw [hhalf]; norm_num
      · rw [hhalf]; norm_num
    calc y ^ (3 / 2 : ℝ) * S.sum
          (fun ρ => (Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2)
        ≤ y ^ (3 / 2 : ℝ) * (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) :=
          mul_le_mul_of_nonneg_left hSbound (Real.rpow_nonneg (by positivity) _)
      _ = (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) * y ^ (3 / 2 : ℝ) := by
          ring
  linarith [htriv, hnon]

/-- The tilted zero sum is summable. -/
private lemma zst_tiltedZeroSum_summable (h : RiemannHypothesis) {y : ℝ} (hy : 1 ≤ y) :
    Summable (fun ρ : ℂ => (Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ) * (y : ℂ) ^ (ρ + 1)
      / (ρ * (ρ + 1))) := by
  have hb : Summable (fun ρ : ℂ => ‖(Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ)
      * (y : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) (fun T => zst_finset_norm_sum_le h hy T)
  exact Summable.of_norm hb

/-- **The tilted zero-sum bound** in the `rpow` shape. -/
private lemma zst_tiltedZeroSum_norm_le (h : RiemannHypothesis) {y : ℝ} (hy : 1 ≤ y) :
    ‖∑' ρ : ℂ, (Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ) * (y : ℂ) ^ (ρ + 1)
        / (ρ * (ρ + 1))‖
      ≤ (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) * y ^ (3 / 2 : ℝ) + 1 / y := by
  have hsumm := zst_tiltedZeroSum_summable h hy
  have hmem : ∀ᶠ T : Finset ℂ in Filter.atTop,
      (∑ ρ ∈ T, (Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ) * (y : ℂ) ^ (ρ + 1)
        / (ρ * (ρ + 1))) ∈ Metric.closedBall (0 : ℂ)
        ((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) * y ^ (3 / 2 : ℝ) + 1 / y) :=
    Filter.Eventually.of_forall (fun T => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_trans (norm_sum_le T _) (zst_finset_norm_sum_le h hy T))
  have hcl := Metric.isClosed_closedBall.mem_of_tendsto hsumm.hasSum hmem
  simpa [Metric.mem_closedBall, dist_zero_right] using hcl

/-- **Lagarias' zero-sum bound.**  Under the Riemann hypothesis, for `x ≥ 2` the tilted sum over
all zeros of `ζ₁` is at most `(2 + γ − log 4π)·x√x + 1/x`. -/
theorem zeroSum_tsum_bound (h : RiemannHypothesis) (x : ℝ) (hx : 2 ≤ x) :
    ‖∑' ρ : ℂ, (Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ) * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖ ≤
      (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) * (x * Real.sqrt x) + 1 / x := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hmain := zst_tiltedZeroSum_norm_le h hx1
  have hrpow : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx0, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rwa [hrpow] at hmain

end

end Work.RHContract.A
