import Mathlib

/-!
# Logarithmic derivative of the principal Dirichlet L-function

For the principal character `1` modulo `q` the Euler product gives

`L(s, 1) = ζ(s) * ∏_{p ∣ q} (1 - p^{-s})`   (`DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta`),

so on the half plane `1 < re s` the logarithmic derivative splits as

`(logDeriv L(·, 1))(s) = (logDeriv ζ)(s) + ∑_{p ∣ q} (log p) / (p^s - 1)`.

Differentiating `j ≤ 2` times (both pieces are analytic on this half plane, hence
`C^j`) gives the statement below, which is the decomposition of the logarithmic
derivative of the principal L-function used in the zero-free region argument.

The file is organised as:

* `logDeriv_one_sub_prime_cpow` : the individual Euler factor,
* `analyticAt_logDeriv_riemannZeta`, `analyticAt_eulerSum` : analyticity of the
  two pieces on `1 < re s`,
* `logDeriv_LFunctionTrivChar_eq` : the pointwise decomposition,
* `LogDerivPrincipalDecomp` : the differentiated form.
-/

open Complex Filter
open scoped Topology

namespace Work.ZeroFreeTables.XY.PrincipalSigma

lemma differentiableAt_prime_cpow_neg (p : ℕ) (hp : p.Prime) (z : ℂ) :
    DifferentiableAt ℂ (fun w : ℂ => (p : ℂ) ^ (-w)) z := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  exact (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => -w) z).const_cpow (Or.inl hp0)

lemma differentiableAt_one_sub_prime_cpow (p : ℕ) (hp : p.Prime) (z : ℂ) :
    DifferentiableAt ℂ (fun w : ℂ => 1 - (p : ℂ) ^ (-w)) z :=
  (differentiableAt_const (1 : ℂ)).sub (differentiableAt_prime_cpow_neg p hp z)

/-- Logarithmic derivative of a single Euler factor `w ↦ 1 - p ^ (-w)`. -/
lemma logDeriv_one_sub_prime_cpow (p : ℕ) (hp : p.Prime) {z : ℂ} (hz : 1 < z.re) :
    logDeriv (fun w : ℂ => 1 - (p : ℂ) ^ (-w)) z
      = (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hne1 : 1 - (p : ℂ) ^ (-z) ≠ 0 := Complex.one_sub_prime_cpow_ne_zero hp hz
  have hcz : (p : ℂ) ^ z ≠ 0 := fun h => hp0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hderiv : deriv (fun w : ℂ => (p : ℂ) ^ (-w)) z
      = -(Complex.log (p : ℂ) * (p : ℂ) ^ (-z)) := by
    rw [Complex.deriv_const_cpow (f := fun w : ℂ => -w) (x := z) (by fun_prop) (p : ℂ),
      deriv_neg'']
    ring
  have hf_deriv : deriv (fun w : ℂ => 1 - (p : ℂ) ^ (-w)) z
      = Complex.log (p : ℂ) * (p : ℂ) ^ (-z) := by
    rw [deriv_const_sub (1 : ℂ), hderiv]
    ring
  have hfac : 1 - ((p : ℂ) ^ z)⁻¹ = ((p : ℂ) ^ z - 1) * ((p : ℂ) ^ z)⁻¹ := by
    rw [sub_mul, one_mul, mul_inv_cancel₀ hcz]
  simp only [logDeriv_apply, hf_deriv]
  rw [Complex.cpow_neg, hfac, mul_div_mul_right _ _ (inv_ne_zero hcz), ← Complex.natCast_log]

/-- The logarithmic derivative of `ζ` is analytic on `1 < re s`. -/
lemma analyticAt_logDeriv_riemannZeta {z : ℂ} (hz : 1 < z.re) :
    AnalyticAt ℂ (logDeriv riemannZeta) z := by
  have hz1 : z ≠ 1 := by rintro rfl; simp at hz
  have hA : AnalyticAt ℂ riemannZeta z := analyticOn_riemannZeta z (by simpa using hz1)
  have hD : AnalyticAt ℂ (deriv riemannZeta) z := hA.deriv
  have h0 : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz
  simpa only [logDeriv] using hD.div hA h0

/-- The finite Euler factor sum is analytic on `1 < re s`. -/
lemma analyticAt_eulerSum (q : ℕ) [NeZero q] {z : ℂ} (hz : 1 < z.re) :
    AnalyticAt ℂ (fun z : ℂ => ∑ p ∈ q.primeFactors,
      (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) z := by
  have hterm : ∀ p ∈ q.primeFactors, AnalyticAt ℂ
      (fun w : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ w - 1)) z := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpos : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
    have hne : (p : ℂ) ^ z - 1 ≠ 0 := by
      intro h
      apply Complex.one_sub_prime_cpow_ne_zero hprime hz
      have h' : (p : ℂ) ^ z = 1 := sub_eq_zero.mp h
      rw [Complex.cpow_neg, h', inv_one, sub_self]
    have hcpow : AnalyticAt ℂ (fun w : ℂ => (p : ℂ) ^ w) z :=
      AnalyticAt.cpow analyticAt_const analyticAt_id ((Complex.ofReal_mem_slitPlane).mpr hpos)
    exact (analyticAt_const (v := (Real.log (p : ℝ) : ℂ))).div
      (hcpow.sub (analyticAt_const (v := (1 : ℂ)))) hne
  have h := Finset.analyticAt_sum (q.primeFactors) hterm
  have hfun : (∑ p ∈ q.primeFactors,
        (fun w : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ w - 1)))
      = (fun z : ℂ => ∑ p ∈ q.primeFactors,
          (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) := by
    funext w
    exact (Finset.sum_apply w q.primeFactors
      (fun p w => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ w - 1)))
  rw [hfun] at h
  exact h

/-- Pointwise decomposition of the logarithmic derivative of the principal character's
L-function on the half plane `1 < re z`. -/
lemma logDeriv_LFunctionTrivChar_eq (q : ℕ) [NeZero q] {z : ℂ} (hz : 1 < z.re) :
    logDeriv (DirichletCharacter.LFunctionTrivChar q) z
      = logDeriv riemannZeta z + ∑ p ∈ q.primeFactors,
          (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1) := by
  have hz1 : z ≠ 1 := by rintro rfl; simp at hz
  have hev : DirichletCharacter.LFunctionTrivChar q =ᶠ[𝓝 z]
      (fun y => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-y))) * riemannZeta y) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hz] with y hy
    exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (by rintro rfl; simp at hy)
  have hPne : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp =>
      Complex.one_sub_prime_cpow_ne_zero (Nat.prime_of_mem_primeFactors hp) hz
  have hζne : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz
  have hPd : DifferentiableAt ℂ
      (fun w : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-w))) z :=
    DifferentiableAt.fun_finsetProd fun p hp =>
      differentiableAt_one_sub_prime_cpow p (Nat.prime_of_mem_primeFactors hp) z
  have hζd : DifferentiableAt ℂ riemannZeta z := differentiableAt_riemannZeta hz1
  calc logDeriv (DirichletCharacter.LFunctionTrivChar q) z
      = logDeriv (fun y => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-y))) * riemannZeta y) z :=
        (logDeriv_congr_nhds hev).eq_of_nhds
    _ = logDeriv (fun w : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-w))) z
          + logDeriv riemannZeta z := by
        erw [logDeriv_mul z hPne hζne hPd hζd]
    _ = (∑ p ∈ q.primeFactors, logDeriv (fun w : ℂ => 1 - (p : ℂ) ^ (-w)) z)
          + logDeriv riemannZeta z := by
        have h := logDeriv_prod (s := q.primeFactors)
          (f := fun (p : ℕ) (w : ℂ) => 1 - (p : ℂ) ^ (-w)) (x := z)
          (fun p hp => Complex.one_sub_prime_cpow_ne_zero (Nat.prime_of_mem_primeFactors hp) hz)
          (fun p hp => differentiableAt_one_sub_prime_cpow p (Nat.prime_of_mem_primeFactors hp) z)
        simp only [Finset.prod_fn] at h
        rw [h]
    _ = (∑ p ∈ q.primeFactors, (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1))
          + logDeriv riemannZeta z := by
        congr 1
        exact Finset.sum_congr rfl fun p hp =>
          logDeriv_one_sub_prime_cpow p (Nat.prime_of_mem_primeFactors hp) hz
    _ = logDeriv riemannZeta z + ∑ p ∈ q.primeFactors,
          (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1) := by
        rw [add_comm]

theorem LogDerivPrincipalDecomp (q : ℕ) [NeZero q] (j : ℕ) (hj : j ≤ 2) {s : ℂ}
    (hs : 1 < s.re) :
    iteratedDeriv j (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))) s
      = iteratedDeriv j (logDeriv riemannZeta) s
        + iteratedDeriv j (fun z : ℂ => ∑ p ∈ q.primeFactors,
            (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s := by
  have hfun : logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) =ᶠ[𝓝 s]
      (logDeriv riemannZeta + fun z : ℂ => ∑ p ∈ q.primeFactors,
          (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    exact logDeriv_LFunctionTrivChar_eq q hz
  rw [Filter.EventuallyEq.iteratedDeriv_eq j hfun]
  exact iteratedDeriv_add (analyticAt_logDeriv_riemannZeta hs).contDiffAt
    (analyticAt_eulerSum q hs).contDiffAt

end Work.ZeroFreeTables.XY.PrincipalSigma
