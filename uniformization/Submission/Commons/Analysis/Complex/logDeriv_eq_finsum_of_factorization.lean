import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Meromorphic.FactorizedRational

/-!
# Logarithmic derivative of a factored analytic function

If a holomorphic function `f` on an open set `U` factors as

  `f z = (∏ᶠ u, (z - u) ^ (d u)) * g z`   (`z ∈ U`)

with `d : ℂ → ℤ` of finite support and `g` analytic and nowhere zero on `U`,
then at every point `x ∈ U` where `f x ≠ 0` the logarithmic derivative of
`f` splits into the contribution of the poles/zeros at the points `u` and the
logarithmic derivative of the zero-free factor:

  `logDeriv f x = ∑ᶠ u, (d u : ℂ) * (1 / (x - u)) + logDeriv g x`.

The point is that the hypothesis `f x ≠ 0` forces `x` to lie outside the
support of `d`, so that each factor `(· - u) ^ (d u)` is differentiable and
non-zero at `x`; then the product rule for `logDeriv` (`logDeriv_prod`) and the
formula `logDeriv (fun z => (z - u) ^ n) x = n / (x - u)` give the claim.

This is the general "logarithmic derivative of a divisor" identity used, for
instance, in the theory of Jensen/Carleman formulas for algebraic integers.
-/

open Filter Function Set
open scoped BigOperators Topology

namespace Commons.Analysis.Complex

/-- Evaluation of the (multiplicative) `finprod` of the factors `(z - u) ^ (d u)`
commutes with the finite-support reduction: since `d` has finite support, the
product `∏ᶠ u, (z - u) ^ (d u)` is the finite product over the support of `d`. -/
lemma finprod_sub_zpow_eq_finset_prod {d : ℂ → ℤ} (hd : d.HasFiniteSupport) (z : ℂ) :
    (∏ᶠ u : ℂ, (z - u) ^ (d u)) = ∏ u ∈ hd.toFinset, (z - u) ^ (d u) := by
  have hd' : (Function.support d).Finite := hd
  refine finprod_eq_prod_of_mulSupport_subset _ ?_
  intro u hu
  by_contra hcon
  have hd0 : d u = 0 := by
    by_contra h
    exact hcon ((Set.Finite.mem_toFinset hd').2 ((Function.mem_support).2 h))
  exact hu (by simp [hd0])

/-- Logarithmic derivative of a single integer power of a translate:
`logDeriv (fun z => (z - u) ^ n) x = n * (1 / (x - u))`. -/
lemma logDeriv_translate_zpow (n : ℤ) (u x : ℂ) :
    logDeriv (fun z : ℂ => (z - u) ^ n) x = (n : ℂ) * (1 / (x - u)) := by
  rw [logDeriv_fun_zpow (f := fun z : ℂ => z - u) (x := x) (by fun_prop)]
  congr 1
  rw [logDeriv_apply]
  have hd1 : deriv (fun z : ℂ => z - u) x = 1 := by simp
  rw [hd1]

/-- Logarithmic derivative of the factored product `∏ᶠ u, (· - u) ^ (d u)`, at a
point `x` lying outside the support of `d`. -/
lemma logDeriv_finprod_zpow {d : ℂ → ℤ} (hd : d.HasFiniteSupport) {x : ℂ}
    (hne : ∀ u ∈ Function.support d, x ≠ u) :
    logDeriv (∏ᶠ u, (· - u) ^ d u) x = ∑ᶠ u, (d u : ℂ) * (1 / (x - u)) := by
  have hd' : (Function.support d).Finite := hd
  have hsub : Function.support (fun u : ℂ => (d u : ℂ) * (1 / (x - u))) ⊆ ↑hd.toFinset := by
    intro u hu
    simp only [Function.mem_support] at hu
    by_contra hcon
    have h0 : d u = 0 := by
      by_contra h
      exact hcon ((Set.Finite.mem_toFinset hd').2 ((Function.mem_support).2 h))
    exact hu (by simp [h0])
  rw [Function.FactorizedRational.finprod_eq_fun hd]
  have hfun : (fun z : ℂ => ∏ᶠ u : ℂ, (z - u) ^ (d u))
      = fun z : ℂ => ∏ u ∈ hd.toFinset, (z - u) ^ (d u) := by
    funext z; exact finprod_sub_zpow_eq_finset_prod hd z
  rw [hfun, logDeriv_fun_prod]
  · rw [finsum_eq_sum_of_support_subset _ hsub]
    apply Finset.sum_congr rfl
    intro u _
    exact logDeriv_translate_zpow (d u) u x
  · intro i hi
    have hxii : x ≠ i := hne i ((Set.Finite.mem_toFinset hd').1 hi)
    exact zpow_ne_zero _ (sub_ne_zero.2 hxii)
  · intro i hi
    have hxii : x ≠ i := hne i ((Set.Finite.mem_toFinset hd').1 hi)
    exact (DifferentiableAt.zpow (by fun_prop) (Or.inl (sub_ne_zero.2 hxii)))

/-- **Logarithmic derivative of a factored analytic function.**

Let `f` and `g` be analytic on an open set `U`, with `g` nowhere zero on `U`,
and suppose that on `U` the function `f` factors as
`f z = (∏ᶠ u, (z - u) ^ (d u)) * g z` for a map `d : ℂ → ℤ` of finite support.
Then at every `x ∈ U` with `f x ≠ 0`,

  `logDeriv f x = ∑ᶠ u, (d u : ℂ) * (1 / (x - u)) + logDeriv g x`. -/
theorem logDeriv_eq_finsum_of_factorization {U : Set ℂ} (hU : IsOpen U)
    {f g : ℂ → ℂ} {d : ℂ → ℤ} (hd : d.HasFiniteSupport)
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hgne : ∀ z ∈ U, g z ≠ 0)
    (hfac : ∀ z ∈ U, f z = (∏ᶠ u : ℂ, (z - u) ^ (d u)) * g z)
    {x : ℂ} (hx : x ∈ U) (hfx : f x ≠ 0) :
    logDeriv f x = (∑ᶠ u : ℂ, (d u : ℂ) * (1 / (x - u))) + logDeriv g x := by
  have hd' : (Function.support d).Finite := hd
  set Q : ℂ → ℂ := ∏ᶠ u, (· - u) ^ d u with hQdef
  have hQval : ∀ z, Q z = ∏ᶠ u : ℂ, (z - u) ^ (d u) := by
    intro z
    rw [hQdef]
    exact congrFun (Function.FactorizedRational.finprod_eq_fun hd) z
  have hfac' : ∀ z ∈ U, f z = Q z * g z := by
    intro z hz
    rw [hfac z hz, hQval z]
  -- `Q x ≠ 0`, since `f x = Q x * g x` and both `f x` and `g x` are non-zero.
  have hQxne : Q x ≠ 0 := by
    intro h0
    have : f x = 0 := by rw [hfac' x hx, h0, zero_mul]
    exact hfx this
  -- `Q` is analytic at `x`, being locally equal to `f / g`.
  have hQana : AnalyticAt ℂ Q x := by
    have hdiv : AnalyticAt ℂ (fun z => f z / g z) x :=
      (hf x hx).div (hg x hx) (hgne x hx)
    refine hdiv.congr ?_
    filter_upwards [hU.mem_nhds hx] with z hz
    rw [hfac' z hz]
    exact mul_div_cancel_right₀ (Q z) (hgne z hz)
  -- `x` lies outside the support of `d`: otherwise the factor `(x - u) ^ (d u)`
  -- would vanish, contradicting `Q x ≠ 0`.
  have hne : ∀ u ∈ Function.support d, x ≠ u := by
    intro u hu hxu
    have hdu : d u ≠ 0 := (Function.mem_support).1 hu
    have hprod : (∏ u ∈ hd.toFinset, (x - u) ^ (d u)) ≠ 0 := by
      rw [← finprod_sub_zpow_eq_finset_prod hd x, ← hQval x]
      exact hQxne
    have hmem : u ∈ hd.toFinset := (Set.Finite.mem_toFinset hd').2 hu
    have hfac_ne : (x - u) ^ (d u) ≠ 0 := Finset.prod_ne_zero_iff.1 hprod u hmem
    rw [hxu, sub_self] at hfac_ne
    exact hfac_ne ((zpow_eq_zero_iff hdu).mpr rfl)
  have hQlog : logDeriv Q x = ∑ᶠ u : ℂ, (d u : ℂ) * (1 / (x - u)) := by
    rw [hQdef]
    exact logDeriv_finprod_zpow hd hne
  have hPge : f =ᶠ[𝓝 x] fun z => Q z * g z := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact hfac' z hz
  have hstep1 : logDeriv f x = logDeriv (fun z => Q z * g z) x := by
    rw [logDeriv_apply, logDeriv_apply, hPge.deriv_eq, hfac' x hx]
  rw [hstep1, logDeriv_fun_mul x hQxne (hgne x hx) hQana.differentiableAt
    (hg x hx).differentiableAt, hQlog]

end Commons.Analysis.Complex