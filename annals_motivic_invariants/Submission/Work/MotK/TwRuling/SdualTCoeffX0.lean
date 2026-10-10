import Mathlib
import Submission.Work.MotK.TwCensus.SdualTPrimeGood
import Submission.Work.MotK.TGen.CensusFactors

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwRuling

open MvPolynomial

-- CONTEXT.  This is the coefficient brick consumed by `Work.MotK.TwRuling.SdThetaKernel` (the
-- presentation `ker (sdTheta) = (sdualT)` of the target ruling divisor, hence `TGen.SdualTClass` ->
-- `TGenCensus_wired` -> `Work.MotK.LinkCertT`); it is the on-disk statement
-- `Work.MotK.TwRuling.SdualTDegreeX0` copied under a fresh name so that it can be delegated (the
-- original file will be re-pointed to it, and its `sorry` removed).  Its two call sites in
-- `SdThetaKernel.lean` use exactly this shape (`hk := le_rfl` for `k = 5`, `by omega` otherwise),
-- followed by `Polynomial.coeff_C`/`MvPolynomial.finSuccEquiv_coeff_coeff`.
--
-- Content: for `k >= 5`, the coefficient of the monomial `X₀^k · X₁^(m 0) · X₂^(m 1)`
-- (`Finsupp.cons k m : Fin 3 →₀ ℕ`) in `sdualT a b h` is `-(a^5 b^5 h^4)` when `k = 5, m = 0`, and
-- vanishes otherwise.  This is a *finite* computation from the explicit twelve-term shape
-- `Work.MotK.TwCensus.sdualT_explicit`: among those twelve monomials only `X₀^5` has `X₀`-exponent
-- `>= 5` (the others have 0, 0, 0, 3, 2, 1, 2, 1, 1, 0, 1), and its coefficient is `-(a^5 b^5 h^4)`.
--
-- Proof (implemented below): rewrite `sdualT` by `Work.MotK.TwCensus.sdualT_explicit`, turn every
-- numeral coefficient into `C _`, normalise all `C`-factors into the coefficients of `monomial`s
-- via `C_pow`/`C_mul`/`C_add`/`C_sub` (backwards), `C_mul_X_pow_eq_monomial`, `X_pow_eq_monomial`
-- and `monomial_mul_monomial`, distribute `coeff` over `±`, and evaluate the twelve
-- `coeff_monomial`s.  The eleven non-leading monomials have `X₀`-exponent `<= 3`, so their index
-- cannot be `Finsupp.cons k m` with `k >= 5` (apply `fun f => f 0`); the leading one is
-- `monomial (Finsupp.single 0 5) (-(a^5 b^5 h^4))`, whose `cons k m`-coefficient is
-- `if k = 5 ∧ m = 0 then -(a^5 b^5 h^4) else 0`.

/-- The `X`-variable of `MvPolynomial (Fin 3) K` as a `monomial`. -/
lemma mv_X_eq_monomial (K : Type) [Field K] (i : Fin 3) :
    (X i : MvPolynomial (Fin 3) K) = monomial (Finsupp.single i 1) 1 := by
  rw [← MvPolynomial.X_pow_eq_monomial, pow_one]

/-- A constant of `MvPolynomial (Fin 3) K` as a `monomial`. -/
lemma mv_C_eq_monomial_zero (K : Type) [Field K] (c : K) :
    (C c : MvPolynomial (Fin 3) K) = monomial 0 c := by
  rw [MvPolynomial.monomial_zero']

/-- The `Finsupp.cons k m`-coefficient of a monomial whose `0`-component is `< k` vanishes: the
`0`-component of `Finsupp.cons k m` is `k`. -/
lemma coeff_monomial_zero_lt {K : Type} [Field K] (c : K) {s : Fin 3 →₀ ℕ} {k : ℕ}
    {m : Fin 2 →₀ ℕ} (h : s 0 < k) :
    ((monomial s c : MvPolynomial (Fin 3) K)).coeff (Finsupp.cons k m) = 0 := by
  rw [MvPolynomial.coeff_monomial]
  have hne : ¬ (s = Finsupp.cons k m) := by
    intro hc
    have h2 := congrArg (fun f : Fin 3 →₀ ℕ => f 0) hc
    rw [Finsupp.cons_zero] at h2
    omega
  rw [ite_eq_right hne]

/-- The `Finsupp.cons k m`-coefficient of the monomial `X₀^5`. -/
lemma coeff_monomial_single_zero_five {K : Type} [Field K] (c : K) (k : ℕ) (m : Fin 2 →₀ ℕ) :
    ((monomial (Finsupp.single (0 : Fin 3) 5) c : MvPolynomial (Fin 3) K)).coeff
        (Finsupp.cons k m)
      = if k = 5 ∧ m = 0 then c else 0 := by
  rw [MvPolynomial.coeff_monomial]
  have h : (Finsupp.single (0 : Fin 3) 5 = Finsupp.cons k m) ↔ (k = 5 ∧ m = 0) := by
    rw [eq_comm, Finsupp.cons_eq_single_zero_iff]
    exact and_comm
  by_cases hQ : k = 5 ∧ m = 0
  · rw [ite_eq_left (h.mpr hQ), ite_eq_left hQ]
  · rw [ite_eq_right (fun hp => hQ (h.mp hp)), ite_eq_right hQ]

theorem SdualTCoeffX0 (K : Type) [Field K] (a b h : K) (k : ℕ) (m : Fin 2 →₀ ℕ)
    (hk : 5 ≤ k) :
    (Work.MotK.TGen.sdualT a b h).coeff (Finsupp.cons k m)
      = if k = 5 ∧ m = 0 then -(a^5*b^5*h^4) else 0 := by
  rw [Work.MotK.TwCensus.sdualT_explicit]
  -- replace the numerals of the coefficient ring by `C`-images
  have h2 : (2 : MvPolynomial (Fin 3) K) = C (2 : K) := (MvPolynomial.C_eq_coe_nat 2).symm
  have h3 : (3 : MvPolynomial (Fin 3) K) = C (3 : K) := (MvPolynomial.C_eq_coe_nat 3).symm
  rw [h2, h3]
  -- collapse every coefficient into a single `C _`
  simp only [← C_pow, ← C_mul, ← C_add, ← C_sub]
  -- normalise each of the twelve terms to a `monomial`
  simp only [MvPolynomial.C_mul_X_pow_eq_monomial]
  simp only [MvPolynomial.X_pow_eq_monomial]
  simp only [mv_X_eq_monomial, mv_C_eq_monomial_zero, MvPolynomial.monomial_mul_monomial,
    mul_one, zero_add]
  -- distribute `coeff` over the `±` and evaluate the twelve monomials
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_sub, MvPolynomial.coeff_neg]
  rw [show ((monomial (Finsupp.single (0 : Fin 3) 5) (a^5*b^5*h^4) : MvPolynomial (Fin 3) K)).coeff
          (Finsupp.cons k m)
        = (if k = 5 ∧ m = 0 then a^5*b^5*h^4 else 0) from
        coeff_monomial_single_zero_five _ k m,
      show ((monomial (Finsupp.single 1 5) (a^5*b^5*h^3) : MvPolynomial (Fin 3) K)).coeff
          (Finsupp.cons k m)
        = 0 from coeff_monomial_zero_lt _ (by simp; omega),
      show ((monomial (Finsupp.single 2 5) (a^5*b^5*h^2) : MvPolynomial (Fin 3) K)).coeff
          (Finsupp.cons k m)
        = 0 from coeff_monomial_zero_lt _ (by simp; omega),
      show ((monomial 0 (a^5*b^5*h) : MvPolynomial (Fin 3) K)).coeff (Finsupp.cons k m)
        = 0 from coeff_monomial_zero_lt _ (by simp; omega),
      show ((monomial (Finsupp.single (0 : Fin 3) 3 + Finsupp.single 2 1)
          (h^3*(2*a^3*b^7 + a^8*b^2)) : MvPolynomial (Fin 3) K)).coeff (Finsupp.cons k m)
        = 0 from coeff_monomial_zero_lt _ (by simp; omega),
      show ((monomial (Finsupp.single (0 : Fin 3) 1 + Finsupp.single 1 1)
          (h^2*(2*a^3*b^7 + a^8*b^2)) : MvPolynomial (Fin 3) K)).coeff (Finsupp.cons k m)
        = 0 from coeff_monomial_zero_lt _ (by simp; omega),
      show ((monomial (Finsupp.single (0 : Fin 3) 2 + Finsupp.single 1 2)
          (h^3*(3*a^6*b^4 + a*b^9)) : MvPolynomial (Fin 3) K)).coeff (Finsupp.cons k m)
        = 0 from coeff_monomial_zero_lt _ (by simp; omega),
      show ((monomial (Finsupp.single (0 : Fin 3) 1 + Finsupp.single 2 2)
          (h^2*(3*a^6*b^4 + a*b^9)) : MvPolynomial (Fin 3) K)).coeff (Finsupp.cons k m)
        = 0 from coeff_monomial_zero_lt _ (by simp; omega),
      show ((monomial ((Finsupp.single (0 : Fin 3) 2 + Finsupp.single 1 1) + Finsupp.single 2 2)
          (h^3*(3*a^4*b^6 - a^9*b)) : MvPolynomial (Fin 3) K)).coeff (Finsupp.cons k m)
        = 0 from coeff_monomial_zero_lt _ (by simp; omega),
      show ((monomial (Finsupp.single (1 : Fin 3) 2 + Finsupp.single 2 1)
          (h^2*(3*a^4*b^6 - a^9*b)) : MvPolynomial (Fin 3) K)).coeff (Finsupp.cons k m)
        = 0 from coeff_monomial_zero_lt _ (by simp; omega),
      show ((monomial ((Finsupp.single (0 : Fin 3) 1 + Finsupp.single 1 3) + Finsupp.single 2 1)
          (h^3*(2*a^7*b^3 - a^2*b^8)) : MvPolynomial (Fin 3) K)).coeff (Finsupp.cons k m)
        = 0 from coeff_monomial_zero_lt _ (by simp; omega),
      show ((monomial (Finsupp.single (1 : Fin 3) 1 + Finsupp.single 2 3)
          (h^2*(2*a^7*b^3 - a^2*b^8)) : MvPolynomial (Fin 3) K)).coeff (Finsupp.cons k m)
        = 0 from coeff_monomial_zero_lt _ (by simp; omega)]
  by_cases hq : k = 5 ∧ m = 0 <;> simp [hq]

end Work.MotK.TwRuling
