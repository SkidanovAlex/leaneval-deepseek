import Mathlib
import Submission.Work.MotK.LinkCertDefs
import Submission.Work.MotA.quotient_vertical
import Submission.Work.CrauderKatz.BlowUp.fractionRing_algEquiv_of_algEquiv
import Submission.Work.CrauderKatz.BlowUp.fractionRing_mvPolynomial_finTwo

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The coordinate hyperplane `x₀ = 0` is a junk divisor

The basic-open/Cremona chapter of the Lin–Shinder development counts the codimension-one points of
`𝔸ⁿ_K` by the `K`-isomorphism class of their residue field, and the "junk" divisors — those that
contribute nothing to the invariant — are the ones whose residue field is ruled over `K`
(`Work.MotV.JunkClass`).  This file discharges the basic instance: the coordinate hyperplane
`x₀ = 0` of `𝔸³_K`, i.e. the height-one prime `(x₀)`, is junk.

Mathematically: cutting out the coordinate `x₀` leaves the affine plane `Spec K[x₁,x₂]`, so the
residue field of `(x₀)` is the rational function field `K(x₁,x₂) = RatFunc (RatFunc K)` — the
one-variable rational function field over the rational function field `K(t) = RatFunc K`, which is
`GeomRuled` over `K` by `Work.MotK.GeomRuled_ratFunc_self`.

The two algebraic ingredients are
* `Work.MotA.quotient_vertical` (`K[x₀,…,xₙ]/(g(x₀)) ≅ K[x₁,…,xₙ] ⊗ K[t]/(g)`), taken at
  `g = Polynomial.X`, which realises `K[x₀,…,xₙ]/(x₀) ≅ K[x₁,…,xₙ] ⊗ K` via
  `Polynomial.quotientSpanXSubCAlgEquiv` (`K[X]/(X - c) ≅ K`) and `MvPolynomial.mapAlgEquiv`;
* `Work.CrauderKatz.BlowUp.fractionRing_mvPolynomial_finTwo` (`Frac K[x,y] ≅ RatFunc (RatFunc K)`),
  together with the transport of fraction fields along an algebra equivalence
  (`Work.CrauderKatz.BlowUp.fractionRing_algEquiv_of_algEquiv`).
-/

namespace Work.MotK

open MvPolynomial Polynomial

/-- **The coordinate hyperplane `x₀ = 0` cuts out the affine `n`-space.**
`K[x₀,…,xₙ]/(x₀) ≅ K[x₁,…,xₙ]`, as `K`-algebras.

Route: `Work.MotA.quotient_vertical K n Polynomial.X Polynomial.prime_X` identifies the quotient by
`(Polynomial.aeval (X 0) Polynomial.X) = (X 0)` with `K[x₁,…,xₙ] ⊗ (K[X]/(X))`, and
`K[X]/(X - 0) ≅ K` (`Polynomial.quotientSpanXSubCAlgEquiv 0`) identifies the coefficient ring. -/
private lemma quotient_span_X_zero_algEquiv (K : Type) [Field K] (n : ℕ) :
    Nonempty ((MvPolynomial (Fin (n + 1)) K ⧸
        Ideal.span {(MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)}) ≃ₐ[K]
      MvPolynomial (Fin n) K) := by
  obtain ⟨φ⟩ := Work.MotA.quotient_vertical K n (Polynomial.X : Polynomial K) Polynomial.prime_X
  -- The variable `Polynomial.X` of the coefficient ring becomes the coordinate `x₀`.
  have hP : ((Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1))) (Polynomial.X : Polynomial K)) :
      MvPolynomial (Fin (n + 1)) K) =
      (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K) :=
    Polynomial.aeval_X _
  rw [hP] at φ
  -- `K[X]/(X) ≅ K`: rewrite `X` as `X - C 0` and evaluate at `0`.
  have ePol : (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K)}) ≃ₐ[K] K :=
    (Ideal.quotientEquivAlgOfEq K (show Ideal.span {(Polynomial.X : Polynomial K)} =
        Ideal.span {(Polynomial.X - Polynomial.C (0 : K) : Polynomial K)} by
          rw [Polynomial.C_0, sub_zero])).trans
      (Polynomial.quotientSpanXSubCAlgEquiv (0 : K))
  exact ⟨φ.trans (MvPolynomial.mapAlgEquiv (Fin n) ePol)⟩

/-- **The height-one prime `(x₀) ⊆ K[x₀,x₁,x₂]` is junk.**  Its residue field is
`K(x₁,x₂) = RatFunc (RatFunc K)`, the rational function field over the `GeomRuled` field
`RatFunc K`, whence `Work.MotV.JunkClass`. -/
theorem JunkClassPrimePointX (K : Type) [Field K]
    (hp : Prime (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) K)) :
    Work.MotV.JunkClass K
      (Work.MotA.primePoint K (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) K) hp) := by
  refine ⟨RatFunc K, inferInstance, inferInstance, GeomRuled_ratFunc_self K, ?_⟩
  -- The residue field `Frac (K[x₀,x₁,x₂]/(x₀))` is that of `Frac K[x,y] = RatFunc (RatFunc K)`.
  obtain ⟨e₂⟩ := quotient_span_X_zero_algEquiv K 2
  obtain ⟨g₁⟩ := Work.CrauderKatz.BlowUp.fractionRing_algEquiv_of_algEquiv e₂
  obtain ⟨g₂⟩ := Work.CrauderKatz.BlowUp.fractionRing_mvPolynomial_finTwo K
  exact ⟨g₁.trans g₂⟩

end Work.MotK
