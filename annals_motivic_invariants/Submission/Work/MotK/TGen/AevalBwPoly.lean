import Mathlib
import Submission.Work.MotK.TGen.TwPoly

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `aeval` computes the inverse link map `χ = π_p ∘ kleinTwR` of the T-twisted link

`Work.MotK.bwPoly K a b h` is the inverse link map `χ = kleinTwPi (kleinPointT a b h) ∘ kleinTwR`
of the T-twisted Crauder--Katz link, written as a vector of polynomials in the five homogeneous
coordinates `V₀,…,V₄` (see `Submission/Work/MotK/TGen/TwPoly`).

The single content of this file is that `kleinTwR` is a *polynomial expression* in its arguments
and `kleinTwPi` is the affine projection `x ↦ x - x₀·p`, both built from `+ - * ^` with
natural-number coefficients.  Hence `MvPolynomial.aeval y` — the `K`-algebra homomorphism sending
`X i ↦ y i` and `C r ↦ algebraMap K A r` — commutes with them: evaluating `bwPoly` at a point `y`
of a `K`-algebra `A` gives the same expression with `a, b, h` mapped through `algebraMap K A` and
the coordinates replaced by `y`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK

/-- `MvPolynomial.aeval` commutes with the twisted inverse map `kleinTwR` of the T-twist: the
latter is a polynomial expression `+ - * ^` (with natural-number coefficients) in its arguments
`a b h y`, so it is respected by the evaluation homomorphism of the polynomial ring applied to
each argument separately. -/
lemma aeval_kleinTwR {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (a b h : K) (y : Fin 5 → A) (j : Fin 5) :
    MvPolynomial.aeval y (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (fun i => MvPolynomial.X i) j)
      = kleinTwR (algebraMap K A a) (algebraMap K A b) (algebraMap K A h) y j := by
  fin_cases j <;>
    simp only [kleinTwR, kleinTwR0, kleinTwR1, kleinTwR2, kleinTwR3, kleinTwR4] <;>
    simp

end Work.MotK

namespace Work.MotK.TGen

theorem AevalBwPoly {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (a b h : K) (y : Fin 5 → A) (j : Fin 5) :
    MvPolynomial.aeval y (Work.MotK.bwPoly K a b h j)
      = Work.MotK.kleinTwPi (fun i => algebraMap K A (Work.MotK.kleinPointT a b h i))
          (Work.MotK.kleinTwR (algebraMap K A a) (algebraMap K A b) (algebraMap K A h) y) j := by
  simp only [Work.MotK.bwPoly, Work.MotK.kleinTwPi]
  simp [Work.MotK.pX5, Work.MotK.aeval_kleinTwR]

end Work.MotK.TGen
