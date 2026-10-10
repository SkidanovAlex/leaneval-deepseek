import Mathlib
import Submission.Work.MotK.TGen.TwPoly

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `aeval` computes the source equation `F_hom` of the T-twisted link

`Work.MotK.FhomPoly K a b h` is the source equation of the T-twisted Crauder--Katz link, written
as the homogeneous polynomial `kleinTwFhom (C a) (C b) (C h) (pX5 K a b h) X` in the five
homogeneous coordinates `V₀,…,V₄` (see `Submission/Work/MotK/TGen/TwPoly`).

The single content of this file is that `kleinTwFhom` is a *polynomial expression* in its seven
arguments, so that `MvPolynomial.aeval y` — the `K`-algebra homomorphism sending `X i ↦ y i` —
commutes with it: evaluating `FhomPoly` at a point `y` of an `K`-algebra `A` gives the same
expression with `a, b, h` mapped through `algebraMap K A` and the coordinates replaced by `y`.
-/

namespace Work.MotK

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

/-- `MvPolynomial.aeval` commutes with the source equation `kleinTwFhom` of the T-twist: the
latter is a polynomial expression `+ - * ^` (with natural-number coefficients) in its seven
arguments `a b h p v`, so it is respected by any ring homomorphism out of the polynomial ring
applied to each argument separately. -/
lemma aeval_kleinTwFhom (a b h : MvPolynomial (Fin 5) K)
    (p v : Fin 5 → MvPolynomial (Fin 5) K) (y : Fin 5 → A) :
    MvPolynomial.aeval y (kleinTwFhom a b h p v)
      = kleinTwFhom (MvPolynomial.aeval y a) (MvPolynomial.aeval y b) (MvPolynomial.aeval y h)
          (fun i => MvPolynomial.aeval y (p i)) (fun i => MvPolynomial.aeval y (v i)) := by
  simp only [kleinTwFhom, kleinTwBilin, kleinTwQ, kleinTwP0, kleinTwStereo, kleinTwS,
    Pi.add_apply]
  simp

end Work.MotK

namespace Work.MotK.TGen

theorem AevalFhomPoly {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (a b h : K) (y : Fin 5 → A) :
    MvPolynomial.aeval y (Work.MotK.FhomPoly K a b h)
      = Work.MotK.kleinTwFhom (algebraMap K A a) (algebraMap K A b) (algebraMap K A h)
          (fun i => algebraMap K A (Work.MotK.kleinPointT a b h i)) y := by
  rw [Work.MotK.FhomPoly, Work.MotK.aeval_kleinTwFhom]
  simp [Work.MotK.pX5]

end Work.MotK.TGen
