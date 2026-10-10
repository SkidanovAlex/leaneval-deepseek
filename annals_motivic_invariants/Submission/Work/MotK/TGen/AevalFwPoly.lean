/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TGen.TwPoly

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Evaluation of the link polynomial `fwPoly`

`Work.MotK.fwPoly K a b h` is the forward link map `f = kleinTwP ∘ kleinTwStereo` written as a
vector of polynomials in the five homogeneous coordinates `V₀,…,V₄`.  This file computes its
value at an arbitrary point `y : Fin 5 → A` of a `K`-algebra `A`:

`aeval y (fwPoly K a b h j) = kleinTwP (a) (b) (h) (kleinTwStereo (a) (b) (h) (p) y) j`,

i.e. evaluation commutes with the whole (purely polynomial) construction: coefficients are sent
by `algebraMap K A`, the polynomial variables by `y`, and the rational point `kleinPointT a b h`
by its image in `A`.

The two auxiliary lemmas isolate the polynomial nature of the two building blocks
`kleinTwP` and `kleinTwStereo`: for *any* families of polynomials `U`, `V` in place of
`pX5 K a b h` and `(Xᵢ)`, evaluation commutes with them.  (The remaining input
`kleinPointT a b h i ↦ algebraMap K A (kleinPointT a b h i)` is then handled by `aeval_C`.)
-/

set_option linter.unusedSectionVars false

namespace Work.MotK.TGen

open Work.MotK

/-- **Evaluation commutes with `kleinTwP`.** For any family of polynomials `U` in the five
homogeneous coordinates, the value of the `j`-th twisted Pfaffian at `U` is computed by
substituting `algebraMap K A` into the coefficients and `aeval y` into the arguments. -/
theorem aeval_kleinTwP_gen {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (a b h : K) (U : Fin 5 → MvPolynomial (Fin 5) K) (y : Fin 5 → A) (j : Fin 5) :
    MvPolynomial.aeval y
        ((kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) U) j)
      = kleinTwP (algebraMap K A a) (algebraMap K A b) (algebraMap K A h)
          (fun i => MvPolynomial.aeval y (U i)) j := by
  fin_cases j <;>
    simp only [fin5_zero, fin5_one, fin5_two, fin5_three, fin5_four,
      kleinTwP_zero, kleinTwP_one, kleinTwP_two, kleinTwP_three, kleinTwP_four,
      kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4,
      map_add, map_sub, map_mul, map_neg, map_pow, MvPolynomial.aeval_C]

/-- **Evaluation commutes with `kleinTwStereo`.** For any families of polynomials `U`, `V` in
the five homogeneous coordinates, the `i`-th coordinate of the inverse stereographic projection
is computed by substituting `algebraMap K A` into the coefficients and `aeval y` into the
arguments. -/
theorem aeval_kleinTwStereo_gen {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (a b h : K) (U V : Fin 5 → MvPolynomial (Fin 5) K) (y : Fin 5 → A) (i : Fin 5) :
    MvPolynomial.aeval y
        (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) U V i)
      = kleinTwStereo (algebraMap K A a) (algebraMap K A b) (algebraMap K A h)
          (fun i => MvPolynomial.aeval y (U i)) (fun i => MvPolynomial.aeval y (V i)) i := by
  simp only [kleinTwStereo, kleinTwBilin, kleinTwQ, kleinTwP0,
    map_add, map_sub, map_mul, map_neg, map_pow, MvPolynomial.aeval_C, Pi.add_apply]

theorem AevalFwPoly {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (a b h : K) (y : Fin 5 → A) (j : Fin 5) :
    MvPolynomial.aeval y (Work.MotK.fwPoly K a b h j)
      = Work.MotK.kleinTwP (algebraMap K A a) (algebraMap K A b) (algebraMap K A h)
          (Work.MotK.kleinTwStereo (algebraMap K A a) (algebraMap K A b) (algebraMap K A h)
            (fun i => algebraMap K A (Work.MotK.kleinPointT a b h i)) y) j := by
  simp only [fwPoly]
  rw [aeval_kleinTwP_gen]
  congr 1
  funext i
  rw [aeval_kleinTwStereo_gen]
  congr 2
  · funext i; simp [pX5]
  · funext i; simp [MvPolynomial.aeval_X]

end Work.MotK.TGen
