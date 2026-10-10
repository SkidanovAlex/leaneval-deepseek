import Mathlib
import Submission.Work.MotAS.AsCoeff6Defs
import Submission.Work.MotAS.kleinRAS0_asRuleQA_notMem_asIdeal6
import Submission.Work.MotAS.rhoV4Light

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.RhoCert.asCoeff6_notMem_gen`

One of the four degree-`6` coefficient forms `asCoeff6 K a b g j` of the AS inverse quadro-cubic
map `R^AS (asRuleQW a b g c X)` on the ruling line is *not* in the degree-`6` part `asIdeal6` of
the AS Pfaffian ideal, for `a b ≠ 0`, `a² - a·b - b² ≠ 0`, and **arbitrary** `g : K`.

## Route

* `Work.MotAS.kleinRAS0_asRuleQA_notMem_asIdeal6` (the light certificate, no generated data) is
  the statement for the `T^0`-coefficient at the *first* ruling vector
  `c ↦ asRuleQA (C a) (C b) (C g) X`: the value of `kleinRAS0` there is outside `asIdeal6`.
* `Work.MotAS.asCoeff6 K a b g 0` is *by definition* the `T^0`-coefficient of
  `asCoeffPoly`, i.e. `(asCoeffPoly K a b g).coeff 0 = (asCoeffPoly K a b g).eval 0`, which by
  `Work.MotAS.RhoL2.eval_asCoeffPoly` at `t = 0` is the value of `kleinRAS0` on the ruling vector
  `A(c) + 0·B(c) = asRuleQA (C a) (C b) (C g) X`.

Hence the `T^0`-coefficient itself witnesses the statement.
-/

set_option autoImplicit false

namespace Work.MotC5N3.RhoCert

/-- **The `g`-free degree-`6` certificate.** -/
theorem asCoeff6_notMem_gen (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : a ^ 2 - a * b - b ^ 2 ≠ 0) :
    ∃ j : ℕ, Work.MotAS.asCoeff6 K a b g j ∉ Work.MotAS.asIdeal6 K a b g := by
  refine ⟨0, ?_⟩
  intro hmem
  refine Work.MotAS.kleinRAS0_asRuleQA_notMem_asIdeal6 K a b g ha hb hd ?_
  -- the `T^0`-coefficient form is the value of `kleinRAS0` at the first ruling vector
  have hbridge : Work.MotAS.asCoeff6 K a b g 0
      = Work.MotAS.kleinRAS0 (R := MvPolynomial (Fin 5) K)
          (MvPolynomial.C (σ := Fin 5) a) (MvPolynomial.C (σ := Fin 5) b)
          (MvPolynomial.C (σ := Fin 5) g)
          (Work.MotAS.asRuleQA (MvPolynomial.C (σ := Fin 5) a) (MvPolynomial.C (σ := Fin 5) b)
            (MvPolynomial.C (σ := Fin 5) g) (fun i => MvPolynomial.X i)) := by
    have h := Work.MotAS.RhoL2.eval_asCoeffPoly (S := MvPolynomial (Fin 5) K)
      (a := MvPolynomial.C (σ := Fin 5) a) (b := MvPolynomial.C (σ := Fin 5) b)
      (g := MvPolynomial.C (σ := Fin 5) g) (c := fun i => MvPolynomial.X i)
      (t := (0 : MvPolynomial (Fin 5) K))
    simp only [zero_mul, add_zero] at h
    rw [Work.MotAS.asCoeff6, Work.MotAS.asCoeffPoly, Polynomial.coeff_zero_eq_eval_zero]
    exact h
  rwa [hbridge] at hmem

end Work.MotC5N3.RhoCert
