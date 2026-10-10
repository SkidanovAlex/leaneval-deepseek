import Mathlib
import Submission.Work.MotK.TwRuling.SdSextDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwRuling

open Work.MotK

/-- `Polynomial.eval` commutes with the polynomial expression `kleinTwR0`: evaluating the
coefficient-ring version of `kleinTwR0` at a scalar `σ` is the same as evaluating each entry of
the coordinate vector at `σ` and then applying `kleinTwR0`. -/
lemma eval_kleinTwR0 {R : Type*} [CommRing R] (a b h σ : R) (y : Fin 5 → Polynomial R) :
    Polynomial.eval σ (kleinTwR0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C h) y)
      = kleinTwR0 a b h (fun i => Polynomial.eval σ (y i)) := by
  simp only [kleinTwR0, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_neg, Polynomial.eval_sub, Polynomial.eval_C]

theorem eval_sdDpoly {R : Type*} [CommRing R] (a b σ : R) :
    Polynomial.eval σ (Work.MotK.TwRuling.sdDpoly a b)
      = Work.MotK.kleinTwR0 a b 1 (fun i => Work.MotK.kleinTwRuleA a b 1 ![a, 0, -a, -b, b] i
          + σ * Work.MotK.kleinTwRuleB a b 1 ![a, 0, -a, -b, b] i) := by
  rw [show Work.MotK.TwRuling.sdDpoly a b
      = kleinTwR0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C 1)
        (fun i => Polynomial.C (kleinTwRuleA a b 1 ![a, 0, -a, -b, b] i)
          + Polynomial.X * Polynomial.C (kleinTwRuleB a b 1 ![a, 0, -a, -b, b] i)) from rfl]
  rw [eval_kleinTwR0]
  congr 1
  funext i
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

end Work.MotK.TwRuling
