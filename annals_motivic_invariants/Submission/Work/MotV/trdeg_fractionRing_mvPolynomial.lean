import Mathlib
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

/-- The fraction field of a domain `S` is algebraic over `S`: every element is of the form
`s / t` with `t` a non-zero-divisor, so is a root of `t X - s`.

(In the form used below: `S` is algebraic over itself, hence over `FractionRing S`.) -/
lemma isAlgebraic_fractionRing_self (S : Type*) [CommRing S] [IsDomain S] :
    Algebra.IsAlgebraic S (FractionRing S) := by
  rw [← IsFractionRing.isAlgebraic_iff' S S (FractionRing S)]
  infer_instance

theorem trdeg_fractionRing_mvPolynomial (F : Type) [Field F] (m : ℕ) :
    Algebra.trdeg F (FractionRing (MvPolynomial (Fin m) F)) = Cardinal.mk (Fin m) := by
  have halg : Algebra.IsAlgebraic (MvPolynomial (Fin m) F)
      (FractionRing (MvPolynomial (Fin m) F)) := isAlgebraic_fractionRing_self _
  -- `trdeg` is additive in towers, and the fraction field contributes nothing.
  have h := trdeg_add_eq F (MvPolynomial (Fin m) F)
    (A := FractionRing (MvPolynomial (Fin m) F))
  have h2 : Algebra.trdeg (MvPolynomial (Fin m) F)
      (FractionRing (MvPolynomial (Fin m) F)) = 0 := trdeg_eq_zero
  rw [h2, add_zero] at h
  rw [← h, MvPolynomial.trdeg_of_isDomain]
  simp

end Work.MotV
