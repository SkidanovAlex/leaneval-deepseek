import Mathlib
import Submission.Work.MotAS.Ker6.Defs
import Submission.Work.MotK.TwRulingSix.finrank_homogeneous_six
import Submission.Work.MotK.TwRuling.sexticTw_notMem_kernel
import Submission.Work.MotK.TwRuling.quinticTw_notMem_kernel

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.Ker6.Lower` — the two lower bounds of the degree-6 kernel computation

Both statements are immediate corollaries of results already proved elsewhere in the workspace:

* `twIdealSixLower` — the degree-6 part of the (plain) Klein Pfaffian ideal has dimension at least
  `180`.  It is `Work.MotK.TwRuling.hilbert_bound` (`finrank Hom₆ ≤ finrank I₆ + 30`, proved by the
  division algorithm for the twisted Pfaffians) combined with
  `Work.MotK.TwRulingSix.finrank_homogeneous_six` (`finrank Hom₆ = 210`) and
  `Work.MotAS.Ker6.kleinIdeal6_eq_twIdeal6` (`kleinIdeal6 a b = twIdeal6 a b 1`).

* `finrank_prodSpan6_ge` — the `R`-span of the sixfold products of the basis
  `sdBas E = ![1, x, y, x², xy]` has dimension at least `30`.  The sixfold products of `sdBas`
  span the same space as the 30 monomials of `sdTF6 E` (`Work.MotK.TwRuling.sdTF6_span`), and
  those are linearly independent (`Work.MotK.TwRuling.sdTF6_linearIndependent`, packaged as
  `Work.MotK.TwRuling.finrank_span_sdTF6`).  (`prodSpanN` and `sdProdSpan` are the same
  definition under two names.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotAS.Ker6

open MvPolynomial

/-- The degree-6 part of the (plain) Klein Pfaffian ideal has dimension at least `180`. -/
theorem twIdealSixLower (R : Type) [Field R] (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    180 ≤ Module.finrank R ↥(kleinIdeal6 R a b) := by
  have h := Work.MotK.TwRuling.hilbert_bound (R := R) a b 1 ha hb
  have h210 : Module.finrank R ↥(MvPolynomial.homogeneousSubmodule (Fin 5) R 6) = 210 :=
    Work.MotK.TwRulingSix.finrank_homogeneous_six R
  rw [kleinIdeal6_eq_twIdeal6]
  omega

/-- The `R`-span of the sixfold products of `sdBas E` has dimension at least `30`. -/
theorem finrank_prodSpan6_ge (R : Type) [Field R] (E : WeierstrassCurve R) :
    30 ≤ Module.finrank R ↥(Work.MotK.TwRuling.prodSpanN R (Work.MotK.TwRuling.sdBas E) 6) := by
  have hsd : Work.MotK.TwRuling.prodSpanN R (Work.MotK.TwRuling.sdBas E) 6
      = Submodule.span R (Set.range (Work.MotK.TwRuling.sdTF6 E)) := by
    rw [show Work.MotK.TwRuling.prodSpanN R (Work.MotK.TwRuling.sdBas E) 6
        = Work.MotK.TwRuling.sdProdSpan R (Work.MotK.TwRuling.sdBas E) 6 from rfl]
    rw [Work.MotK.TwRuling.sdProdSpan_eq_sdProdSpan6]
    exact Work.MotK.TwRuling.sdTF6_span R E
  rw [hsd, Work.MotK.TwRuling.finrank_span_sdTF6 R E]

end Work.MotAS.Ker6
