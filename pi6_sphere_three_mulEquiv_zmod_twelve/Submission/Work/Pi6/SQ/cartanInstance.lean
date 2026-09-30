import Mathlib
import Submission.Work.Pi6.SQ.CartanDefs
import Submission.Work.Pi6.SQ.CartanCompute
import Submission.Work.Pi6.SQ.CartanMain
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQ

noncomputable section

open Work.Cohomology

/-- **The Cartan instance** `Sq²(x²) = (Sq¹x)²` for 2-cocycles, at the cochain level: the lead's explicit natural 5-cochain `H(x) = Work.Pi6.SQ.cartanCochain X x` (`REFS/pi6_cartan_H.json`, 31 quartic terms in the values of `x` on the faces `σ|0ab`) satisfies `δH(x) = (x∪x)∪₂(x∪x) + (x∪₁x)∪(x∪₁x)` for every 2-cocycle `x`. -/
theorem cartanInstance (X : SSet) (x : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 2) (hx : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X x = 0) : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X (Work.Pi6.SQ.cartanCochain X x) = Work.Pi6.SQ.cup2 X 4 4 (Work.Cohomology.cup Work.Pi6.SQ.F2 X x x) (Work.Cohomology.cup Work.Pi6.SQ.F2 X x x) + Work.Cohomology.cup Work.Pi6.SQ.F2 X (Work.Pi6.SQ.cup1m X 2 2 x x) (Work.Pi6.SQ.cup1m X 2 2 x x) := by
  apply genEval_ext
  intro τ
  rw [genEval_cochainDiff, Fin.sum_univ_seven]
  simp only [neg_one_pow_F2, one_mul]
  rw [Hval_0 X x τ hx, Hval_1 X x τ hx, Hval_2 X x τ hx, Hval_3 X x τ hx, Hval_4 X x τ hx,
    Hval_5 X x τ hx, Hval_6 X x τ hx]
  rw [genEval_add, Rval_cup2 X x τ hx, Rval_cup1m X x τ hx]
  ring_nf
  simp only [zmod2_ofNat_mod, Nat.reduceMod, mul_zero, zero_mul, add_zero, zero_add, one_mul,
    mul_one]
  ring

end

end Work.Pi6.SQ
