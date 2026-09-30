import Mathlib
import Submission.Work.Pi6.SQM.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.SQM.SIG

/-- The mod-2 cup-1 product vanishes when its **second** argument is zero.  This is immediate from
the evaluation formula `genEval_cup1`: at every simplex `σ` the value of `cup1 α 0` is an
alternating sum of products `± genEval α (...) * genEval 0 (...)`, and each term contains the
factor `genEval 0 (...) = 0`. -/
lemma cup1_zero_right (X : SSet) (n m : ℕ)
    (α : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X n) :
    Work.Cohomology.cup1 Work.Pi6.SQ.F2 X n m α
      (0 : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X m) = 0 := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Cohomology.genEval_cup1]
  simp [Work.Cohomology.genEval]

/-- `cup1m` is the library's `cup1` with the two arguments interchanged (and the degree transported
along `m + n - 1 = n + m - 1`), so it vanishes whenever its first argument is zero. -/
theorem cup1mZeroLeft : ∀ (X : SSet) (n m : ℕ) (v : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X m),
    Work.Pi6.SQ.cup1m X n m (0 : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X n) v = 0 := by
  intro X n m v
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Pi6.SQ.genEval_cup1m]
  rw [cup1_zero_right]
  simp [Work.Cohomology.genEval]

end Work.Pi6.SQM.SIG
