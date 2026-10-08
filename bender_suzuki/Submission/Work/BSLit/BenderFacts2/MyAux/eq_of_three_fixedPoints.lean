import Mathlib
import Submission.Work.Models.Port.Sz.TwoTransitive
import Submission.Work.Models.Port.Sz.Weyl
import Submission.Work.Models.Port.BenderAction
import Submission.Work.ZassenhausSuzuki.suzukiFProp

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.BenderFacts2.MyAux

theorem eq_of_three_fixedPoints (n : ℕ) (hn : 1 ≤ n) {x : LeanEval.GroupTheory.Defs.SzModel n} (hx : x ≠ 1)
    {a b c : LeanEval.GroupTheory.Defs.SzModel n ⧸ Submission.Sz.szBorelS n}
    (ha : x • a = a) (hb : x • b = b) (hc : x • c = c) :
    a = b ∨ a = c ∨ b = c := by
  by_contra h
  have hab : a ≠ b := fun h' => h (Or.inl h')
  have hac : a ≠ c := fun h' => h (Or.inr (Or.inl h'))
  have hbc : b ≠ c := fun h' => h (Or.inr (Or.inr h'))
  exact hx (Work.ZassenhausSuzuki.szBorelS_isZassenhaus n hn a b c hab hac hbc x ha hb hc)

end Work.BSLit.BenderFacts2.MyAux
