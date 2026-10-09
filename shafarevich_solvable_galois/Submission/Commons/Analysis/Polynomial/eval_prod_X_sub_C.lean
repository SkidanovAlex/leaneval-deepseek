import Mathlib.Algebra.Polynomial.Eval.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Polynomial

lemma eval_prod_X_sub_C {L : Type*} [Field L] (α : L) (m : Multiset L) :
    ((Multiset.map (fun β : L => Polynomial.X - Polynomial.C β) m).prod).eval α =
      (Multiset.map (fun β : L => α - β) m).prod := by
  induction m using Multiset.induction with
  | empty => simp
  | cons β s ih => simp [ih]

end Commons.Analysis.Polynomial