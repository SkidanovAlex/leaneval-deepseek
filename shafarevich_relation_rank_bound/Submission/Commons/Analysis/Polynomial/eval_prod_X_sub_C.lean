import Mathlib.Algebra.Polynomial.Eval.Defs

namespace Commons.Analysis.Polynomial

lemma eval_prod_X_sub_C {L : Type*} [Field L] (α : L) (m : Multiset L) :
    ((Multiset.map (fun β : L => Polynomial.X - Polynomial.C β) m).prod).eval α =
      (Multiset.map (fun β : L => α - β) m).prod := by
  induction m using Multiset.induction with
  | empty => simp
  | cons β s ih => simp [ih]

end Commons.Analysis.Polynomial