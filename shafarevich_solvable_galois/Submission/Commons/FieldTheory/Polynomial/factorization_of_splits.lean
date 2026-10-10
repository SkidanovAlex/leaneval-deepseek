import Mathlib.Algebra.Polynomial.Splits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.FieldTheory.Polynomial

lemma factorization_of_splits {L : Type*} [Field L] (g : Polynomial L)
    (hg : g ≠ 0) (hs : g.Splits) :
    g = Polynomial.C g.leadingCoeff *
        (Multiset.map (fun β : L => Polynomial.X - Polynomial.C β) (Polynomial.roots g)).prod ∧
      (Polynomial.roots g).card = g.natDegree := by
  constructor
  · simpa using hs.eq_prod_roots
  · exact hs.natDegree_eq_card_roots.symm

end Commons.FieldTheory.Polynomial
