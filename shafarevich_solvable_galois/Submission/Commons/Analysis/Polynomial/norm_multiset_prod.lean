import Mathlib.Analysis.Normed.Field.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Polynomial

lemma norm_multiset_prod {L : Type*} [NormedField L] (m : Multiset L) :
    ‖m.prod‖ = (Multiset.map (fun z : L => ‖z‖) m).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.prod_cons, norm_mul, ih]

end Commons.Analysis.Polynomial