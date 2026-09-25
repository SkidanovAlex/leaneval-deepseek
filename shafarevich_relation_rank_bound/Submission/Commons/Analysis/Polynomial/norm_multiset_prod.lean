import Mathlib.Analysis.Normed.Field.Basic

namespace Commons.Analysis.Polynomial

lemma norm_multiset_prod {L : Type*} [NormedField L] (m : Multiset L) :
    ‖m.prod‖ = (Multiset.map (fun z : L => ‖z‖) m).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.prod_cons, norm_mul, ih]

end Commons.Analysis.Polynomial