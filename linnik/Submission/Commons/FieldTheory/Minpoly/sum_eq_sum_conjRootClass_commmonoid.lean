import Mathlib.FieldTheory.Minpoly.ConjRootClass
import Submission.Commons.FieldTheory.Minpoly.sum_eq_sum_conjRootClass

namespace Commons.FieldTheory.Minpoly

theorem sum_eq_sum_conjRootClass_commmonoid {K L M : Type*} [Field K] [Field L] [Fintype L]
    [DecidableEq L] [AddCommMonoid M] [Algebra K L] [Normal K L] [Fintype (Gal(L/K))]
    [Fintype (ConjRootClass K L)] (f : L → M) :
    ∑ x : L, f x = ∑ c : ConjRootClass K L, ∑ x ∈ c.carrier.toFinset, f x := by
  classical
  have hfiber : ∀ c : ConjRootClass K L,
      (Finset.univ.filter (fun x : L => ConjRootClass.mk K x = c)) = c.carrier.toFinset := by
    intro c
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
      ConjRootClass.mem_carrier]
  rw [← Finset.sum_fiberwise (Finset.univ : Finset L) (ConjRootClass.mk K) f]
  exact Finset.sum_congr rfl fun c _ => by rw [hfiber c]

end Commons.FieldTheory.Minpoly