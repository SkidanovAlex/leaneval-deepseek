import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.RankAPI.diagonal_rank

namespace Work.ORHughesFree.RankAPI

theorem rk_diagonal_eq_sum {R : Type*} [Ring R] (rk : Work.ORHughesFree.SylvesterRank R) {k : ℕ}
    (a : Fin k → R) :
    rk.rk k k (Matrix.diagonal a)
      = ∑ j : Fin k, rk.rk 1 1 (Work.ORHughesFree.oneByOne (a j)) :=
  Work.ORHughesFree.RankAPI.diagonal_rank rk a

end Work.ORHughesFree.RankAPI
