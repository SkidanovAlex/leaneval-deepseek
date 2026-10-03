import Mathlib
import Submission.Work.ORHughesFree.Tree.Log

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-- **The tree order is detected by the logarithm**: if `log x = some a` and `log y = some b`
are the maximal children of `x` and of `y`, then `a < b` implies `x < y`.

Indeed `log y = some b` exhibits the nonempty multiset `fam y` as the "added" part `Z` of the
Dershowitz–Manna witness (with `X = 0` and `Y = fam x`), and every child `a'` of `x` satisfies
`a' ≤ a < b` with `b ∈ fam y`. -/
theorem lt_of_log_lt {x y a b : Work.ORHughesFree.Tree}
    (hx : Work.ORHughesFree.Tree.log x = some a) (hy : Work.ORHughesFree.Tree.log y = some b)
    (h : Work.ORHughesFree.Tree.lt a b) : Work.ORHughesFree.Tree.lt x y := by
  obtain ⟨-, hmax⟩ := (log_spec x).2.1 a hx
  obtain ⟨hb, -⟩ := (log_spec y).2.1 b hy
  rw [lt_iff]
  refine ⟨0, fam x, fam y, fun hf => by rw [hf] at hb; exact absurd hb (by simp), ?_, ?_, ?_⟩
  · rw [Multiset.zero_add]
  · rw [Multiset.zero_add]
  · intro a' ha'
    refine ⟨b, hb, ?_⟩
    rcases hmax a' ha' with h' | h'
    · rw [h']; exact h
    · exact lt_trans h' h

end Work.ORHughesFree.Tree
