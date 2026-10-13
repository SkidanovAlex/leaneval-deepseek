import Mathlib
import Submission.Work.DSCOH.Norm.Defs

/-!
# Deleting a repeated entry of a nondecreasing tuple

If `x : Fin (n+2) → ι` is nondecreasing and takes the same value at `a` and `b`, then deleting
the `a`-th entry or the `b`-th entry of `x` gives the same tuple.

The mathematical content is that a nondecreasing tuple is constant on the segment between two
positions carrying equal values: for `a ≤ b` with `x a = x b` and `a ≤ i ≤ b` we have
`x i = x a`.  Deleting `a` or deleting `b` then produces the same list, because at every
position the two deleted tuples either literally agree, or differ by an adjacent pair `i`, `i+1`
inside that constant segment.
-/

universe w

namespace Work.DSCOH.Norm

/-- Auxiliary form of `del_eq_of_monotone_of_eq` for `a ≤ b`: a nondecreasing tuple is constant
on the segment joining two positions with equal values. -/
private lemma del_eq_of_le {ι : Type w} [LinearOrder ι] {n : ℕ} {x : Fin (n + 2) → ι}
    (hx : Monotone x) {a b : Fin (n + 2)} (hab : a ≤ b) (h : x a = x b) :
    del x a = del x b := by
  -- `x` is constant on the whole segment from `a` to `b`.
  have hconst : ∀ i : Fin (n + 2), a ≤ i → i ≤ b → x i = x a := by
    intro i hai hib
    exact le_antisymm (le_trans (hx hib) h.symm.le) (hx hai)
  funext j
  simp only [del_apply]
  -- Compare `a.succAbove j` with `b.succAbove j`, splitting on where `j.castSucc` sits.
  by_cases h1 : (j.castSucc : Fin (n + 2)) < a
  · -- `j` lies below `a ≤ b`: both deletions keep the entry `j`.
    rw [Fin.succAbove_of_castSucc_lt a j h1,
      Fin.succAbove_of_castSucc_lt b j (lt_of_lt_of_le h1 hab)]
  · have h1' : a ≤ (j.castSucc : Fin (n + 2)) := not_lt.mp h1
    by_cases h2 : (j.castSucc : Fin (n + 2)) < b
    · -- `a ≤ j < b`: deleting `a` keeps the entry `j+1`, deleting `b` keeps the entry `j`,
      -- and `j`, `j+1` both lie in the constant segment.
      rw [Fin.succAbove_of_le_castSucc a j h1', Fin.succAbove_of_castSucc_lt b j h2,
        hconst j.succ (le_trans h1' (Fin.castSucc_le_succ j))
          (Fin.castSucc_lt_iff_succ_le.mp h2),
        hconst j.castSucc h1' (le_of_lt h2)]
    · -- `b ≤ j`: both deletions keep the entry `j+1`.
      have h2' : b ≤ (j.castSucc : Fin (n + 2)) := not_lt.mp h2
      rw [Fin.succAbove_of_le_castSucc a j (le_trans hab h2'),
        Fin.succAbove_of_le_castSucc b j h2']

theorem del_eq_of_monotone_of_eq {ι : Type w} [LinearOrder ι] {n : ℕ} {x : Fin (n + 2) → ι}
    (hx : Monotone x) {a b : Fin (n + 2)} (h : x a = x b) :
    Work.DSCOH.Norm.del x a = Work.DSCOH.Norm.del x b := by
  rcases le_total a b with hab | hba
  · exact del_eq_of_le hx hab h
  · exact (del_eq_of_le hx hba h.symm).symm

end Work.DSCOH.Norm
