import Mathlib
import Submission.Work.Diff.EXT.evolX.mulOpJetsDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.evolX

open scoped BigOperators

/-- **The arithmetic kernel of `sumWordsChoose`.**  Summed Pascal's rule: adding `g` shifted by one
to the level-`n` binomial sum produces the level-`(n+1)` binomial sum. -/
private lemma sum_choose_add_shift (n : ℕ) (g : ℕ → ℝ) :
    (∑ a ∈ Finset.range (n + 1), (Nat.choose n a : ℝ) * g a)
      + (∑ a ∈ Finset.range (n + 1), (Nat.choose n a : ℝ) * g (a + 1))
    = ∑ a ∈ Finset.range (n + 2), (Nat.choose (n + 1) a : ℝ) * g a := by
  have h1 : (∑ a ∈ Finset.range (n + 1), (Nat.choose n a : ℝ) * g a)
      = ∑ a ∈ Finset.range n, (Nat.choose n (a + 1) : ℝ) * g (a + 1) + g 0 := by
    rw [Finset.sum_range_succ']
    simp
  have h2 : (∑ a ∈ Finset.range (n + 2), (Nat.choose (n + 1) a : ℝ) * g a)
      = ∑ a ∈ Finset.range (n + 1), (Nat.choose (n + 1) a : ℝ) * g a + g (n + 1) := by
    rw [Finset.sum_range_succ]
    simp
  have h3 : (∑ a ∈ Finset.range (n + 1), (Nat.choose (n + 1) a : ℝ) * g a)
      = ∑ a ∈ Finset.range n, (Nat.choose (n + 1) (a + 1) : ℝ) * g (a + 1) + g 0 := by
    rw [Finset.sum_range_succ']
    simp
  have h4 : (∑ a ∈ Finset.range n, (Nat.choose (n + 1) (a + 1) : ℝ) * g (a + 1))
      = (∑ a ∈ Finset.range n, (Nat.choose n (a + 1) : ℝ) * g (a + 1))
        + (∑ a ∈ Finset.range n, (Nat.choose n a : ℝ) * g (a + 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    have : (Nat.choose (n + 1) (a + 1) : ℝ)
        = (Nat.choose n (a + 1) : ℝ) + (Nat.choose n a : ℝ) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    rw [this]; ring
  have h5 : (∑ a ∈ Finset.range (n + 1), (Nat.choose n a : ℝ) * g (a + 1))
      = ∑ a ∈ Finset.range n, (Nat.choose n a : ℝ) * g (a + 1) + g (n + 1) := by
    rw [Finset.sum_range_succ]
    simp
  rw [h1, h2, h3, h4, h5]
  ring

/-- **Counting the words by their number of `true`s.**  The `n`-letter binary words `Word n` split
according to how many of their letters are `true`: there are `Nat.choose n a` words with `a` trues. -/
theorem sumWordsChoose (n : ℕ) (g : ℕ → ℝ) :
    Finset.sum Finset.univ (fun w : Work.Diff.EXT.evolX.Word n => g (Work.Diff.EXT.evolX.wCntT w))
      = Finset.sum (Finset.range (n + 1)) (fun a => (Nat.choose n a : ℝ) * g a) := by
  induction n generalizing g with
  | zero =>
    have h : (Finset.univ : Finset (Word 0)) = {default} := rfl
    rw [h, Finset.sum_singleton]
    have hw : wCntT (default : Word 0) = 0 := rfl
    rw [hw]
    norm_num [Finset.sum_range_one]
  | succ n ih =>
    -- peel the newest letter: `Word (n+1) ≃ Bool × Word n`
    have hreindex : (∑ p : Bool × Word n, g (wCntT (Word.cons p.1 p.2)))
        = ∑ w : Word (n + 1), g (wCntT w) :=
      Fintype.sum_equiv (Word.consEquiv n)
        (fun p : Bool × Word n => g (wCntT (Word.cons p.1 p.2)))
        (fun w : Word (n + 1) => g (wCntT w)) (fun _ => rfl)
    rw [← hreindex, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [wCntT_cons_false, wCntT_cons_true]
    rw [ih (fun a => g (a + 1)), ih g]
    rw [show (∑ a ∈ Finset.range (n + 1), (Nat.choose n a : ℝ) * g (a + 1))
          + (∑ a ∈ Finset.range (n + 1), (Nat.choose n a : ℝ) * g a)
          = (∑ a ∈ Finset.range (n + 1), (Nat.choose n a : ℝ) * g a)
          + (∑ a ∈ Finset.range (n + 1), (Nat.choose n a : ℝ) * g (a + 1)) from
        add_comm _ _]
    exact sum_choose_add_shift n g

end Work.Diff.EXT.evolX
