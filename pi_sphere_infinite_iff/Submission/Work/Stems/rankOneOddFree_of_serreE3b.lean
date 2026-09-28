import Mathlib
import Submission.Work.Rat.RankOneEMDefs
import Submission.Work.Rat.rankOneC1Ab
import Submission.Work.Stems.RankOneClauses
import Submission.Work.Stems.rankOne_evenStep
import Submission.Work.Stems.rankOne_oddStep
import Submission.Work.Serre.Engine

/-!
# The rank-one odd clause of the `K(A,n)` computation, from Serre's Euler class statement

`Work.Rat.RankOneOddFree c` is the *odd* clause of the rank-one Eilenberg--MacLane computation:
for odd `n ≥ 3`, a space whose homotopy groups vanish up to degree `N` except in degree `n`, where
`H_n(-;ℚ) ≅ ℚ`, has vanishing rational homology in degrees `n < j ≤ N - c·n`.

This file assembles the `c = 1` case from the two steps of the `C2`-style mutual induction on the
level (`Submission/Work/Stems/RankOneClauses.lean` splits the interface into the level clauses):

* `Work.Stems.rankOne_evenStep` — the even step (`OddClauseR (2j-1) → EvenClauseR j`), the
  Euler-class / Gysin periodicity of `Work.Serre.SerreE3b`;
* `Work.Stems.rankOne_oddStep` — the odd step (`EvenClauseR j → OddClauseR (2j+1)`), the
  cover/Wang argument;
* `Work.Rat.rankOneC1Ab` — the base case at level `1`.

The mutual induction is well founded because the even step at level `j` uses the odd clause at the
lower level `2j-1` and the odd step at level `2j+1` uses the even clause at the lower level `j`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems

noncomputable section

/-- **The level clauses of the rank-one interface, by strong induction on the level.** -/
theorem rankOneClauses (hE3b : Work.Serre.SerreE3b) (hC1 : Work.Rat.RankOneC1Ab) :
    (∀ (n N : ℕ), Odd n → OddClauseR n N) ∧ (∀ (j N : ℕ), 1 ≤ j → EvenClauseR j N) := by
  have key : ∀ ℓ : ℕ,
      (∀ (j : ℕ) (hj : 1 ≤ j), 2 * j ≤ ℓ → ∀ N : ℕ, EvenClauseR j N) ∧
      (∀ (n : ℕ), Odd n → n ≤ ℓ → ∀ N : ℕ, OddClauseR n N) := by
    intro ℓ
    induction ℓ using Nat.strong_induction_on with
    | h ℓ ih =>
      refine ⟨?_, ?_⟩
      · intro j hj hjℓ N
        have hodd : ∀ M : ℕ, OddClauseR (2 * j - 1) M := fun M =>
          (ih (2 * j - 1) (by omega)).2 (2 * j - 1) ⟨j - 1, by omega⟩ le_rfl M
        intro h2jN X tX x₀ hvan hgen
        exact (rankOne_evenStep hE3b j hj hodd N) h2jN x₀ hvan hgen
      · intro n hnodd hnℓ N
        rcases eq_or_lt_of_le (show 1 ≤ n from hnodd.pos) with h1 | h2
        · subst h1
          intro X tX x₀ hab hvan hgen j' hj1 hj2
          exact (oddClauseR_one_of_c1 hC1 N) x₀ hab hvan hgen j' hj1 hj2
        · obtain ⟨k, hk⟩ := hnodd
          have hk1 : 1 ≤ k := by omega
          subst hk
          have heven : ∀ M : ℕ, EvenClauseR k M := fun M =>
            (ih (2 * k) (by omega)).1 k hk1 le_rfl M
          intro X tX x₀ hab hvan hgen j' hj1 hj2
          exact (rankOne_oddStep k hk1 heven N) x₀ hab hvan hgen j' hj1 hj2
  exact ⟨fun n N hnodd => (key n).2 n hnodd le_rfl N,
    fun j N hj => (key (2 * j)).1 j hj le_rfl N⟩

/-- **Serre's finiteness for the rank-one `K(A,n)`, from the Euler class statement `E3(b)`.** -/
theorem rankOneOddFree_of_serreE3b (hE3b : Work.Serre.SerreE3b) : Work.Rat.RankOneOddFree 1 :=
  rankOneOddFree_of_clauses
    (fun n N hn hnodd => (rankOneClauses hE3b Work.Rat.rankOneC1Ab).1 n N hnodd)

end

end Work.Stems
