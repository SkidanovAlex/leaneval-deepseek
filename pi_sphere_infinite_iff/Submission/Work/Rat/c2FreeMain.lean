import Mathlib
import Submission.Work.Stems.c2EvenStepLocal
import Submission.Work.Stems.c2OddStepLocal
import Submission.Work.Stems.c2OddBase
import Submission.Work.Stems.c2FreeClauses
import Submission.Work.Serre.serreE3a

/-!
# The free-top `C2` layer, assembled

`Work.Stems.Engine.C2evenFree c` / `C2oddFree c` are the two halves of the `C2` layer of the Serre
blueprint in *free-top, range-model* form: a range model of `K(ℤ,2j)` through degree `N` has the
rational homology of `ℂP^∞` rescaled by `2j` through degree `N - c(2j)`, and a range model of
`K(ℤ,n)` (`n` odd) through degree `N` has the rational homology of `Sⁿ` through degree `N - c·n`.

The two *mutual-induction steps* are proved elsewhere, level-locally:
* `Work.Stems.evenStepLocal` — level `j` from the odd clause at level `2j-1`, using `SerreE3b`;
* `Work.Stems.oddStepLocal` — level `2j+1` from the even clause at level `j`, using the mapping
  theorem `Work.Serre.SerreE3a` (which is proved).
* the base case is level `1`, `Work.Stems.oddClauseOne`.

What is missing (and supplied here) is the *assembly*: an ordinary strong induction on the level
that runs the two steps.  The mutual induction is well founded because
`2j - 1 < 2j` and `2j < 2j + 1`: the even step at level `j` uses the odd clause at the *lower* level
`2j-1`, and the odd step at level `2j+1` uses the even clause at the *lower* level `2j`.

The result is `Work.Rat.c2Free`, i.e. `C2evenFree 1 ∧ C2oddFree 1` from `Work.Serre.SerreE3b`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre

/-- `IsEMSpaceUpTo` does not depend on the proof of `0 < m`. -/
theorem IsEMSpaceUpTo.congr {A : Type} [AddCommGroup A] {m N : ℕ} {hm1 hm2 : 0 < m}
    {X : Type} [TopologicalSpace X] {pt : X} (h : IsEMSpaceUpTo A m hm1 N X pt) :
    IsEMSpaceUpTo A m hm2 N X pt :=
  Eq.mp (congrArg (fun p => IsEMSpaceUpTo A m p N X pt) (Subsingleton.elim hm1 hm2)) h

end Work.Serre

namespace Work.Stems

/-! ## Congruences in the redundant proof arguments -/

/-- The even clause does not depend on the proof of `1 ≤ j`. -/
theorem EvenClause.congr {c j N : ℕ} {h1 h2 : 1 ≤ j} (h : EvenClause c j h1 N) :
    EvenClause c j h2 N :=
  Eq.mp (congrArg (fun p => EvenClause c j p N) (Subsingleton.elim h1 h2)) h

/-- The odd clause does not depend on the proof of `1 ≤ n`. -/
theorem OddClause.congr {c n N : ℕ} {h1 h2 : 1 ≤ n} (h : OddClause c n h1 N) :
    OddClause c n h2 N :=
  Eq.mp (congrArg (fun p => OddClause c n p N) (Subsingleton.elim h1 h2)) h

/-! ## The base case, level `1` -/

/-- **The level-`1` odd clause.**  A range model of `K(ℤ,1)` through degree `N` has the rational
homology of `S¹` through degree `N - 1`: this is `Work.Stems.oddClauseOne` with the (weaker) bound
of the free-top interface, and the bottom cell supplied by `Work.Stems.bottomCellOne`. -/
theorem oddClauseOneFree (N : ℕ) : OddClause 1 1 (by norm_num) N := by
  intro X _ pt hX
  obtain ⟨hgen, hvan⟩ := oddClauseOne X pt N (Work.Serre.IsEMSpaceUpTo.congr hX)
    (bottomCellOne X pt N (Work.Serre.IsEMSpaceUpTo.congr hX))
  exact ⟨hgen, fun d hd0 hdN hd1 => hvan d hd0 (by omega) hd1⟩

/-! ## The two induction steps, with the proof arguments made flexible -/

/-- The even step, with the odd clause supplied for an arbitrary proof of `1 ≤ 2j-1`. -/
theorem evenStepLocal' (c : ℕ) (hE3b : Work.Serre.SerreE3b) {j : ℕ} (hj : 1 ≤ j)
    (hodd : ∀ (M : ℕ) (h : 1 ≤ 2 * j - 1), OddClause c (2 * j - 1) h M) :
    ∀ N : ℕ, EvenClause c j hj N :=
  fun N => evenStepLocal c hE3b j hj (2 * j - 1) rfl
    (fun M => OddClause.congr (hodd M (by omega))) N

/-- The odd step, with the even clause supplied for an arbitrary proof of `1 ≤ j`. -/
theorem oddStepLocal' (c : ℕ) (hE3a : Work.Serre.SerreE3a) {j : ℕ} (hj : 1 ≤ j)
    (heven : ∀ (M : ℕ) (h : 1 ≤ j), EvenClause c j h M) :
    ∀ N : ℕ, OddClause c (2 * j + 1) (by omega) N :=
  fun N => OddClause.congr (oddStepLocal c hE3a j hj (fun M => EvenClause.congr (heven M hj)) N)

/-! ## The mutual induction -/

/-- **The two `C2` clauses, level by level, by strong induction on the level.** -/
theorem c2FreeClauses (hE3b : Work.Serre.SerreE3b) :
    (∀ (j : ℕ) (hj : 1 ≤ j) (N : ℕ), EvenClause 1 j hj N) ∧
      (∀ (n : ℕ) (hn : 1 ≤ n), Odd n → ∀ N : ℕ, OddClause 1 n hn N) := by
  have key : ∀ ℓ : ℕ,
      (∀ (j : ℕ) (hj : 1 ≤ j), 2 * j ≤ ℓ → ∀ N : ℕ, EvenClause 1 j hj N) ∧
        (∀ (n : ℕ) (hn : 1 ≤ n), Odd n → n ≤ ℓ → ∀ N : ℕ, OddClause 1 n hn N) :=
    fun ℓ => Nat.strong_induction_on ℓ (fun ℓ ih => by
      refine ⟨?_, ?_⟩
      · -- the even step: the odd clause is available at the lower level `2j-1`
        intro j hj hjℓ N
        refine evenStepLocal' 1 hE3b hj ?_ N
        intro M h
        exact OddClause.congr
          ((ih (2 * j - 1) (by omega)).2 (2 * j - 1) (by omega) ⟨j - 1, by omega⟩ le_rfl M)
      · -- the odd step
        intro n hn hnodd hnℓ N
        rcases eq_or_lt_of_le hn with h1 | h2
        · -- `n = 1`: the base case
          subst h1
          exact OddClause.congr (oddClauseOneFree N)
        · -- `n ≥ 2` and odd, so `n = 2k+1` with `k ≥ 1`
          obtain ⟨k, hk⟩ := hnodd
          have hk1 : 1 ≤ k := by
            rcases Nat.eq_zero_or_pos k with h0 | hpos
            · exfalso; omega
            · exact hpos
          subst hk
          refine OddClause.congr (oddStepLocal' 1 Work.Serre.serreE3a (by omega) ?_ N)
          intro M h
          exact EvenClause.congr ((ih (2 * k) (by omega)).1 k (by omega) le_rfl M))
  exact ⟨fun j hj N => (key (2 * j)).1 j hj le_rfl N,
    fun n hn hnodd N => (key n).2 n hn hnodd le_rfl N⟩

end Work.Stems

namespace Work.Rat

/-- **The free-top `C2` layer from `SerreE3b`.**  Both halves of the `K(ℤ,n)` computation, with the
free-top (range-model) form of the interface and the constant `c = 1`. -/
theorem c2Free (hE3b : Work.Serre.SerreE3b) :
    Work.Stems.Engine.C2evenFree 1 ∧ Work.Stems.Engine.C2oddFree 1 :=
  ⟨(Work.Stems.c2evenFree_iff 1).mpr (Work.Stems.c2FreeClauses hE3b).1,
    (Work.Stems.c2oddFree_iff 1).mpr (Work.Stems.c2FreeClauses hE3b).2⟩

end Work.Rat
