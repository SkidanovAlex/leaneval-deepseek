import Submission.Work.Item3.WitnessCover

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
set_option autoImplicit false

/-!
# Item 3, OldWitness: the old witness at the balanced coordinate is destroyed

The pass at the balanced coordinate `c` (`w_c = A ++ B`, `|A| = |B|`) combines
every *neighbour* coordinate in `Q` (the two neighbours of the old witness,
each carrying one of the covering words `invRev A` / `invRev B`), leaving the
balanced element itself inert (`c ∉ Q`, so `item2Pass_fix` keeps
`w_c = A ++ B`).  This module commits the three elementary consequences of
that reading, each kernel-checked:

* `pass_balanced_word_unchanged`: the balanced coordinate `c` keeps its word
  `A ++ B` under the pass (direct from `item2Pass_fix`);
* `factor_inv_word_ends`: an *inverse* factor `es[j] = w_u⁻¹` whose word is
  `invRev B ++ Z` — the covering word of a left neighbour — makes `w_u` end
  with `B`, i.e. the underlying basis coordinate is in the ends-with-`B`
  class that the pass combines (`toWord_inv` + `invRev_append` +
  `invRev_invRev`);
* `factor_plus_word_begins`: a *plus* factor `es[j] = w_u` whose word is
  `invRev B ++ Z` — the covering word of a right neighbour — makes `w_u`
  begin with `B⁻¹`, i.e. the underlying basis coordinate is in the
  begins-with-`B⁻¹` class (`lam` branch of the pass).

Together with `WitnessCover` these give the per-coordinate covering of the
witness triple `(w'_{row i}, predecessor, successor)` at a hypothetical
surviving row position `i ≤ p`: the two neighbours are affected (their
coordinates are in the ends-with-`B` / begins-with-`B⁻¹` classes via the two
factor lemmas above), so every genuinely-new letter of each affected word
lies in `newLetterSet A` (`|newLetterSet A| ≤ 2·|A|`), while `c` itself keeps
`A ++ B`.

**Remaining genuine obligation.**  The classical no-reappearance assertion —
*no element at a row position `i ≤ p` is exactly-half absorbed after the
pass* — is NOT a valid direct contradiction from the covering bound alone
(containment of new letters in `newLetterSet A` is not contradictory): it is
a *global* statement about the new automorphism's image aggregates and still
requires the aggregate-level analysis.  Nothing in this module claims it;
do not mint a lemma of that shape from these facts alone.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- **The balanced coordinate keeps its word under the pass** (`c ∉ Q`):
`item2Pass_fix` makes the pass act trivially on `a_c`, so
`toWord((α·pass)(a_c)) = A ++ B`. -/
theorem pass_balanced_word_unchanged {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (c : Fin n) (A B : List (Fin n × Bool)) (Q : List (Fin n))
    (hcQ : c ∉ Q) (hmid : (α (FreeGroup.of c)).toWord = A ++ B) :
    ((α * item2Pass α c A B Q) (FreeGroup.of c)).toWord = A ++ B := by
  have hfix := item2Pass_fix α c A B Q hcQ
  rw [hfix]
  exact hmid

/-- **An inverse factor with the left-covering word makes its basis image end
with `B`.**  If `es[j] = w_u⁻¹` and `toWord(es[j]) = invRev B ++ Z` (the
covering word of a left neighbour in the witness aggregate), then `w_u` ends
with `B` — the ends-with-`B` class the pass combines. -/
theorem factor_inv_word_ends {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) {j : ℕ} (hj : j < es.length) {u : Fin n}
    (B Z : List (Fin n × Bool))
    (hright : (es[j]).toWord = FreeGroup.invRev B ++ Z)
    (hu : es[j] = (α (FreeGroup.of u))⁻¹) :
    ∃ Y : List (Fin n × Bool), (α (FreeGroup.of u)).toWord = Y ++ B := by
  refine ⟨FreeGroup.invRev Z, ?_⟩
  have hw : (α (FreeGroup.of u)) = (es[j])⁻¹ := by
    rw [hu]
    simp
  calc
    (α (FreeGroup.of u)).toWord = ((es[j])⁻¹).toWord := by rw [hw]
    _ = FreeGroup.invRev (es[j].toWord) := by rw [FreeGroup.toWord_inv]
    _ = FreeGroup.invRev (FreeGroup.invRev B ++ Z) := by rw [hright]
    _ = FreeGroup.invRev Z ++ FreeGroup.invRev (FreeGroup.invRev B) := by
        rw [FreeGroup.invRev_append]
    _ = FreeGroup.invRev Z ++ B := by rw [FreeGroup.invRev_invRev]

/-- **A plus factor with the right-covering word makes its basis image begin
with `B⁻¹`.**  If `es[j] = w_u` and `toWord(es[j]) = invRev B ++ Z` (the
covering word of a right neighbour in the witness aggregate), then `w_u`
begins with `B⁻¹` — the begins-with-`B⁻¹` class the pass combines. -/
theorem factor_plus_word_begins {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) {j : ℕ} (hj : j < es.length) {u : Fin n}
    (B Z : List (Fin n × Bool))
    (hright : (es[j]).toWord = FreeGroup.invRev B ++ Z)
    (hu : es[j] = α (FreeGroup.of u)) :
    ∃ Y : List (Fin n × Bool), (α (FreeGroup.of u)).toWord = FreeGroup.invRev B ++ Y := by
  refine ⟨Z, ?_⟩
  rw [← hu]
  exact hright

end Submission.Nielsen
