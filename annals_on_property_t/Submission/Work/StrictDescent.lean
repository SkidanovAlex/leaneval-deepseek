import Submission.Work.AssemblyBridge
import Submission.Work.ShortImagesSigned
import Submission.Work.AggregateStep
import Submission.Work.RebalanceProtocol
import Mathlib.Data.Fin.Tuple.Sort

open Submission.Nielsen
open Submission.FreeGroupAut
open FreeGroup
set_option autoImplicit false

/-!
# The strict `N`-descent pin for `aut_nielsen`

`AssemblyBridge.aut_nielsen_of_reachable_signed` reduces `aut_nielsen` to the
reachability statement `∀ α, ∃ γ ∈ AutClosure n, IsSignedPermutation (α · γ)`.
This module proves that reachability follows from the *strict-descent step*:

    strict_step_of_not_signed (n) (α) :
      ¬ IsSignedPermutation α  ⟹  ∃ γ ∈ AutClosure n, N (α · γ) < N α

by a well-founded recursion on the total reduced length `N` (each step is
right composition by a closure element, `N` strictly decreases, so the
recursion terminates; at a state with no step the contrapositive of the step
lemma says the state *is* a signed permutation — the `1`-move closes it):

    theorem reachable_signed_of_strict (hstrict : ...strict step...) :
        ∀ α, ∃ γ ∈ AutClosure n, IsSignedPermutation (α · γ)
    theorem aut_nielsen_of_strict (hstrict : ...) :
        Subgroup.closure (AutGen n : Set (MulAut (FreeGroup (Fin n)))) = ⊤

The recursion is `WellFounded.fix` over the well-founded strict-`N` relation
(`InvImage.wf` of `Nat.lt`); in the non-terminal case the witness is
`γ₀·γ₁` (the step move followed by the recursive witness), which lies in the
closure because `AutClosure n` is a subgroup.

**Why this is the right pin.**  `peakAut` (`LongArm.lean`) shows a single
elementary move need not decrease `N` at a genuine (Fall-II balanced) basis,
so `strict_step_of_not_signed` is *not* the naive single-move gradient
descent.  Its proof is the classical two-phase analysis already decomposed in
this project:

* `α` not a signed permutation ⟹ some image is long
  (contrapositive of `ShortImagesSigned.short_images_signed`);
* `AggregateStep.aggregate_reduces_or_balanced` turns a long image into
  either a strict single elementary move (Fall I, already attached by
  `AggregateDispatch.confined_strict_*_move`) or a Fall-II balanced
  configuration (`es[j] = ±w_p = A·B`, halves covered by the two neighbours);
* **Open (the Fall-II rebalancing core, to be transcribed faithfully from
  the classical source, not guessed):** a Fall-II configuration of `α`
  yields a closure *macro* `γ` with `N (α·γ) < N α`.  The infrastructure the
  transcription consumes is in place: the balanced content
  (`AggregateProtocol.aggregate_balanced_element`,
  `ImageAggregate.aggregate_element_dichotomy`), the element-level
  rebalancing moves (`AggregateCoordinate.balanced_attach_right_plus/minus`,
  `balanced_attach_left_plus/minus`, `balanced_closure_move_*`), the witness
  selectors (`witness_begin_invB`/`witness_end_B`/…, the `u ≠ p` selectors
  `witness_ne_*` from `SystemReduced`), the word-level combination lemmas
  (`T3RebalanceTuple.rebalance_move_N_le[_left]`,
  `rebalance_move_N_lt[_of_align]`, `norm_mul_inv_end_lt`,
  `norm_mul_begin_lt`), and the termination scaffold
  (`RebalanceProtocol.RebalanceData` + `protocol_wf` + `descend_terminal`).

**The Fall-II pin.**  The Fall-I half of `strict_step_of_not_signed` is
already attached (`AggregateStep.aggregate_reduces_or_balanced` gives a strict
single elementary move from a long image when the strict phase fires).  The
remaining obligation is isolated as the *Fall-II pin* `hF` of
`aut_nielsen_of_fallII`:

    FallTwoConfig α  —  `a_m`'s image aggregate has an interior confined
      factor `j` in the balanced half-half state (`es[j] = A ++ B`,
      `|A| = |B|`, neighbours `X ++ invRev A` / `invRev B ++ Z`)
    ⟹  ∃ γ ∈ AutClosure n, N (α · γ) < N α

(`not_signed_has_long_image` + `aggregate_reduces_or_balanced` turn any
non-signed-permutation `α` into either a strict Fall-I move or a
`FallTwoConfig` state, so `aut_nielsen_of_fallII` is exactly
`aut_nielsen_of_strict` with the Fall-II half left as the single open
obligation.)  The proof of the pin is the classical rebalancing run, whose
building blocks are committed: the non-strict propagation moves
(`AggregateCoordinate.balanced_closure_move_*`, with word tracking in
`T3RebalanceTuple.rebalance_image_word[_left]`) push the balanced position,
and the strict reappearance cases `FallII.fallII_right_minus_strict`,
`fallII_right_plus_strict`, `fallII_left_plus_strict`, `fallII_left_minus_strict`
fire exactly when the pushed configuration develops a boundary cancellation
(a stub meets a half); a faithful transcription of that run (from the
classical source, not guessed) is what remains.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- **Strict descent reaches a signed permutation.**  If every automorphism
that is not a signed permutation can be right-composed by a closure element
to strictly smaller total length `N`, then every automorphism can be
right-composed by closure elements into a signed permutation: iterate the
strict step (well-founded recursion on `N`); when no strict step exists the
contrapositive says the state is already a signed permutation, closed by the
trivial move. -/
theorem reachable_signed_of_strict {n : ℕ}
    (hstrict : ∀ α : MulAut (FreeGroup (Fin n)), ¬ IsSignedPermutation α →
      ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α) :
    ∀ α : MulAut (FreeGroup (Fin n)),
      ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ IsSignedPermutation (α * γ) := by
  classical
  let C : MulAut (FreeGroup (Fin n)) → Prop :=
    fun α => ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ IsSignedPermutation (α * γ)
  have hwf : WellFounded (fun b a : MulAut (FreeGroup (Fin n)) => N b < N a) :=
    InvImage.wf (f := N) (Nat.lt_wfRel.wf)
  intro α
  refine WellFounded.fix hwf (C := C) ?_ α
  intro x rec
  by_cases ht : IsSignedPermutation x
  · refine ⟨1, ?_, ?_⟩
    · exact (AutClosure n).one_mem
    · simpa using ht
  · rcases hstrict x (by intro hs; exact ht hs) with ⟨γ0, hγ0, hN⟩
    rcases rec (x * γ0) hN with ⟨γ1, hγ1, hS⟩
    refine ⟨γ0 * γ1, ?_, ?_⟩
    · exact (AutClosure n).mul_mem hγ0 hγ1
    · simpa [mul_assoc] using hS

/-- **`aut_nielsen` from the strict-descent step.**  If every
non-signed-permutation automorphism admits a strict closure move, then the
elementary Nielsen moves generate `Aut(F_n)`. -/
theorem aut_nielsen_of_strict {n : ℕ}
    (hstrict : ∀ α : MulAut (FreeGroup (Fin n)), ¬ IsSignedPermutation α →
      ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α) :
    Subgroup.closure (AutGen n : Set (MulAut (FreeGroup (Fin n)))) = ⊤ := by
  exact aut_nielsen_of_reachable_signed n (fun α => reachable_signed_of_strict (n := n) hstrict α)

/-! ## The Fall-II pin: from a balanced configuration to a strict move -/

/-- **The Fall-II (balanced, non-minimal) configuration of `α`.**  Some
standard generator `a_m` has an image-aggregate expression with an *interior
confined* factor `j` in the balanced half-half state: `es[j] = A ++ B` with
`|A| = |B|`, the left neighbour covering `invRev A` from the right
(`es[j-1] = X ++ invRev A`) and the right neighbour covering `invRev B` from
the left (`es[j+1] = invRev B ++ Z`).  (Exactly the second disjunct of
`AggregateStep.aggregate_reduces_or_balanced`.) -/
def FallTwoConfig {n : ℕ} (α : MulAut (FreeGroup (Fin n))) : Prop :=
  ∃ (m : Fin n) (j : ℕ) (hj : j < (imageAggregate α m).length)
    (hj0 : 0 < j) (hj1 : j + 1 < (imageAggregate α m).length),
    Confined (aggregateWords (imageAggregate α m)) j ∧
    ∃ (A B X Z : List (Fin n × Bool)),
      ((imageAggregate α m)[j]).toWord = A ++ B ∧ A.length = B.length ∧
      ((imageAggregate α m)[j - 1]).toWord = X ++ FreeGroup.invRev A ∧
      ((imageAggregate α m)[j + 1]).toWord = FreeGroup.invRev B ++ Z

/-- Not a signed permutation ⟹ some basis image has reduced length ≥ 2
(contrapositive of `ShortImagesSigned.short_images_signed`). -/
theorem not_signed_has_long_image {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (h : ¬ IsSignedPermutation α) :
    ∃ i : Fin n, 1 < FreeGroup.norm (α (FreeGroup.of i)) := by
  by_contra hn
  apply h
  exact short_images_signed α (by
    intro i
    have hle : ¬ 1 < FreeGroup.norm (α (FreeGroup.of i)) := by
      intro hgt
      exact hn ⟨i, hgt⟩
    omega)

/-- **Reachability from the Fall-II pin.**  If every Fall-II configuration of
an automorphism admits a strict closure move, then every automorphism can be
right-composed by closure elements into a signed permutation: a non-signed
permutation has a long image (`not_signed_has_long_image`), the aggregate
analysis (`AggregateStep.aggregate_reduces_or_balanced`) yields either a
strict Fall-I move or a Fall-II configuration, and the strict descent of
`reachable_signed_of_strict` terminates. -/
theorem reachable_signed_of_fallII {n : ℕ}
    (hF : ∀ α : MulAut (FreeGroup (Fin n)), FallTwoConfig α →
      ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α) :
    ∀ α : MulAut (FreeGroup (Fin n)),
      ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ IsSignedPermutation (α * γ) := by
  refine reachable_signed_of_strict (n := n) ?_
  intro α hnot
  rcases not_signed_has_long_image α hnot with ⟨i, hi⟩
  rcases aggregate_reduces_or_balanced α ⟨i, hi⟩ with hs | hb
  · exact hs
  · exact hF α hb

/-- **`aut_nielsen` from the Fall-II pin.**  If every balanced (Fall-II)
configuration of an automorphism admits a strict closure macro
(`FallII.fallII_*_strict` fire on the boundary-cancellation cases; the
rebalancing run must show such a case develops), then the elementary Nielsen
moves generate `Aut(F_n)`. -/
theorem aut_nielsen_of_fallII {n : ℕ}
    (hF : ∀ α : MulAut (FreeGroup (Fin n)), FallTwoConfig α →
      ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α) :
    Subgroup.closure (AutGen n : Set (MulAut (FreeGroup (Fin n)))) = ⊤ := by
  exact aut_nielsen_of_strict (n := n) (by
    intro α hnot
    rcases not_signed_has_long_image α hnot with ⟨i, hi⟩
    rcases aggregate_reduces_or_balanced α ⟨i, hi⟩ with hs | hb
    · exact hs
    · exact hF α hb)

/-- **A Fall-Two configuration of `α` yields an exactly-half-absorbed element
of an ordered state.**  The middle factor of the Fall-Two aggregate is a
basis image `±α(a_u)` (every aggregate factor is, by
`imageAggregate_isImageAggregate`); ordering `α`'s coordinates into a sorted
row and taking the row position of `u`, the element at that position is
exactly-half absorbed between two elements of the state
(`ExactlyHalfAbsorbed`, the pinned form of the Fall-Two content).  This is
the bridge that turns the pin's `FallTwoConfig` into the state-level input of
the rebalancing run. -/
theorem fallTwoConfig_to_state {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hF : FallTwoConfig α) :
    ∃ S : RebalanceState n, S.α = α ∧ ∃ p : Fin n, ExactlyHalfAbsorbed S p := by
  classical
  rcases hF with ⟨m, j, hj, hj0, hj1, hconf, A, B, X, Z, hA, hAB, hX, hZ⟩
  let k : Fin n → ℕ := fun i => FreeGroup.norm (α (FreeGroup.of i))
  let row : Equiv.Perm (Fin n) := Tuple.sort k
  have hrow : ∀ i j : Fin n, i.val < j.val →
      FreeGroup.norm (α (FreeGroup.of (row i))) ≤ FreeGroup.norm (α (FreeGroup.of (row j))) := by
    intro i j hij
    exact Tuple.monotone_sort k (le_of_lt hij)
  have himg := imageAggregate_isImageAggregate α m
  rcases himg ((imageAggregate α m)[j]) (List.getElem_mem hj) with ⟨u, hu⟩
  let p : Fin n := row.symm u
  refine ⟨⟨α, row, hrow⟩, rfl, p, ?_⟩
  refine ⟨m, j, ?hj, hj0, hj1, hconf, ?mid, A, B, X, Z, hA, hAB, hX, hZ⟩
  · simpa [row, p] using hj
  · have hpu : row p = u := by
      unfold p
      exact Equiv.apply_symm_apply row u
    rcases hu with hu | hu
    · left
      simpa [hpu] using hu
    · right
      simpa [hpu] using hu

end Submission.Nielsen
