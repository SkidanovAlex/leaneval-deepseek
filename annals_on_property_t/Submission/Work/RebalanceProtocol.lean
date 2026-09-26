import Submission.Work.T3Rebalance
import Submission.Work.ImageAggregate
import Submission.Work.AggregateProtocol
import Submission.Work.AggregateCoordinate
import Submission.Work.Nielsen
import Mathlib.Data.Fin.Tuple.Sort

open Submission.FreeGroupAut
set_option autoImplicit false

/-!
# The rebalancing protocol as a parameterised structure

The classical two-phase reduction of a system `S = (α₁,…,αₙ)` orders the
elements by length and rebalances the *balanced* (half-half) element `α_p`
against further elements, shifting the balanced position forward at constant
total length until a strict ("more than half") shortening reappears.  A
faithful transcription of that system-level protocol still requires the
classical source (Lyndon–Schupp / Magnus–Karrass–Solitar); nothing about it is
guessed here.  What this module fixes instead is the *interface* the protocol
must satisfy, as a parameterised structure, together with the generic
termination/descent machinery built over it (which is independent of the
combinatorial content).

## Where this sits in the `aut_nielsen` architecture (session note)

The outer loop of the reduction is **not** a hand-written two-phase
algorithm; it is the strict `N`-descent pinned in
`Submission/Work/StrictDescent.lean`:

    aut_nielsen_of_strict (hstrict : ∀ α, ¬ IsSignedPermutation α →
        ∃ γ ∈ AutClosure n, N (α · γ) < N α) : closure (AutGen n) = ⊤

(well-founded recursion on `N`; each step is right composition by a closure
element, possibly a *macro* — a product of elementary moves — which is how
the Fall-II/balanced phase is absorbed into a single strict step).  The
remaining obligation `hstrict` is exactly the content of the classical
rebalancing theorem: from a Fall-II balanced configuration (`AggregateStep.
aggregate_reduces_or_balanced`'s second disjunct: `w_p = A·B`, `|A| = |B|`,
the two neighbours covering the two halves) one obtains a closure element
strictly shortening `N`.

This module's `RebalanceData` is the *template* for that Fall-II analysis at
the system level (its State is a system description carrying the balanced
position `idx` of length-order index `< c`, and its step relation encodes
that each move strictly shortens or keeps `N` while advancing `idx`).  The
generic results below (`protocol_wf`, `step_wf`, `descend`, `descend_no_step`,
`descend_reachable`, `descend_terminal`) give the well-founded
termination/descent over any faithful instantiation; the element-level move
content such an instantiation must supply is already committed:
`AggregateCoordinate.balanced_attach_right_plus/minus`,
`balanced_attach_left_plus/minus` and their closure forms
`balanced_closure_move_*` (right composition by `lam`/`rhoNeg`, `N`
non-increasing), `AggregateProtocol.witness_*` (the `B`-ending /
`B⁻¹`-beginning structure of the witness basis image), the `u ≠ p`
selectors `witness_ne_*` (`SystemReduced`), and the word-level replacement
identities `T3RebalanceTuple.mul_inv_end_toWord` /
`norm_mul_inv_end_lt` / `rebalance_move_N_lt[_of_align]` giving the *strict*
shortening once a boundary cancellation occurs.

### The Fall-II run, read from the classical text (faithful reading note)

Nielsen 1919, Math. Ann. 79, pp. 270–271 (OCR archived at
`Submission/Work/Nielsen1919_reference.txt`), decoded (support measure in the
source; the formalisation uses reduced length with the same structure):

1. If a system admits no strict (more-than-half) combination, some element
   `α_p` is absorbed *exactly half* by its two neighbours; write it
   `α_p = A_p·B_p` in halves.  Order the system as a row with no element
   longer than a later one, and take `α_p` to be the *first* such
   half-absorbed element.
2. While another system element *ends with* `B_p` (resp. *begins with*
   `B_p⁻¹`), combine it with `α_p` so that `A_p⁻¹` (resp. `A_p`) takes its
   place — exactly the `rhoNeg`/`lam` moves of `balanced_attach_*`, which
   keep the total length fixed (`|A_p| = |B_p|`).
3. After these moves `α_p` has lost the property and no *earlier* element
   has newly acquired it (their initial/terminal parts below the length of
   `A_p` are unchanged) — so the next half-absorbed element, if no strict
   cancellation has appeared, has a strictly later index.
4. Since the index only advances and the system is finite, the procedure
   terminates; for a genuine (primitive) system a strict "more than half"
   cancellation must therefore recur — the Fall-I configuration that the
   `FallII.fallII_*_strict` lemmas convert into a strict closure move and
   the descent pin (`StrictDescent.aut_nielsen_of_fallII`) consumes.

Item 2's moves and item 4's strict reappearance cases are committed
(`AggregateCoordinate.balanced_attach_*` / `balanced_closure_move_*`,
`FallII.fallII_*_strict`, post-move words in `FallII.fallII_*_word`); the
missing formal content is the *run invariant* of item 3 (index advance) and
the *forced reappearance* of item 4 — the faithful transcription still to be
written.

### Item 3, stated precisely (index-advance lemma — formalisation target)

The run-invariant lemma the transcription must establish, stated over the
ordered-system layer it will require (not yet formalised; nothing here is
guessed — the claim is the literal content of Nielsen 1919 p. 271, and the
local word facts it needs are committed):

> **Index-advance.**  Let `S = (α₁,…,α_n)` be the system ordered so that no
> element is longer than a later one, and let `p` be the *first* index such
> that `α_p` is exactly-half absorbed between two other elements of `S`
> (write `α_p = A_p·B_p`, `|A_p| = |B_p|`).  Let `S'` be obtained from `S`
> by replacing every element ending with `B_p` by its `rhoNeg`-combination
> with `α_p`, and every element beginning with `B_p⁻¹` by its
> `lam`-combination with `α_p`.  Then
> (i) `α_p` is no longer exactly-half absorbed between two elements of `S'`,
> and
> (ii) no `α_i` with `i < p` is exactly-half absorbed between two elements
> of `S'`;
> hence the least exactly-half-absorbed index of `S'` (if any) exceeds `p`.

Formal definitions the statement needs (all faithful to the source): an
ordered *system state* (basis images ordered by `norm`), the predicate
"`α_i` is exactly-half absorbed between two elements of the state" (the
`FallTwoConfig`-style balanced condition relative to the two aggregate
neighbours), and the one-step transformation `S ↦ S'` of item 2.  The local
facts it is built on are committed: an item-2 move changes *only* the
combined coordinate (`Nielsen.mul_rhoNeg_apply_other` / `mul_lam_apply_other`),
keeps every other image — in particular the balanced `α_p = A_p·B_p` and all
elements preceding `p` that are not combined — word-for-word unchanged, and
gives the combined coordinate the explicit post-move word of
`FallII.fallII_*_word` (the `B_p`-suffix replaced by `invRev A_p`, the
`B_p⁻¹`-prefix by `A_p`); so no half-absorbed element strictly before `p` is
created or destroyed except by its own combination, which removes the
`B_p`/`B_p⁻¹` boundary that its half-absorption depended on.  The interface:`

    structure RebalanceData where
      State      : Type                       -- the system states
      N          : State → ℕ                  -- total reduced length
      idx        : State → ℕ                  -- current balanced position (length-order index)
      c          : ℕ                          -- number of positions (finite system)
      hbound     : ∀ s, idx s < c             -- the balanced position is within the system
      step       : State → State → Prop       -- the rebalancing move
      step_progress : ∀ {s t}, step s t →     -- each move either strictly shortens,
        N t < N s ∨ (N t = N s ∧ idx s < idx t)   -- or keeps length and advances idx

The facts the source must supply when instantiating the structure are
precisely the field obligations `hbound` and `step_progress` (plus the *existence*
of a step whenever a balanced element has a further element `α_q` ending with
`B_p` / beginning with `A_p^{±1}` — the classical combination move whose word
content is already in `T3Rebalance.rebalance_join_reduce` /
`rebalance_join_le` — and the terminal-state classification "no step ⟹ signed
permutation", which closes the `aut_nielsen` assembly).

Generic results over the structure (all kernel-checked):

* `protocol_wf` — the lexicographic measure `(N, c − idx)` is well-founded
  (instance of `rebalance_protocol_terminates`), so any step sequence
  terminates ("der Index dauernd wächst … nicht unbegrenzt fortsetzbar");
* `step_wf` — the step relation itself is well-founded;
* `descend`, `descend_no_step`, `descend_reachable` — from every state a finite
  step chain reaches a state admitting no further step.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- **Rebalance protocol data.**  A parameterised description of the
classical rebalancing protocol, collecting exactly the obligations the
classical source must supply: the system states, the total-length measure
`N`, the current balanced position `idx < c` (finite system), the rebalancing
step, and the progress guarantee that every step either strictly decreases
`N` or keeps `N` constant while strictly advancing `idx`. -/
structure RebalanceData where
  /-- The system states (concretely: the ordered tuples of a free basis being
  reduced, together with their aggregate context). -/
  State : Type
  /-- Total reduced length of the system. -/
  N : State → ℕ
  /-- Current balanced position (index in the length order of the element
  being rebalanced). -/
  idx : State → ℕ
  /-- Number of elements of the (finite) system. -/
  c : ℕ
  /-- The balanced position is within the system. -/
  hbound : ∀ s : State, idx s < c
  /-- The rebalancing step: `step s t` means `s` moves to `t` by one protocol
  move (combination of the balanced element with a further element ending in
  `B_p` / beginning in `A_p^{±1}`). -/
  step : State → State → Prop
  /-- Progress: every step either strictly decreases the total length, or
  keeps the length equal and strictly advances the balanced position. -/
  step_progress : ∀ {s t : State}, step s t →
    N t < N s ∨ (N t = N s ∧ idx s < idx t)

namespace RebalanceData

variable (D : RebalanceData)

/-- The lexicographic progress measure `(N, idx)`: `x` is below `y` when `N`
drops, or `N` is equal and the balanced index has advanced from `x` to `y`. -/
def Protocol (D : RebalanceData) : D.State → D.State → Prop :=
  fun x y => D.N x < D.N y ∨ (D.N x = D.N y ∧ D.idx y < D.idx x)

/-- The protocol measure is well-founded: no step sequence can run forever
(the lexicographic pair `(N, c − idx)` over `ℕ × ℕ`; instance of
`rebalance_protocol_terminates`). -/
theorem protocol_wf (D : RebalanceData) : WellFounded D.Protocol := by
  exact rebalance_protocol_terminates (N := D.N) (idx := D.idx) (c := D.c)
    (by intro s; exact D.hbound s)

/-- The step relation of the protocol is well-founded: every step either
decreases `N` or keeps `N` and advances `idx`, so infinite execution is
impossible. -/
theorem step_wf (D : RebalanceData) : WellFounded (fun t s : D.State => D.step s t) := by
  have hwfP : WellFounded D.Protocol := D.protocol_wf
  exact WellFounded.intro (fun t =>
    WellFounded.induction hwfP
      (C := fun y : D.State => Acc (fun a b : D.State => D.step b a) y) t (by
        intro y ih
        refine Acc.intro y ?_
        intro s hsy
        exact ih s (D.step_progress hsy)))

/-- The recursion step of the descent: from `s`, follow an arbitrary step if
one exists, else stop at `s`. -/
noncomputable def F (D : RebalanceData) (x : D.State)
    (rec : ∀ y : D.State, (fun t s : D.State => D.step s t) y x → D.State) : D.State := by
  classical
  exact if h : ∃ t : D.State, D.step x t then
    rec (Classical.choose h) (Classical.choose_spec h) else x

/-- From every state, iterate protocol steps as long as possible. -/
noncomputable def descend (D : RebalanceData) : D.State → D.State :=
  WellFounded.fix (D.step_wf) (D.F)

/-- The defining equation of the descent: `descend s` is `s` when no step
leaves `s`, and otherwise equals the descent of a chosen successor. -/
lemma descend_fix (D : RebalanceData) (s : D.State) :
    D.descend s = D.F s (fun y _ => D.descend y) := by
  unfold descend
  exact WellFounded.fix_eq (D.step_wf) (D.F) s

/-- When a step leaves `s`, descending `s` equals descending a chosen
successor. -/
lemma descend_step_eq (D : RebalanceData) (s : D.State) (h : ∃ t : D.State, D.step s t) :
    D.descend s = D.descend (Classical.choose h) := by
  rw [D.descend_fix s]
  simp [F, h]

/-- When no step leaves `s`, the descent stops at `s`. -/
lemma descend_no_step_eq (D : RebalanceData) (s : D.State) (h : ¬ ∃ t : D.State, D.step s t) :
    D.descend s = s := by
  rw [D.descend_fix s]
  simp [F, h]

/-- The descent terminates at a state admitting no further step. -/
theorem descend_no_step (D : RebalanceData) (s : D.State) :
    ¬ ∃ t : D.State, D.step (D.descend s) t := by
  classical
  refine WellFounded.induction (D.step_wf)
    (C := fun x : D.State => ¬ ∃ t : D.State, D.step (D.descend x) t) s ?_
  intro x ih
  by_cases hx : ∃ t : D.State, D.step x t
  · rw [D.descend_step_eq x hx]
    exact ih (Classical.choose hx) (Classical.choose_spec hx)
  · rw [D.descend_no_step_eq x hx]
    exact hx

/-- The descent reaches its terminal state by a finite chain of protocol
steps. -/
theorem descend_reachable (D : RebalanceData) (s : D.State) :
    Relation.ReflTransGen D.step s (D.descend s) := by
  classical
  refine WellFounded.induction (D.step_wf)
    (C := fun x : D.State => Relation.ReflTransGen D.step x (D.descend x)) s ?_
  intro x ih
  by_cases hx : ∃ t : D.State, D.step x t
  · rw [D.descend_step_eq x hx]
    exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (Classical.choose_spec hx))
      (ih (Classical.choose hx) (Classical.choose_spec hx))
  · have hd : D.descend x = x := by
      rw [D.descend_fix x]
      simp [F, hx]
    -- rewriting `descend x ↦ x` makes the reflexive-transitive chain the
    -- trivial one; rw closes the goal
    rw [hd]

/-- From every state, a finite chain of protocol steps reaches a terminal
state: one with no further step available.  (The chain respects the
lexicographic measure, so the balanced position can only advance finitely
often between strict shortenings.) -/
theorem descend_terminal (D : RebalanceData) (s : D.State) :
    Relation.ReflTransGen D.step s (D.descend s) ∧
      ¬ ∃ t : D.State, D.step (D.descend s) t :=
  ⟨D.descend_reachable s, D.descend_no_step s⟩

end RebalanceData

/-! ## The ordered system state and the half-absorbed predicate

The run of the Fall-II phase operates on an *ordered system state*: the
current basis images `w_i = α(a_i)` together with a row (a linear order of
the coordinates) in which no element is longer than a later one
(`RebalanceState`).  The balanced-phase moves replace equal-length content
(`|A_p| = |B_p|`), so every element's reduced length is invariant and the row
stays sorted throughout the run; the row position of the balanced element is
the "index" whose strict advance is item 3 of the protocol.

The element at row position `p` is *exactly-half absorbed between two
elements of the state* (`ExactlyHalfAbsorbed S p`, Nielsen 1919 p. 271
"zwischen zwei anderen je zur Hälfte absorbiert") when some standard
generator `a_m` has an image-aggregate expression with a *confined* interior
factor at position `j` whose value is `± α(a_{row p})` and whose word splits
into two halves `A ++ B` (`|A| = |B|`) covered exactly by the two
neighbouring factors (`X ++ invRev A` and `invRev B ++ Z`) — the
`FallTwoConfig`-style balanced content of `StrictDescent.lean` pinned to the
given row element.  With this predicate, item 3's index-advance lemma
(documented above) is a bounded statement over the committed local facts
(`Nielsen.mul_rhoNeg_apply_other` / `mul_lam_apply_other`,
`FallII.fallII_*_word`).
-/

/-- **Ordered system state.**  The current automorphism `α` (basis images
`w_i = α(a_i)`) together with a row: a linear order of the coordinates in
which no element is longer than a later one.  The balanced-phase moves of
the Fall-II run preserve every element's length (`|A_p| = |B_p|`), so the
row stays sorted throughout; the row position of the balanced element is
the protocol index. -/
structure RebalanceState (n : ℕ) where
  /-- The current automorphism; the basis images are `w_i = α(a_i)`. -/
  α : MulAut (FreeGroup (Fin n))
  /-- The row: `row i` is the coordinate (system element) at row position
  `i`. -/
  row : Equiv.Perm (Fin n)
  /-- The row is ordered by non-decreasing reduced length: no element is
  longer than a later one. -/
  sorted : ∀ i j : Fin n, i.val < j.val →
    FreeGroup.norm (α (FreeGroup.of (row i))) ≤ FreeGroup.norm (α (FreeGroup.of (row j)))

namespace RebalanceState

/-- The element at row position `p`. -/
def element {n : ℕ} (S : RebalanceState n) (p : Fin n) : FreeGroup (Fin n) :=
  S.α (FreeGroup.of (S.row p))

/-- Its reduced length. -/
def elen {n : ℕ} (S : RebalanceState n) (p : Fin n) : ℕ :=
  FreeGroup.norm (S.element p)

end RebalanceState

/-- **Exactly-half absorbed between two elements of the state.**  The
element at row position `p` is exactly-half absorbed when some standard
generator `a_m` has an image-aggregate expression with a *confined* interior
factor at position `j` whose value is `± α(a_{row p})`, and whose word
splits into two halves `A ++ B` (`|A| = |B|`) covered exactly by the two
neighbouring factors (`X ++ invRev A` on the left, `invRev B ++ Z` on the
right).  This is the `FallTwoConfig`-style balanced content pinned to the
row element — Nielsen 1919 p. 271 "zwischen zwei anderen je zur Hälfte
absorbiert". -/
def ExactlyHalfAbsorbed {n : ℕ} (S : RebalanceState n) (p : Fin n) : Prop :=
  ∃ (m : Fin n) (j : ℕ) (hj : j < (imageAggregate S.α m).length)
    (hj0 : 0 < j) (hj1 : j + 1 < (imageAggregate S.α m).length),
    Confined (aggregateWords (imageAggregate S.α m)) j ∧
    ((imageAggregate S.α m)[j] = S.α (FreeGroup.of (S.row p)) ∨
      (imageAggregate S.α m)[j] = (S.α (FreeGroup.of (S.row p)))⁻¹) ∧
    ∃ (A B X Z : List (Fin n × Bool)),
      ((imageAggregate S.α m)[j]).toWord = A ++ B ∧ A.length = B.length ∧
      ((imageAggregate S.α m)[j - 1]).toWord = X ++ FreeGroup.invRev A ∧
      ((imageAggregate S.α m)[j + 1]).toWord = FreeGroup.invRev B ++ Z

/-! ### Orderability: every automorphism admits an ordered state -/

/-- **Every automorphism admits a sorted row.**  There is a permutation of
the coordinates in which no basis image is longer than a later one —
`Tuple.sort` by the reduced lengths of the images, which is monotone
(`Tuple.monotone_sort`). -/
theorem exists_sorted_row {n : ℕ} (α : MulAut (FreeGroup (Fin n))) :
    ∃ row : Equiv.Perm (Fin n),
      ∀ i j : Fin n, i.val < j.val →
        FreeGroup.norm (α (FreeGroup.of (row i))) ≤ FreeGroup.norm (α (FreeGroup.of (row j))) := by
  classical
  let k : Fin n → ℕ := fun i => FreeGroup.norm (α (FreeGroup.of i))
  refine ⟨Tuple.sort k, ?_⟩
  intro i j hij
  exact Tuple.monotone_sort k (le_of_lt hij)

namespace RebalanceState

/-- **Every automorphism has an ordered state.**  For the descent to start
from any `α`, some `RebalanceState` carries it as its automorphism. -/
theorem exists_ordered {n : ℕ} (α : MulAut (FreeGroup (Fin n))) :
    ∃ S : RebalanceState n, S.α = α := by
  rcases exists_sorted_row α with ⟨row, hsorted⟩
  exact ⟨⟨α, row, hsorted⟩, rfl⟩

end RebalanceState

/-! ### Item 2 of the Fall-II run: the elementary combination transform

`item2` is the *atomic* item-2 move (Nielsen 1919 p. 271): at the balanced
coordinate `c` with halves `A`, `B` (`|A| = |B|`), an element at coordinate
`q ≠ c` whose word ends with `B` is combined on the right (`rhoNeg q c`,
replacing the `B`-suffix by `invRev A`), and one whose word begins with
`B⁻¹` is combined on the left (`lam q c`, replacing the prefix by `A`);
otherwise `α` is fixed.  The word effect is the committed
`FallII.fallII_*_word` / `T3RebalanceTuple.rebalance_image_word[_left]`
content; the transform is a closure element (`item2_mem_closure`), fixes
every coordinate but `q` (`item2_apply_other`), and is length *non-
increasing* at `q` (`|A| = |B|` replaces equal-length content) — strictly
decreasing exactly when a boundary cancellation occurs, which is the
Fall-I reappearance (`FallII.fallII_*_strict`) that ends the balanced phase
rather than a step of the run.
-/


/-- **Item 2 of the Fall-II run at coordinate `q`.**  If `q`'s word ends with
`B` (the second half of the balanced element at coordinate `c`), combine `q`
with `c` on the right (`rhoNeg q c`, replacing the `B`-suffix by `invRev A`);
if instead it begins with `B⁻¹` (`invRev B`), combine on the left
(`lam q c`, replacing the prefix by `A`); otherwise (or if `q = c`) leave
`α` fixed.  (Word effect, closure membership and length behaviour are the
lemmas below.) -/
noncomputable def item2 {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c q : Fin n)
    (_A B : List (Fin n × Bool)) : MulAut (FreeGroup (Fin n)) := by
  classical
  exact
    if hqc : q ≠ c then
      if hE : ∃ Y : List (Fin n × Bool), (α (FreeGroup.of q)).toWord = Y ++ B then
        rhoNeg q c hqc
      else if hB : ∃ Y : List (Fin n × Bool),
          (α (FreeGroup.of q)).toWord = FreeGroup.invRev B ++ Y then
        lam q c hqc
      else 1
    else 1

/-- An ends-with-`B` element (`q ≠ c`) is combined by `rhoNeg q c`. -/
theorem item2_eq_rhoNeg {n : ℕ} (α : MulAut (FreeGroup (Fin n))) {c q : Fin n} (hqc : q ≠ c)
    (A B : List (Fin n × Bool))
    (hE : ∃ Y : List (Fin n × Bool), (α (FreeGroup.of q)).toWord = Y ++ B) :
    item2 α c q A B = rhoNeg q c hqc := by
  classical
  simp [item2, hqc, hE]

/-- A begins-with-`B⁻¹` element that does not end with `B` (`q ≠ c`) is
combined by `lam q c`. -/
theorem item2_eq_lam {n : ℕ} (α : MulAut (FreeGroup (Fin n))) {c q : Fin n} (hqc : q ≠ c)
    (A B : List (Fin n × Bool))
    (hnoE : ¬ ∃ Y : List (Fin n × Bool), (α (FreeGroup.of q)).toWord = Y ++ B)
    (hB : ∃ Y : List (Fin n × Bool),
      (α (FreeGroup.of q)).toWord = FreeGroup.invRev B ++ Y) :
    item2 α c q A B = lam q c hqc := by
  classical
  simp [item2, hqc, hnoE, hB]

/-- Otherwise the transform is the identity (in particular for `q = c`). -/
theorem item2_eq_one {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c q : Fin n)
    (A B : List (Fin n × Bool)) (hqc : ¬ q ≠ c) : item2 α c q A B = 1 := by
  classical
  simp [item2, hqc]

/-- The item-2 transform is a closure element. -/
theorem item2_mem_closure {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c q : Fin n)
    (A B : List (Fin n × Bool)) :
    item2 α c q A B ∈ AutClosure n := by
  classical
  by_cases hqc : q ≠ c
  · by_cases hE : ∃ Y : List (Fin n × Bool), (α (FreeGroup.of q)).toWord = Y ++ B
    · rw [item2_eq_rhoNeg α hqc A B hE]
      exact rhoNeg_mem_closure hqc
    · by_cases hB : ∃ Y : List (Fin n × Bool),
          (α (FreeGroup.of q)).toWord = FreeGroup.invRev B ++ Y
      · rw [item2_eq_lam α hqc A B hE hB]
        exact lam_mem_closure hqc
      · simp [item2, hqc, hE, hB]
  · rw [item2_eq_one α c q A B hqc]
    exact (AutClosure n).one_mem

/-- Coordinates other than `q` are fixed by the item-2 transform at `q`. -/
theorem item2_apply_other {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c q k : Fin n)
    (A B : List (Fin n × Bool)) (hk : k ≠ q) :
    ((α * item2 α c q A B) (FreeGroup.of k)) = α (FreeGroup.of k) := by
  classical
  by_cases hqc : q ≠ c
  · by_cases hE : ∃ Y : List (Fin n × Bool), (α (FreeGroup.of q)).toWord = Y ++ B
    · rw [item2_eq_rhoNeg α hqc A B hE]
      exact mul_rhoNeg_apply_other (α := α) hqc hk
    · by_cases hB : ∃ Y : List (Fin n × Bool),
          (α (FreeGroup.of q)).toWord = FreeGroup.invRev B ++ Y
      · rw [item2_eq_lam α hqc A B hE hB]
        exact mul_lam_apply_other (α := α) hqc hk
      · simp [item2, hqc, hE, hB]
  · rw [item2_eq_one α c q A B hqc]
    simp

/-! ### The item-2 pass over the affected coordinates

`item2Pass` is item 2 applied to a list `Q` of coordinates (all other than
the balanced coordinate `c`): the right-composition by `item2` at every
`q ∈ Q`.  Moves on distinct coordinates act on disjoint standard generators,
so the pass replaces each affected element's `B`-suffix / `B⁻¹`-prefix once
against the unchanged balanced element.  Core facts: the pass is a closure
element (`item2Pass_mem_closure`), fixes every coordinate not in `Q`
(`item2Pass_fix` — in particular the balanced coordinate, when `c ∉ Q`,
keeps its word `A ++ B`), and the elementary move fixes `a_k` for `k ≠ q`
(`item2_fix_generator`).
-/


/-- The **item-2 pass** over the coordinates `Q`: right composition by the
item-2 transform at every `q ∈ Q` (each move computed against the original
images).  Moves on distinct coordinates act on disjoint standard generators,
so the pass replaces each affected element's `B`-suffix / `B⁻¹`-prefix once,
against the unchanged balanced element at `c`. -/
noncomputable def item2Pass {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool)) (Q : List (Fin n)) : MulAut (FreeGroup (Fin n)) :=
  List.prod (Q.map (fun q : Fin n => item2 α c q A B))

/-- The item-2 transform at `q` fixes the generator `a_k` for `k ≠ q`. -/
theorem item2_fix_generator {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c q k : Fin n)
    (A B : List (Fin n × Bool)) (hk : k ≠ q) :
    (item2 α c q A B) (FreeGroup.of k) = FreeGroup.of k := by
  classical
  by_cases hqc : q ≠ c
  · by_cases hE : ∃ Y : List (Fin n × Bool), (α (FreeGroup.of q)).toWord = Y ++ B
    · rw [item2_eq_rhoNeg α hqc A B hE]
      exact rhoNeg_apply_other hqc hk
    · by_cases hB : ∃ Y : List (Fin n × Bool),
          (α (FreeGroup.of q)).toWord = FreeGroup.invRev B ++ Y
      · rw [item2_eq_lam α hqc A B hE hB]
        exact lam_apply_other hqc hk
      · simp [item2, hqc, hE, hB]
  · rw [item2_eq_one α c q A B hqc]
    simp

-- If every automorphism in the list fixes the generator `a_k`, so does
-- their product.
theorem prod_fix_generator {n : ℕ} (L : List (MulAut (FreeGroup (Fin n)))) (k : Fin n)
    (hfix : ∀ σ ∈ L, σ (FreeGroup.of k) = FreeGroup.of k) :
    (List.prod L) (FreeGroup.of k) = FreeGroup.of k := by
  induction L with
  | nil => simp
  | cons σ t ih =>
      rw [List.prod_cons]
      change σ ((List.prod t) (FreeGroup.of k)) = FreeGroup.of k
      rw [ih (by
        intro τ hτ
        exact hfix τ (List.mem_cons.mpr (Or.inr hτ)))]
      exact hfix σ (by simp)

-- **The pass fixes non-affected coordinates.**  If `k` is not among the
-- coordinates of `Q`, its image is unchanged by the item-2 pass (in
-- particular the balanced coordinate `c ∉ Q` keeps its word `A ++ B`).
theorem item2Pass_fix {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool)) (Q : List (Fin n)) {k : Fin n} (hk : k ∉ Q) :
    (α * item2Pass α c A B Q) (FreeGroup.of k) = α (FreeGroup.of k) := by
  have hfix : ∀ σ ∈ Q.map (fun q : Fin n => item2 α c q A B),
      σ (FreeGroup.of k) = FreeGroup.of k := by
    intro σ hσ
    rcases List.mem_map.mp hσ with ⟨q, hq, rfl⟩
    exact item2_fix_generator α c q k A B (by
      intro hkq
      exact hk (by simpa [hkq] using hq))
  have hpf := prod_fix_generator (L := Q.map (fun q : Fin n => item2 α c q A B)) k hfix
  unfold item2Pass
  change α ((List.prod (Q.map (fun q : Fin n => item2 α c q A B))) (FreeGroup.of k)) =
    α (FreeGroup.of k)
  rw [hpf]

/-- The pass is a closure element. -/
theorem item2Pass_mem_closure {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool)) (Q : List (Fin n)) :
    item2Pass α c A B Q ∈ AutClosure n := by
  unfold item2Pass
  induction Q with
  | nil => simp
  | cons q t ih =>
      rw [List.map_cons, List.prod_cons]
      exact (AutClosure n).mul_mem (item2_mem_closure α c q A B) ih


end Submission.Nielsen
