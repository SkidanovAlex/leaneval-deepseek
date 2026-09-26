import Submission.Work.ResidualBalanced
import Submission.Work.AggregateCoordinate
import Submission.Work.Item3.RowInvariant

open Submission.FreeGroupAut
open FreeGroup
set_option autoImplicit false

/-!
# Fall-II: excess-short covering junctions shorten strictly (Conjecture-K fragment)

**Conjecture K** (machine-validated, open as a full theorem) asserts that
every balanced (`FallTwoConfig`/`ExactlyHalfAbsorbed`) configuration of
half-length `k ≥ 2` admits a strict elementary move — equivalently no
`NoEndCancel` (residual) state has a `k ≥ 2` balanced element.  Its clean
provable fragment is the **excess-short junction**: in the balanced
configuration's image-aggregate witness (factor `es[j]` with word `A ++ B`,
`|A| = |B|`, left neighbour `es[j-1]` with word `X ++ invRev A`), if the
left-excess `X` is shorter than the half `A` (`|X| < |A|`), then the product
`es[j-1] · es[j]` is strictly shorter than `es[j]`
(`RowInvariant.excessLeftShortens`: the `A⁻¹`-suffix of `es[j-1]` cancels
the whole first half `A`).  Since `es[j-1] = ± w_p` and `es[j] = ± w_q`
(`p ≠ q`, `AggregateDispatch.strict_right_coord_ne`), the strict right
junction attaches an elementary Nielsen move (`StrictAttach.strict_attach_right`),
giving the `hF`-shape conclusion `∃ γ ∈ AutClosure n, N (α·γ) < N α`.

Machine (harness `/tmp/fg2`): of 46 machine-found `k ≥ 2` balanced rows in
random bases at n = 3, 44 have an aggregate witness with an excess-short side
(85 of 87 witness candidates); the theorem below closes those as single
strict moves.  The remaining rows (and the classical both-excess-long
witnesses, where the local covering triple alone does **not** force a move —
machine counterexample triples exist) need the global confined-aggregate
structure and remain open (recorded in `Item3/FallTwoRunNotes.md`).

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

open scoped BigOperators

/-- **Fall-II, excess-short left junction.**  In the image aggregate of the
standard generator `a_m`, an interior factor `j` has word `A ++ B` and the
left neighbour factor `j - 1` has word `X ++ invRev A` with the excess `X`
shorter than the half `A`.  Then the product `es[j-1]·es[j]` is strictly
shorter than `es[j]`, and attaching the elementary move (`± w_p` against
`± w_q` over the junction) yields a single Nielsen move strictly decreasing
`N`: `∃ γ ∈ AutClosure n, N (α·γ) < N α`. -/
theorem fallTwo_excess_left {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (m : Fin n) (j : ℕ) (hj : j < (imageAggregate α m).length)
    (hj0 : 0 < j) (A B X : List (Fin n × Bool))
    (hA : ((imageAggregate α m)[j]).toWord = A ++ B)
    (hX : ((imageAggregate α m)[j - 1]).toWord = X ++ FreeGroup.invRev A)
    (hshort : X.length < A.length) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  classical
  let es : List (FreeGroup (Fin n)) := imageAggregate α m
  have himg : ImageAggregate α es := by
    dsimp [es]
    exact imageAggregate_isImageAggregate α m
  have hred : SystemReduced es := by
    dsimp [es]
    exact SystemReduced_imageAggregate α m
  have hej : j < es.length := by
    dsimp [es]
    exact hj
  have hm : j - 1 < es.length := by omega
  have hjp : (j - 1) + 1 < es.length := by omega
  have hstrict : FreeGroup.norm (es[j - 1] * es[j]) < FreeGroup.norm (es[j]) := by
    simpa [es] using
      (excessLeftShortens A B X (es[j]) (by simpa [es] using hA) (es[j - 1])
        (by simpa [es] using hX) hshort)
  rcases aggregate_factor_coordinate α es himg hm with ⟨p, hp⟩
  rcases aggregate_factor_coordinate α es himg hej with ⟨q, hq⟩
  have hsub : (j - 1) + 1 = j := by omega
  have hq' : es[(j - 1) + 1] = α (FreeGroup.of q) ∨
      es[(j - 1) + 1] = (α (FreeGroup.of q))⁻¹ := by
    simpa [hsub] using hq
  have hstrict' : FreeGroup.norm (es[j - 1] * es[(j - 1) + 1]) <
      FreeGroup.norm (es[(j - 1) + 1]) := by
    simpa [hsub] using hstrict
  have hpq : p ≠ q := strict_right_coord_ne α es hred (j := j - 1) hm hjp hp hq' hstrict'
  exact strict_attach_right α es (j := j - 1) hm hjp hpq hp hq' hstrict' 

/-- **Fall-II, excess-short right junction (mirror).**  An interior factor
`j` has word `A ++ B` and the right neighbour factor `j + 1` has word
`invRev B ++ Z` with the excess `Z` shorter than the half `B`.  Then the
product `es[j]·es[j+1]` is strictly shorter than `es[j]`
(`RowInvariant.excessRightShortens`), and attaching the elementary move over
the junction yields a single Nielsen move strictly decreasing `N`. -/
theorem fallTwo_excess_right {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (m : Fin n) (j : ℕ) (hj : j < (imageAggregate α m).length)
    (hjk : j + 1 < (imageAggregate α m).length)
    (A B Z : List (Fin n × Bool))
    (hA : ((imageAggregate α m)[j]).toWord = A ++ B)
    (hZ : ((imageAggregate α m)[j + 1]).toWord = FreeGroup.invRev B ++ Z)
    (hshort : Z.length < B.length) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  classical
  let es : List (FreeGroup (Fin n)) := imageAggregate α m
  have himg : ImageAggregate α es := by
    dsimp [es]
    exact imageAggregate_isImageAggregate α m
  have hred : SystemReduced es := by
    dsimp [es]
    exact SystemReduced_imageAggregate α m
  have hej : j < es.length := by
    dsimp [es]
    exact hj
  have hejk : j + 1 < es.length := by
    dsimp [es]
    exact hjk
  have hj0 : 0 < j + 1 := by omega
  have hmj : (j + 1) - 1 < es.length := by omega
  have hstrict : FreeGroup.norm (es[j] * es[j + 1]) < FreeGroup.norm (es[j]) := by
    simpa [es] using
      (excessRightShortens A B Z (es[j]) (by simpa [es] using hA) (es[j + 1])
        (by simpa [es] using hZ) hshort)
  rcases aggregate_factor_coordinate α es himg hej with ⟨p, hp⟩
  rcases aggregate_factor_coordinate α es himg hejk with ⟨q, hq⟩
  have hp' : es[(j + 1) - 1] = α (FreeGroup.of p) ∨
      es[(j + 1) - 1] = (α (FreeGroup.of p))⁻¹ := by
    simpa using hp
  have hstrict' : FreeGroup.norm (es[(j + 1) - 1] * es[j + 1]) <
      FreeGroup.norm (es[(j + 1) - 1]) := by
    simpa using hstrict
  have hpq : p ≠ q := strict_left_coord_ne α es hred (j := j + 1) hejk hj0 hmj hp' hq hstrict'
  exact strict_attach_left α es (j := j + 1) hejk hmj hpq hp' hq hstrict'

/-- **The excess-left Fall-II configuration.**  A `FallTwoConfig`-shaped
witness (confined interior factor of the aggregate of `a_m` with word
`A ++ B`, `|A| = |B|`, left neighbour `X ++ invRev A`) whose *left excess* is
short: `|X| < |A|`. -/
def FallTwoExcessConfigLeft {n : ℕ} (α : MulAut (FreeGroup (Fin n))) : Prop :=
  ∃ (m : Fin n) (j : ℕ) (hj : j < (imageAggregate α m).length)
    (hj0 : 0 < j) (hj1 : j + 1 < (imageAggregate α m).length),
    Confined (aggregateWords (imageAggregate α m)) j ∧
    ∃ (A B X Z : List (Fin n × Bool)),
      ((imageAggregate α m)[j]).toWord = A ++ B ∧ A.length = B.length ∧
      ((imageAggregate α m)[j - 1]).toWord = X ++ FreeGroup.invRev A ∧
      X.length < A.length

/-- **The excess-right Fall-II configuration.**  Mirror of
`FallTwoExcessConfigLeft` with the *right* neighbour `invRev B ++ Z` and
`|Z| < |B|`. -/
def FallTwoExcessConfigRight {n : ℕ} (α : MulAut (FreeGroup (Fin n))) : Prop :=
  ∃ (m : Fin n) (j : ℕ) (hj : j < (imageAggregate α m).length)
    (hj0 : 0 < j) (hj1 : j + 1 < (imageAggregate α m).length),
    Confined (aggregateWords (imageAggregate α m)) j ∧
    ∃ (A B X Z : List (Fin n × Bool)),
      ((imageAggregate α m)[j]).toWord = A ++ B ∧ A.length = B.length ∧
      ((imageAggregate α m)[j + 1]).toWord = FreeGroup.invRev B ++ Z ∧
      Z.length < B.length

/-- **An excess-left Fall-II configuration admits a single strict move.**
`FallTwoExcessConfigLeft α` (balanced confined factor with a short left
excess) yields `∃ γ ∈ AutClosure n, N (α·γ) < N α` — the excess-short half
of Conjecture K at the `FallTwoConfig` level. -/
theorem fallTwoExcessConfigLeft_strict {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hF : FallTwoExcessConfigLeft α) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  rcases hF with ⟨m, j, hj, hj0, hj1, hconf, A, B, X, Z, hA, hAB, hX, hshort⟩
  exact fallTwo_excess_left α m j hj hj0 A B X hA hX hshort

/-- **An excess-right Fall-II configuration admits a single strict move.**
Mirror of `fallTwoExcessConfigLeft_strict`. -/
theorem fallTwoExcessConfigRight_strict {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hF : FallTwoExcessConfigRight α) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  rcases hF with ⟨m, j, hj, hj0, hj1, hconf, A, B, X, Z, hA, hAB, hZ, hshort⟩
  exact fallTwo_excess_right α m j hj hj1 A B Z hA hZ hshort

end Submission.Nielsen
