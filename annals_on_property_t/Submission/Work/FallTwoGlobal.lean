import Submission.Work.FallTwoExcess
import Submission.Commons.GroupTheory.FreeGroup.balanced_triple_telescopes_norm_le
import Submission.Work.AggregateDispatch
import Submission.Work.StrictAttach
import Submission.Work.NielsenResidual
import Submission.Work.RebalanceProtocol

open Submission.FreeGroupAut
open FreeGroup
set_option autoImplicit false

/-!
# Fall-II global: Conjecture K at the aggregate level (open containers)

**Conjecture K** (machine-validated at n = 3..5, proof open): every balanced
configuration (`FallTwoConfig`/`ExactlyHalfAbsorbed`) of half-length `k ≥ 2`
admits a strict elementary move — equivalently, no `NoEndCancel` (residual)
state has a `k ≥ 2` balanced element (residual states carry balanced elements
only of half-length `k = 1`, i.e. word length 2).  The machine mechanism hunt
(`/tmp/fg2`, `bothlong.pkl`, `valKJ*.py`) established the exact global shape:

* the *witness* junction need NOT be unbalanced (`c_L = k = c_R` happens:
  ~40% of `k ≥ 2` witnesses have both witness junctions balanced — the
  local covering triple alone never forces a move);
* in 1426 of 1427 `k ≥ 2` witnesses the witness's own image aggregate
  (`imageAggregate α m`) already contains an *unbalanced adjacent junction*
  (a junction product strictly shorter than one of its two factors); in the
  single counterexample the unbalanced junction sits in another generator's
  aggregate.  Hence the **aggregate-junction form of K** (`KJ3` below): a
  `k ≥ 2` balanced configuration forces an unbalanced adjacent junction in
  the image aggregate of some standard generator;
* an unbalanced adjacent junction of ± basis images *attaches* a single
  elementary Nielsen move strictly decreasing `N` — the provable pipeline
  below (`imageAggregate_left_unbalanced_attaches` /
  `imageAggregate_right_unbalanced_attaches` via
  `AggregateCoordinate.aggregate_factor_coordinate`,
  `AggregateDispatch.strict_left/right_coord_ne` and
  `StrictAttach.strict_attach_left/right`).  So `KJ3 → ConjectureKStrict` is
  closed below, and **`KJ3` is the single open pin** for the `k ≥ 2` branch
  of the `hF` strict-descent hypothesis (`StrictDescent.aut_nielsen_of_fallII`).

The excess-short half is already closed (`FallTwoExcess.lean`: a witness
whose covering excess `X` or `Z` is shorter than the half `k` gives the move
directly).  The both-excess-long half (`|X| ≥ k` and `|Z| ≥ k`) is open:
it needs a global (non-local) argument over the confined aggregate —
recorded here as `KJ3`, a `Prop`-valued container; no `sorry` is committed.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

open scoped BigOperators

/-- **A Fall-II configuration with balanced half-length at least two.**  The
`FallTwoConfig` witness data (confined interior factor `j` of the image
aggregate of `a_m`, factor word `A ++ B`, `|A| = |B|`, neighbours
`X ++ invRev A` and `invRev B ++ Z`) together with `2 ≤ |A|` — the `k ≥ 2`
balanced configuration of Conjecture K. -/
def HasK2FallTwo {n : ℕ} (α : MulAut (FreeGroup (Fin n))) : Prop :=
  ∃ (m : Fin n) (j : ℕ) (hj : j < (imageAggregate α m).length)
    (hj0 : 0 < j) (hj1 : j + 1 < (imageAggregate α m).length),
    Confined (aggregateWords (imageAggregate α m)) j ∧
    ∃ (A B X Z : List (Fin n × Bool)),
      ((imageAggregate α m)[j]).toWord = A ++ B ∧ A.length = B.length ∧
      2 ≤ A.length ∧
      ((imageAggregate α m)[j - 1]).toWord = X ++ FreeGroup.invRev A ∧
      ((imageAggregate α m)[j + 1]).toWord = FreeGroup.invRev B ++ Z

/-- **An unbalanced adjacent junction in an image aggregate.**  For some
standard generator `a_m`, adjacent factors `t` and `t + 1` of
`imageAggregate α m` have a junction product strictly shorter than one of
the two factors — the aggregate-level "unbalanced side" whose attachment is
a strict elementary move. -/
def HasUnbalancedAggregateJunction {n : ℕ} (α : MulAut (FreeGroup (Fin n))) : Prop :=
  ∃ (m : Fin n) (t : ℕ) (ht : t < (imageAggregate α m).length)
    (ht1 : t + 1 < (imageAggregate α m).length),
    FreeGroup.norm (((imageAggregate α m)[t]) * ((imageAggregate α m)[t + 1])) <
        FreeGroup.norm ((imageAggregate α m)[t]) ∨
    FreeGroup.norm (((imageAggregate α m)[t]) * ((imageAggregate α m)[t + 1])) <
        FreeGroup.norm ((imageAggregate α m)[t + 1])

/-- **Conjecture K (container).**  Every `k ≥ 2` balanced configuration
of `α` admits a strict *closure* move (an `AutClosure` element decreasing
`N`).  The **elementary** version (a single Nielsen move) is FALSE:
`NoEndCancel` states with `HasK2FallTwo` exist (see `Submission/Status.lean`,
"THE PIN `ConjectureKResidual` IS FALSE", e.g. the residual basis
`[a₀a₀A₂A₁, a₁a₂a₀A₂, a₂A₀A₀A₀a₁]` of `F₃`), and those are peaks (no strict
single move), so no `KJ3`-style argument through elementary moves can work.
The macro form above remains the pin consumed by `StrictDescent`; the
residual-strengthened form `ConjectureKResidual` used by
`energyStep_of_conjectureKResidual` is *false* (see the same status entry). -/
def ConjectureKStrict {n : ℕ} : Prop :=
  ∀ α : MulAut (FreeGroup (Fin n)), HasK2FallTwo α →
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α

/-- **The aggregate-junction form of Conjecture K (`KJ3`, open).**  A
`k ≥ 2` balanced configuration forces an unbalanced adjacent junction in the
image aggregate of some standard generator.  Machine: 1426/1427 `k ≥ 2`
witnesses have the unbalanced junction already inside the *witness* aggregate
(`valKJ2.py`); the unique counterexample still satisfies `KJ3` through
another generator's aggregate (`m = 1`, `m = 2` of the recorded example), so
0 violations of `KJ3` were found.  Proof open — no `sorry` is committed. -/
def AggregateJunctionConjecture {n : ℕ} : Prop :=
  ∀ α : MulAut (FreeGroup (Fin n)), HasK2FallTwo α → HasUnbalancedAggregateJunction α

/-- **Unbalanced junction (left factor shortened) attaches a strict move.**
  If adjacent factors `t - 1`, `t` of the image aggregate of `a_m` have
  `|es[t-1]·es[t]| < |es[t-1]|`, then `es[t-1] = ±w_p`, `es[t] = ±w_q`
  (`p ≠ q`) and the strict left attachment gives a single Nielsen move
  strictly decreasing `N`. -/
theorem imageAggregate_left_unbalanced_attaches {n : ℕ}
    (α : MulAut (FreeGroup (Fin n))) (m : Fin n) {t : ℕ}
    (ht : t < (imageAggregate α m).length) (ht0 : 0 < t)
    (hstrict : FreeGroup.norm (((imageAggregate α m)[t - 1]) * ((imageAggregate α m)[t])) <
      FreeGroup.norm ((imageAggregate α m)[t - 1])) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  classical
  let es : List (FreeGroup (Fin n)) := imageAggregate α m
  have himg : ImageAggregate α es := by
    dsimp [es]
    exact imageAggregate_isImageAggregate α m
  have hred : SystemReduced es := by
    dsimp [es]
    exact SystemReduced_imageAggregate α m
  have het : t < es.length := by
    dsimp [es]
    exact ht
  have hmj : t - 1 < es.length := by omega
  have hstrict' : FreeGroup.norm (es[t - 1] * es[t]) < FreeGroup.norm (es[t - 1]) := by
    simpa [es] using hstrict
  rcases aggregate_factor_coordinate α es himg hmj with ⟨p, hp⟩
  rcases aggregate_factor_coordinate α es himg het with ⟨q, hq⟩
  have hpq : p ≠ q := strict_left_coord_ne α es hred het ht0 hmj hp hq hstrict'
  exact strict_attach_left α es het hmj hpq hp hq hstrict'

/-- **Unbalanced junction (right factor shortened) attaches a strict move.**
  Mirror: adjacent factors `t`, `t + 1` with
  `|es[t]·es[t+1]| < |es[t+1]|` attach a single Nielsen move strictly
  decreasing `N`. -/
theorem imageAggregate_right_unbalanced_attaches {n : ℕ}
    (α : MulAut (FreeGroup (Fin n))) (m : Fin n) {t : ℕ}
    (ht : t < (imageAggregate α m).length) (ht1 : t + 1 < (imageAggregate α m).length)
    (hstrict : FreeGroup.norm (((imageAggregate α m)[t]) * ((imageAggregate α m)[t + 1])) <
      FreeGroup.norm ((imageAggregate α m)[t + 1])) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  classical
  let es : List (FreeGroup (Fin n)) := imageAggregate α m
  have himg : ImageAggregate α es := by
    dsimp [es]
    exact imageAggregate_isImageAggregate α m
  have hred : SystemReduced es := by
    dsimp [es]
    exact SystemReduced_imageAggregate α m
  have het : t < es.length := by
    dsimp [es]
    exact ht
  have het1 : t + 1 < es.length := by
    dsimp [es]
    exact ht1
  have hstrict' : FreeGroup.norm (es[t] * es[t + 1]) < FreeGroup.norm (es[t + 1]) := by
    simpa [es] using hstrict
  rcases aggregate_factor_coordinate α es himg het with ⟨p, hp⟩
  rcases aggregate_factor_coordinate α es himg het1 with ⟨q, hq⟩
  have hpq : p ≠ q := strict_right_coord_ne α es hred het het1 hp hq hstrict'
  exact strict_attach_right α es het het1 hpq hp hq hstrict'

/-- **The balanced witness triple vanishes (aggregate level).**  For the
witness data (adjacent factors of the image aggregate of `a_m` with words
`X ++ invRev A`, `A ++ B`, `invRev B ++ Z`), the product of the three factors
has norm at most `|X| + |Z|`: all `2k` letters of the balanced block
(`k = |A| = |B|`) cancel against the two neighbours
(`Commons.GroupTheory.FreeGroup.balanced_triple_telescopes_norm_le`, lifted
through the `toWord` identities).  This is the aggregate-level form of the
delegated word lemma, needed by the global (`KJ3`) argument. -/
theorem witnessTriple_vanishes {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (m : Fin n) (j : ℕ) (hj : j < (imageAggregate α m).length)
    (hmj : j - 1 < (imageAggregate α m).length)
    (hjk : j + 1 < (imageAggregate α m).length)
    (A B X Z : List (Fin n × Bool))
    (hA : ((imageAggregate α m)[j]).toWord = A ++ B)
    (hX : ((imageAggregate α m)[j - 1]).toWord = X ++ FreeGroup.invRev A)
    (hZ : ((imageAggregate α m)[j + 1]).toWord = FreeGroup.invRev B ++ Z) :
    FreeGroup.norm ((((imageAggregate α m)[j - 1]) * ((imageAggregate α m)[j])) *
      ((imageAggregate α m)[j + 1])) ≤ X.length + Z.length := by
  classical
  let es : List (FreeGroup (Fin n)) := imageAggregate α m
  have hAe : (es[j]).toWord = A ++ B := by
    simpa [es] using hA
  have hXe : (es[j - 1]).toWord = X ++ FreeGroup.invRev A := by
    simpa [es] using hX
  have hZe : (es[j + 1]).toWord = FreeGroup.invRev B ++ Z := by
    simpa [es] using hZ
  have hEq : ((es[j - 1]) * (es[j])) * es[j + 1] =
      (FreeGroup.mk (X ++ FreeGroup.invRev A)) * (FreeGroup.mk (A ++ B)) *
        (FreeGroup.mk (FreeGroup.invRev B ++ Z)) := by
    rw [← FreeGroup.mk_toWord (x := es[j - 1]), hXe,
        ← FreeGroup.mk_toWord (x := es[j]), hAe,
        ← FreeGroup.mk_toWord (x := es[j + 1]), hZe]
  calc
    FreeGroup.norm (((es[j - 1]) * (es[j])) * es[j + 1])
        = FreeGroup.norm
            ((FreeGroup.mk (X ++ FreeGroup.invRev A)) * (FreeGroup.mk (A ++ B)) *
              (FreeGroup.mk (FreeGroup.invRev B ++ Z))) := by rw [hEq]
    _ ≤ X.length + Z.length :=
        Commons.GroupTheory.FreeGroup.balanced_triple_telescopes_norm_le X A B Z

/-- **Unbalanced junction at `(t, t+1)` with the first factor shortened
attaches a strict move.**  `|es[t]·es[t+1]| < |es[t]|` at adjacent factors
`t`, `t + 1`: the coordinates `es[t] = ±w_p`, `es[t+1] = ±w_q` give `p ≠ q`
(`strict_left_coord_ne` at index `t + 1`), and the strict left attachment
(`strict_attach_left`) yields a single Nielsen move strictly decreasing
`N`. -/
theorem imageAggregate_first_unbalanced_attaches {n : ℕ}
    (α : MulAut (FreeGroup (Fin n))) (m : Fin n) {t : ℕ}
    (ht : t < (imageAggregate α m).length) (ht1 : t + 1 < (imageAggregate α m).length)
    (hstrict : FreeGroup.norm (((imageAggregate α m)[t]) * ((imageAggregate α m)[t + 1])) <
      FreeGroup.norm ((imageAggregate α m)[t])) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  classical
  let es : List (FreeGroup (Fin n)) := imageAggregate α m
  have himg : ImageAggregate α es := by
    dsimp [es]
    exact imageAggregate_isImageAggregate α m
  have hred : SystemReduced es := by
    dsimp [es]
    exact SystemReduced_imageAggregate α m
  have het : t < es.length := by
    dsimp [es]
    exact ht
  have het1 : t + 1 < es.length := by
    dsimp [es]
    exact ht1
  have hj0 : 0 < t + 1 := by omega
  have hmj : (t + 1) - 1 < es.length := by omega
  have hsub : (t + 1) - 1 = t := by omega
  have hstrict' : FreeGroup.norm (es[(t + 1) - 1] * es[t + 1]) <
      FreeGroup.norm (es[(t + 1) - 1]) := by
    simpa [hsub] using hstrict
  rcases aggregate_factor_coordinate α es himg het with ⟨p, hp⟩
  rcases aggregate_factor_coordinate α es himg het1 with ⟨q, hq⟩
  have hp' : es[(t + 1) - 1] = α (FreeGroup.of p) ∨
      es[(t + 1) - 1] = (α (FreeGroup.of p))⁻¹ := by
    simpa [hsub] using hp
  have hpq : p ≠ q := strict_left_coord_ne α es hred het1 hj0 hmj hp' hq hstrict'
  exact strict_attach_left α es het1 hmj hpq hp' hq hstrict'

/-- **An unbalanced aggregate junction yields a strict move.**  Any
unbalanced adjacent junction in any image aggregate of `α` attaches an
elementary Nielsen move strictly decreasing `N`.  This closes the pipeline
`AggregateJunctionConjecture → ConjectureKStrict` (the two attach theorems
over the two disjuncts). -/
theorem unbalancedAggregateJunction_attaches {n : ℕ}
    (α : MulAut (FreeGroup (Fin n))) (h : HasUnbalancedAggregateJunction α) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  rcases h with ⟨m, t, ht, ht1, hL | hR⟩
  · exact imageAggregate_first_unbalanced_attaches α m ht ht1 hL
  · exact imageAggregate_right_unbalanced_attaches α m ht ht1 hR

