import Mathlib
import Submission.RealIntervalShape

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S216 — nested-chain unions: the real-coordinate limit step of the
interval side (module Submission/ChainUnionInterval.lean)

Every route to the interval-case gate (`TrisecantComponentIntervalSide`,
the S206 generic extraction `noncompact_connected_oneManifold_interval`)
ends with a coordinate-level limit: the exhaustion prefixes are
interval-charted (each `≃ₜ (0,1)`), and at the level of the real
coordinates their union — an increasing union of open preconnected real
sets — must be identified with an open connected subset of ℝ, hence
`≃ₜ (0,1)` (`RealIntervalShape.open_connected_ℝ_homeo_openUnit`).  This
module supplies that real-coordinate step in its cleanest form, purely
topologically (no problem-specific content), as a shared lemma the S206
assembly (or any exhaustion-to-interval argument) imports:

1. **`nested_chain_preconnected_iUnion`** (generic, any topological
   space): the union of a nested chain of nonempty preconnected sets
   (`U n ⊆ U (n+1)`) is preconnected — Mathlib's
   `IsPreconnected.iUnion_of_chain` with the consecutive overlaps
   `U n ∩ U (n+1) = U n` (nonempty by hypothesis);
2. **`nested_chain_connected_iUnion`** — the connected variant;
3. **`nested_open_preconnected_ℝ_union_open_preconnected`** — for
   nonempty open preconnected subsets of ℝ: the union is again open and
   preconnected;
4. **`nested_open_preconnected_ℝ_union_shape`** — the shape
   classification of that union (one of `Ioo a b`, `Ioi a`, `Iio a`,
   `univ`) via `RealIntervalShape.open_preconnected_nonempty_ℝ_shape`;
5. **`nested_open_preconnected_ℝ_union_homeo_openUnit`** — THE limit
   step: the union (as a subtype of ℝ) is homeomorphic to
   `OpenRealInterval 0 1` — any open connected subset of ℝ, including
   the whole line, is `≃ₜ (0,1)`
   (`RealIntervalShape.open_connected_ℝ_homeo_openUnit`);
6. **`not_isCompact_of_proper_nested_open_exhaustion`** and
   **`not_compactSpace_of_proper_nested_open_exhaustion`** — the
   properness marker (contrapositive of the S161 compactness marker
   `RealIntervalShape.exists_eq_univ_of_compact_nested_union`): a space
   exhausted by PROPER open sets nested increasing cannot be compact —
   the mechanism by which the interval side's non-compactness hypothesis
   keeps the arc-prefix exhaustion infinite/proper.

HOW THIS IS USED (S216 analysis, also recorded in ROADMAP): in the
exhaustion-to-interval assembly of the S206 route, a candidate "limit
coordinate" of a point of the non-compact component is a real value lying
in the union of the coordinate images of the prefixes; the subset of ℝ so
obtained is an increasing union of open preconnected sets and is
therefore an open connected subset of ℝ (this module), and the interval
chart of the whole space is read off by (5).  (The construction of the
limit coordinate itself — and the data guaranteeing its
well-definedness, continuity and bijectivity — is the remaining content
of the interval side; see the ROADMAP S216 entry for its precise
statement.)

Everything here is elementary and verified (no axioms, no `sorry`).
-/

/-- **The union of a nested chain of nonempty preconnected sets is
preconnected** (any topological space; `U n ⊆ U (n+1)` for all `n`). -/
theorem nested_chain_preconnected_iUnion {X : Type*} [TopologicalSpace X] {U : ℕ → Set X}
    (hpc : ∀ n, IsPreconnected (U n)) (hne : ∀ n, (U n).Nonempty)
    (hnest : ∀ n, U n ⊆ U (n + 1)) : IsPreconnected (⋃ n, U n) := by
  have K : ∀ n : ℕ, (U n ∩ U (Nat.succ n)).Nonempty := by
    intro n
    rw [show Nat.succ n = n + 1 by omega]
    rcases hne n with ⟨x, hx⟩
    exact ⟨x, hx, hnest n hx⟩
  simpa [Nat.succ_eq_add_one] using (IsPreconnected.iUnion_of_chain (s := U) hpc K)

/-- **The union of a nested chain of nonempty connected sets is
connected.** -/
theorem nested_chain_connected_iUnion {X : Type*} [TopologicalSpace X] {U : ℕ → Set X}
    (hconn : ∀ n, IsConnected (U n)) (hnest : ∀ n, U n ⊆ U (n + 1)) :
    IsConnected (⋃ n, U n) := by
  have hne : ∀ n, (U n).Nonempty := fun n => (hconn n).1
  exact ⟨(by rcases hne 0 with ⟨x, hx⟩; exact ⟨x, Set.mem_iUnion.mpr ⟨0, hx⟩⟩),
    nested_chain_preconnected_iUnion (fun n => (hconn n).2) hne hnest⟩

/-- **The union of a nested chain of nonempty open preconnected subsets of
ℝ is again open and preconnected.** -/
theorem nested_open_preconnected_ℝ_union_open_preconnected {U : ℕ → Set ℝ}
    (hopen : ∀ n, IsOpen (U n)) (hpc : ∀ n, IsPreconnected (U n))
    (hne0 : (U 0).Nonempty) (hnest : ∀ n, U n ⊆ U (n + 1)) :
    IsOpen (⋃ n, U n) ∧ IsPreconnected (⋃ n, U n) := by
  have hne : ∀ n, (U n).Nonempty := by
    intro n
    induction n with
    | zero => exact hne0
    | succ n ih =>
        rcases ih with ⟨x, hx⟩
        exact ⟨x, hnest n hx⟩
  exact ⟨isOpen_iUnion hopen, nested_chain_preconnected_iUnion hpc hne hnest⟩

/-- **Shape classification of the union**: a nested chain of nonempty open
preconnected subsets of ℝ has union of one of the canonical shapes
`(a,b)`, `(a,∞)`, `(−∞,b)`, or all of ℝ. -/
theorem nested_open_preconnected_ℝ_union_shape {U : ℕ → Set ℝ}
    (hopen : ∀ n, IsOpen (U n)) (hpc : ∀ n, IsPreconnected (U n))
    (hne0 : (U 0).Nonempty) (hnest : ∀ n, U n ⊆ U (n + 1)) :
    (∃ a b : ℝ, (⋃ n, U n) = Ioo a b) ∨ (∃ a : ℝ, (⋃ n, U n) = Ioi a) ∨
      (∃ a : ℝ, (⋃ n, U n) = Iio a) ∨ (⋃ n, U n) = univ := by
  have hU := nested_open_preconnected_ℝ_union_open_preconnected hopen hpc hne0 hnest
  have hne : (⋃ n, U n).Nonempty := by
    rcases hne0 with ⟨x, hx⟩
    exact ⟨x, Set.mem_iUnion.mpr ⟨0, hx⟩⟩
  exact open_preconnected_nonempty_ℝ_shape hU.1 hU.2 hne

/-- **The real-coordinate limit step**: the union of a nested chain of
nonempty open preconnected subsets of ℝ is homeomorphic to the open unit
interval `(0,1)` (every nonempty open connected subset of ℝ is, including
all of ℝ). -/
theorem nested_open_preconnected_ℝ_union_homeo_openUnit {U : ℕ → Set ℝ}
    (hopen : ∀ n, IsOpen (U n)) (hpc : ∀ n, IsPreconnected (U n))
    (hne0 : (U 0).Nonempty) (hnest : ∀ n, U n ⊆ U (n + 1)) :
    Nonempty (({x : ℝ // x ∈ ⋃ n, U n}) ≃ₜ OpenRealInterval 0 1) := by
  have hU := nested_open_preconnected_ℝ_union_open_preconnected hopen hpc hne0 hnest
  have hne : (⋃ n, U n).Nonempty := by
    rcases hne0 with ⟨x, hx⟩
    exact ⟨x, Set.mem_iUnion.mpr ⟨0, hx⟩⟩
  exact open_connected_ℝ_homeo_openUnit hU.1 hU.2 hne

/-- **Proper-nested exhaustion forces non-compactness (set level)**:
if `X` is exhausted by PROPER open sets `U n` nested increasing
(`U n ≠ univ` for every `n`, `⋃ n, U n = univ`), then `univ` is not
compact — the contrapositive of
`RealIntervalShape.exists_eq_univ_of_compact_nested_union` (the S161
compactness marker).  This is how the non-compactness hypothesis of the
interval side keeps the arc-prefix exhaustion proper: a nested open
exhaustion of a compact ambient must absorb the ambient at some finite
stage. -/
theorem not_isCompact_of_proper_nested_open_exhaustion {X : Type*} [TopologicalSpace X]
    [Nonempty X] {U : ℕ → Set X} (hopen : ∀ n, IsOpen (U n))
    (hnest : ∀ n, U n ⊆ U (n + 1)) (hcover : (⋃ n, U n) = univ)
    (hproper : ∀ n, U n ≠ univ) : ¬ IsCompact (univ : Set X) := by
  intro hC
  have hneX : (univ : Set X).Nonempty := ⟨Classical.choice ‹Nonempty X›, trivial⟩
  rcases exists_eq_univ_of_compact_nested_union hC hneX hopen hnest hcover with ⟨k, hk⟩
  exact hproper k hk

/-- **Proper-nested exhaustion forces non-compactness (type level)**:
a space exhausted by proper open sets nested increasing is not
`CompactSpace`. -/
theorem not_compactSpace_of_proper_nested_open_exhaustion {X : Type*} [TopologicalSpace X]
    [Nonempty X] {U : ℕ → Set X} (hopen : ∀ n, IsOpen (U n))
    (hnest : ∀ n, U n ⊆ U (n + 1)) (hcover : (⋃ n, U n) = univ)
    (hproper : ∀ n, U n ≠ univ) : ¬ CompactSpace X := by
  intro hC
  have hCset : IsCompact (univ : Set X) := hC.isCompact_univ
  exact not_isCompact_of_proper_nested_open_exhaustion hopen hnest hcover hproper hCset

end LeanEval.KnotTheory.Quadrisecant

