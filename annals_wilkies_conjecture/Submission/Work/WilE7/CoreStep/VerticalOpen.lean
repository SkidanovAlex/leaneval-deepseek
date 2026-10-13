/-
  S52 / `CoreLT_succ`: **a REFUTATION record** and two glue lemmas.

  ## The refutation (do not re-try)

  `NOTES_S52_vertical_row_status.md` records the analysis.  The tempting claim

  > if `C` is preconnected, `f : C → ℝ` continuous with `|f x| ≤ 1`, and `A ⊆ cyl C` is open in
  > `cyl C`, then `gr C f ⊆ A ∨ Disjoint (gr C f) A`

  is **FALSE**.  Counterexample: `p = 1`, `C = (-2,2)`, `f ≡ 0`,
  `A = {y : Fin 2 → ℝ | y 1 < -y 0} ∩ cyl C`.  Then `A` is open in `cyl C` (its complement in
  `cyl C` is closed), `|f| ≤ 1`, and `gr C f ∩ A = {x ∈ C | x < 0}` is neither empty nor all of
  `gr C f`: the graph meets `fr A` at `x = 0`, enters `A` for `x < 0`, and is outside `closure A`
  for `x > 0`.

  The faulty argument that suggested the claim was: `E := {x | (x, f x) ∈ fr A}` is clopen in `C`.
  `E` **is** closed (`fr A` is closed, `A` being open), but it is **not** open in general: the
  argument that `Eᶜ` is open (if `(x,fx) ∈ A` then a neighbourhood is in `A` by openness; if
  `(x,fx) ∉ closure A` then a neighbourhood misses `closure A`) proves exactly that `E` is closed.
  So the dichotomy `E = ∅ ∨ E = C` does **not** follow, and the hypothesis `hcl` of
  `Work.WilE7.CoreStep.gr_subset_or_disjoint_of_open_of_closed` (S51's "node A") is genuinely needed.

  Consequently the vertical row of `CoreLT_succ` still needs the input that no level graph crosses
  `fr A`; the notes analyse the two candidate routes (the pair-set / level-pair-set route of
  S51 §8, and the "sections of the fibre cut"/index-constancy route of S47 §11).

  ## The glue lemmas

  `compat_of_iUnion` and `compat_of_iUnion_list` are the (trivial but load-bearing) transfers used
  by the assembly: compatibility of a set with each member of a covering family gives compatibility
  with the union.  It is what lets a fibre cut replace a set `π(X)` by the union of the projections
  of its pieces (the reduction used in `NOTES_S52_vertical_row_status.md` §2).
-/
import Mathlib

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE7.CoreStep

/-- **Compatibility transfers to unions.**  If `S` is the union of a finite family `B` and `κ` is
contained in, or disjoint from, every `B i`, then the same holds with `S`. -/
theorem compat_of_iUnion {X ι : Type*} [Fintype ι] {B : ι → Set X} {S κ : Set X}
    (hS : S = ⋃ i, B i) (h : ∀ i, κ ⊆ B i ∨ Disjoint κ (B i)) :
    κ ⊆ S ∨ Disjoint κ S := by
  by_cases hsome : ∃ i, κ ⊆ B i
  · obtain ⟨i, hi⟩ := hsome
    left
    intro x hx
    rw [hS]
    exact Set.mem_iUnion.mpr ⟨i, hi hx⟩
  · right
    rw [Set.disjoint_left]
    intro x hx hxS
    rw [hS, Set.mem_iUnion] at hxS
    obtain ⟨i, hi⟩ := hxS
    by_cases hsub : κ ⊆ B i
    · exact hsome ⟨i, hsub⟩
    · exact Set.disjoint_left.mp ((h i).resolve_left hsub) hx hi

/-- **Compatibility transfers to unions, indexed by a list.**  (The form the assembly uses: the
pieces of a fibre cut are given as a list whose projections cover `π(X)`, so compatibility with the
set `π(X)` reduces to compatibility with each piece.) -/
theorem compat_of_iUnion_list {X : Type*} {l : List (Set X)} {S κ : Set X}
    (hS : S = ⋃ B ∈ l, B) (h : ∀ B ∈ l, κ ⊆ B ∨ Disjoint κ B) :
    κ ⊆ S ∨ Disjoint κ S := by
  by_cases hsome : ∃ B ∈ l, κ ⊆ B
  · obtain ⟨B, hB, hBκ⟩ := hsome
    left
    intro x hx
    rw [hS]
    exact Set.mem_iUnion₂.mpr ⟨B, hB, hBκ hx⟩
  · right
    rw [Set.disjoint_left]
    intro x hx hxS
    rw [hS, Set.mem_iUnion₂] at hxS
    obtain ⟨B, hB, hxB⟩ := hxS
    by_cases hsub : κ ⊆ B
    · exact hsome ⟨B, hB, hsub⟩
    · exact Set.disjoint_left.mp ((h B hB).resolve_left hsub) hx hxB

end Work.WilE7.CoreStep
