import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore

/-!
# Conversion between `IsSmall` (Set-valued cover, ChallengeDeps) and `Sel.pSmall` (Finset cover).

PROVE the two final declarations below (no unfinished proofs); add helpers as needed.

WARNING (very important): sums over a `Set s` elaborate as `s.toFinset.sum` and the
`Fintype ↑s` / decidability instances are NON-CANONICAL (`Subtype.fintype` vs
`FinsetCoe.fintype`, `propDecidable` vs `decidableMem'`), so expressions that look
identical may NOT be definitionally equal and `rw`/`change` may fail mysteriously.
Workarounds that work:
  - rewrite with lemmas whose LEFT side is the whole `(∑ x ∈ s, f x)` binder form
    (e.g. `sum_set_univ` below), then continue;
  - avoid re-elaborating `(s : Set _).toFinset` in separate `have`s;
  - if stuck, add  `attribute [-instance] FinsetCoe.fintype
attribute [-instance] Finset.decidableMem'` (as a command at top
    of file, AFTER imports) and similar for any other offending instance; this
    affects only later elaborations in this file and files imported after it.
The declarations' statements themselves are FIXED below (do not change them).
-/

attribute [-instance] FinsetCoe.fintype
attribute [-instance] Finset.decidableMem'

set_option autoImplicit false
set_option maxHeartbeats 600000
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace PConv

open Frame
open Sel

variable {X : Type*} [Fintype X]

/-- membership in the bounded union of superset-families -/
lemma mem_bUnion_set (𝓖s : Set (Set X)) (S : Set X) :
    S ∈ (⋃ s ∈ 𝓖s, {t : Set X | s ⊆ t}) ↔ ∃ s ∈ 𝓖s, s ⊆ S := by
  classical
  simpa using (Set.mem_iUnion₂ (x := S) (s := fun (s : Set X) (_ : s ∈ 𝓖s) => {t : Set X | s ⊆ t}))

/-- a set-sum equals the sum over the universal filter -/
lemma sum_set_univ (𝓖s : Set (Set X)) (f : Set X → ℝ) :
    (∑ s ∈ 𝓖s, f s) = ∑ s : Set X, if s ∈ 𝓖s then f s else 0 := by
  classical
  have hs : 𝓖s.toFinset = Finset.univ.filter (fun s : Set X => s ∈ 𝓖s) := by
    ext s
    simp [Set.mem_toFinset]
  rw [hs]
  rw [Finset.sum_filter]

/-- sum over the elements of a Finset (as a Set) equals the Finset sum -/
lemma sum_set_finset (𝓖 : Finset (Set X)) (f : Set X → ℝ) :
    (∑ s ∈ (𝓖 : Set (Set X)), f s) = ∑ s ∈ 𝓖, f s := by
  classical
  let A : Finset (Set X) := (𝓖 : Set (Set X)).toFinset
  have hAB : A = 𝓖 := by
    ext s
    constructor
    · intro hs
      have h := (Set.mem_toFinset).1 (by simpa [A] using hs : s ∈ (𝓖 : Set (Set X)).toFinset)
      simpa using h
    · intro hs
      have hmem : s ∈ (𝓖 : Set (Set X)) := by simpa using hs
      exact (Set.mem_toFinset).2 hmem
  calc
    (∑ s ∈ (𝓖 : Set (Set X)), f s) = A.sum f := by rfl
    _ = (∑ s ∈ 𝓖, f s) := by rw [hAB]

/-- Finset-cover smallness implies Set-cover smallness -/
lemma pSmall_imp_IsSmall (p : I) (𝓕 : Set (Set X)) : pSmall (p : ℝ) 𝓕 → IsSmall p 𝓕 := by
  classical
  rintro ⟨𝓖, hcov, hcost⟩
  refine ⟨(𝓖 : Set (Set X)), ?_, ?_⟩
  · intro S hS
    rcases hcov S hS with ⟨g, hg, hsub⟩
    exact (mem_bUnion_set (𝓖 : Set (Set X)) S).2 ⟨g, (by simpa using hg), hsub⟩
  · let A : Finset (Set X) := (𝓖 : Set (Set X)).toFinset
    have hAB : A = 𝓖 := by
      ext s
      constructor
      · intro hs
        have h := (Set.mem_toFinset).1 (by simpa [A] using hs : s ∈ (𝓖 : Set (Set X)).toFinset)
        simpa using h
      · intro hs
        have hmem : s ∈ (𝓖 : Set (Set X)) := by simpa using hs
        exact (Set.mem_toFinset).2 hmem
    calc
      (∑ s ∈ (𝓖 : Set (Set X)), (p : ℝ) ^ s.ncard) = A.sum (fun s : Set X => (p : ℝ) ^ s.ncard) := by rfl
      _ = totalCost (p : ℝ) 𝓖 := by simp [hAB, totalCost]
      _ ≤ (2 : ℝ)⁻¹ := hcost

/-- Set-cover smallness implies Finset-cover smallness -/
lemma IsSmall_imp_pSmall (p : I) (𝓕 : Set (Set X)) : IsSmall p 𝓕 → pSmall (p : ℝ) 𝓕 := by
  classical
  rintro ⟨𝓖s, hcov, hcost⟩
  refine ⟨𝓖s.toFinset, ?_, ?_⟩
  · intro S hS
    rcases (mem_bUnion_set 𝓖s S).1 (hcov hS) with ⟨g, hg, hsub⟩
    exact ⟨g, (Set.mem_toFinset).2 hg, hsub⟩
  · simpa [totalCost] using hcost

attribute [instance] FinsetCoe.fintype
attribute [instance] Finset.decidableMem'

end PConv
end Submission
