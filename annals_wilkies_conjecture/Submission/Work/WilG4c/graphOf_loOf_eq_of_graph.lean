/-
  WilG4c — `graphOf_loOf_eq_of_graph`.

  Let `Z ⊆ ℝ^{m+1}` be the graph of a function `f` over a base `C ⊆ ℝ^m`, i.e.

      z ∈ Z ↔ Fin.init z ∈ C ∧ z (Fin.last m) = f (Fin.init z).

  Then every fibre of `Z` over a parameter `l` is either the singleton `{f l}` (when `l ∈ C`) or
  empty.  Consequently the pointwise infimum `loOf m Z l` is `f l` when `l ∈ C` and the fallback
  `0` otherwise, and the first-order set `A_lo m Z` (the graph of that infimum, built in
  `FiberEndsDefs`) is exactly the graph of `loOf m Z`.  The second part of the statement records
  that every point of `Z` lies on that graph.

  This is the graph-case companion of `FiberEndsLo.graphOf_loOf_eq`, which needs an interval
  hypothesis on the fibres instead of the graph structure.
-/
import Mathlib
import Submission.Work.WilG4c.FiberEndsDefs
import Submission.Work.WilG4c.FiberEndsLo

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-! ## 1. The fibres of a graph are singletons or empty -/

theorem fibre_eq_of_graph {m : ℕ} {Z : Set (Fin (m + 1) → ℝ)}
    {C : Set (Fin m → ℝ)} {f : (Fin m → ℝ) → ℝ}
    (hmem : ∀ z : Fin (m + 1) → ℝ,
      z ∈ Z ↔ Fin.init z ∈ C ∧ z (Fin.last m) = f (Fin.init z)) (l : Fin m → ℝ) :
    fibre m Z l = if l ∈ C then {f l} else ∅ := by
  by_cases h : l ∈ C
  · rw [if_pos h]
    ext x
    rw [mem_fibre, hmem]
    simp [Fin.init_snoc, Fin.snoc_last, h]
  · rw [if_neg h]
    ext x
    rw [mem_fibre, hmem]
    simp [Fin.init_snoc, Fin.snoc_last, h]

/-! ## 2. `loOf` of a graph is the function itself -/

theorem loOf_eq_of_graph {m : ℕ} {Z : Set (Fin (m + 1) → ℝ)}
    {C : Set (Fin m → ℝ)} {f : (Fin m → ℝ) → ℝ}
    (hmem : ∀ z : Fin (m + 1) → ℝ,
      z ∈ Z ↔ Fin.init z ∈ C ∧ z (Fin.last m) = f (Fin.init z)) (l : Fin m → ℝ) :
    loOf m Z l = if l ∈ C then f l else 0 := by
  unfold loOf
  rw [fibre_eq_of_graph hmem l]
  by_cases h : l ∈ C <;> simp [h]

/-! ## 3. The pointwise description of `A_lo` for a graph -/

theorem mem_A_lo_iff_eq_loOf_of_graph {m : ℕ} {Z : Set (Fin (m + 1) → ℝ)}
    {C : Set (Fin m → ℝ)} {f : (Fin m → ℝ) → ℝ}
    (hmem : ∀ z : Fin (m + 1) → ℝ,
      z ∈ Z ↔ Fin.init z ∈ C ∧ z (Fin.last m) = f (Fin.init z))
    (l : Fin m → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ A_lo m Z ↔ y = loOf m Z l := by
  have hfib := fibre_eq_of_graph hmem l
  have hlo := loOf_eq_of_graph hmem l
  rw [mem_A_lo_snoc]
  have ht : ∀ t : ℝ, (Fin.snoc l t ∈ Z) ↔ t ∈ fibre m Z l :=
    fun t => (mem_fibre m Z l t).symm
  simp only [ht]
  rw [hfib]
  by_cases h : l ∈ C
  · rw [if_pos h, hlo, if_pos h]
    constructor
    · rintro (⟨_, h1, h2⟩ | ⟨hne, _⟩)
      · exact le_antisymm (h1 (f l) (by simp))
          (h2 (f l) (fun t ht => le_of_eq (Set.mem_singleton_iff.mp ht).symm))
      · exact absurd (Set.singleton_nonempty (f l)) hne
    · intro hy
      left
      refine ⟨Set.singleton_nonempty _, ?_, ?_⟩
      · intro t ht; rw [Set.mem_singleton_iff.mp ht, hy]
      · intro u hu
        have := hu (f l) (by simp)
        rwa [hy]
  · rw [if_neg h, hlo, if_neg h]
    simp

/-! ## 4. The target -/

theorem graphOf_loOf_eq_of_graph {m : ℕ} {Z : Set (Fin (m + 1) → ℝ)}
    {C : Set (Fin m → ℝ)} {f : (Fin m → ℝ) → ℝ}
    (hmem : ∀ z : Fin (m + 1) → ℝ,
      z ∈ Z ↔ Fin.init z ∈ C ∧ z (Fin.last m) = f (Fin.init z)) :
    WilkiesDesign.graphOf (Work.WilG4c.loOf m Z) = Work.WilG4c.A_lo m Z ∧
      ∀ l ∈ Z, ∃ μ : Fin m → ℝ, Fin.snoc μ (Work.WilG4c.loOf m Z μ) = l := by
  constructor
  · ext z
    rw [show z = Fin.snoc (Fin.init z) (z (Fin.last m)) from (snoc_init_self m z).symm]
    rw [mem_graphOf_loOf_iff m Z (Fin.init z) (z (Fin.last m)),
      mem_A_lo_iff_eq_loOf_of_graph hmem (Fin.init z) (z (Fin.last m))]
  · intro l hl
    obtain ⟨hlC, hlval⟩ := (hmem l).mp hl
    refine ⟨Fin.init l, ?_⟩
    rw [loOf_eq_of_graph hmem (Fin.init l), if_pos hlC, hlval.symm]
    exact snoc_init_self m l

end Work.WilG4c
