import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.Misiurewicz.frontier_finite_subset

/-!
# A null-frontier finite partition adapted to a finite open family

Given a finite family of open sets `V : Fin m → Set X`, each with `ν`-null frontier, there is a
finite measurable partition `P` of `X` all of whose parts have `ν`-null frontier and such that
every part meeting `⋃ j, V j` is contained in a single `V j`.

The construction is the partition into *membership patterns*: for `S : Finset (Fin m)` put

  `W S = {x | ∀ i, (x ∈ V i ↔ i ∈ S)} = ⋂ i, (if i ∈ S then V i else (V i)ᶜ)`.

These are finitely many measurable sets, pairwise disjoint, covering `X`.  Each `W S` is a finite
intersection of the members `V i`, `(V i)ᶜ`, so (by `frontier_iInter_subset`) its frontier is
contained in `⋃ i, frontier (V i)`, a finite union of `ν`-null sets.  Finally `W S ⊆ V i` for
every `i ∈ S`, so a part meeting `⋃ V` (which forces `S` to be nonempty) lies in some `V j`.
-/

namespace Work.Misiurewicz

open Set MeasureTheory

theorem exists_finPart_null_frontier_of_finite_cover {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (ν : MeasureTheory.Measure X) {m : ℕ}
    (V : Fin m → Set X) (hVo : ∀ i, IsOpen (V i))
    (hVfr : ∀ i, ν (frontier (V i)) = 0) :
    ∃ P : Work.EKLContract.FinPart X,
      (∀ k, ν (frontier (P.parts k)) = 0) ∧
      (∀ k, (P.parts k ∩ (⋃ j, V j)).Nonempty → ∃ j, P.parts k ⊆ V j) := by
  classical
  let W : Finset (Fin m) → Set X := fun S => ⋂ i, if i ∈ S then V i else (V i)ᶜ
  have hWmem : ∀ S (x : X), x ∈ W S ↔ ∀ i, (x ∈ V i ↔ i ∈ S) := by
    intro S x
    show x ∈ (⋂ i, if i ∈ S then V i else (V i)ᶜ) ↔ _
    rw [Set.mem_iInter]
    constructor
    · intro h i
      by_cases hi : i ∈ S
      · have hhi := h i; rw [if_pos hi] at hhi
        exact ⟨fun _ => hi, fun _ => hhi⟩
      · have hhi := h i; rw [if_neg hi] at hhi
        exact ⟨fun hx => absurd hx hhi, fun hh => absurd hh hi⟩
    · intro h i
      by_cases hi : i ∈ S
      · rw [if_pos hi]; exact (h i).mpr hi
      · rw [if_neg hi]; exact fun hx => hi ((h i).mp hx)
  have hWmeas : ∀ S, MeasurableSet (W S) := by
    intro S
    show MeasurableSet (⋂ i, if i ∈ S then V i else (V i)ᶜ)
    refine MeasurableSet.iInter (fun i => ?_)
    by_cases hi : i ∈ S
    · rw [if_pos hi]; exact (hVo i).measurableSet
    · rw [if_neg hi]; exact ((hVo i).measurableSet).compl
  have hWfr : ∀ S, ν (frontier (W S)) = 0 := by
    intro S
    refine measure_mono_null ?_ (measure_iUnion_null hVfr)
    show frontier (⋂ i, if i ∈ S then V i else (V i)ᶜ) ⊆ ⋃ i, frontier (V i)
    refine (frontier_iInter_subset _).trans ?_
    rintro x hx
    rw [Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi⟩ := hx
    refine ⟨i, ?_⟩
    by_cases h : i ∈ S
    · rwa [if_pos h] at hi
    · rwa [if_neg h, frontier_compl] at hi
  have hWdisj : ∀ S T, S ≠ T → Disjoint (W S) (W T) := by
    intro S T hST
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact hST (Finset.ext (fun i => ((hWmem S x).mp hx1 i).symm.trans ((hWmem T x).mp hx2 i)))
  have hWcov : (⋃ S, W S) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_iUnion]
    refine ⟨Finset.univ.filter (fun i => x ∈ V i), ?_⟩
    rw [hWmem]
    intro i
    simp
  have hWcont : ∀ S, (W S ∩ (⋃ j, V j)).Nonempty → ∃ j, W S ⊆ V j := by
    intro S hne
    rcases hne with ⟨x, hx⟩
    rw [Set.mem_inter_iff] at hx
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx.2
    refine ⟨j, fun y hy => ?_⟩
    exact ((hWmem S y).mp hy j).mpr (((hWmem S x).mp hx.1 j).mp hxj)
  let e : Finset (Fin m) ≃ Fin (Fintype.card (Finset (Fin m))) := Fintype.equivFin _
  let P₀ : Work.EKLContract.FinPart X :=
    { n := Fintype.card (Finset (Fin m))
      parts := fun k => W (e.symm k)
      measurable := fun k => hWmeas (e.symm k)
      disjoint := by
        intro i j hij
        exact hWdisj _ _ (fun h => hij (e.symm.injective h))
      cover := by
        rw [Set.eq_univ_iff_forall]
        intro x
        rw [Set.mem_iUnion]
        obtain ⟨S, hS⟩ := Set.mem_iUnion.mp (by rw [hWcov]; exact Set.mem_univ x)
        exact ⟨e S, by show x ∈ W (e.symm (e S)); rw [Equiv.symm_apply_apply]; exact hS⟩ }
  refine ⟨P₀, ?_, ?_⟩
  · intro k
    show ν (frontier (W (e.symm k))) = 0
    exact hWfr _
  · intro k hk
    show ∃ j, W (e.symm k) ⊆ V j
    exact hWcont _ hk

end Work.Misiurewicz
