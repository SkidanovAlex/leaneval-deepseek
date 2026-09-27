import Mathlib
import Submission.Work.Noncompact.CompressionTube.spike_removal

/-!
# Removing finitely many spikes

`Work.Noncompact.CompressionTube.spike_removal_finite`: finitely many pairwise disjoint
"slits with a free end" (half-open arcs `σ j '' Ioc 0 1` with `σ j 0 ∉ C` and
`σ j '' Ioc 0 1 ⊆ C`) do not disconnect an open preconnected `C` of an `n`-manifold, `n ≥ 2`.

This is the finite-family form of the proved single-spike lemma
`Work.Noncompact.CompressionTube.spike_removal` (peel the spikes one at a time).  Note that
`hσC` forces the *included* end `σ j 1` to lie in `C` (as `1 ∈ Ioc 0 1`), so each removed piece
is a slit from the boundary into the interior, not a crosscut.
-/

set_option linter.unusedSectionVars false

namespace Work.Noncompact.CompressionTube

open Set Topology

variable {M : Type*} [TopologicalSpace M]

/-- A half-open union of slits can be replaced by the union of the closures when the free ends
lie outside `C`. -/
lemma sdiff_iUnion_Ioc_eq_sdiff_iUnion_Icc {C : Set M} {k : ℕ} {σ : Fin k → ℝ → M}
    (h0 : ∀ j, σ j 0 ∉ C) :
    C \ (⋃ j : Fin k, σ j '' Set.Ioc (0:ℝ) 1) =
      C \ ⋃ j : Fin k, σ j '' Set.Icc (0:ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨hxC, hx⟩
    refine ⟨hxC, ?_⟩
    intro hu
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hu
    obtain ⟨t, ht, htx⟩ := hj
    rcases eq_or_lt_of_le ht.1 with h | h
    · have hx0 : x = σ j 0 := by rw [← htx, h]
      exact h0 j (hx0 ▸ hxC)
    · exact hx (Set.mem_iUnion.mpr ⟨j, ⟨t, ⟨h, ht.2⟩, htx⟩⟩)
  · rintro ⟨hxC, hx⟩
    refine ⟨hxC, ?_⟩
    intro hu
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hu
    obtain ⟨t, ht, htx⟩ := hj
    exact hx (Set.mem_iUnion.mpr ⟨j, ⟨t, ⟨ht.1.le, ht.2⟩, htx⟩⟩)

/-- Removing finitely many pairwise disjoint spikes keeps an open preconnected set
preconnected. -/
theorem spike_removal_finite {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {C : Set M} (hC : IsOpen C) (hCpre : IsPreconnected C)
    {k : ℕ} {σ : Fin k → ℝ → M} (hσc : ∀ j, Continuous (σ j))
    (hσinj : ∀ j, Set.InjOn (σ j) (Set.Icc (0:ℝ) 1))
    (hσC : ∀ j, σ j '' Set.Ioc (0:ℝ) 1 ⊆ C)
    (hσ0 : ∀ j, σ j 0 ∉ C)
    (hdisj : ∀ j j', j ≠ j' → Disjoint (σ j '' Set.Icc (0:ℝ) 1) (σ j' '' Set.Icc (0:ℝ) 1)) :
    IsPreconnected (C \ ⋃ j : Fin k, σ j '' Set.Ioc (0:ℝ) 1) := by
  classical
  induction k with
  | zero =>
    have h0 : (⋃ j : Fin 0, σ j '' Set.Ioc (0:ℝ) 1) = (∅ : Set M) := by simp
    rw [h0]
    simpa using hCpre
  | succ k ih =>
    set A : Set M := ⋃ j : Fin k, σ j.castSucc '' Set.Ioc (0:ℝ) 1 with hA
    have hunion : (⋃ j : Fin (k+1), σ j '' Set.Ioc (0:ℝ) 1) =
        A ∪ σ (Fin.last k) '' Set.Ioc (0:ℝ) 1 := by
      rw [hA]
      ext x
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨j, hj⟩
        rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
        · exact Or.inl ⟨i, hj⟩
        · exact Or.inr hj
      · rintro (⟨i, hi⟩ | h)
        · exact ⟨i.castSucc, hi⟩
        · exact ⟨Fin.last k, h⟩
    have hApre : IsPreconnected (C \ A) := by
      rw [hA]
      exact ih (fun j => hσc j.castSucc) (fun j => hσinj j.castSucc)
        (fun j => hσC j.castSucc) (fun j => hσ0 j.castSucc)
        (fun j j' h => hdisj j.castSucc j'.castSucc
          (fun hh => h (Fin.castSucc_injective k hh)))
    have hAopen : IsOpen (C \ A) := by
      rw [hA, sdiff_iUnion_Ioc_eq_sdiff_iUnion_Icc (C := C) (σ := fun j : Fin k => σ j.castSucc)
        (fun j : Fin k => hσ0 j.castSucc)]
      exact hC.sdiff (isCompact_iUnion fun j : Fin k => isCompact_Icc.image (hσc j.castSucc)).isClosed
    have hlastC : σ (Fin.last k) '' Set.Ioc (0:ℝ) 1 ⊆ C \ A := by
      rintro x ⟨t, ht, rfl⟩
      refine ⟨hσC (Fin.last k) ⟨t, ht, rfl⟩, ?_⟩
      intro hmem
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hmem
      obtain ⟨s, hs, hjs⟩ := hj
      have hne : j.castSucc ≠ Fin.last k := ne_of_lt (Fin.castSucc_lt_last j)
      exact (Set.disjoint_left.mp (hdisj j.castSucc (Fin.last k) hne))
        ⟨s, ⟨hs.1.le, hs.2⟩, hjs⟩ ⟨t, ⟨ht.1.le, ht.2⟩, rfl⟩
    have hlast0 : σ (Fin.last k) 0 ∉ C \ A := fun h => hσ0 (Fin.last k) h.1
    have hres : IsPreconnected ((C \ A) \ σ (Fin.last k) '' Set.Ioc (0:ℝ) 1) :=
      spike_removal hn hAopen hApre (hσc (Fin.last k)) (hσinj (Fin.last k)) hlastC hlast0
    have heq : C \ (A ∪ σ (Fin.last k) '' Set.Ioc (0:ℝ) 1) =
        (C \ A) \ σ (Fin.last k) '' Set.Ioc (0:ℝ) 1 := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_union]
      tauto
    rw [hunion, heq]
    exact hres

end Work.Noncompact.CompressionTube
