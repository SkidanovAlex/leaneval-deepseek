import Mathlib
import Submission.Work.Noncompact.CompressionTube.spike_removal_finite

/-!
# Auxiliary lemmas for the level step of the spine recursion

This file contains two lemmas that the shell-by-shell construction of `SpineData` needs and that
have nothing to do with the routing proper:

* `Work.Noncompact.CompressionTube.spike_removal_finite_or` — the **either/or** form of
  `spike_removal_finite`: the slits that are removed are only required to be *either* contained in
  `C` *or* disjoint from `C`.  This is the form the construction uses: the walls handed from one
  level to the next are connected, so each of them is either inside the carrier or disjoint from it.

* `Work.Noncompact.CompressionTube.closure_connectedComponentIn_interior_meets_frontier` — if `E` is
  open and preconnected, `p ∈ E ∩ interior K` and `E` meets the complement of `K`, then the
  component of `p` in `E ∩ interior K` accumulates at the frontier of `K`.  This is the
  "the inner region reaches the frontier" step of the level routing: it produces the point `z` close
  to `∂K` from which the crossing starts.
-/

set_option linter.unusedSectionVars false

namespace Work.Noncompact.CompressionTube

open Set Topology

variable {M : Type*} [TopologicalSpace M]

/-- **Either/or form of `spike_removal_finite`.**

Finitely many pairwise disjoint slits with free end outside `C`, each *either* contained in `C` or
disjoint from it, do not disconnect an open preconnected `C` of an `n`-manifold, `n ≥ 2`. -/
theorem spike_removal_finite_or {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {C : Set M} (hC : IsOpen C) (hCpre : IsPreconnected C)
    {k : ℕ} {σ : Fin k → ℝ → M} (hσc : ∀ j, Continuous (σ j))
    (hσinj : ∀ j, Set.InjOn (σ j) (Set.Icc (0:ℝ) 1))
    (hσC : ∀ j, σ j '' Set.Ioc (0:ℝ) 1 ⊆ C ∨ Disjoint (σ j '' Set.Ioc (0:ℝ) 1) C)
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
    have hunion : (⋃ j : Fin (k+1), σ j '' Set.Ioc (0:ℝ) 1) =
        (⋃ j : Fin k, σ j.castSucc '' Set.Ioc (0:ℝ) 1) ∪ σ (Fin.last k) '' Set.Ioc (0:ℝ) 1 := by
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
    have hApre : IsPreconnected (C \ ⋃ j : Fin k, σ j.castSucc '' Set.Ioc (0:ℝ) 1) :=
      ih (fun j => hσc j.castSucc) (fun j => hσinj j.castSucc)
        (fun j => hσC j.castSucc) (fun j => hσ0 j.castSucc)
        (fun j j' h => hdisj j.castSucc j'.castSucc (fun hh => h (Fin.castSucc_injective k hh)))
    rcases hσC (Fin.last k) with hlastC | hlastdisj
    · -- the last slit lies in `C`
      have hAopen : IsOpen (C \ ⋃ j : Fin k, σ j.castSucc '' Set.Ioc (0:ℝ) 1) := by
        rw [sdiff_iUnion_Ioc_eq_sdiff_iUnion_Icc (C := C)
          (σ := fun j : Fin k => σ j.castSucc) (fun j : Fin k => hσ0 j.castSucc)]
        exact hC.sdiff (isCompact_iUnion fun j : Fin k => isCompact_Icc.image (hσc j.castSucc)).isClosed
      have hlastC' : σ (Fin.last k) '' Set.Ioc (0:ℝ) 1 ⊆
          C \ ⋃ j : Fin k, σ j.castSucc '' Set.Ioc (0:ℝ) 1 := by
        rintro x ⟨t, ht, rfl⟩
        refine ⟨hlastC ⟨t, ht, rfl⟩, ?_⟩
        intro hmem
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hmem
        obtain ⟨s, hs, hjs⟩ := hj
        have hne : j.castSucc ≠ Fin.last k := ne_of_lt (Fin.castSucc_lt_last j)
        exact (Set.disjoint_left.mp (hdisj j.castSucc (Fin.last k) hne))
          ⟨s, ⟨hs.1.le, hs.2⟩, hjs⟩ ⟨t, ⟨ht.1.le, ht.2⟩, rfl⟩
      have hlast0' : σ (Fin.last k) 0 ∉ C \ ⋃ j : Fin k, σ j.castSucc '' Set.Ioc (0:ℝ) 1 :=
        fun h => hσ0 (Fin.last k) h.1
      have hres : IsPreconnected
          ((C \ ⋃ j : Fin k, σ j.castSucc '' Set.Ioc (0:ℝ) 1) \
            σ (Fin.last k) '' Set.Ioc (0:ℝ) 1) :=
        spike_removal hn hAopen hApre (hσc (Fin.last k)) (hσinj (Fin.last k)) hlastC' hlast0'
      have heq : C \ ((⋃ j : Fin k, σ j.castSucc '' Set.Ioc (0:ℝ) 1) ∪
            σ (Fin.last k) '' Set.Ioc (0:ℝ) 1) =
          ((C \ ⋃ j : Fin k, σ j.castSucc '' Set.Ioc (0:ℝ) 1) \
            σ (Fin.last k) '' Set.Ioc (0:ℝ) 1) := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_union, Set.mem_iUnion]
        tauto
      rw [hunion, heq]
      exact hres
    · -- the last slit misses `C`
      have heq : C \ ((⋃ j : Fin k, σ j.castSucc '' Set.Ioc (0:ℝ) 1) ∪
            σ (Fin.last k) '' Set.Ioc (0:ℝ) 1) =
          C \ ⋃ j : Fin k, σ j.castSucc '' Set.Ioc (0:ℝ) 1 := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_union, Set.mem_iUnion]
        constructor
        · rintro ⟨hxC, hnot⟩
          exact ⟨hxC, fun hA => hnot (Or.inl hA)⟩
        · rintro ⟨hxC, hA⟩
          refine ⟨hxC, fun h => ?_⟩
          rcases h with h | h
          · exact hA h
          · exact Set.disjoint_left.mp hlastdisj h hxC
      rw [hunion, heq]
      exact hApre

/-- **The inner region reaches the frontier.**  If `E` is open and preconnected, `p ∈ E ∩ interior K`
and `E` meets the complement of `K`, then the component of `p` in `E ∩ interior K` accumulates at
the frontier of `K`. -/
theorem closure_connectedComponentIn_interior_meets_frontier {M : Type*} [TopologicalSpace M]
    [LocallyConnectedSpace M]
    {K E : Set M} (hKc : IsClosed K) (hE : IsOpen E) (hEpre : IsPreconnected E)
    {p : M} (hp : p ∈ E ∩ interior K) (hout : (E ∩ Kᶜ).Nonempty) :
    (closure (connectedComponentIn (E ∩ interior K) p) ∩ frontier K).Nonempty := by
  classical
  set R : Set M := connectedComponentIn (E ∩ interior K) p with hR
  have hpF : p ∈ E ∩ interior K := hp
  have hpR : p ∈ R := by rw [hR]; exact mem_connectedComponentIn hpF
  have hRsub : R ⊆ E ∩ interior K := by rw [hR]; exact connectedComponentIn_subset _ _
  have hRpre : IsPreconnected R := by rw [hR]; exact isPreconnected_connectedComponentIn
  have hRopen : IsOpen R := by
    rw [hR]; exact (hE.inter isOpen_interior).connectedComponentIn
  by_contra hcon
  have hcon' : closure R ∩ frontier K = ∅ := Set.not_nonempty_iff_eq_empty.mp hcon
  have hclsub : closure R ⊆ interior K := by
    intro x hx
    have hxK : x ∈ K := by
      have h1 : x ∈ closure (interior K) := closure_mono (fun y hy => (hRsub hy).2) hx
      have h2 : closure (interior K) ⊆ K := by
        have h2' := closure_mono (interior_subset : interior K ⊆ K)
        rwa [hKc.closure_eq] at h2'
      exact h2 h1
    have h3 : x ∈ interior K ∪ frontier K := by
      have hxcl : x ∈ closure K := by rwa [hKc.closure_eq]
      rwa [closure_eq_interior_union_frontier] at hxcl
    rcases h3 with h | h
    · exact h
    · exfalso
      have : x ∈ closure R ∩ frontier K := ⟨hx, h⟩
      rw [hcon'] at this
      exact this
  have hclER : closure R ∩ E ⊆ R := by
    intro y hy
    have hyF : y ∈ E ∩ interior K := ⟨hy.2, hclsub hy.1⟩
    have hpre : IsPreconnected (R ∪ {y}) :=
      IsPreconnected.subset_closure hRpre Set.subset_union_left (by
        intro z hz
        rcases hz with hz | hz
        · exact subset_closure hz
        · rw [Set.mem_singleton_iff] at hz
          rw [hz]
          exact hy.1)
    have hsub : R ∪ {y} ⊆ E ∩ interior K := by
      intro z hz
      rcases hz with hz | hz
      · exact hRsub hz
      · rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact hyF
    have h4 : R ∪ {y} ⊆ R := by
      rw [hR]
      exact hpre.subset_connectedComponentIn (Or.inl hpR) hsub
    exact h4 (Or.inr rfl)
  have hER : E ⊆ R :=
    hEpre.subset_of_closure_inter_subset hRopen ⟨p, hpF.1, hpR⟩ hclER
  obtain ⟨z, hzE, hzKc⟩ := hout
  exact hzKc (interior_subset (hRsub (hER hzE)).2)

end Work.Noncompact.CompressionTube
