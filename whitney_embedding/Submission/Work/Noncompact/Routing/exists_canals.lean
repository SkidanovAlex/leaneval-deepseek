import Mathlib
import Submission.Work.Noncompact.CompressionTube.LineBuild.nested_canals

/-!
# Disjoint "canals to infinity" through a locally finite set

`Work.Noncompact.Routing.exists_canals`: let `M` be a connected non-compact topological
`n`-manifold (`n ≥ 2`) and `B ⊆ M` locally finite (every compact set meets `B` finitely).  Then
there is a family `W : B → Set M` of pairwise disjoint open "canals" with

* `b ∈ W b`,
* the canal escapes to infinity: after removing any compact set `C` there is a point of `W b \ C`
  whose component in `W b \ C` has non-compact closure,
* the family is locally finite: only finitely many canals meet a given compact set.

**`Work.Noncompact.Routing.exists_canals_nested`** is the *stronger* export needed by the line
construction: besides the canals it also returns the compact exhaustion `K` and, for every `b`, the
nested family `D b : ℕ → Set M` of `K`-avoiding open preconnected regions with non-compact closure
produced by `exists_nested_canals` (`D b 0 = W b`, `D b (i+1) ⊆ D b i`, `D b i ∩ K i = ∅`).

The cofinality clause of `exists_canals` alone is **not** sufficient to cut a proper line inside the
canal (see `NOTES.md`: a "hub with a corridor to a comb" satisfies it but contains no proper curve at
all); the nested family `D` is the hypothesis the line construction actually uses.
-/

namespace Work.Noncompact.Routing

open Set Topology

/-- Every compact set is contained in some level of a monotone exhaustion through its interiors. -/
private lemma exists_subset_of_mono_exhaust {M : Type*} [TopologicalSpace M]
    {K : ℕ → Set M} (hKmono : Monotone K) (hKint : ∀ i, K i ⊆ interior (K (i + 1)))
    (hKcov : (⋃ i, K i) = (Set.univ : Set M)) {C : Set M} (hC : IsCompact C) :
    ∃ N, C ⊆ K N := by
  have hopen : C ⊆ ⋃ i, interior (K (i + 1)) := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (show x ∈ ⋃ i, K i by rw [hKcov]; trivial)
    exact Set.mem_iUnion.mpr ⟨i, hKint i hi⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun i : ℕ => interior (K (i + 1)))
    (fun i => isOpen_interior) hopen
  refine ⟨t.sup (fun i => i + 1), fun x hx => ?_⟩
  obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact hKmono (Finset.le_sup (f := fun i => i + 1) hit) (interior_subset hxi)

/-- **Pairwise disjoint preconnected canals to infinity through a locally finite set.** -/
theorem exists_canals {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [T2Space M] [SecondCountableTopology M] [ConnectedSpace M] (hM : ¬ CompactSpace M)
    (B : Set M) (hB : ∀ K : Set M, IsCompact K → (B ∩ K).Finite) :
    ∃ W : B → Set M,
      (∀ b, IsOpen (W b)) ∧ (∀ b, IsPreconnected (W b)) ∧ (∀ b, (b : M) ∈ W b) ∧
      (∀ b : B, ∀ C : Set M, IsCompact C → ∃ x ∈ W b, x ∉ C ∧
        ¬ IsCompact (closure (connectedComponentIn (W b \ C) x))) ∧
      (∀ b b', b ≠ b' → Disjoint (W b) (W b')) ∧
      (∀ K : Set M, IsCompact K → {b : B | (W b ∩ K).Nonempty}.Finite) := by
  obtain ⟨K, W, D, lev, q, γ, hKc, hK0, hKsub, hKuniv, hWo, hWb, hWpc, hD0, hDo, hDpc, hDne,
    hDmono, hDsub, hDK, hWdisj, hWfin, hDnc, hdata, htail, hqlev⟩ :=
    Work.Noncompact.CompressionTube.exists_nested_canals (n := n) hn hM B hB
  have hKmono : Monotone K := Work.Noncompact.CompressionTube.monotone_K K hKsub
  refine ⟨W, hWo, hWpc, hWb, ?_, hWdisj, hWfin⟩
  intro b C hC
  obtain ⟨N, hN⟩ := exists_subset_of_mono_exhaust hKmono hKsub hKuniv hC
  obtain ⟨x, hxD⟩ := hDne b N
  have hxnot : x ∉ C := fun hxC => hDK b N hxD (hN hxC)
  have hDsub' : D b N ⊆ W b \ C :=
    fun z hz => ⟨hDsub b N hz, fun hzC => hDK b N hz (hN hzC)⟩
  have hsub : D b N ⊆ connectedComponentIn (W b \ C) x :=
    IsPreconnected.subset_connectedComponentIn (hDpc b N) hxD hDsub'
  refine ⟨x, hDsub b N hxD, hxnot, ?_⟩
  intro hcomp
  exact hDnc b N (hcomp.of_isClosed_subset isClosed_closure (closure_mono hsub))

/-- **The nested export.**  The canals together with the compact exhaustion and the nested family of
`K`-avoiding open preconnected regions with non-compact closure (`exists_nested_canals`), plus the
cofinality clause of `exists_canals`.  This is the interface of the line construction. -/
theorem exists_canals_nested {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [T2Space M] [SecondCountableTopology M] [ConnectedSpace M] (hM : ¬ CompactSpace M)
    (B : Set M) (hB : ∀ K : Set M, IsCompact K → (B ∩ K).Finite) :
    ∃ (K : ℕ → Set M) (W : B → Set M) (D : B → ℕ → Set M)
      (lev : B → ℕ) (q : B → ℕ → M) (γ : B → ℕ → ℝ → M),
      (∀ i, IsCompact (K i)) ∧ (∀ i, K i ⊆ interior (K (i + 1))) ∧
      (⋃ i, K i) = (Set.univ : Set M) ∧
      (∀ b, IsOpen (W b)) ∧ (∀ b, (b : M) ∈ W b) ∧ (∀ b, IsPreconnected (W b)) ∧
      (∀ b i, IsOpen (D b i)) ∧ (∀ b i, IsPreconnected (D b i)) ∧ (∀ b i, (D b i).Nonempty) ∧
      (∀ b i, D b (i + 1) ⊆ D b i) ∧ (∀ b i, D b i ⊆ W b) ∧ (∀ b i, D b i ⊆ (K i)ᶜ) ∧
      (∀ b i, ¬ IsCompact (closure (D b i))) ∧ (∀ b, (b : M) ∈ D b 0) ∧
      (∀ b b', b ≠ b' → Disjoint (W b) (W b')) ∧
      (∀ K' : Set M, IsCompact K' → {b : B | (W b ∩ K').Nonempty}.Finite) ∧
      (∀ b : B, ∀ C : Set M, IsCompact C → ∃ x ∈ W b, x ∉ C ∧
        ¬ IsCompact (closure (connectedComponentIn (W b \ C) x))) ∧
      Work.Noncompact.CompressionTube.SpineData K B lev q γ ∧
      (∀ (b : B) (i : ℕ), lev b ≤ i →
        (⋃ j : {j : ℕ // i ≤ j}, γ b (j : ℕ) '' Set.Icc (0:ℝ) 1) ⊆ D b i) ∧
      (∀ b : B, q b (lev b) = (b : M)) := by
  obtain ⟨K, W, D, lev, q, γ, hKc, hK0, hKsub, hKuniv, hWo, hWb, hWpc, hD0, hDo, hDpc, hDne,
    hDmono, hDsub, hDK, hWdisj, hWfin, hDnc, hdata, htail, hqlev⟩ :=
    Work.Noncompact.CompressionTube.exists_nested_canals (n := n) hn hM B hB
  have hKmono : Monotone K := Work.Noncompact.CompressionTube.monotone_K K hKsub
  have hcof : ∀ b : B, ∀ C : Set M, IsCompact C → ∃ x ∈ W b, x ∉ C ∧
      ¬ IsCompact (closure (connectedComponentIn (W b \ C) x)) := by
    intro b C hC
    obtain ⟨N, hN⟩ := exists_subset_of_mono_exhaust hKmono hKsub hKuniv hC
    obtain ⟨x, hxD⟩ := hDne b N
    have hxnot : x ∉ C := fun hxC => hDK b N hxD (hN hxC)
    have hDsub' : D b N ⊆ W b \ C :=
      fun z hz => ⟨hDsub b N hz, fun hzC => hDK b N hz (hN hzC)⟩
    have hsub : D b N ⊆ connectedComponentIn (W b \ C) x :=
      IsPreconnected.subset_connectedComponentIn (hDpc b N) hxD hDsub'
    refine ⟨x, hDsub b N hxD, hxnot, ?_⟩
    intro hcomp
    exact hDnc b N (hcomp.of_isClosed_subset isClosed_closure (closure_mono hsub))
  exact ⟨K, W, D, lev, q, γ, hKc, hKsub, hKuniv, hWo, hWb, hWpc, hDo, hDpc, hDne, hDmono, hDsub,
    hDK, hDnc, (fun b => by rw [hD0 b]; exact hWb b), hWdisj, hWfin, hcof, hdata, htail, hqlev⟩

end Work.Noncompact.Routing
