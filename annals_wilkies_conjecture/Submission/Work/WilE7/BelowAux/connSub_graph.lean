import Mathlib

namespace Work.WilE7.BelowAux

/-- If a preconnected set `T` lies inside the union of the graphs of the functions `s i` over a
common domain `C` (with each `s i` continuous on `C` and, for `x ∈ C`, the family `i ↦ s i x`
injective), and `T` meets the graph of `s j`, then `T` is contained in the graph of `s j`.

Indeed, on the natural domain of the union the graph of `s j` is both closed and open, so a
preconnected set meeting it lies inside it. -/
theorem connSub_graph
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [T2Space β]
    {C : Set α} {k : ℕ} (s : Fin k → α → β) (j : Fin k)
    (hcont : ∀ i, ContinuousOn (s i) C)
    (hinj : ∀ x ∈ C, Function.Injective fun i : Fin k => s i x)
    {T : Set (α × β)} (hT : IsPreconnected T)
    (hTU : T ⊆ {q : α × β | q.1 ∈ C ∧ ∃ i, q.2 = s i q.1})
    (hTj : ∃ q ∈ T, q.2 = s j q.1) :
    T ⊆ {q : α × β | q.1 ∈ C ∧ q.2 = s j q.1} := by
  classical
  have hps : PreconnectedSpace T := Subtype.preconnectedSpace hT
  -- each point of `T` lies in the domain and selects some sheet
  have hCU : ∀ q : T, (q : α × β).1 ∈ C := fun q => (hTU q.2).1
  have hSel : ∀ q : T, ∃ i, (q : α × β).2 = s i (q : α × β).1 := fun q => (hTU q.2).2
  -- the graph of each `s i`, as a subset of `T`, is closed
  have hAclosed : ∀ i, IsClosed {q : T | (q : α × β).2 = s i (q : α × β).1} := by
    intro i
    have hCβ : Continuous (fun x : C => s i (x : α)) := by
      have h := continuousOn_iff_continuous_domRestrict.mp (hcont i)
      rwa [Set.domRestrict_eq] at h
    have hTC : Continuous (fun q : T => (⟨(q : α × β).1, hCU q⟩ : C)) :=
      continuous_subtype_val.fst.subtype_mk _
    have h2 : Continuous (fun q : T => s i (q : α × β).1) := hCβ.comp hTC
    have h1 : Continuous (fun q : T => (q : α × β).2) := continuous_subtype_val.snd
    exact isClosed_eq h1 h2
  have hAj_nonempty : ({q : T | (q : α × β).2 = s j (q : α × β).1}).Nonempty := by
    obtain ⟨q, hqT, hqj⟩ := hTj
    exact ⟨⟨q, hqT⟩, hqj⟩
  -- inside `T` the graph of `s j` is exactly the complement of the union of the other graphs
  have hAj_eq : {q : T | (q : α × β).2 = s j (q : α × β).1}
      = (⋃ i ∈ (Finset.univ.erase j), {q : T | (q : α × β).2 = s i (q : α × β).1})ᶜ := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, exists_prop]
    rw [not_exists]
    constructor
    · intro hq i hi
      obtain ⟨hij, hiq⟩ := hi
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hij
      refine hij ((hinj (q : α × β).1 (hCU q)) ?_)
      show s i (q : α × β).1 = s j (q : α × β).1
      rw [← hiq, ← hq]
    · intro hq
      obtain ⟨i, hi⟩ := hSel q
      rcases eq_or_ne i j with rfl | hij
      · exact hi
      · exact absurd ⟨by simp [hij], hi⟩ (hq i)
  have hAj_clopen : IsClopen {q : T | (q : α × β).2 = s j (q : α × β).1} := by
    refine ⟨hAclosed j, ?_⟩
    rw [hAj_eq]
    exact (isClosed_biUnion_finset (fun i _ => hAclosed i)).isOpen_compl
  -- a clopen subset of the preconnected space `T` is empty or everything
  rcases (preconnectedSpace_iff_clopen.mp hps)
      {q : T | (q : α × β).2 = s j (q : α × β).1} hAj_clopen with h | h
  · exact absurd h hAj_nonempty.ne_empty
  · intro q hq
    have hmem : (⟨q, hq⟩ : T) ∈ {q : T | (q : α × β).2 = s j (q : α × β).1} := by
      rw [h]; trivial
    exact ⟨hCU ⟨q, hq⟩, hmem⟩

end Work.WilE7.BelowAux
