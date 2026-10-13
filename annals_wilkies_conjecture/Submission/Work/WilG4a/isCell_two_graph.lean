import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilkiesH.Cell.isCell_nonempty

namespace Work.WilG4a

/-- A `2`-dimensional cylindrical cell which is contained in the graph of a function
`F : ℝ¹ → ℝ` is itself the graph of `F` over its (necessarily `1`-dimensional) base cell.

The only possible shapes of a `2`-cell are `graph` and `band` over a `1`-cell `C`.  A
nonempty `band` cell contains an open vertical segment, so it can never be contained in a
graph — one perturbs the last coordinate slightly.  Hence the cell must be a `graph` cell,
say with apex function `f`; then `F` and `f` agree on `C`, so `C` and `F` are the required
witnesses (`ψ := F`). -/
theorem isCell_two_graph {κ : Set (Fin 2 → ℝ)} {F : (Fin 1 → ℝ) → ℝ}
    (h : WilkiesDesign.IsCell 2 κ) (hne : κ.Nonempty)
    (hsub : κ ⊆ WilkiesDesign.graphOf F) :
    ∃ (C0 : Set (Fin 1 → ℝ)) (ψ : (Fin 1 → ℝ) → ℝ),
      WilkiesDesign.IsCell 1 C0 ∧ ContinuousOn ψ C0 ∧
      κ = {z : Fin 2 → ℝ | Fin.init z ∈ C0 ∧ z (Fin.last 1) = ψ (Fin.init z)} ∧
      (Fin.init '' κ = C0) ∧ (∀ p ∈ C0, ψ p = F p) := by
  cases h with
  | graph hC f hf =>
    rename_i C
    -- `F` and the apex function `f` agree on the base cell `C`.
    have hFf : ∀ y ∈ C, F y = f y := by
      intro y hy
      have hz : Fin.snoc y (f y) ∈
          {z : Fin 2 → ℝ | Fin.init z ∈ C ∧ z (Fin.last 1) = f (Fin.init z)} := by
        refine ⟨?_, ?_⟩
        · simpa only [Fin.init_snoc] using hy
        · simp only [Fin.init_snoc, Fin.snoc_last]
      have hg := hsub hz
      simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at hg
      exact hg.symm
    refine ⟨C, F, hC, ?_, ?_, ?_, ?_⟩
    · exact hf.congr (fun y hy => hFf y hy)
    · ext z
      constructor
      · intro hz
        obtain ⟨h1, h2⟩ := hz
        exact ⟨h1, hsub ⟨h1, h2⟩⟩
      · intro hz
        obtain ⟨h1, h2⟩ := hz
        refine ⟨h1, ?_⟩
        show z (Fin.last 1) = f (Fin.init z)
        rw [h2]
        exact hFf (Fin.init z) h1
    · ext y
      constructor
      · rintro ⟨z, hz, hzy⟩
        rw [← hzy]
        exact hz.1
      · intro hy
        refine ⟨Fin.snoc y (f y), ⟨?_, ?_⟩, ?_⟩
        · simpa only [Fin.init_snoc] using hy
        · simp only [Fin.init_snoc, Fin.snoc_last]
        · simp only [Fin.init_snoc]
    · intro p hp
      rfl
  | band hC a b ha hb hab =>
    rename_i C
    exfalso
    obtain ⟨z, hz⟩ := hne
    obtain ⟨hzC, hza, hzb⟩ := hz
    -- A real number strictly between the two `EReal` boundary values, different from `F y`.
    have hex : ∃ s : ℝ, a (Fin.init z) < (s : EReal) ∧ (s : EReal) < b (Fin.init z) ∧
        s ≠ F (Fin.init z) := by
      obtain ⟨s, hs1, hs2⟩ := EReal.lt_iff_exists_real_btwn.mp hzb
      by_cases hs : s = F (Fin.init z)
      · refine ⟨z (Fin.last (0 + 1)), hza, hzb, ?_⟩
        intro hc
        have h1 := hs1
        rw [hc, ← hs] at h1
        exact absurd h1 (lt_irrefl _)
      · exact ⟨s, lt_trans hza hs1, hs2, hs⟩
    obtain ⟨s0, hs0a, hs0b, hs0ne⟩ := hex
    have hz' : Fin.snoc (Fin.init z) s0 ∈
        {w : Fin 2 → ℝ | Fin.init w ∈ C ∧
          a (Fin.init w) < (w (Fin.last (0 + 1)) : EReal) ∧
          (w (Fin.last (0 + 1)) : EReal) < b (Fin.init w)} := by
      refine ⟨?_, ?_, ?_⟩
      · simpa only [Fin.init_snoc] using hzC
      · simpa only [Fin.init_snoc, Fin.snoc_last] using hs0a
      · simpa only [Fin.init_snoc, Fin.snoc_last] using hs0b
    have hzg : Fin.snoc (Fin.init z) s0 ∉ WilkiesDesign.graphOf F := by
      intro hmem
      simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at hmem
      exact hs0ne hmem
    exact hzg (hsub hz')

end Work.WilG4a
