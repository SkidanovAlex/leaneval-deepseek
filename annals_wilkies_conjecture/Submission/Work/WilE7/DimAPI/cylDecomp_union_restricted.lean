import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.singleton_cylDecomp

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.DimAPI

/-! ## Local structural lemmas about `IsCylDecompOn`

`private` copies of the two elementary facts about a cylindrical decomposition that the gluing
argument needs (so that they can never clash with the copies other files in this directory
carry). -/

private theorem cylDecompOn_pairwiseDisjoint (n : ℕ) :
    ∀ {A : Set (Fin n → ℝ)} {C : Finset (Set (Fin n → ℝ))},
      WilkiesDesign.E.IsCylDecompOn n A C → (C : Set (Set (Fin n → ℝ))).PairwiseDisjoint id := by
  induction n with
  | zero =>
      intro A C h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [Set.pairwiseDisjoint_iff] <;> simp
  | succ n ih => intro A C h; exact h.2.1

private theorem cylDecompOn_cover (n : ℕ) :
    ∀ {A : Set (Fin n → ℝ)} {C : Finset (Set (Fin n → ℝ))},
      WilkiesDesign.E.IsCylDecompOn n A C → ⋃₀ (C : Set (Set (Fin n → ℝ))) = A := by
  induction n with
  | zero => intro A C h; rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  | succ n ih => intro A C h; exact h.2.2.1

/-- Gluing a cylindrical decomposition of `A` out of the fibres of a decomposition of the
projection `Fin.init '' A`: if `B` decomposes `Fin.init '' A`, each fibre
`A ∩ {z | Fin.init z ∈ b}` over `b ∈ B` is decomposed by `B' b`, every `κ ∈ B' b` projects
exactly onto `b`, and every `κ ∈ B' b` is contained in `A`, then `⋃_{b ∈ B} B' b` decomposes
`A`.  (Both `hsub` and `hproj` are only used for `κ ∈ B' b` with `b ∈ B`, which is exactly
what the restricted hypotheses provide.) -/
theorem cylDecomp_union_restricted {n : ℕ} (A : Set (Fin (n + 1) → ℝ))
    (B : Finset (Set (Fin n → ℝ)))
    (B' : Set (Fin n → ℝ) → Finset (Set (Fin (n + 1) → ℝ)))
    (hB : WilkiesDesign.E.IsCylDecompOn n (Fin.init '' A) B)
    (hne : ∀ b ∈ B, (B' b).Nonempty)
    (hsub : ∀ b ∈ B, ∀ κ ∈ B' b, κ ⊆ A)
    (hproj : ∀ b ∈ B, ∀ κ ∈ B' b, Fin.init '' κ = b)
    (hB' : ∀ b ∈ B, WilkiesDesign.E.IsCylDecompOn (n + 1) (A ∩ {z | Fin.init z ∈ b}) (B' b)) :
    WilkiesDesign.E.IsCylDecompOn (n + 1) A (B.biUnion B') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- every member of `B.biUnion B'` is a nonempty cell
    intro c hc
    obtain ⟨b, hb, hcb⟩ := Finset.mem_biUnion.mp hc
    exact (hB' b hb).1 c hcb
  · -- pairwise disjointness: cells with a common point coincide
    rw [Set.pairwiseDisjoint_iff]
    intro c₁ hc₁ c₂ hc₂ hne12
    obtain ⟨b₁, hb₁, hc₁'⟩ := Finset.mem_biUnion.mp hc₁
    obtain ⟨b₂, hb₂, hc₂'⟩ := Finset.mem_biUnion.mp hc₂
    obtain ⟨z, hz₁, hz₂⟩ := hne12
    -- the two cells project into their base cells, so their base cells meet
    have h1 : Fin.init z ∈ b₁ := by
      rw [← hproj b₁ hb₁ c₁ hc₁']; exact ⟨z, hz₁, rfl⟩
    have h2 : Fin.init z ∈ b₂ := by
      rw [← hproj b₂ hb₂ c₂ hc₂']; exact ⟨z, hz₂, rfl⟩
    have hb : b₁ = b₂ :=
      (Set.pairwiseDisjoint_iff.mp (cylDecompOn_pairwiseDisjoint n hB)) hb₁ hb₂
        ⟨Fin.init z, h1, h2⟩
    -- transport the second cell into the fibre over `b₁` and use the decomposition there
    exact (Set.pairwiseDisjoint_iff.mp (hB' b₁ hb₁).2.1) hc₁' (hb.symm ▸ hc₂')
      ⟨z, hz₁, hz₂⟩
  · -- the union of `B.biUnion B'` is all of `A`
    refine Set.Subset.antisymm ?_ ?_
    · intro z hz
      rw [Set.mem_sUnion] at hz
      obtain ⟨c, hc, hzc⟩ := hz
      obtain ⟨b, hb, hcb⟩ := Finset.mem_biUnion.mp hc
      exact hsub b hb c hcb hzc
    · intro z hz
      have hzπ : Fin.init z ∈ Fin.init '' A := ⟨z, hz, rfl⟩
      have hzB : Fin.init z ∈ ⋃₀ ((B : Finset (Set (Fin n → ℝ))) : Set (Set (Fin n → ℝ))) := by
        rw [cylDecompOn_cover n hB]; exact hzπ
      obtain ⟨b, hb, hbz⟩ := Set.mem_sUnion.mp hzB
      have hzC : z ∈
          ⋃₀ ((B' b : Finset (Set (Fin (n + 1) → ℝ))) : Set (Set (Fin (n + 1) → ℝ))) := by
        rw [cylDecompOn_cover (n + 1) (hB' b hb)]
        exact ⟨hz, hbz⟩
      obtain ⟨c, hc, hzc⟩ := Set.mem_sUnion.mp hzC
      exact Set.mem_sUnion.mpr ⟨c, Finset.mem_biUnion.mpr ⟨b, hb, hc⟩, hzc⟩
  · -- projecting the glued family returns the base family `B`
    have hCim : (B.biUnion B').image (fun c => Fin.init '' c) = B := by
      refine Finset.Subset.antisymm ?_ ?_
      · intro b hb
        obtain ⟨c, hc, hcb⟩ := Finset.mem_image.mp hb
        obtain ⟨b₀, hb₀, hc'⟩ := Finset.mem_biUnion.mp hc
        rw [← hcb, hproj b₀ hb₀ c hc']
        exact hb₀
      · intro b hb
        obtain ⟨κ, hκ⟩ := hne b hb
        exact Finset.mem_image.mpr
          ⟨κ, Finset.mem_biUnion.mpr ⟨b, hb, hκ⟩, hproj b hb κ hκ⟩
    rw [hCim]
    exact hB

end Work.WilE7.DimAPI
