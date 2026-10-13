import Mathlib
import Submission.Work.Wilkies.E.Spec

noncomputable section
open Classical
namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-! ## Local structural lemmas about `IsCylDecompOn`

These are self-contained copies (with `private` names, so that they never clash with the
copies other files in this directory already carry) of the four elementary facts about a
cylindrical decomposition that the gluing argument needs. -/

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

private theorem cylDecompOn_subset (n : ℕ) :
    ∀ {A : Set (Fin n → ℝ)} {C : Finset (Set (Fin n → ℝ))},
      WilkiesDesign.E.IsCylDecompOn n A C → ∀ c ∈ C, c ⊆ A := by
  intro A C h c hc
  rw [← cylDecompOn_cover n h]
  exact Set.subset_sUnion_of_mem hc

private theorem cylDecompOn_nonempty (n : ℕ) :
    ∀ {A : Set (Fin n → ℝ)} {C : Finset (Set (Fin n → ℝ))},
      WilkiesDesign.E.IsCylDecompOn n A C → ∀ κ ∈ C, κ.Nonempty := by
  induction n with
  | zero =>
      intro A C h κ hκ
      rcases h with ⟨hA, hC⟩ | ⟨hA, hC⟩
      · subst hC
        rw [Finset.mem_singleton] at hκ
        subst hκ
        exact ⟨fun i => i.elim0, trivial⟩
      · subst hC
        exact absurd hκ (Finset.notMem_empty κ)
  | succ n ih => intro A C h κ hκ; exact (h.1 κ hκ).2

/-- Gluing a cylindrical decomposition of `A` out of the fibres of a decomposition of the
projection `Fin.init '' A`: if `B` decomposes `Fin.init '' A`, each fibre over `b ∈ B` is
decomposed by `B' b`, and every `κ ∈ B' b` projects exactly onto `b`, then `⋃_{b ∈ B} B' b`
decomposes `A`. -/
theorem cylDecomp_union {n : ℕ} (B : Finset (Set (Fin n → ℝ))) (A : Set (Fin (n + 1) → ℝ))
    (B' : Set (Fin n → ℝ) → Finset (Set (Fin (n + 1) → ℝ)))
    (hcyl : A = {z : Fin (n + 1) → ℝ | Fin.init z ∈ Fin.init '' A})
    (hB : WilkiesDesign.E.IsCylDecompOn n (Fin.init '' A) B)
    (hproj : ∀ b ∈ B, ∀ κ ∈ B' b, Fin.init '' κ = b)
    (hB' : ∀ b ∈ B, WilkiesDesign.E.IsCylDecompOn (n + 1)
      {z : Fin (n + 1) → ℝ | Fin.init z ∈ b} (B' b)) :
    WilkiesDesign.E.IsCylDecompOn (n + 1) A (B.biUnion B') := by
  -- Each `B' b` covers exactly the fibre over `b`.
  have hcover : ∀ b ∈ B,
      ⋃₀ ((B' b : Finset (Set (Fin (n + 1) → ℝ))) : Set (Set (Fin (n + 1) → ℝ)))
        = {z : Fin (n + 1) → ℝ | Fin.init z ∈ b} :=
    fun b hb => cylDecompOn_cover (n + 1) (hB' b hb)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- every member of `B.biUnion B'` is a nonempty cell
    intro c hc
    obtain ⟨b, hb, hcb⟩ := Finset.mem_biUnion.mp hc
    exact (hB' b hb).1 c hcb
  · -- pairwise disjointness
    intro c₁ hc₁ c₂ hc₂ hne
    obtain ⟨b₁, hb₁, hc₁'⟩ := Finset.mem_biUnion.mp hc₁
    obtain ⟨b₂, hb₂, hc₂'⟩ := Finset.mem_biUnion.mp hc₂
    by_cases hbb : b₁ = b₂
    · -- two cells over the same `b`
      rw [← hbb] at hc₂'
      exact (cylDecompOn_pairwiseDisjoint (n + 1) (hB' b₁ hb₁)) hc₁' hc₂' hne
    · -- two cells over distinct `b`'s, which are disjoint
      refine Set.disjoint_left.mpr fun z hz₁ hz₂ => ?_
      have h₁ : Fin.init z ∈ b₁ := (cylDecompOn_subset (n + 1) (hB' b₁ hb₁) c₁ hc₁') hz₁
      have h₂ : Fin.init z ∈ b₂ := (cylDecompOn_subset (n + 1) (hB' b₂ hb₂) c₂ hc₂') hz₂
      exact (Set.disjoint_left.mp ((cylDecompOn_pairwiseDisjoint n hB) hb₁ hb₂ hbb)) h₁ h₂
  · -- the union is all of `A`
    refine Set.Subset.antisymm ?_ ?_
    · intro z hz
      rw [Set.mem_sUnion] at hz
      obtain ⟨c, hc, hzc⟩ := hz
      obtain ⟨b, hb, hcb⟩ := Finset.mem_biUnion.mp hc
      have h₁ : Fin.init z ∈ b := (cylDecompOn_subset (n + 1) (hB' b hb) c hcb) hzc
      have h₂ : Fin.init z ∈ Fin.init '' A := (cylDecompOn_subset n hB b hb) h₁
      rw [hcyl]
      exact h₂
    · intro z hz
      have hz' : Fin.init z ∈ Fin.init '' A := ⟨z, hz, rfl⟩
      have hzB : Fin.init z ∈ ⋃₀ ((B : Finset (Set (Fin n → ℝ))) : Set (Set (Fin n → ℝ))) := by
        rw [cylDecompOn_cover n hB]; exact hz'
      obtain ⟨b, hb, hbz⟩ := Set.mem_sUnion.mp hzB
      have hzC : z ∈
          ⋃₀ ((B' b : Finset (Set (Fin (n + 1) → ℝ))) : Set (Set (Fin (n + 1) → ℝ))) := by
        rw [hcover b hb]; exact hbz
      obtain ⟨c, hc, hzc⟩ := Set.mem_sUnion.mp hzC
      exact Set.mem_sUnion.mpr ⟨c, Finset.mem_biUnion.mpr ⟨b, hb, hc⟩, hzc⟩
  · -- the projected family is again `B`
    have hCim : (B.biUnion B').image (fun c => Fin.init '' c) = B := by
      refine Finset.Subset.antisymm ?_ ?_
      · intro b hb
        obtain ⟨c, hc, hcb⟩ := Finset.mem_image.mp hb
        obtain ⟨b₀, hb₀, hc'⟩ := Finset.mem_biUnion.mp hc
        rw [← hcb, hproj b₀ hb₀ c hc']
        exact hb₀
      · intro b hb
        obtain ⟨y, hy⟩ := cylDecompOn_nonempty n hB b hb
        have hinit : Fin.init (Fin.snoc (α := fun _ => ℝ) y (0 : ℝ)) = y := Fin.init_snoc _ _
        have hzmem : Fin.snoc (α := fun _ => ℝ) y (0 : ℝ) ∈
            {z : Fin (n + 1) → ℝ | Fin.init z ∈ b} := by
          show Fin.init (Fin.snoc (α := fun _ => ℝ) y (0 : ℝ)) ∈ b
          rw [hinit]
          exact hy
        have hzC : Fin.snoc (α := fun _ => ℝ) y (0 : ℝ) ∈
            ⋃₀ ((B' b : Finset (Set (Fin (n + 1) → ℝ))) : Set (Set (Fin (n + 1) → ℝ))) := by
          rw [hcover b hb]; exact hzmem
        obtain ⟨c, hc, hzc⟩ := Set.mem_sUnion.mp hzC
        exact Finset.mem_image.mpr ⟨c, Finset.mem_biUnion.mpr ⟨b, hb, hc⟩, hproj b hb c hc⟩
    rw [hCim]
    exact hB

end Work.WilE7
