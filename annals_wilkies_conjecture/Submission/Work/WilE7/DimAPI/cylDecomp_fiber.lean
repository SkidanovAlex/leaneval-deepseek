import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.singleton_cylDecomp

set_option autoImplicit false
noncomputable section
namespace Work.WilE7.DimAPI

open WilkiesDesign WilkiesDesign.E

/-! ## The fibre of a cylindrical decomposition over a cell of the projection

Let `C` be a cylindrical decomposition of `A ⊆ ℝ^{n+1}`.  Dropping the last coordinate
turns it into a cylindrical decomposition `D = C.image (fun c => Fin.init '' c)` of
`Fin.init '' A ⊆ ℝⁿ`.  For `b ∈ D`, the sub-family of `C` consisting of the cells whose
projection is exactly `b` is a cylindrical decomposition of the fibre
`A ∩ {z | Fin.init z ∈ b}`.

The three structural ingredients are

* pairwise disjointness of the projections (`cylDecompOn_pairwiseDisjoint`), which shows that
  every cell of `C` meeting the fibre has projection exactly `b`;
* the covering property (`h.2.2.1`), which shows that the filtered family covers the fibre;
* the fact that the projection of a nonempty cell of a decomposition is again a cell of a
  decomposition one dimension less (`Work.WilE7.singleton_cylDecomp`), which supplies the
  recursive clause. -/

/-- Distinct cells of a cylindrical decomposition are disjoint (formulated for the *images*
`Fin.init '' c`: two members with a common point are equal). -/
private theorem cylDecompOn_pairwiseDisjoint (n : ℕ) :
    ∀ {A : Set (Fin n → ℝ)} {C : Finset (Set (Fin n → ℝ))},
      WilkiesDesign.E.IsCylDecompOn n A C → (C : Set (Set (Fin n → ℝ))).PairwiseDisjoint id := by
  induction n with
  | zero =>
      intro A C h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [Set.pairwiseDisjoint_iff] <;> simp
  | succ n ih => intro A C h; exact h.2.1

theorem cylDecomp_fiber {n : ℕ} (A : Set (Fin (n + 1) → ℝ))
    (C : Finset (Set (Fin (n + 1) → ℝ))) (h : WilkiesDesign.E.IsCylDecompOn (n + 1) A C)
    (b : Set (Fin n → ℝ)) (hb : b ∈ C.image (fun c => Fin.init '' c)) :
    WilkiesDesign.E.IsCylDecompOn (n + 1) (A ∩ {z | Fin.init z ∈ b})
      (C.filter (fun c => Fin.init '' c = b)) := by
  -- a cell `c₀ ∈ C` with `Fin.init '' c₀ = b`, and its projection as a cell of `ℝⁿ`
  obtain ⟨c₀, hc₀, hc₀b⟩ := Finset.mem_image.mp hb
  have hc₀' : WilkiesDesign.IsCell (n + 1) c₀ ∧ c₀.Nonempty := h.1 c₀ hc₀
  have hbase : WilkiesDesign.IsCell n b ∧ b.Nonempty := by
    have h0 := Work.WilE7.singleton_cylDecomp.2 (n := n) c₀ hc₀'.1 hc₀'.2
    rwa [hc₀b] at h0
  have hb_sing : WilkiesDesign.E.IsCylDecompOn n b {b} :=
    Work.WilE7.singleton_cylDecomp.1 (n := n) b hbase.1 hbase.2
  -- distinct projections of cells of `C` are disjoint
  have hpd := (Set.pairwiseDisjoint_iff).mp (cylDecompOn_pairwiseDisjoint n h.2.2.2)
  -- the fibre over `b` projects onto `b`
  have hA' : Fin.init '' (A ∩ {z : Fin (n + 1) → ℝ | Fin.init z ∈ b}) = b := by
    ext y
    constructor
    · rintro ⟨z, ⟨-, hz⟩, rfl⟩
      exact hz
    · intro hy
      have hy' : y ∈ Fin.init '' c₀ := by rw [hc₀b]; exact hy
      obtain ⟨z, hz, hzy⟩ := hy'
      refine ⟨z, ⟨?_, ?_⟩, hzy⟩
      · exact h.2.2.1 ▸ Set.mem_sUnion.mpr ⟨c₀, hc₀, hz⟩
      · show Fin.init z ∈ b
        rw [hzy]; exact hy
  -- the projections of the filtered family are exactly `{b}`
  have himg : (C.filter (fun c => Fin.init '' c = b)).image (fun c => Fin.init '' c) = {b} := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨c, ⟨-, hcb⟩, hfx⟩
      rw [← hfx]; exact hcb
    · intro hx
      rw [hx]
      exact ⟨c₀, ⟨hc₀, hc₀b⟩, hc₀b⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the members are nonempty cells
    intro c hc
    exact h.1 c (Finset.mem_of_mem_filter c hc)
  · -- pairwise disjointness is inherited from `C`
    rw [Set.pairwiseDisjoint_iff]
    intro c₁ hc₁ c₂ hc₂ hne
    exact (Set.pairwiseDisjoint_iff).mp h.2.1
      (Finset.mem_of_mem_filter c₁ hc₁) (Finset.mem_of_mem_filter c₂ hc₂) hne
  · -- the union of the filtered family is the fibre
    refine Set.Subset.antisymm ?_ ?_
    · intro z hz
      obtain ⟨c, hc, hzc⟩ := Set.mem_sUnion.mp hz
      have hcC : c ∈ C := Finset.mem_of_mem_filter c hc
      have hcb : Fin.init '' c = b := (Finset.mem_filter.mp hc).2
      refine ⟨?_, ?_⟩
      · have hzU : z ∈ ⋃₀ (C : Set (Set (Fin (n + 1) → ℝ))) :=
          Set.mem_sUnion.mpr ⟨c, hcC, hzc⟩
        rwa [h.2.2.1] at hzU
      · have hz' : Fin.init z ∈ Fin.init '' c := ⟨z, hzc, rfl⟩
        rwa [hcb] at hz'
    · intro z hz
      obtain ⟨hzA, hzb⟩ := hz
      have hzU : z ∈ ⋃₀ (C : Set (Set (Fin (n + 1) → ℝ))) := by
        rw [h.2.2.1]; exact hzA
      obtain ⟨c, hcC, hzc⟩ := Set.mem_sUnion.mp hzU
      -- `Fin.init z` lies in both `Fin.init '' c` and `b`, so the two projections coincide
      have hz' : Fin.init z ∈ Fin.init '' c := ⟨z, hzc, rfl⟩
      have heq : Fin.init '' c = b :=
        hpd (Finset.mem_image.mpr ⟨c, hcC, rfl⟩) hb ⟨Fin.init z, hz', hzb⟩
      exact Set.mem_sUnion.mpr ⟨c, Finset.mem_filter.mpr ⟨hcC, heq⟩, hzc⟩
  · -- the projection of the filtered family is `{b}`, and `{b}` is a decomposition of `b`
    rw [hA', himg]
    exact hb_sing

end Work.WilE7.DimAPI
