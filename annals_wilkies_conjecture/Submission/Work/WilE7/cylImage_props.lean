import Mathlib
import Submission.Work.WilE7.Defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesDesign WilkiesDesign.E

/-! ## Cylindrical decompositions and coordinate projections

`cylImage n M C` projects the `M` last coordinates out of a finite family `C` of subsets of
`ℝ^{n+M}`.  This file establishes the three structural facts about it that area E7 needs:

* `cylImage_eq_image` : `cylImage n M C` is exactly the family of projections
  `projFirst n M '' c`, `c ∈ C` (the third component of the target statement);
* `projFirst_image_isCylDecompOn` : the projection of a cylindrical decomposition of `A` is a
  cylindrical decomposition of `projFirst n M '' A` (hence, with `A = cubeC (n+M)`,
  `cylImage n M C` is a cylindrical decomposition of `cubeC n`);
* `cylImage_compat` : compatibility with a subset `Y` is inherited by the projections.

The equidimensional ingredient is `projFirst_cells_eq_of_inter`: two cells of a cylindrical
decomposition whose projections meet have *equal* projections.  (Two distinct members of a
cylindrical decomposition are disjoint, and the projections of cells of a cylindrical
decomposition are pairwise disjoint once duplicates are removed -- see
`isCylDecompOn_pairwiseDisjoint`.) -/

/-! ### Elementary facts about `projFirst` -/

theorem projFirst_zero_image {n : ℕ} (S : Set (Fin (n + 0) → ℝ)) :
    projFirst n 0 '' S = S := by
  ext x; constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨x, hx, rfl⟩

theorem projFirst_zero_image_finset {n : ℕ} (C : Finset (Set (Fin (n + 0) → ℝ))) :
    C.image (fun c => projFirst n 0 '' c) = C := by
  ext c; simp [projFirst_zero_image]

theorem projFirst_one_image_eq {n : ℕ} (S : Set (Fin (n + 1) → ℝ)) :
    projFirst n 1 '' S = Fin.init '' S :=
  Set.image_congr (fun x _ => rfl)

theorem projFirst_one_image_eq_finset {n : ℕ} (C : Finset (Set (Fin (n + 1) → ℝ))) :
    C.image (fun c => projFirst n 1 '' c) = C.image (fun c => Fin.init '' c) :=
  Finset.image_congr (fun c _ => projFirst_one_image_eq c)

theorem projFirst_image_comp {n M : ℕ} (A : Set (Fin (n + (M + 1)) → ℝ)) :
    projFirst n M '' (projFirst (n + M) 1 '' A) = projFirst n (M + 1) '' A := by
  rw [Set.image_image]
  exact Set.image_congr (fun x _ => funext fun i => rfl)

theorem projFirst_image_comp_finset {n M : ℕ} (C : Finset (Set (Fin (n + (M + 1)) → ℝ))) :
    (C.image (fun c => projFirst (n + M) 1 '' c)).image (fun c => projFirst n M '' c)
      = C.image (fun c => projFirst n (M + 1) '' c) := by
  rw [Finset.image_image]
  exact Finset.image_congr (fun c _ => projFirst_image_comp (n := n) (M := M) c)

theorem projFirst_cubeC {n M : ℕ} : projFirst n M '' (cubeC (n + M)) = cubeC n := by
  ext y; constructor
  · rintro ⟨x, hx, rfl⟩ i; exact hx (Fin.castAdd M i)
  · intro hy
    refine ⟨padZ (n + M) y, ?_, ?_⟩
    · intro i
      simp only [padZ]
      split
      · rename_i h; exact hy ⟨i.val, h⟩
      · norm_num
    · funext i
      simp only [projFirst, padZ]
      rw [Fin.val_castAdd, dif_pos i.isLt]

/-! ### General facts about `IsCylDecompOn` -/

theorem isCylDecompOn_pairwiseDisjoint (n : ℕ) :
    ∀ {A : Set (Fin n → ℝ)} {C : Finset (Set (Fin n → ℝ))},
      IsCylDecompOn n A C → (C : Set (Set (Fin n → ℝ))).PairwiseDisjoint id := by
  induction n with
  | zero =>
      intro A C h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [Set.pairwiseDisjoint_iff] <;> simp
  | succ n ih => intro A C h; exact h.2.1

theorem isCylDecompOn_cover (n : ℕ) :
    ∀ {A : Set (Fin n → ℝ)} {C : Finset (Set (Fin n → ℝ))},
      IsCylDecompOn n A C → ⋃₀ (C : Set (Set (Fin n → ℝ))) = A := by
  induction n with
  | zero => intro A C h; rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  | succ n ih => intro A C h; exact h.2.2.1

theorem isCylDecompOn_subset (n : ℕ) :
    ∀ {A : Set (Fin n → ℝ)} {C : Finset (Set (Fin n → ℝ))},
      IsCylDecompOn n A C → ∀ c ∈ C, c ⊆ A := by
  intro A C h c hc
  rw [← isCylDecompOn_cover n h]
  exact Set.subset_sUnion_of_mem hc

/-! ### `cylImage` as a set of coordinate projections -/

theorem cylImage_eq_image (n : ℕ) (M : ℕ) : ∀ C : Finset (Set (Fin (n + M) → ℝ)),
    cylImage n M C = C.image (fun c => projFirst n M '' c) := by
  induction M with
  | zero => intro C; rw [cylImage_zero]; exact (projFirst_zero_image_finset (n := n) C).symm
  | succ M ih =>
      intro C
      change cylImage n M (C.image (fun c => projFirst (n + M) 1 '' c)) = _
      rw [ih]
      exact projFirst_image_comp_finset (n := n) (M := M) C

/-! ### Projections of cylindrical decompositions -/

theorem projFirst_one_isCylDecompOn (n : ℕ) {A : Set (Fin (n + 1) → ℝ)}
    {C : Finset (Set (Fin (n + 1) → ℝ))} (h : IsCylDecompOn (n + 1) A C) :
    IsCylDecompOn n (projFirst n 1 '' A) (C.image (fun c => projFirst n 1 '' c)) := by
  rw [projFirst_one_image_eq (n := n) A, projFirst_one_image_eq_finset (n := n) C]
  exact h.2.2.2

theorem projFirst_image_isCylDecompOn (n : ℕ) (M : ℕ) :
    ∀ {A : Set (Fin (n + M) → ℝ)} {C : Finset (Set (Fin (n + M) → ℝ))},
      IsCylDecompOn (n + M) A C →
      IsCylDecompOn n (projFirst n M '' A) (C.image (fun c => projFirst n M '' c)) := by
  induction M with
  | zero => intro A C h; rw [projFirst_zero_image (n := n) A, projFirst_zero_image_finset (n := n) C]; exact h
  | succ M ih =>
      intro A C h
      have h1 := projFirst_one_isCylDecompOn (n + M) h
      have h2 := ih h1
      rw [projFirst_image_comp (n := n) (M := M) A,
        projFirst_image_comp_finset (n := n) (M := M) C] at h2
      exact h2

/-- Two cells of a cylindrical decomposition whose projections meet have equal projections. -/
theorem projFirst_cells_eq_of_inter (n M : ℕ) {A : Set (Fin (n + M) → ℝ)}
    {C : Finset (Set (Fin (n + M) → ℝ))} (h : IsCylDecompOn (n + M) A C)
    {c c' : Set (Fin (n + M) → ℝ)} (hc : c ∈ C) (hc' : c' ∈ C)
    (hne : (projFirst n M '' c ∩ projFirst n M '' c').Nonempty) :
    projFirst n M '' c = projFirst n M '' c' := by
  have hpd := isCylDecompOn_pairwiseDisjoint n (projFirst_image_isCylDecompOn n M h)
  rw [Set.pairwiseDisjoint_iff] at hpd
  exact hpd (Finset.mem_image_of_mem (fun c => projFirst n M '' c) hc)
    (Finset.mem_image_of_mem (fun c => projFirst n M '' c) hc') hne

/-! ### Compatibility is inherited -/

theorem cylImage_compat (n M : ℕ) {C : Finset (Set (Fin (n + M) → ℝ))}
    {Y : Set (Fin (n + M) → ℝ)} (h : IsCylDecompOn (n + M) (cubeC (n + M)) C)
    (hY : Y ⊆ cubeC (n + M)) (hC : ∀ κ ∈ C, κ ⊆ Y ∨ Disjoint κ Y) :
    ∀ κ ∈ cylImage n M C, κ ⊆ projFirst n M '' Y ∨ Disjoint κ (projFirst n M '' Y) := by
  intro κ hκ
  rw [cylImage_eq_image (n := n) M] at hκ
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hκ
  by_cases hd : Disjoint (projFirst n M '' c) (projFirst n M '' Y)
  · exact Or.inr hd
  · refine Or.inl ?_
    rw [Set.not_disjoint_iff] at hd
    obtain ⟨x, hxc, hxY⟩ := hd
    simp only [Set.mem_image] at hxc hxY
    obtain ⟨u, hu, hux⟩ := hxc
    obtain ⟨w, hw, hwx⟩ := hxY
    -- `w` lies in the cube, hence in some cell `c''`, which must be contained in `Y`
    have hwcube : w ∈ cubeC (n + M) := hY hw
    have hwU : w ∈ ⋃₀ (C : Set (Set (Fin (n + M) → ℝ))) := by
      rw [isCylDecompOn_cover (n + M) h]; exact hwcube
    simp only [Set.mem_sUnion] at hwU
    obtain ⟨c'', hc'', hwc''⟩ := hwU
    have hc''Y : c'' ⊆ Y := by
      rcases hC c'' hc'' with hsub | hdisj
      · exact hsub
      · exact absurd hdisj (Set.not_disjoint_iff.mpr ⟨w, hwc'', hw⟩)
    -- `projFirst n M '' c = projFirst n M '' c''`, since `x` lies in both
    have hxcc'' : (projFirst n M '' c ∩ projFirst n M '' c'').Nonempty :=
      ⟨x, by rw [← hux]; exact Set.mem_image_of_mem _ hu,
        by rw [← hwx]; exact Set.mem_image_of_mem _ hwc''⟩
    have heq := projFirst_cells_eq_of_inter n M h hc hc'' hxcc''
    rw [heq]
    rintro y ⟨v, hv, rfl⟩
    exact Set.mem_image_of_mem _ (hc''Y hv)

/-! ### The target statement -/

theorem cylImage_props :
    (∀ {n M : ℕ} {C : Finset (Set (Fin (n + M) → ℝ))},
        WilkiesDesign.E.IsCylDecompOn (n + M) (WilkiesDesign.E.cubeC (n + M)) C →
        WilkiesDesign.E.IsCylDecompOn n (WilkiesDesign.E.cubeC n) (Work.WilE7.cylImage n M C)) ∧
    (∀ {n M : ℕ} {C : Finset (Set (Fin (n + M) → ℝ))} {Y : Set (Fin (n + M) → ℝ)},
        WilkiesDesign.E.IsCylDecompOn (n + M) (WilkiesDesign.E.cubeC (n + M)) C →
        Y ⊆ WilkiesDesign.E.cubeC (n + M) →
        (∀ κ ∈ C, κ ⊆ Y ∨ Disjoint κ Y) →
        ∀ κ ∈ Work.WilE7.cylImage n M C,
          κ ⊆ WilkiesDesign.E.projFirst n M '' Y ∨
            Disjoint κ (WilkiesDesign.E.projFirst n M '' Y)) ∧
    (∀ {n M : ℕ} {C : Finset (Set (Fin (n + M) → ℝ))} {κ : Set (Fin n → ℝ)},
        κ ∈ Work.WilE7.cylImage n M C ↔ ∃ c ∈ C, WilkiesDesign.E.projFirst n M '' c = κ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n M C h
    rw [cylImage_eq_image (n := n) M, ← projFirst_cubeC (n := n) (M := M)]
    exact projFirst_image_isCylDecompOn n M h
  · intro n M C Y h hY hC
    exact cylImage_compat n M h hY hC
  · intro n M C κ
    rw [cylImage_eq_image (n := n) M, Finset.mem_image]

end Work.WilE7
