import Submission.Work.WilkiesH.Defs

/-!
# Area H (counting) — basic API for `Set.alg`, `Set.trans`, `DimLE`, `degreeHeightLE`

Elementary consequences of the frozen vocabulary of `Work.Wilkies.Defs` that
the counting argument uses everywhere.  Nothing here is specific to the
interpolation step.
-/

set_option autoImplicit false
noncomputable section

open Classical

namespace Work.WilkiesH

open WilkiesDesign WilkiesConjecture

/-! ## The algebraic part `X.alg` and the transcendental part `X.trans` -/

theorem mem_alg_iff {n : ℕ} {X : Set (Fin n → ℝ)} {x : Fin n → ℝ} :
    x ∈ X.alg ↔ ∃ Y : Set (Fin n → ℝ),
      Y ⊆ X ∧ IsSemialgebraic Y ∧ Y.Infinite ∧ IsConnected Y ∧ x ∈ Y := by
  have h : x ∈ X.alg ↔ ∃ Y ∈ {Y : Set (Fin n → ℝ) |
      Y ⊆ X ∧ IsSemialgebraic Y ∧ Y.Infinite ∧ IsConnected Y}, x ∈ Y := by
    rw [Set.alg, Set.sSup_eq_sUnion, Set.mem_sUnion]
  rw [h]
  constructor
  · rintro ⟨Y, ⟨h1, h2, h3, h4⟩, hx⟩
    exact ⟨Y, h1, h2, h3, h4, hx⟩
  · rintro ⟨Y, h1, h2, h3, h4, hx⟩
    exact ⟨Y, ⟨h1, h2, h3, h4⟩, hx⟩

theorem alg_subset {n : ℕ} (X : Set (Fin n → ℝ)) : X.alg ⊆ X := by
  intro x hx
  obtain ⟨Y, hYX, -, -, -, hxY⟩ := mem_alg_iff.mp hx
  exact hYX hxY

theorem alg_mono {n : ℕ} {X Y : Set (Fin n → ℝ)} (h : X ⊆ Y) : X.alg ⊆ Y.alg := by
  intro x hx
  obtain ⟨Z, hZX, hZ1, hZ2, hZ3, hxZ⟩ := mem_alg_iff.mp hx
  exact mem_alg_iff.mpr ⟨Z, hZX.trans h, hZ1, hZ2, hZ3, hxZ⟩

/-- Any connected infinite semialgebraic subset of `X` is contained in `X.alg`. -/
theorem subset_alg_of_semialg {n : ℕ} {Y X : Set (Fin n → ℝ)} (hYX : Y ⊆ X)
    (hY : IsSemialgebraic Y) (hYinf : Y.Infinite) (hYc : IsConnected Y) : Y ⊆ X.alg :=
  fun x hx => mem_alg_iff.mpr ⟨Y, hYX, hY, hYinf, hYc, hx⟩

theorem mem_trans_iff {n : ℕ} {X : Set (Fin n → ℝ)} {x : Fin n → ℝ} :
    x ∈ X.trans ↔ x ∈ X ∧ x ∉ X.alg := Iff.rfl

theorem trans_subset {n : ℕ} (X : Set (Fin n → ℝ)) : X.trans ⊆ X := fun _ hx => hx.1

theorem trans_eq_compl_alg {n : ℕ} (X : Set (Fin n → ℝ)) : X.trans = X \ X.alg := rfl

theorem trans_union_alg {n : ℕ} (X : Set (Fin n → ℝ)) : X.trans ∪ X.alg = X := by
  refine Set.Subset.antisymm (Set.union_subset (trans_subset X) (alg_subset X)) fun x hx =>
    (Classical.em (x ∈ X.alg)).elim (fun h => Or.inr h) (fun h => Or.inl ⟨hx, h⟩)

/-! ## `DimLE` -/

theorem dimLE_top {n : ℕ} (X : Set (Fin n → ℝ)) : DimLE X n := fun e =>
  absurd (Fintype.card_le_of_injective e e.injective) (by simp)

theorem dimLE_of_subset {n μ : ℕ} {Y X : Set (Fin n → ℝ)} (h : DimLE X μ) (hYX : Y ⊆ X) :
    DimLE Y μ := fun e => by
  rw [← Set.subset_empty_iff]
  exact (interior_mono (Set.image_mono hYX)).trans_eq (h e)

/-! ## `degreeHeightLE` -/

theorem degreeHeightLE_mono {n : ℕ} {X Y : Set (Fin n → ℝ)} (h : X ⊆ Y) (g H : ℕ) :
    degreeHeightLE X g H ⊆ degreeHeightLE Y g H :=
  fun x hx => ⟨h hx.1, hx.2⟩

theorem degreeHeightLE_mono_H {n : ℕ} (X : Set (Fin n → ℝ)) {g H H' : ℕ} (h : H ≤ H') :
    degreeHeightLE X g H ⊆ degreeHeightLE X g H' :=
  fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.trans (Nat.cast_le.mpr h)⟩

theorem degreeHeightLE_mono_g {n : ℕ} (X : Set (Fin n → ℝ)) {g g' H : ℕ} (h : g ≤ g') :
    degreeHeightLE X g H ⊆ degreeHeightLE X g' H :=
  fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.1.trans (Nat.cast_le.mpr h), hx.2.2.2⟩

theorem mem_degreeHeightLE_iff {n : ℕ} {X : Set (Fin n → ℝ)} {g H : ℕ} {x : Fin n → ℝ} :
    x ∈ degreeHeightLE X g H ↔ x ∈ X ∧ (∀ i, IsIntegral ℚ (x i)) ∧
      Module.finrank ℚ (IntermediateField.adjoin ℚ (Set.range x)) ≤ g ∧ height x ≤ H :=
  Iff.rfl

end Work.WilkiesH
