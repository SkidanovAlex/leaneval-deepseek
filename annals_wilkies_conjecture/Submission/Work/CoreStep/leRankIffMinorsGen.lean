import Mathlib

/-!
# Rank vs. nonzero minors, general index type

For a matrix `A : Matrix ι (Fin N) ℝ` with `ι` an arbitrary finite type, the rank of `A` is at
least `k` if and only if `A` has a `k × k` submatrix with nonzero determinant.

The key linear-algebra input is `exists_injective_linearIndependent_sub_gen`: a finite family of
vectors spanning a space of dimension `≥ k` contains `k` linearly independent members.
-/

namespace Work.CoreStep

open Function Submodule

/-- A family of vectors `v : α → M` spanning a space of dimension at least `k` contains
`k` linearly independent members. -/
lemma exists_injective_linearIndependent_sub_gen {K : Type*} [Field K] {M : Type*}
    [AddCommGroup M] [Module K M] {α : Type*} [Fintype α] {k : ℕ} (v : α → M)
    (h : k ≤ Module.finrank K (Submodule.span K (Set.range v))) :
    ∃ τ : Fin k ↪ α, LinearIndependent K (v ∘ (τ : Fin k → α)) := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K v
  have hFin : Finite κ := Finite.of_injective a ha
  have hFintype : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = Module.finrank K (Submodule.span K (Set.range v)) := by
    rw [← hspan]
    exact (finrank_span_eq_card hli).symm
  have hk : k ≤ Fintype.card κ := by rw [hcard]; exact h
  obtain ⟨t, -, htc⟩ := Finset.exists_subset_card_eq (s := Finset.univ) (by simpa using hk)
  set g : Fin k → κ := fun i => ((Finset.equivFinOfCardEq htc).symm i : κ) with hg
  have hg_inj : Injective g := by
    intro i j hij
    exact (Finset.equivFinOfCardEq htc).symm.injective (Subtype.ext hij)
  refine ⟨⟨a ∘ g, ha.comp hg_inj⟩, ?_⟩
  have := hli.comp g hg_inj
  simpa [Function.comp_assoc] using this

theorem leRankIffMinorsGen {ι : Type*} [Fintype ι] {N k : ℕ} (A : Matrix ι (Fin N) ℝ) :
    k ≤ A.rank ↔
      ∃ (σ : Fin k ↪ ι) (τ : Fin k ↪ Fin N), (A.submatrix σ τ).det ≠ 0 := by
  constructor
  · intro h
    -- Pick `k` linearly independent columns of `A`; call the resulting matrix `B`.
    have hcols : k ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range A.col)) := by
      rw [← Matrix.rank_eq_finrank_span_cols]; exact h
    obtain ⟨τ, hτli⟩ := exists_injective_linearIndependent_sub_gen A.col hcols
    set B : Matrix ι (Fin k) ℝ := A.submatrix id (τ : Fin k → Fin N) with hB
    have hBcol : B.col = A.col ∘ τ := by rw [hB]; rfl
    have hli : LinearIndependent ℝ B.col := by rw [hBcol]; exact hτli
    -- `B` has full column rank `k`.
    have hinj : Function.Injective (B.mulVecLin : (Fin k → ℝ) → (ι → ℝ)) := by
      have h2 := (Matrix.mulVec_injective_iff (M := B)).mpr hli
      simpa [Matrix.coe_mulVecLin] using h2
    have hBrank : B.rank = k := by
      rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj,
        Module.finrank_eq_card_basis (Pi.basisFun ℝ (Fin k)), Fintype.card_fin]
    -- Hence the rows of `B` span `ℝ^k`, and we can pick `k` independent ones.
    have hBtr : k ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range B.row)) := by
      rw [← Matrix.rank_eq_finrank_span_row, hBrank]
    obtain ⟨σ, hσli⟩ := exists_injective_linearIndependent_sub_gen B.row hBtr
    refine ⟨σ, τ, ?_⟩
    have hrow : LinearIndependent ℝ ((B.submatrix σ id).row) := by
      have hrow_eq : (B.submatrix σ id).row = B.row ∘ (σ : Fin k → ι) := rfl
      rw [hrow_eq]; exact hσli
    have hunit : IsUnit (B.submatrix σ id) :=
      Matrix.linearIndependent_rows_iff_isUnit.mp hrow
    have hdet : (B.submatrix σ id).det ≠ 0 := by
      rw [← isUnit_iff_ne_zero]
      exact (Matrix.isUnit_iff_isUnit_det _).mp hunit
    have hEq : B.submatrix σ id = A.submatrix σ τ := by
      rw [hB, Matrix.submatrix_submatrix]
      simp
    rw [← hEq]
    exact hdet
  · rintro ⟨σ, τ, hdet⟩
    -- A nonsingular `k × k` submatrix has rank `k`, hence `A` has rank at least `k`.
    have h1 : (A.submatrix σ τ).rank = k := by
      rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin]
    have h2 : (A.submatrix σ τ).rank ≤ A.rank := Matrix.rank_submatrix_le A σ τ
    rw [h1] at h2
    exact h2

end Work.CoreStep
