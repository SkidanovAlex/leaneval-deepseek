import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

set_option linter.style.haveILetI false

namespace Commons.LinearAlgebra.Matrix

/-- If the subspace spanned by the family `v : ι → V` has dimension at least `k`,
then some `k` of the vectors are linearly independent (picked via an embedding of `Fin k`). -/
lemma exists_linearIndependent_comp_fin {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] {ι : Type*} [Fintype ι] (v : ι → V) {k : ℕ}
    (h : k ≤ Module.finrank K (Submodule.span K (Set.range v))) :
    ∃ e : Fin k ↪ ι, LinearIndependent K (v ∘ e) := by
  classical
  obtain ⟨κ, a, hainj, hspan, hli⟩ := exists_linearIndependent' K v
  letI : Finite κ := Finite.of_injective a hainj
  letI : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ = Module.finrank K (Submodule.span K (Set.range (v ∘ a))) := by
    simpa [Set.finrank] using (linearIndependent_iff_card_eq_finrank_span.mp hli)
  have hcard : Fintype.card κ = Module.finrank K (Submodule.span K (Set.range v)) := by
    rw [hspan] at hc
    exact hc
  have hkle : k ≤ Fintype.card κ := hcard ▸ h
  let eκ : Fin k → κ := (Fintype.equivFin κ).symm ∘ Fin.castLE hkle
  have hκinj : Function.Injective eκ := by
    dsimp [eκ]
    exact (Equiv.injective (Fintype.equivFin κ).symm).comp (Fin.castLE_injective hkle)
  refine ⟨⟨a ∘ eκ, hainj.comp hκinj⟩, ?_⟩
  simpa [Function.comp_assoc] using hli.comp eκ hκinj

/-- A matrix of rank at least `k` has a `k × k` submatrix with nonzero determinant:
choose `k` linearly independent columns, then `k` linearly independent rows from them. -/
theorem exists_det_ne_zero_of_rank_ge {m n k : ℕ} {K : Type*} [Field K]
    (A : Matrix (Fin m) (Fin n) K) (h : k ≤ A.rank) :
    ∃ (e : Fin k ↪ Fin m) (f : Fin k ↪ Fin n), (A.submatrix e f).det ≠ 0 := by
  classical
  -- the column space of `A` has dimension at least `k`
  have hcol : k ≤ Module.finrank K (Submodule.span K (Set.range A.col)) := by
    simpa [Matrix.rank_eq_finrank_span_cols] using h
  obtain ⟨f, hfcol⟩ := exists_linearIndependent_comp_fin A.col hcol
  -- `P` keeps only the `k` independent columns
  let P : Matrix (Fin m) (Fin k) K := A.submatrix (id : Fin m → Fin m) f
  have hPcol : LinearIndependent K P.col := by
    have hfam : (A.submatrix (id : Fin m → Fin m) f).col = A.col ∘ f := by
      ext i j
      simp [Matrix.col_apply]
    simpa [P, hfam] using hfcol
  have hPrk : P.rank = k := by
    rw [Matrix.rank_eq_finrank_span_cols]
    have hc : Fintype.card (Fin k) = Set.finrank K (Set.range P.col) := by
      simpa using (linearIndependent_iff_card_eq_finrank_span.mp hPcol)
    change Set.finrank K (Set.range P.col) = k
    simpa using hc.symm
  -- so the row space of `P` also has dimension `k`
  have hrow : k ≤ Module.finrank K (Submodule.span K (Set.range P.row)) := by
    rw [← Matrix.rank_eq_finrank_span_row P]
    simp [hPrk]
  obtain ⟨e, herow⟩ := exists_linearIndependent_comp_fin P.row hrow
  -- `Q` is the square submatrix with the chosen independent rows
  let Q : Matrix (Fin k) (Fin k) K := P.submatrix e (id : Fin k → Fin k)
  have hQrow : LinearIndependent K Q.row := by
    have hfam : (P.submatrix e (id : Fin k → Fin k)).row = P.row ∘ e := by
      ext i j
      simp [Matrix.row_apply]
    simpa [Q, hfam] using herow
  have hQunit : IsUnit Q := Matrix.linearIndependent_rows_iff_isUnit.mp hQrow
  have hQdet : Q.det ≠ 0 := by
    have hu := (Matrix.isUnit_iff_isUnit_det Q).mp hQunit
    exact (isUnit_iff_ne_zero.mp hu)
  refine ⟨e, f, ?_⟩
  have hQeq : A.submatrix e f = Q := by
    simp [Q, P, Matrix.submatrix_submatrix]
  rwa [hQeq]

end Commons.LinearAlgebra.Matrix