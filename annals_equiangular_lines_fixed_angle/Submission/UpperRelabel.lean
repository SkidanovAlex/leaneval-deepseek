import Submission.Components
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

open EquiangularLinesFixedAngle
open Matrix
open scoped BigOperators

namespace Submission

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

noncomputable section

/-! Spectral-radius invariance under relabelling (used to connect component spectral data to
the `spectralRadiusOrder` of graphs on `Fin k`). -/

/-- equal characteristic polynomials give equal real spectra (index types may differ). -/
lemma spectrum_eq_of_charpoly {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    [DecidableEq ι'] {A : Matrix ι ι ℝ} {B : Matrix ι' ι' ℝ} (hch : A.charpoly = B.charpoly) :
    spectrum ℝ A = spectrum ℝ B := by
  classical
  ext μ
  constructor
  · intro hμ
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hμ ⊢
    rwa [hch] at hμ
  · intro hμ
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hμ ⊢
    rwa [← hch] at hμ

/-- equal characteristic polynomials give equal spectral radii (index types may differ). -/
lemma spectralRadius_eq_of_charpoly {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    [DecidableEq ι'] {A : Matrix ι ι ℝ} {B : Matrix ι' ι' ℝ} (hch : A.charpoly = B.charpoly) :
    spectralRadius ℝ A = spectralRadius ℝ B := by
  classical
  unfold spectralRadius
  rw [spectrum_eq_of_charpoly hch]

/-- the spectral radius is invariant under relabelling (reindexing) the index type. -/
lemma spectralRadius_reindex {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    [DecidableEq ι'] (e : ι ≃ ι') (A : Matrix ι ι ℝ) :
    spectralRadius ℝ (reindex e e A) = spectralRadius ℝ A := by
  classical
  exact spectralRadius_eq_of_charpoly (Matrix.charpoly_reindex e A)

/-- graph pullback along an equivalence: adjacency matrix is the reindexed one. -/
lemma adjMatrix_comap_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (G : SimpleGraph ι) [DecidableRel G.Adj] (e : ι ≃ ι') :
    (G.comap e.symm).adjMatrix ℝ = reindex e e (G.adjMatrix ℝ) := by
  classical
  ext i j
  rfl

/-- the spectral radius of a graph is invariant under relabelling. -/
lemma spectralRadius_comap {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    [DecidableEq ι'] (G : SimpleGraph ι) [DecidableRel G.Adj] (e : ι ≃ ι') :
    spectralRadius ℝ ((G.comap e.symm).adjMatrix ℝ) = spectralRadius ℝ (G.adjMatrix ℝ) := by
  classical
  rw [adjMatrix_comap_equiv]
  exact spectralRadius_reindex e (G.adjMatrix ℝ)

/-- any graph whose adjacency has spectral radius `lam0` witnesses that `spectralRadiusOrder`
is at most the number of vertices. -/
lemma spectralRadiusOrder_le_card {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) {lam0 : ℝ} (hρ : spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal lam0) :
    spectralRadiusOrder lam0 ≤ (Fintype.card ι : ℕ∞) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hρ' : spectralRadius ℝ ((G.comap e.symm).adjMatrix ℝ) = ENNReal.ofReal lam0 := by
    rw [spectralRadius_comap G e]
    exact hρ
  change spectralRadiusOrder lam0 ≤ (Fintype.card ι : ℕ∞)
  rw [spectralRadiusOrder]
  exact iInf₂_le (Fintype.card ι) ⟨G.comap e.symm, hρ'⟩

/-- if the spectral radius order is finite, its value is at most any witnessing cardinal. -/
lemma spectralRadiusOrder_toNat_le_card {ι : Type*} [Fintype ι]
    {lam0 : ℝ} (G : SimpleGraph ι)
    (hρ : spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal lam0) :
    (spectralRadiusOrder lam0).toNat ≤ Fintype.card ι := by
  classical
  have hle : spectralRadiusOrder lam0 ≤ (Fintype.card ι : ℕ∞) := spectralRadiusOrder_le_card G hρ
  exact ENat.toNat_le_toNat hle (ne_of_lt (WithTop.coe_lt_top (Fintype.card ι)))

end
end Submission
