import Mathlib
import Submission.Work.KT.Fund.Clutch

/-!
# `Work.KT.Fund.graphProj_block_defs`

General-shape versions of `graphB` and `orthProj`.

`Work.KT.Fund.graphB`/`Work.KT.Fund.orthProj` are only available when the index set is literally
`Fin n`, which is too rigid to even *state* the block decomposition of a `graphProj` along the
shuffle `blkEquiv n k : (Fin n ⊕ Fin n) ⊕ (Fin k ⊕ Fin k) ≃ Fin (n + k) ⊕ Fin (n + k)`.
The declarations below remove that restriction, so that the block decomposition can be phrased as
a composite of general facts about `Matrix.reindex` and about block diagonal matrices.
-/

namespace Work.KT.Fund

open Matrix

noncomputable section

/-- The block vector `[[1],[F]]` attached to a square matrix on a general index type.  The
special case `κ = Fin n` is `Work.KT.Fund.graphB`. -/
def graphBGen (R : Type*) [Zero R] [One R] {κ : Type*} [DecidableEq κ]
    (F : Matrix κ κ R) : Matrix (κ ⊕ κ) κ R :=
  fun i j => match i with
    | Sum.inl a => if a = j then 1 else 0
    | Sum.inr a => F a j

/-- The orthogonal projection onto the image of a general `ρ × κ` matrix:
`B * (Bᴴ * B)⁻¹ * Bᴴ`.  The special case `ρ = Fin n ⊕ Fin n`, `κ = Fin n` is
`Work.KT.Fund.orthProj`. -/
def orthProjGen (R : Type*) [CommRing R] [Star R] {ρ κ : Type*} [Fintype ρ] [Fintype κ]
    [DecidableEq κ] (B : Matrix ρ κ R) : Matrix ρ ρ R :=
  B * Ring.inverse (Matrix.conjTranspose B * B) * Matrix.conjTranspose B

@[simp] lemma graphBGen_eq_graphB (R : Type) [Ring R] {n : ℕ} (F : Matrix (Fin n) (Fin n) R) :
    graphBGen R F = graphB R F := by
  ext i j
  rcases i with a | a <;> simp [graphBGen, graphB]

@[simp] lemma orthProjGen_eq_orthProj (R : Type) [CommRing R] [Star R] {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n) R) :
    orthProjGen R B = orthProj R B := by
  simp only [orthProjGen, orthProj]

lemma graphProj_eq_orthProjGen (R : Type) [CommRing R] [Star R] {n : ℕ}
    (F : Matrix (Fin n) (Fin n) R) :
    graphProj R F = orthProjGen R (graphBGen R F) := by
  rw [graphProj, ← graphBGen_eq_graphB R F]
  exact (orthProjGen_eq_orthProj R (graphBGen R F)).symm

end

end Work.KT.Fund
