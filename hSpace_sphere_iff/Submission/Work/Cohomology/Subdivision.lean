/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The barycentric subdivision of the standard simplex

This file starts the development of the *small-simplex* (Mayer–Vietoris) theorem for singular
cohomology.  The key device is the barycentric subdivision operator on singular chains.

A *piece* of the subdivision of `Δⁿ` is encoded by its list of vertices
(`Piece n m := Fin (m+1) → TSimplex n`: a piece of dimension `m`), and converted into a singular
simplex by `affineSimplex` (`SimplexGeom.lean`).  The reason for this encoding is that the face
formula `(affineSimplex q) ∘ δᵢ = affineSimplex (q ∘ Fin.succAbove i)` holds for the *vertex
lists*, so that the faces of a piece are again given by vertex lists — this is what makes the
recursion `sd (n+1) = ∑ᵢ (-1)ⁱ cone (barycentre) (push δᵢ (sd n))` go through.

* `conePiece b q`: prepend the vertex `b` (the "cone" over a piece);
* `facePiece q i`: the `i`-th face of a piece;
* `facePiece_conePiece_zero`, `facePiece_conePiece_succ`: the faces of a cone.

`facePiece_conePiece_succ` is a pure `Fin`-index computation (Mathlib's
`Fin.cons_comp_succ_succAbove` does it).  Everything downstream (`conePiece_faces`: `∂ ∘ cone = id - cone ∘ ∂`
on pieces, then the subdivision chains `sdPieces`/`sdChain` and the chain-map property
`∂ ∘ sd = sd ∘ ∂`) is routine from the two face lemmas.
-/
import Mathlib
import Submission.Work.Cohomology.SimplexGeom

open CategoryTheory Simplicial Opposite

namespace Submission.Cohomology

noncomputable section

/-- A piece of a subdivision of `Δⁿ` of dimension `m`: its list of vertices. -/
abbrev Piece (n m : ℕ) : Type := Fin (m+1) → TSimplex n

/-- The `i`-th face of a piece: drop the `i`-th vertex. -/
def facePiece {n m : ℕ} (q : Piece n (m+1)) (i : Fin (m+2)) : Piece n m :=
  q ∘ Fin.succAbove i

/-- The cone over a piece with apex `b`: prepend `b` to the vertex list. -/
def conePiece {n m : ℕ} (b : TSimplex n) (q : Piece n m) : Piece n (m+1) :=
  Fin.cases b q

@[simp] lemma conePiece_zero {n m : ℕ} (b : TSimplex n) (q : Piece n m) :
    conePiece b q 0 = b := rfl

@[simp] lemma conePiece_succ {n m : ℕ} (b : TSimplex n) (q : Piece n m) (j : Fin (m+1)) :
    conePiece b q j.succ = q j := rfl

/-- The `0`-th face of the cone is the original piece. -/
lemma facePiece_conePiece_zero {n m : ℕ} (b : TSimplex n) (q : Piece n (m+1)) :
    facePiece (conePiece b q) (0 : Fin (m+3)) = q := by
  funext t
  have hs : (Fin.succAbove (0 : Fin (m+3)) t : Fin (m+3)) = t.succ :=
    Fin.succAbove_of_le_castSucc 0 t (by simp)
  simp only [facePiece, Function.comp_apply, hs, conePiece_succ]

/-- The faces of the cone: for `i ≥ 1` it is the cone over the corresponding face.

TODO (next session): this is a pure `Fin`-index computation.  The ingredients are
`Fin.succAbove_of_castSucc_lt` / `Fin.succAbove_of_le_castSucc` (translate the value of
`succAbove`), `Fin.castSucc_succ` / `Fin.succ_castSucc` (so that `Fin.cases` reduces) and
`conePiece_zero` / `conePiece_succ`.  The two cases to split on are `j < s` and `s ≤ j`
(and in the latter, `s = j` versus `s < j`). -/
lemma facePiece_conePiece_succ {n m : ℕ} (b : TSimplex n) (q : Piece n (m+1))
    (j : Fin (m+2)) :
    facePiece (conePiece b q) (j.succ : Fin (m+3)) = conePiece b (facePiece q j) := by
  show (conePiece b q ∘ Fin.succAbove (j.succ : Fin (m+3)))
      = conePiece b (q ∘ Fin.succAbove j)
  rw [show (conePiece b q : Fin (m+3) → TSimplex n) = Fin.cons b q from rfl]
  rw [Fin.cons_comp_succ_succAbove]
  rfl

end

end Submission.Cohomology
