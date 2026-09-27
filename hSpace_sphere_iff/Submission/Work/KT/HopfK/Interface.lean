/-
# Interface lemmas for the final assembly of `hopf_K`

Small plumbing between the mapping-cone algebra `coneAlg f`, its cell component (the "h-part")
and the disk-side `W`-construction of `Submission.Work.KT.HopfK.Disk`.
-/
import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.HopfK.Basic
import Submission.Work.KT.HopfK.Disk

namespace Work.KT.HopfK

open _root_.Matrix

noncomputable section

/-- The cell part of a matrix over the mapping cone `coneAlg f`: the component in
`C(Ball (Eu m × Eu m), ℂ)`. -/
abbrev coneCell {m : ℕ} {n : ℕ} (f : C(Sph (Eu m × Eu m), Tgt m))
    (p : Matrix (Fin n) (Fin n) (coneAlg f)) :
    Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)) :=
  p.map ((AlgHom.snd ℂ C(Tgt m, ℂ) C(Ball (Eu m × Eu m), ℂ)).comp (coneAlg f).val).toRingHom

@[simp] lemma coneCell_apply {m n : ℕ} (f : C(Sph (Eu m × Eu m), Tgt m))
    (p : Matrix (Fin n) (Fin n) (coneAlg f)) (i j : Fin n) :
    coneCell f p i j = ((p i j : coneAlg f) : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)).2 := rfl

/-- Evaluation of the cell part of `p` at a point of the ball. -/
@[simp] lemma coneCell_apply_apply {m n : ℕ} (f : C(Sph (Eu m × Eu m), Tgt m))
    (p : Matrix (Fin n) (Fin n) (coneAlg f)) (i j : Fin n) (z : Ball (Eu m × Eu m)) :
    coneCell f p i j z = ((p i j : coneAlg f) : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)).2 z := rfl

lemma coneCell_mul_apply {m n : ℕ} (f : C(Sph (Eu m × Eu m), Tgt m))
    (p : Matrix (Fin n) (Fin n) (coneAlg f)) (z : Ball (Eu m × Eu m)) :
    (coneCell f p).map (evalC z) = p.map (evalD m f z) := by
  rw [Matrix.map_map]
  ext i j
  rfl

/-- `evalD` is the evaluation of the cell part. -/
lemma map_evalD_eq_coneCell_map_evalC {m n : ℕ} (f : C(Sph (Eu m × Eu m), Tgt m))
    (p : Matrix (Fin n) (Fin n) (coneAlg f)) (z : Ball (Eu m × Eu m)) :
    p.map (evalD m f z).toRingHom = (coneCell f p).map (evalC z).toRingHom := rfl

lemma coneCell_mul {m n : ℕ} (f : C(Sph (Eu m × Eu m), Tgt m))
    (p q : Matrix (Fin n) (Fin n) (coneAlg f)) :
    coneCell f (p * q) = coneCell f p * coneCell f q :=
  Matrix.map_mul

lemma coneCell_one {m n : ℕ} (f : C(Sph (Eu m × Eu m), Tgt m)) :
    coneCell f (1 : Matrix (Fin n) (Fin n) (coneAlg f)) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

/-- The cell part of the constant diagonal idempotent `diag(1_r,0)`. -/
lemma coneCell_coneDiag (m r n : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) :
    coneCell f (coneDiag m f r n).2
      = matConst (C(Ball (Eu m × Eu m), ℂ)) (diagIdemMat r n) := by
  ext i j z
  rw [coneCell, Matrix.map_apply]
  by_cases h : i = j
  · subst h
    by_cases hr : (i : ℕ) < r
    · simp [coneDiag, Matrix.diagonal_apply, matConst, diagIdemMat, hr]
    · simp [coneDiag, Matrix.diagonal_apply, matConst, diagIdemMat, hr]
  · simp [coneDiag, Matrix.diagonal_apply, matConst, diagIdemMat, h]

end

end Work.KT.HopfK
