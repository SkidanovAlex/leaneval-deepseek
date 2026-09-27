import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.cubeAux
import Submission.Work.KT.Psi.k3Aux
import Submission.Work.KT.Psi.cubeMvNAux

/-!
# `Work.KT.Psi.cubePart_conj`

The two non-trivial isotypic components of the cyclic permutation on `p ⊗ p ⊗ p` have the same
class in `K₀`:

`cls (cubePart omega p) = cls (cubePart (omega ^ 2) p)`.

The reason is that the flip `(i, j, k) ↦ (j, i, k)` of the first two tensor factors conjugates the
cyclic permutation `c` into its square, hence carries the `ω`-projector `(1 + ω⁻¹c + ω⁻²c²)/3`
into the `ω²`-projector.  This is `Work.KT.Psi.K3.cubePartP_conj`; the remaining step is that a
permutation of the index set does not change the class of a matrix in `K₀`, which is
`cls_reindex_perm_gen` below (no idempotency hypothesis is needed for that).
-/

namespace Work.KT.Psi

open Matrix

/-! ## Reindexing by a permutation does not change the class -/

/-- The class of a square matrix is unchanged by a permutation of its index set.  No idempotency
hypothesis is needed: for an idempotent this is `cls_reindex_perm`, and a non-idempotent matrix
stays non-idempotent under reindexing, so both classes vanish. -/
theorem cls_reindex_perm_gen {R : Type} [Ring R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (τ : Equiv.Perm (Fin n)) :
    cls (⟨n, M⟩ : Mat R) = cls (⟨n, Matrix.reindex τ τ M⟩ : Mat R) := by
  by_cases hM : M * M = M
  · exact cls_reindex_perm R M hM τ
  · have hback : Matrix.reindex τ.symm τ.symm (Matrix.reindex τ τ M) = M := by
      rw [reindex_reindex, Equiv.self_trans_symm]
      rfl
    have h2 : Matrix.reindex τ.symm τ.symm
        (Matrix.reindex τ τ M * Matrix.reindex τ τ M) = M * M := by
      rw [reindex_mul_self, hback]
    have hre : ¬ (Matrix.reindex τ τ M * Matrix.reindex τ τ M = Matrix.reindex τ τ M) := by
      intro h
      have h' := congrArg (Matrix.reindex τ.symm τ.symm) h
      rw [h2, hback] at h'
      exact hM h'
    rw [cls_zero_of_not_idem (p := (⟨n, M⟩ : Mat R)) hM,
      cls_zero_of_not_idem (p := (⟨n, Matrix.reindex τ τ M⟩ : Mat R)) hre]

/-! ## The flip of the first two tensor factors, in `Fin (n * n * n)` coordinates -/

/-- The flip of the first two tensor factors of the triple tensor power, transported from
`(Fin n × Fin n) × Fin n` to `Fin (n * n * n)` along `cycIdx n`. -/
def flipIdx (n : ℕ) : Equiv.Perm (Fin (n * n * n)) :=
  (cycIdx n).trans ((K3.FL n).trans (cycIdx n).symm)

/-- Conjugating by the flip commutes with the transport along `cycIdx`. -/
theorem flipIdx_trans (n : ℕ) :
    (cycIdx n).symm.trans (flipIdx n) = (K3.FL n).trans (cycIdx n).symm := by
  ext x
  simp [flipIdx, Equiv.trans_apply]

/-- Reindexing by the transported flip, expressed through the untransported one. -/
theorem reindex_flipIdx_reindex {A : Type} [Ring A] {n : ℕ}
    (M : Matrix ((Fin n × Fin n) × Fin n) ((Fin n × Fin n) × Fin n) A) :
    Matrix.reindex (flipIdx n) (flipIdx n)
        (Matrix.reindex (cycIdx n).symm (cycIdx n).symm M) =
      Matrix.reindex (cycIdx n).symm (cycIdx n).symm
        (Matrix.reindex (K3.FL n) (K3.FL n) M) := by
  rw [reindex_reindex (e₁ := (cycIdx n).symm) (e₂ := flipIdx n), flipIdx_trans n,
    ← reindex_reindex (e₁ := K3.FL n) (e₂ := (cycIdx n).symm)]

/-! ## The main lemma -/

theorem cubePart_conj {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    {p : Mat A} (hp : p.IsIdem) :
    cls (cubePart omega p) = cls (cubePart (omega ^ 2) p) := by
  have hstep : cls (⟨p.1 * p.1 * p.1,
        Matrix.reindex (cycIdx p.1).symm (cycIdx p.1).symm (cubePartP omega p)⟩ : Mat A) =
      cls (⟨p.1 * p.1 * p.1,
        Matrix.reindex (flipIdx p.1) (flipIdx p.1)
          (Matrix.reindex (cycIdx p.1).symm (cycIdx p.1).symm (cubePartP omega p))⟩ : Mat A) :=
    cls_reindex_perm_gen _ (flipIdx p.1)
  have hcomp := reindex_flipIdx_reindex (n := p.1) (cubePartP omega p)
  rw [cubePart_eq omega p, hstep, hcomp, K3.cubePartP_conj hA p,
    ← cubePart_eq (omega ^ 2) p]

end Work.KT.Psi
