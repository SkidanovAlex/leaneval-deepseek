import Mathlib
import Submission.Work.Idx.WPenBlk
import Submission.Work.Idx.WPenPsi
import Submission.Work.Idx.WPenRes
import Submission.Work.Idx.WPenAppendDefs
import Submission.Work.KT.Basic
import Submission.Work.Idx.penProj_idem

/-!
# `Work.Idx.WPenEndgame` — the K-theoretic endgame of `wPen_prepend`

Given the structural comparison of the two companion pencils
(`Work.Idx.blkPenProj_preSeq_blocks`: the restriction of the projection of the `(d+2)`-block
pencil of `preSeq X b` to the first `d+1` blocks is the projection of the `(d+1)`-block pencil of
`b` plus the correction `U = wUpdate n d b (wPsi X n d b)`), and the orthogonality
`U * Pb = 0` (proved separately from the explicit resolvent), the class identity
`cls Pbig = cls Pb + cls ⟨n,1⟩` follows by assembling Murray–von Neumann equivalences:

* the restriction of `Pbig` to the first `d+1` blocks is MvN to `Pbig` itself (the last block
  column of `Pbig` vanishes: `A = wBA` has vanishing last block column, so the same holds for the
  integrand and for the integral);
* `M = Pb + U` is MvN to the block diagonal of `Pb` and `U` (orthogonal idempotents);
* `U = wCol · wRow` is MvN to `1` (`wRow · wCol = 1` is the Fourier relation `wRow_wPsi`).

The statements are phrased with `MvNGen` for matrices on arbitrary finite index types
(`Submission/Work/Idx/WPenAppendDefs.lean`) and converted to `Work.KT.Mat.MvN` at the end.
-/

namespace Work.Idx

open Matrix
open scoped BigOperators

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- **`wQ` a unit implies the W pencil is a unit.**  (The converse is
`Work.Idx.wQ_isUnit_of_pencil`.) -/
theorem wBlk_isUnit_of_wQ {n D : ℕ} (c : Fin (D + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (z : ℂ) (hQ : IsUnit (wQ (A := C(X, ℂ)) n D c z)) :
    IsUnit (z • wBA (A := C(X, ℂ)) n D + wBB n D c) := by
  have hE : wQ (A := C(X, ℂ)) n D c z * Ring.inverse (wQ (A := C(X, ℂ)) n D c z) = 1 :=
    Ring.mul_inverse_cancel _ hQ
  have hmul := wBlk_mul_wInv n D c z hE
  have hdet : (z • wBA (A := C(X, ℂ)) n D + wBB n D c).det *
      (wInv n D c z (Ring.inverse (wQ (A := C(X, ℂ)) n D c z))).det = 1 := by
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  rw [Matrix.isUnit_iff_isUnit_det]
  exact ⟨⟨_, _, hdet, by rw [mul_comm, hdet]⟩, rfl⟩

/-- The pencil of a coefficient sequence is a unit on the circle as soon as `wQ` is. -/
theorem wBlk_pencil_isUnit {n D : ℕ} (c : Fin (D + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (hQ : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (wQ (A := C(X, ℂ)) n D c z)) :
    ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • wBA (A := C(X, ℂ)) n D + wBB n D c) :=
  fun z hz => wBlk_isUnit_of_wQ X c z (hQ z hz)

/-- Idempotency of the projection, in the block index. -/
theorem blkPenProj_idem {n D : ℕ} (c : Fin (D + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (hQ : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (wQ (A := C(X, ℂ)) n D c z)) :
    blkPenProj X (wBA (A := C(X, ℂ)) n D) (wBB n D c) *
        blkPenProj X (wBA (A := C(X, ℂ)) n D) (wBB n D c)
      = blkPenProj X (wBA (A := C(X, ℂ)) n D) (wBB n D c) := by
  have h := @penProj_idem_gen (Matrix (Fin (D + 1) × Fin n) (Fin (D + 1) × Fin n) C(X, ℂ))
    Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra (Matrix.instCompleteSpace _ _ _)
    (wBA (A := C(X, ℂ)) n D) (wBB n D c) (wBlk_pencil_isUnit X c hQ)
  simpa only [blkPenProj] using h

end

end Work.Idx
