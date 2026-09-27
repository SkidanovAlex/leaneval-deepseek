import Mathlib
import Submission.Work.KT.Psi.ClsM
import Submission.Work.KT.Psi.orth_idem_split

/-!
# `Work.KT.Psi.clsM_idem_add`

For two idempotent matrices `E`, `F` over an arbitrary finite index type `ι` which are orthogonal
(`E * F = 0`, `F * E = 0`), the class in `K₀` of the idempotent `E + F` is the sum of the classes
of `E` and `F`.

The proof reduces along the canonical reindexing `ι ≃ Fin (Fintype.card ι)` to the `Fin n`-statement
`Work.KT.Psi.orth_idem_split`, which exhibits a Murray–von Neumann equivalence between `E + F` and
the block sum `E ⊕ F`.
-/

namespace Work.KT.Psi

open Matrix

theorem clsM_idem_add {A : Type} [Ring A] {ι : Type} [Fintype ι]
    (E F : Matrix ι ι A) (hE : E * E = E) (hF : F * F = F)
    (hEF : E * F = 0) (hFE : F * E = 0) :
    clsM ι (E + F) = clsM ι E + clsM ι F := by
  rw [clsM_eq_cls, clsM_eq_cls, clsM_eq_cls]
  set e := Fintype.equivFin ι
  have hE' : Matrix.reindex e e E * Matrix.reindex e e E = Matrix.reindex e e E := by
    change (Matrix.reindexRingEquiv A e) E * (Matrix.reindexRingEquiv A e) E =
      (Matrix.reindexRingEquiv A e) E
    rw [← map_mul, hE]
  have hF' : Matrix.reindex e e F * Matrix.reindex e e F = Matrix.reindex e e F := by
    change (Matrix.reindexRingEquiv A e) F * (Matrix.reindexRingEquiv A e) F =
      (Matrix.reindexRingEquiv A e) F
    rw [← map_mul, hF]
  have hEF' : Matrix.reindex e e E * Matrix.reindex e e F = 0 := by
    change (Matrix.reindexRingEquiv A e) E * (Matrix.reindexRingEquiv A e) F = 0
    rw [← map_mul, hEF, map_zero]
  have hFE' : Matrix.reindex e e F * Matrix.reindex e e E = 0 := by
    change (Matrix.reindexRingEquiv A e) F * (Matrix.reindexRingEquiv A e) E = 0
    rw [← map_mul, hFE, map_zero]
  have hu : (Matrix.reindex e e E + Matrix.reindex e e F) *
      (Matrix.reindex e e E + Matrix.reindex e e F) =
      Matrix.reindex e e E + Matrix.reindex e e F := by
    rw [add_mul, mul_add, mul_add, hE', hEF', hFE', hF']
    abel
  have hsum : Matrix.reindex e e (E + F) = Matrix.reindex e e E + Matrix.reindex e e F := by
    change (Matrix.reindexRingEquiv A e) (E + F) =
      (Matrix.reindexRingEquiv A e) E + (Matrix.reindexRingEquiv A e) F
    rw [map_add]
  rw [hsum]
  exact orth_idem_split hu hE' hF' rfl hEF' hFE'

end Work.KT.Psi
