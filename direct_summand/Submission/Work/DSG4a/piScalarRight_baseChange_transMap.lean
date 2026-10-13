import Mathlib
import Submission.Work.DSG4a.Present

namespace Work.DSG4a

open TensorProduct

/-- Compatibility of the transposed matrix map `transMap D` with scalar extension.

Concretely: the canonical identification `A' ⊗[A] (Fin k → A) ≃ (Fin k → A')`
(`TensorProduct.piScalarRight`) intertwines the base change of `transMap D` (a map of
`A`-modules) with the transposed matrix map of the entrywise-extended matrix
`i j ↦ algebraMap A A' (D i j)` (a map of `A'`-modules). -/
theorem piScalarRight_baseChange_transMap {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A']
    {m n : ℕ} (D : Fin m → Fin n → A) (x : TensorProduct A A' (Fin m → A)) :
    TensorProduct.piScalarRight A A' A' (Fin n)
        (LinearMap.baseChange A' (Work.DSG4a.transMap D) x) =
      Work.DSG4a.transMap (fun i j => algebraMap A A' (D i j))
        (TensorProduct.piScalarRight A A' A' (Fin m) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a z =>
    ext j
    simp only [LinearMap.baseChange_tmul, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul, transMap_apply, Algebra.smul_def, map_sum, map_mul]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  | add x y ihx ihy =>
    simp only [map_add, ihx, ihy]

end Work.DSG4a
