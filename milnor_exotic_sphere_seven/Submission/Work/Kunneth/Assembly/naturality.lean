import Mathlib
import Submission.Work.Kunneth.Assembly.Defs
import Submission.Work.LerayHirsch.MvPieceTranslate
import Submission.Work.Kunneth.zeta_qTriv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Naturality of the Leray–Hirsch family map along `(projMap, qTriv)`

The Leray–Hirsch family map `Work.LerayHirsch.lhMap (Zb m B) k xf = Σ_i π^*(xf i) ⌣ ζ^i` on
`P(ε^m over B)` is the pullback along the homeomorphism `hMap m B = (projMap, qTriv)` of the
space-level family map `Work.Kunneth.Asm.crFam m B k xf` on `B × Qb m`:

`lhMap Zb k xf = (CohMap (hMap m B) ℤ (2k)) (crFam m B k xf)`,

and its odd-degree companion for `Work.LerayHirsch.lhMapOdd`.

The proof is term by term: `π₁ ∘ hMap = projMap`, `π₂ ∘ hMap = qTriv`, the naturality of the
product `cupChern`/`cupH'`, and `qTriv^* ζ = ζ` (`Work.Kunneth.zeta_qTriv`).
-/

namespace Work.Kunneth.Asm

open CategoryTheory CategoryTheory.Limits Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization MonoidalCategory TensorProduct

noncomputable section

theorem lhMap_eq_CohMap_crFam (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (xf : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * (k - (i : ℕ))) B) :
    Work.LerayHirsch.lhMap (Zb m B) k xf
      = (Work.Thom.CohMap (hMap m B) ℤ (2 * k)).hom (crFam m B k xf) := by
  rw [Work.LerayHirsch.lhMap_apply, crFam, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [crTerm, Work.LerayHirsch.lhTerm_def, Work.Thom.cohTransport_CohMap,
    Work.Whitney.cupChern_CohMap]
  have hxi : (Work.Thom.CohMap (hMap m B) ℤ (2 * (k - (i : ℕ)))).hom
      ((Work.Thom.CohMap (pi1 m B) ℤ (2 * (k - (i : ℕ)))).hom (xf i))
      = (Work.Thom.CohMap (Work.LerayHirsch.projMap (Zb m B)) ℤ
          (2 * (k - (i : ℕ)))).hom (xf i) := by
    rw [show (Work.Thom.CohMap (hMap m B) ℤ (2 * (k - (i : ℕ)))).hom
        ((Work.Thom.CohMap (pi1 m B) ℤ (2 * (k - (i : ℕ)))).hom (xf i))
        = ((Work.Thom.CohMap (pi1 m B) ℤ (2 * (k - (i : ℕ)))
            ≫ Work.Thom.CohMap (hMap m B) ℤ (2 * (k - (i : ℕ)))).hom) (xf i) from rfl]
    rw [← Work.Thom.CohMap_comp]
    rfl
  have hzi : (Work.Thom.CohMap (hMap m B) ℤ (2 * (i : ℕ))).hom
      ((Work.Thom.CohMap (pi2 m B) ℤ (2 * (i : ℕ))).hom
        (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ)))
      = Work.LerayHirsch.zetaPow (Zb m B) (i : ℕ) := by
    rw [show (Work.Thom.CohMap (hMap m B) ℤ (2 * (i : ℕ))).hom
        ((Work.Thom.CohMap (pi2 m B) ℤ (2 * (i : ℕ))).hom
          (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ)))
        = ((Work.Thom.CohMap (pi2 m B) ℤ (2 * (i : ℕ))
            ≫ Work.Thom.CohMap (hMap m B) ℤ (2 * (i : ℕ))).hom)
            (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ)) from rfl]
    rw [← Work.Thom.CohMap_comp]
    rw [show Work.Thom.CohMap ((pi2 m B).comp (hMap m B)) ℤ (2 * (i : ℕ))
        = Work.Thom.CohMap (Work.Kunneth.qTriv m B) ℤ (2 * (i : ℕ)) from by congr 1]
    rw [show (Work.Thom.CohMap (Work.Kunneth.qTriv m B) ℤ (2 * (i : ℕ))).hom
        (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ))
        = (Work.Thom.CohMap (Work.Kunneth.qTriv m B) ℤ (2 * (i : ℕ))).hom
            (Work.Kunneth.pow2 (Work.LerayHirsch.zeta (Work.LerayHirsch.trivCore m)) (i : ℕ))
        from congrArg _ (Work.Kunneth.pow2_zeta (Work.LerayHirsch.trivCore m) (i : ℕ)).symm]
    rw [Work.Kunneth.pow2_CohMap, Work.Kunneth.zeta_qTriv, ← Work.Kunneth.pow2_zeta]
  rw [hxi, hzi]

theorem lhMapOdd_eq_CohMap_crFamOdd (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (xf : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B) :
    Work.LerayHirsch.lhMapOdd (Zb m B) k xf
      = (Work.Thom.CohMap (hMap m B) ℤ (2 * k + 1)).hom (crFamOdd m B k xf) := by
  rw [Work.LerayHirsch.lhMapOdd, crFamOdd, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [crTermOdd, Work.LerayHirsch.lhTermOdd, Work.Thom.cohTransport_CohMap,
    Work.LerayHirsch.CohMap_cupH'_apply]
  have hxi : (Work.Thom.CohMap (hMap m B) ℤ (2 * k + 1 - 2 * (i : ℕ))).hom
      ((Work.Thom.CohMap (pi1 m B) ℤ (2 * k + 1 - 2 * (i : ℕ))).hom (xf i))
      = (Work.Thom.CohMap (Work.LerayHirsch.projMap (Zb m B)) ℤ
          (2 * k + 1 - 2 * (i : ℕ))).hom (xf i) := by
    rw [show (Work.Thom.CohMap (hMap m B) ℤ (2 * k + 1 - 2 * (i : ℕ))).hom
        ((Work.Thom.CohMap (pi1 m B) ℤ (2 * k + 1 - 2 * (i : ℕ))).hom (xf i))
        = ((Work.Thom.CohMap (pi1 m B) ℤ (2 * k + 1 - 2 * (i : ℕ))
            ≫ Work.Thom.CohMap (hMap m B) ℤ (2 * k + 1 - 2 * (i : ℕ))).hom) (xf i) from rfl]
    rw [← Work.Thom.CohMap_comp]
    rfl
  have hzi : (Work.Thom.CohMap (hMap m B) ℤ (2 * (i : ℕ))).hom
      ((Work.Thom.CohMap (pi2 m B) ℤ (2 * (i : ℕ))).hom
        (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ)))
      = Work.LerayHirsch.zetaPow (Zb m B) (i : ℕ) := by
    rw [show (Work.Thom.CohMap (hMap m B) ℤ (2 * (i : ℕ))).hom
        ((Work.Thom.CohMap (pi2 m B) ℤ (2 * (i : ℕ))).hom
          (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ)))
        = ((Work.Thom.CohMap (pi2 m B) ℤ (2 * (i : ℕ))
            ≫ Work.Thom.CohMap (hMap m B) ℤ (2 * (i : ℕ))).hom)
            (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ)) from rfl]
    rw [← Work.Thom.CohMap_comp]
    rw [show Work.Thom.CohMap ((pi2 m B).comp (hMap m B)) ℤ (2 * (i : ℕ))
        = Work.Thom.CohMap (Work.Kunneth.qTriv m B) ℤ (2 * (i : ℕ)) from by congr 1]
    rw [show (Work.Thom.CohMap (Work.Kunneth.qTriv m B) ℤ (2 * (i : ℕ))).hom
        (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ))
        = (Work.Thom.CohMap (Work.Kunneth.qTriv m B) ℤ (2 * (i : ℕ))).hom
            (Work.Kunneth.pow2 (Work.LerayHirsch.zeta (Work.LerayHirsch.trivCore m)) (i : ℕ))
        from congrArg _ (Work.Kunneth.pow2_zeta (Work.LerayHirsch.trivCore m) (i : ℕ)).symm]
    rw [Work.Kunneth.pow2_CohMap, Work.Kunneth.zeta_qTriv, ← Work.Kunneth.pow2_zeta]
  rw [hxi, hzi]

end

end Work.Kunneth.Asm
