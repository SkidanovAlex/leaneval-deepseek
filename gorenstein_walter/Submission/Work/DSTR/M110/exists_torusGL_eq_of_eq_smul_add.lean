import Mathlib
import Submission.Work.DSTR.M110.nonsplitAux

set_option linter.style.haveILetI false

namespace Work.DSTR.M110

open scoped MatrixGroups
open OnePoint Polynomial

/-- Every matrix of the form `α • B + β • 1`, where `(B : M₂(F))` satisfies `B * B = c • 1` and
`c` is not a square, is the image under `torusGL` of a unit of the quadratic algebra
`F[X]/(X² - c)`.

Indeed `torusAlgHom B c hB : F[X]/(X²-c) →+* M₂(F)` is injective (as `X² - c` is irreducible when
`c` is not a square), so the preimage `β + α·X` of `α • B + β • 1` is non-zero, hence a unit since
the algebra is a field; and `torusGL` is `Units.map` of `torusAlgHom`. -/
lemma exists_torusGL_eq_of_eq_smul_add {F : Type*} [Field F] [DecidableEq F]
    (B : Matrix.GeneralLinearGroup (Fin 2) F) (c : F)
    (hB : (B : Matrix (Fin 2) (Fin 2) F) * B = c • 1) (hc : ¬ IsSquare c)
    (D : Matrix.GeneralLinearGroup (Fin 2) F) (α β : F)
    (hD : (D : Matrix (Fin 2) (Fin 2) F) = α • (B : Matrix (Fin 2) (Fin 2) F) + β • 1) :
    ∃ v : Work.DSTR.M110.TorUnits F c, Work.DSTR.M110.torusGL B c hB v = D := by
  haveI : Fact (Irreducible (X ^ 2 - C c : F[X])) := ⟨irreducible_X_sq_sub_C hc⟩
  -- The preimage of `α • B + β • 1` under `torusAlgHom`, namely `β + α · X`.
  let Z : AdjoinRoot (X ^ 2 - C c : F[X]) :=
    algebraMap F (AdjoinRoot (X ^ 2 - C c : F[X])) β
      + algebraMap F (AdjoinRoot (X ^ 2 - C c : F[X])) α *
        AdjoinRoot.root (X ^ 2 - C c : F[X])
  have hZval : torusAlgHom B c hB Z = α • (B : Matrix (Fin 2) (Fin 2) F) + β • 1 := by
    simp only [Z, map_add, map_mul, torusAlgHom_of, torusAlgHom_root]
    rw [Matrix.smul_mul, Matrix.one_mul]
    abel
  -- `Z` is non-zero because `D ≠ 0` and `torusAlgHom` is injective on a field.
  have hZne : Z ≠ 0 := by
    intro h0
    have h1 : torusAlgHom B c hB Z = 0 := by rw [h0, map_zero]
    rw [hZval] at h1
    exact D.ne_zero (by rw [hD, h1])
  refine ⟨Units.mk0 Z hZne, ?_⟩
  apply Units.ext
  simp only [torusGL, Units.coe_map, Units.val_mk0]
  exact hZval.trans hD.symm

end Work.DSTR.M110
