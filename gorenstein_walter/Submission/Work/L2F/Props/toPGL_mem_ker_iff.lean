import Mathlib
import Submission.Work.L2F.Defs

namespace Work.L2F.Props

-- The hypothesis `h2` of `toPGL_mem_ker_iff` is not needed (the statement also holds in
-- characteristic two, where `-1 = 1`); it is kept for compatibility with the request.
set_option linter.unusedVariables false

open scoped MatrixGroups
open Matrix

/-! ## Auxiliary facts about the centre of `SL(2,F)` -/

/-- The scalar matrix `-1` of `GL` is the underlying matrix of the element `-1` of `SL(2,F)`. -/
lemma scalar_neg_one_eq_negOne (F : Type*) [Field F] :
    Matrix.scalar (Fin 2) (-1 : F) =
      ((Work.L2F.negOne F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Work.L2F.negOne]

/-- The centre of `SL(2,F)` consists of the scalars `±1`: an element is central iff it is `1`
or `-1`.  (In characteristic `2` the two coincide, so no hypothesis on `2` is needed.) -/
theorem mem_center_SL2_iff (F : Type*) [Field F] (x : SL(2, F)) :
    x ∈ Subgroup.center (SL(2, F)) ↔ x = 1 ∨ x = Work.L2F.negOne F := by
  constructor
  · intro hx
    -- A central element of `SL` is a central element of `GL`, hence a scalar matrix.
    have hxGL : Matrix.SpecialLinearGroup.toGL x ∈ Subgroup.center (GL (Fin 2) F) :=
      (Matrix.SpecialLinearGroup.toGL_mem_center_iff x).mpr hx
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hxGL
    obtain ⟨r, hr⟩ := hxGL
    -- Taking determinants, `r ^ 2 = det (scalar r) = 1`.
    have hdet : r ^ 2 = 1 := by
      have h := congrArg Matrix.GeneralLinearGroup.det hr
      rwa [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin,
        Matrix.SpecialLinearGroup.coeToGL_det] at h
    have hval : (r : F) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hdet, Units.val_one]
    -- In a field, `r ^ 2 = 1` forces `r = ±1`.
    have hmat : (x : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (r : F) := by
      have h := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hr
      simpa [Matrix.GeneralLinearGroup.coe_scalar] using h.symm
    rcases sq_eq_one_iff.mp hval with h1 | h1
    · left
      apply Subtype.ext
      rw [hmat, h1]
      simp [Matrix.scalar_apply]
    · right
      apply Subtype.ext
      rw [hmat, h1]
      exact scalar_neg_one_eq_negOne F
  · -- Conversely `1` and `-1` are central.
    rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · rw [← Matrix.SpecialLinearGroup.toGL_mem_center_iff]
      exact Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
        ⟨-1, scalar_neg_one_eq_negOne F⟩

/-- In odd characteristic the natural map `SL(2,F) → PGL(2,F)` has kernel `{1, -1}`: it is the
composite of `toGL` with the quotient by the centre of `GL(2,F)`, so `toPGL x = 1` iff `toGL x` is a
scalar matrix, and `det x = 1` forces the scalar `r` to satisfy `r ^ 2 = 1`, hence `r = ±1`. -/
theorem toPGL_mem_ker_iff (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix.SpecialLinearGroup.toPGL x = 1 ↔ x = 1 ∨ x = Work.L2F.negOne F := by
  rw [← MonoidHom.mem_ker, Matrix.SpecialLinearGroup.toPGL_ker]
  exact mem_center_SL2_iff F x

end Work.L2F.Props
