import Mathlib
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs
import Submission.Work.L2F.Mat2.pslMap_eq_one_iff

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props

/-! ## Auxiliary lemmas for `centralizer_mk_eq`

The whole content of the target statement is the computation of the centralizer of `mk S` in
`PGL(2,F)`: an element `mk A` (with `A = toGL x`, `x ∈ SL(2,F)`) centralizes `mk S` iff
`A S A⁻¹` is a *scalar* multiple of `S`, and since the scalar matrix has determinant `u²` while
`det (A S A⁻¹) = det S`, the scalar is a unit `u` with `u ^ 2 = 1`, i.e. `u = ±1`.  Hence
`A S A⁻¹ = S` or `A S A⁻¹ = -S`, which is precisely `x ∈ cmtK F S`.

The next three lemmas are the three pieces of that computation. -/

/-- **Conjugation in `PGL(2,F)`.**  For `A, X ∈ GL(2,F)`, the images `mk A` and `mk X` commute
in `PGL(2,F) = GL(2,F)/Z` iff `A X A⁻¹` differs from `X` by a scalar matrix.

The forward direction: `mk (A * X) = mk (X * A)` means `A * X * scalar u = X * A`
(`ProjGenLinGroup.mk_eq_mk_iff`); right-multiplying by `A⁻¹` and using that scalar matrices are
central in `GL(2,F)` (`GeneralLinearGroup.scalar_commute`) gives `(A X A⁻¹) * scalar u = X`, whence
`A X A⁻¹ = scalar u⁻¹ * X`.  The converse is the same computation backwards. -/
lemma mk_mul_comm_mk_iff {F : Type*} [Field F] {A X : GL (Fin 2) F} :
    Matrix.ProjGenLinGroup.mk A * Matrix.ProjGenLinGroup.mk X =
        Matrix.ProjGenLinGroup.mk X * Matrix.ProjGenLinGroup.mk A ↔
      ∃ u : Fˣ, A * X * A⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 2) u * X := by
  constructor
  · intro h
    rw [← map_mul, ← map_mul] at h
    rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff] at h
    obtain ⟨u, hu⟩ := h
    refine ⟨u⁻¹, ?_⟩
    have h1 : (A * X * A⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin 2) u = X := by
      calc (A * X * A⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin 2) u
          = A * X * (A⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u) := by group
        _ = A * X * (Matrix.GeneralLinearGroup.scalar (Fin 2) u * A⁻¹) := by
              rw [Matrix.GeneralLinearGroup.scalar_commute]
        _ = A * X * Matrix.GeneralLinearGroup.scalar (Fin 2) u * A⁻¹ := by group
        _ = (X * A) * A⁻¹ := by rw [hu]
        _ = X := by group
    have h2 : A * X * A⁻¹ = X * (Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹ :=
      eq_mul_inv_of_mul_eq h1
    rw [h2, ← map_inv]
    rw [Matrix.GeneralLinearGroup.scalar_commute]
  · rintro ⟨u, hu⟩
    rw [← map_mul, ← map_mul]
    rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨u⁻¹, ?_⟩
    calc A * X * Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹
        = (A * X * A⁻¹) * A * Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ := by group
      _ = (Matrix.GeneralLinearGroup.scalar (Fin 2) u * X) * A *
            Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ := by rw [hu]
      _ = X * A := by
            calc (Matrix.GeneralLinearGroup.scalar (Fin 2) u * X) * A *
                  Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹
                = Matrix.GeneralLinearGroup.scalar (Fin 2) u * (X * A) *
                    Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ := by group
              _ = (X * A) * Matrix.GeneralLinearGroup.scalar (Fin 2) u *
                    Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ := by
                    rw [Matrix.GeneralLinearGroup.scalar_commute]
              _ = X * A := by
                    rw [map_inv (Matrix.GeneralLinearGroup.scalar (Fin 2)) u]
                    group

/-- The scalar matrix `-1` of `GL(2,F)` is `negOneGL F`; this is the element used in `negGL`. -/
lemma scalar_neg_one_eq_negOneGL (F : Type*) [Field F] :
    Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : Fˣ) = negOneGL F := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, negOneGL_apply, Units.val_neg, Units.val_one]
  rw [Matrix.scalar_apply]
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/-- **A scalar multiple of `X` by `A X A⁻¹` is `±X`.**  If `A X A⁻¹ = c • X` for a scalar
`c` (`c = scalar 2 u`, `u ∈ Fˣ`) then `c = ±1`:  taking determinants,
`det (A X A⁻¹) = det X` while `det (c • X) = u ^ 2 * det X`, and `det X` is a unit, so `u ^ 2 = 1`
and `u = ±1` (`sq_eq_one_iff` in the field `F`).  Consequently `A X A⁻¹ = X` or `A X A⁻¹ = -X`. -/
lemma eq_or_eq_negGL_of_eq_scalar_mul {F : Type*} [Field F] {A X : GL (Fin 2) F} {u : Fˣ}
    (h : A * X * A⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 2) u * X) :
    A * X * A⁻¹ = X ∨ A * X * A⁻¹ = negGL F X := by
  have hdet : Matrix.GeneralLinearGroup.det (A * X * A⁻¹) =
      Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) u * X) := by rw [h]
  rw [map_mul, map_mul, map_inv, map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
    at hdet
  have h1 : Matrix.GeneralLinearGroup.det A * Matrix.GeneralLinearGroup.det X *
      (Matrix.GeneralLinearGroup.det A)⁻¹ = Matrix.GeneralLinearGroup.det X :=
    mul_inv_cancel_comm _ _
  rw [h1] at hdet
  have hu2 : u ^ 2 = 1 := by
    have := congrArg (fun z : Fˣ => z * (Matrix.GeneralLinearGroup.det X)⁻¹) hdet
    simpa [mul_assoc] using this.symm
  have hu2F : ((u : F)) ^ 2 = 1 := by
    have := congrArg (fun z : Fˣ => (z : F)) hu2
    simpa using this
  rcases sq_eq_one_iff.mp hu2F with hu | hu
  · left
    have hu1 : u = 1 := Units.ext hu
    rw [h, hu1, map_one, one_mul]
  · right
    have hum1 : u = -1 := by
      apply Units.ext
      rw [hu, Units.val_neg, Units.val_one]
    rw [h, hum1, scalar_neg_one_eq_negOneGL F]

/-- The `SL`-part of the centralizer of `mk S` in `PGL(2,F)` is the image of `cmtK F S`.
Hint: `x ∈ SL` centralizes `mk S` iff `x S x⁻¹ = c • S` for a scalar `c`; squaring with
`S² = lam • 1`, `lam ≠ 0` gives `c² = 1`, so `c = ±1`; note `hS`, `hlam` are only needed for that
step (the statement is even true without them).  Mathlib API: `ProjGenLinGroup.mk_eq_one`,
`mk_eq_mk_iff`, `GeneralLinearGroup.center_eq_range_scalar`, `SpecialLinearGroup.toPGL`. -/
theorem centralizer_mk_eq (F : Type*) [Field F] (S : Matrix.GeneralLinearGroup (Fin 2) F) (lam : F)
    (hS : (S : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) = lam • 1)
    (hlam : lam ≠ 0) :
    Work.L2F.Props.SLsub F ⊓
        Subgroup.centralizer ({Matrix.ProjGenLinGroup.mk S} :
          Set (Matrix.ProjGenLinGroup (Fin 2) F)) =
      (Work.L2F.Props.cmtK F S).map Matrix.SpecialLinearGroup.toPGL := by
  apply le_antisymm
  · -- An element of `SL(2,F) ∩ C_{PGL}(mk S)` lies in `cmtK F S`.
    intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hg1, hg2⟩ := hg
    obtain ⟨x, rfl⟩ := (mem_SLsub F).mp hg1
    rw [Subgroup.mem_map]
    refine ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hg2
    have hcomm : Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL x) *
          Matrix.ProjGenLinGroup.mk S =
        Matrix.ProjGenLinGroup.mk S *
          Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL x) := hg2
    rw [mk_mul_comm_mk_iff] at hcomm
    obtain ⟨u, hu⟩ := hcomm
    rw [mem_cmtK_iff]
    exact eq_or_eq_negGL_of_eq_scalar_mul hu
  · -- The image of `cmtK F S` lies in `SL(2,F) ∩ C_{PGL}(mk S)`.
    intro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    rw [Subgroup.mem_inf]
    refine ⟨toPGL_mem_SLsub F x, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL x) *
        Matrix.ProjGenLinGroup.mk S =
      Matrix.ProjGenLinGroup.mk S *
        Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL x)
    rw [mk_mul_comm_mk_iff]
    rw [mem_cmtK_iff] at hx
    rcases hx with hx | hx
    · exact ⟨1, by rw [hx]; simp⟩
    · exact ⟨-1, by rw [hx, scalar_neg_one_eq_negOneGL F]⟩

end Work.L2F.Props
