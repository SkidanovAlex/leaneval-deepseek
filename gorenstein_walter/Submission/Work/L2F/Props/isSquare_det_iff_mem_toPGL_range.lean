import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs

namespace Work.L2F.Props

/-- `s ∈ L₂(F) = range (PSL(2,F) → PGL(2,F))` iff the determinant of a lift `S : GL(2,F)` of `s` is a square in `F`.
Both directions are the elementary rescaling: if `det S = r * r` then `r⁻¹ • S` has determinant `1`, lies in `SL(2,F)` and has the same image in `PGL(2,F)`; conversely if `s = toPGL X` for `X ∈ SL(2,F)` then `S = X * scalar u` for some unit `u`, so `det S = (↑u⁻¹) * (↑u⁻¹)`. -/
theorem isSquare_det_iff_mem_toPGL_range (F : Type*) [Field F]
    (S : Matrix.GeneralLinearGroup (Fin 2) F) (s : Matrix.ProjGenLinGroup (Fin 2) F)
    (hS : Matrix.ProjGenLinGroup.mk S = s) :
    IsSquare ((S : Matrix (Fin 2) (Fin 2) F).det) ↔
      s ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL :
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) F →*
          Matrix.ProjGenLinGroup (Fin 2) F).range := by
  constructor
  · -- If `det S = r * r`, rescale `S` by the unit `r` to land in `SL(2,F)`; the image in
    -- `PGL(2,F)` is unchanged because the rescaling is by a scalar matrix.
    intro h
    obtain ⟨r, hr⟩ := h
    have h0 : (S : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := S.det_ne_zero
    have hrne : r ≠ 0 := by
      intro hz
      rw [hr, hz, mul_zero] at h0
      exact h0 rfl
    let u : Fˣ := Units.mk0 r hrne
    have hu : (u : F) * (u : F) = (S : Matrix (Fin 2) (Fin 2) F).det := by
      show r * r = (S : Matrix (Fin 2) (Fin 2) F).det
      rw [hr]
    have hdetS : Matrix.GeneralLinearGroup.det S = u * u := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul]
      exact hu.symm
    have hdetU : Matrix.GeneralLinearGroup.det
        (S * Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹) = 1 := by
      rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, hdetS]
      simp [Fintype.card_fin]
      group
    have hmat : ((S * Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ :
        Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      have h1 := congrArg (fun x : Fˣ => (x : F)) hdetU
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using h1
    let X : Matrix.SpecialLinearGroup (Fin 2) F :=
      ⟨(S * Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ :
        Matrix.GeneralLinearGroup (Fin 2) F), hmat⟩
    have hX : Matrix.SpecialLinearGroup.toGL X =
        S * Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ := Units.ext rfl
    rw [← hS]
    refine ⟨(X : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F), ?_⟩
    rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, hX, map_mul,
      Matrix.ProjGenLinGroup.mk_scalar, mul_one]
  · -- If `mk S` lies in the image of `PSL(2,F)`, then `S` differs from a determinant-one
    -- matrix by a scalar matrix `scalar u`, so `det S = u * u` is a square.
    intro hmem
    obtain ⟨p, hp⟩ := hmem
    obtain ⟨X, hX⟩ := QuotientGroup.mk_surjective p
    rw [← hS, ← hX, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk X] at hp
    obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hp
    have hdet : Matrix.GeneralLinearGroup.det S = u * u := by
      rw [← hu, map_mul, Matrix.SpecialLinearGroup.coeToGL_det, one_mul,
        Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_two]
    refine ⟨(u : F), ?_⟩
    have h1 := congrArg (fun x : Fˣ => (x : F)) hdet
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul] at h1
    exact h1

end Work.L2F.Props
