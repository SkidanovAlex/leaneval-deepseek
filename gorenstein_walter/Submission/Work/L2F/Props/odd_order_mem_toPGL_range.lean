import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Props.isSquare_det_iff_mem_toPGL_range

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props

/-- Any element of `PGL(2,F)` of odd order lies in the image of `SL(2,F)`, i.e. is in the range of
`Matrix.SpecialLinearGroup.toPGL`.

This is the elementary statement that `PGL_2(F) = L_2(F) ⋊ ⟨δ⟩` with `δ` of order `2` modulo the
diagonal: an element of odd order must lie in `L_2(F) = PSL(2,F)`.

Proof.  Lift `g` to some `S : GL(2,F)` and put `n = orderOf g`, odd.  Then `g ^ n = 1`, so
`S ^ n` is a scalar matrix, `S ^ n = scalar c`; taking determinants gives
`(det S) ^ n = c * c`, a square in `Fˣ`.  As `n` is odd, `det S = (det S) ^ n * ((det S) ^ k)⁻²`
where `n = 2k+1`, so `det S` is itself a square; `isSquare_det_iff_mem_toPGL_range` then puts `g`
in the range of `PSL(2,F) → PGL(2,F)`, whose range is that of `SL(2,F) → PGL(2,F)`. -/
theorem odd_order_mem_toPGL_range (F : Type*) [Field F]
    (g : Matrix.ProjGenLinGroup (Fin 2) F) (hg : Odd (orderOf g)) :
    g ∈ (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  -- Lift `g` to `GL(2,F)`.
  obtain ⟨S, hS⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  -- `S ^ orderOf g` lies in the centre of `GL(2,F)`, because `g ^ orderOf g = 1`.
  have hmem_center : S ^ orderOf g ∈ Subgroup.center (GL (Fin 2) F) := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one, map_pow, hS, pow_orderOf_eq_one]
  -- A central element of `GL(2,F)` is a scalar matrix.
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hmem_center
  obtain ⟨c, hc⟩ := hmem_center
  -- Taking determinants: `(det S) ^ orderOf g = c * c`, a square in `Fˣ`.
  have hdet : (Matrix.GeneralLinearGroup.det S) ^ orderOf g = c * c := by
    have h := congrArg Matrix.GeneralLinearGroup.det hc
    simp only [map_pow, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h
    rw [← h, pow_two]
  -- As `orderOf g` is odd, `det S` is a square in `Fˣ`, hence `det S` is a square in `F`.
  have hsquare : IsSquare ((S : Matrix (Fin 2) (Fin 2) F).det) := by
    obtain ⟨k, hk⟩ := hg
    have h1 : IsSquare ((Matrix.GeneralLinearGroup.det S) ^ orderOf g) := ⟨c, hdet⟩
    have hs : IsSquare ((((Matrix.GeneralLinearGroup.det S) ^ k)⁻¹) ^ 2) :=
      ⟨((Matrix.GeneralLinearGroup.det S) ^ k)⁻¹, by rw [pow_two]⟩
    have hprod : IsSquare ((Matrix.GeneralLinearGroup.det S) ^ orderOf g *
        (((Matrix.GeneralLinearGroup.det S) ^ k)⁻¹) ^ 2) := h1.mul hs
    have heq : (Matrix.GeneralLinearGroup.det S) ^ orderOf g *
        (((Matrix.GeneralLinearGroup.det S) ^ k)⁻¹) ^ 2 = Matrix.GeneralLinearGroup.det S := by
      rw [hk]
      group
    rw [heq] at hprod
    obtain ⟨y, hy⟩ := hprod
    refine ⟨↑y, ?_⟩
    rw [← Matrix.GeneralLinearGroup.val_det_apply S]
    exact congrArg (fun u : Fˣ => (u : F)) hy
  -- `g` lies in the image of `PSL(2,F) → PGL(2,F)`.
  have hmem : g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
    (Work.L2F.Props.isSquare_det_iff_mem_toPGL_range F S g hS).mp hsquare
  -- The image of `SL(2,F)` is the same as that of `PSL(2,F) = SL(2,F)/Z`.
  obtain ⟨x, hx⟩ := hmem
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨y, ?_⟩
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk] at hx
  exact hx

end Work.L2F.Props
