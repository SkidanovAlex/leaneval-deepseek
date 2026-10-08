import Mathlib

/-!
# `PGL(2, q)` has a proper nontrivial normal subgroup

For a finite field `F` of odd characteristic, the image of `SL(2, F)` inside `PGL(2, F)` is a
normal subgroup of index `2` (hence proper and nontrivial).  This gives the required subgroup of
`PGL(2, GaloisField p k)` for every odd prime `p` with `p ^ k ≥ 5`.
-/

open scoped MatrixGroups
open Matrix

namespace Work.ASM

/-- The image of `SL(2, F)` in `PGL(2, F)` is a proper, nontrivial, normal subgroup for every
finite field `F` of odd characteristic. -/
private lemma exists_normal_subgroup_of_field (F : Type*) [Field F] [Finite F]
    (hF : ringChar F ≠ 2) :
    ∃ N : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F), N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  refine ⟨(Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range, ?_, ?_, ?_⟩
  · -- The image of `SL` is the image of the (normal) kernel of `det`; `mk` is surjective.
    rw [Matrix.SpecialLinearGroup.toPGL, MonoidHom.range_comp,
      Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    exact Subgroup.Normal.map (MonoidHom.normal_ker _) _ Matrix.ProjGenLinGroup.mk_surjective
  · -- `[[1,1],[0,1]] ∈ SL` is not scalar, so its image is a nontrivial element.
    intro hbot
    let s : Matrix.SpecialLinearGroup (Fin 2) F :=
      ⟨(!![(1 : F), 1; 0, 1] : Matrix (Fin 2) (Fin 2) F), by simp [Matrix.det_fin_two]⟩
    have hne : Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F) s ≠ 1 := by
      show (Matrix.ProjGenLinGroup.mk.comp Matrix.SpecialLinearGroup.toGL) s ≠ 1
      rw [MonoidHom.comp_apply]
      intro h
      rw [Matrix.ProjGenLinGroup.mk_eq_one,
        Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
      obtain ⟨u, hu⟩ := h
      have h01 := congrArg (fun g : GL (Fin 2) F => ((g : Matrix (Fin 2) (Fin 2) F)) 0 1) hu
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply] at h01
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h01
      rw [Matrix.SpecialLinearGroup.coe_mk] at h01
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h01
      rw [ite_eq_right (by decide : ¬ ((0 : Fin 2) = 1))] at h01
      exact zero_ne_one h01
    have hmem : Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F) s ∈
        (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
      MonoidHom.mem_range.mpr ⟨s, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hne hmem
  · -- An element of `GL` whose determinant is not a square is not in the image of `SL`.
    intro htop
    obtain ⟨d, hd⟩ := FiniteField.exists_nonsquare (F := F) hF
    have hd0 : d ≠ 0 := fun h0 => hd ⟨0, by simp [h0]⟩
    let u : Fˣ := Units.mk0 d hd0
    obtain ⟨g, hg⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin 2) (R := F) u
    have hmem : Matrix.ProjGenLinGroup.mk g ∈
        (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
      rw [htop]; exact Subgroup.mem_top g
    rw [Matrix.SpecialLinearGroup.toPGL, MonoidHom.range_comp,
      Matrix.SpecialLinearGroup.range_toGL_eq_ker_det] at hmem
    obtain ⟨h, hhker, hhmk⟩ := Subgroup.mem_map.mp hmem
    have hdet1 : Matrix.GeneralLinearGroup.det h = 1 := MonoidHom.mem_ker.mp hhker
    rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff] at hhmk
    obtain ⟨v, hv⟩ := hhmk
    have hdg : Matrix.GeneralLinearGroup.det g = v ^ 2 := by
      have h1 : Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det h *
          Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) v) := by
        rw [← hv, map_mul]
      rw [h1, hdet1, one_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
    rw [hg] at hdg
    refine hd ?_
    exact ⟨(v : F), by
      have h2 := congrArg (fun w : Fˣ => (w : F)) hdg
      simpa only [u, Units.val_mk0, Units.val_pow_eq_pow_val, pow_two, Units.val_mul] using h2⟩

theorem PGL_exists_normal_subgroup (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k) :
    ∃ N : Subgroup (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)), N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  refine exists_normal_subgroup_of_field (GaloisField p k) ?_
  have hchar : ringChar (GaloisField p k) = p := ringChar.eq _ p
  rw [hchar]
  obtain ⟨m, hm⟩ := hp
  omega

end Work.ASM
