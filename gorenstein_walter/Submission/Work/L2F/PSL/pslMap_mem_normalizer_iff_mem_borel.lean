import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Conic.mem_borel
import Submission.Work.L2F.Mat2.conj_unipotent_entry
import Submission.Work.L2F.Mat2.pslMap_eq_one_iff
import Submission.Work.L2F.PSL.pslMap_mem_normalizer_pslUnipotent

open scoped MatrixGroups
open Matrix

namespace Work.L2F.PSL

/-- If two elements `X Y` of `SL(2,F)` have the same image in `PSL(2,F)` and `Y` is upper
triangular (its `(1,0)`-entry vanishes), then `X` is upper triangular as well.

Indeed `pslMap F (X * Y⁻¹) = 1`, and the kernel of the quotient map is `{1, -1}`
(`Work.L2F.Mat2.pslMap_eq_one_iff`, which uses `(2 : F) ≠ 0`), so `X = Y` or `X = -Y`; both
preserve the vanishing of the `(1,0)`-entry. -/
theorem entry_zero_of_pslMap_eq (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    {X Y : Matrix.SpecialLinearGroup (Fin 2) F}
    (hY : (Y : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (h : Work.PSL2.pslMap F X = Work.PSL2.pslMap F Y) :
    (X : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  have h1 : Work.PSL2.pslMap F (X * Y⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  rcases (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (X * Y⁻¹)).mp h1 with hXY | hXY
  · have hX : X = Y := mul_inv_eq_one.mp hXY
    rw [hX]
    exact hY
  · have hX : X = Work.L2F.negOne F * Y := by
      calc X = X * Y⁻¹ * Y := by group
        _ = Work.L2F.negOne F * Y := by rw [hXY]
    rw [hX]
    have hc : ((Work.L2F.negOne F * Y : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = -(Y : Matrix (Fin 2) (Fin 2) F) := by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      have h' : ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) = -1 := rfl
      rw [h', neg_one_mul]
    rw [hc, Matrix.neg_apply, hY, neg_zero]

theorem pslMap_mem_normalizer_iff_mem_borel (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    Work.PSL2.pslMap F A ∈ Subgroup.normalizer
        (Work.L2F.pslUnipotent F : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) ↔
      A ∈ Work.L2F.borel F := by
  constructor
  · intro h
    -- Conjugating the upper unipotent `unipotent 1` by `A⁻¹` stays in `pslUnipotent`.
    have hconj : Work.PSL2.pslMap F (A⁻¹ * Work.PSL2.unipotent F 1 * A) ∈
        Work.L2F.pslUnipotent F := by
      have hmem : Work.PSL2.pslMap F (Work.PSL2.unipotent F 1) ∈ Work.L2F.pslUnipotent F := by
        rw [Work.L2F.pslUnipotent, Subgroup.mem_map]
        exact ⟨Work.PSL2.unipotent F 1, ⟨Multiplicative.ofAdd (1 : F), rfl⟩, rfl⟩
      have hg := (Subgroup.mem_normalizer_iff''.mp h)
        (Work.PSL2.pslMap F (Work.PSL2.unipotent F 1))
      have hg' := hg.mp hmem
      simpa only [map_mul, map_inv] using hg'
    -- Lift this relation back to `SL(2,F)`: some upper unipotent `M` has the same image.
    rw [Work.L2F.pslUnipotent, Subgroup.mem_map] at hconj
    obtain ⟨M, hM, hMeq⟩ := hconj
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hM
    have hMtri : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      rw [← hb]
      change ((Work.PSL2.unipotent F (Multiplicative.toAdd b) :
        Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
      rw [Work.PSL2.coe_unipotent]
      simp
    have hentry : ((A⁻¹ * Work.PSL2.unipotent F 1 * A :
        Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
      entry_zero_of_pslMap_eq F h2 hMtri hMeq.symm
    -- Evaluate the `(1,0)`-entry of the conjugate.
    rw [Work.L2F.Mat2.conj_unipotent_entry F A 1, mul_one, neg_eq_zero, pow_two] at hentry
    exact (Work.L2F.Conic.mem_borel F A).mpr (mul_self_eq_zero.mp hentry)
  · intro h
    exact pslMap_mem_normalizer_pslUnipotent F A ((Work.L2F.Conic.mem_borel F A).mp h)

end Work.L2F.PSL
