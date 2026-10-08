import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Mat2.pslMap_eq_one_iff

open scoped MatrixGroups
open Matrix

namespace Work.L2F.PSL

/-- `!![1,b;0,1] = 1` forces `b = 0`. -/
lemma unipotent_eq_one_iff (F : Type*) [Field F] (a : F) :
    Work.PSL2.unipotent F a = 1 ↔ a = 0 := by
  constructor
  · intro h
    have hmat : (!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Work.PSL2.coe_unipotent, h, Matrix.SpecialLinearGroup.coe_one]
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hmat
    simpa using h01
  · intro ha
    apply Subtype.ext
    change ((Work.PSL2.unipotent F a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      ((1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
    rw [Work.PSL2.coe_unipotent, Matrix.SpecialLinearGroup.coe_one, ha]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- In odd characteristic the unipotent matrix `!![1,b;0,1]` is never `-1`. -/
lemma unipotent_ne_negOne (F : Type*) [Field F] (h2 : (2:F) ≠ 0) (a : F) :
    Work.PSL2.unipotent F a ≠ Work.L2F.negOne F := by
  intro h
  have hmat : (!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) F) = -1 := by
    rw [← Work.PSL2.coe_unipotent, h]
    rfl
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hmat
  have h1 : (1 : F) = -1 := by simpa using h00
  have h20 : (2 : F) = 0 := by
    have h' : (1 : F) + 1 = 0 := by
      have h'' : (1 : F) - (-1) = 0 := sub_eq_zero.mpr h1
      simpa using h''
    rwa [one_add_one_eq_two] at h'
  exact h2 h20

/-- The image in `PSL(2,F)` of the upper unipotent subgroup has `q = Nat.card F` elements.
Proof: `Work.PSL2.unipotentHom` is injective (`unipotent b = unipotent c → b = c`), so
`Nat.card (unipotentSubgroup F) = Nat.card F`; the kernel of the restriction of `pslMap` to it is
`unipotentSubgroup F ⊓ Z = {1}` (`pslMap_eq_one_iff`, and a unipotent matrix `!![1,b;0,1]` equals
`±1` only for `b = 0`). -/
theorem pslUnipotent_card (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) :
    Nat.card (Work.L2F.pslUnipotent F) = Nat.card F := by
  -- A unipotent matrix is killed by `pslMap` only for `b = 0`.
  have huni : ∀ a : F, Work.PSL2.pslMap F (Work.PSL2.unipotent F a) = 1 ↔ a = 0 := by
    intro a
    rw [Work.L2F.Mat2.pslMap_eq_one_iff F h2]
    constructor
    · rintro (h | h)
      · exact (unipotent_eq_one_iff F a).mp h
      · exact absurd h (unipotent_ne_negOne F h2 a)
    · intro ha; left; exact (unipotent_eq_one_iff F a).mpr ha
  -- Hence `pslUnipotentHom` has trivial kernel, i.e. is injective.
  have hker : ∀ x : Multiplicative F, Work.PSL2.pslUnipotentHom F x = 1 → x = 1 := by
    intro x hx
    have hx1 : Work.PSL2.pslMap F (Work.PSL2.unipotent F (Multiplicative.toAdd x)) = 1 := hx
    have hx' : Multiplicative.toAdd x = 0 := (huni _).mp hx1
    exact Multiplicative.toAdd.injective (by simpa using hx')
  have hinj : Function.Injective (Work.PSL2.pslUnipotentHom F) := by
    intro a b hab
    have h1 : Work.PSL2.pslUnipotentHom F (a * b⁻¹) = 1 := by
      rw [map_mul, hab, map_inv, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hker _ h1)
  -- `pslUnipotent F` is the range of that homomorphism.
  have hsub : Work.L2F.pslUnipotent F = (Work.PSL2.pslUnipotentHom F).range := by
    simp only [Work.L2F.pslUnipotent, Work.L2F.unipotentSubgroup, Work.PSL2.unipotentSubgroup,
      Work.PSL2.pslUnipotentHom]
    exact MonoidHom.map_range _ _
  rw [hsub]
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨MonoidHom.rangeRestrict_injective_iff.mpr hinj,
      MonoidHom.rangeRestrict_surjective _⟩)).symm.trans
    (Nat.card_congr (Multiplicative.ofAdd : F ≃ Multiplicative F)).symm

end Work.L2F.PSL
