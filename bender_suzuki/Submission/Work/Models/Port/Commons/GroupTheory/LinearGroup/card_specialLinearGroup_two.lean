import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Cardinality of `SL(2, F)` over a finite field

For a finite field `F` with `q = |F|` elements, the special linear group
`SL(2, F) = Matrix.SpecialLinearGroup (Fin 2) F` has cardinality
`q * (q ^ 2 - 1)`.

The proof uses the determinant homomorphism
`det : GL(2, F) →* Fˣ`, which is surjective.  Its kernel is isomorphic to
`SL(2, F)` (an invertible matrix has determinant `1` exactly when it is the
matrix of a `SL(2, F)`-element), so the index of the kernel equals
`|Fˣ| = q - 1`.  Combined with the known cardinality
`|GL(n, F)| = ∏ i, (q ^ n - q ^ i)` (Mathlib's `Matrix.card_GL_field`) and
the group identity `|ker| * index = |GL|`, cancelling the factor `q - 1`
yields the result.
-/

open scoped MatrixGroups

namespace Commons.GroupTheory.LinearGroup

theorem card_specialLinearGroup_two {F : Type*} [Field F] [Fintype F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  have hqF : Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
  have hq2 : 2 ≤ Nat.card F := by
    rw [hqF]
    exact Nat.succ_le_of_lt (Fintype.one_lt_card (α := F))
  have hpos : 0 < Nat.card F - 1 := by omega
  set det : GL (Fin 2) F →* Fˣ := Matrix.GeneralLinearGroup.det with hdet
  have hsurj : Function.Surjective det := Matrix.GeneralLinearGroup.det_surjective
  -- `SL(2, F)` is the kernel of the determinant.
  have hsl : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card det.ker := by
    let e : Matrix.SpecialLinearGroup (Fin 2) F ≃ det.ker :=
      { toFun := fun A => ⟨Matrix.SpecialLinearGroup.toGL A, by
          rw [MonoidHom.mem_ker, Matrix.SpecialLinearGroup.coeToGL_det]⟩
        invFun := fun x => ⟨(x.1 : GL (Fin 2) F).1, by
          have hx : det x.1 = 1 := x.2
          exact congrArg Units.val hx⟩
        left_inv := fun A => by
          apply Subtype.ext
          rfl
        right_inv := fun x => by
          apply Subtype.ext
          apply Units.ext
          rfl }
    exact Nat.card_congr e
  -- the index of the kernel is `|Fˣ| = q - 1`.
  have hindex : det.ker.index = Nat.card Fˣ := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective det hsurj, Subgroup.card_top]
  have hcard : Nat.card det.ker * (Nat.card F - 1) = Nat.card (GL (Fin 2) F) := by
    rw [← Nat.card_units F, ← hindex]
    exact Subgroup.card_mul_index det.ker
  -- `|GL(2, F)| = (q ^ 2 - 1) * (q ^ 2 - q)`.
  have hGL : Nat.card (GL (Fin 2) F) =
      (Fintype.card F ^ 2 - 1) * (Fintype.card F ^ 2 - Fintype.card F) := by
    rw [Matrix.card_GL_field 2, Fin.prod_univ_two]
    simp
  have hGL' : Nat.card (GL (Fin 2) F) =
      (Nat.card F ^ 2 - 1) * (Nat.card F ^ 2 - Nat.card F) := by
    rw [hGL, ← hqF]
  -- elementary arithmetic identity.
  have harith : (Nat.card F ^ 2 - 1) * (Nat.card F ^ 2 - Nat.card F)
      = (Nat.card F * (Nat.card F ^ 2 - 1)) * (Nat.card F - 1) := by
    have h1 : Nat.card F ^ 2 - Nat.card F = Nat.card F * (Nat.card F - 1) := by
      have h := Nat.mul_sub_left_distrib (Nat.card F) (Nat.card F) 1
      simp only [mul_one] at h
      rw [pow_two, ← h]
    have h2 : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
      have h := Nat.sq_sub_sq (Nat.card F) 1
      simpa using h
    rw [h1, h2]; ring
  have hfinal : Nat.card det.ker * (Nat.card F - 1) =
      (Nat.card F * (Nat.card F ^ 2 - 1)) * (Nat.card F - 1) := by
    rw [hcard, hGL', harith]
  calc Nat.card (Matrix.SpecialLinearGroup (Fin 2) F)
      = Nat.card det.ker := hsl
    _ = Nat.card F * (Nat.card F ^ 2 - 1) := Nat.mul_right_cancel hpos hfinal

end Commons.GroupTheory.LinearGroup