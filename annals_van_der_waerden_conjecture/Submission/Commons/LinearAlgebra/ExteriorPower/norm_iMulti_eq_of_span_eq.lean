import Mathlib
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_norm_eq_of_det_abs_one

/-!
# Norm of `exteriorPower.ιMulti` depends only on the integer span

If two `k`-tuples `a` and `b` are linearly independent over `ℤ` and span the same
`ℤ`-submodule of the real inner product space `E`, then the norms of their
`k`-th exterior products (computed in the real exterior algebra) coincide.

Indeed, both tuples are `ℤ`-bases of the same free `ℤ`-module, so each `b j`
is an integer linear combination of the `a i` with a change-of-basis matrix of
determinant `±1`.  Casting to a real matrix, the norms of the two exterior
products agree by `iMulti_norm_eq_of_det_abs_one`.
-/

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

open Submodule Set
open scoped BigOperators

namespace Commons.LinearAlgebra.ExteriorPower

noncomputable section

/-- If `a` and `b` are `ℤ`-linearly independent and generate the same `ℤ`-submodule,
then the (real) exterior powers of the two families have the same norm. -/
theorem norm_iMulti_eq_of_span_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {k : ℕ} (a b : Fin k → E)
    (hLIa : LinearIndependent ℤ a) (hLIb : LinearIndependent ℤ b)
    (hspan : Submodule.span ℤ (Set.range a) = Submodule.span ℤ (Set.range b)) :
    ‖exteriorPower.ιMulti ℝ k b‖ = ‖exteriorPower.ιMulti ℝ k a‖ := by
  classical
  let Λ : Submodule ℤ E := Submodule.span ℤ (Set.range a)
  -- `a` is a ℤ-basis of Λ.
  let aB : Module.Basis (Fin k) ℤ Λ := Module.Basis.span hLIa
  -- `b` is also a ℤ-basis of the same submodule Λ.
  let b0 : Module.Basis (Fin k) ℤ (Submodule.span ℤ (Set.range b)) := Module.Basis.span hLIb
  let bB : Module.Basis (Fin k) ℤ Λ :=
    b0.map (LinearEquiv.ofEq (Submodule.span ℤ (Set.range b)) Λ hspan.symm)
  -- Change-of-basis matrix (columns give the coordinates of b in the basis a).
  let C : Matrix (Fin k) (Fin k) ℤ := aB.toMatrix bB
  have haB : ∀ i : Fin k, ((aB i : Λ) : E) = a i := by
    intro i
    change ((Module.Basis.span hLIa i : Submodule.span ℤ (Set.range a)) : E) = a i
    simp
  have hbB : ∀ j : Fin k, ((bB j : Λ) : E) = b j := by
    intro j
    simp [bB, b0, LinearEquiv.coe_ofEq_apply]
  -- In E, each b j is the real linear combination of the a i given by column j of C.
  have hbE : ∀ j : Fin k, (∑ i : Fin k, (C i j : ℝ) • a i) = b j := by
    intro j
    have hcoordΛ : (∑ i : Fin k, C i j • aB i) = bB j := by
      simpa [C] using (Module.Basis.sum_toMatrix_smul_self aB bB j)
    have hsub : (Submodule.subtype Λ) (∑ i : Fin k, C i j • aB i) =
        ∑ i : Fin k, C i j • (aB i : E) := by
      rw [map_sum]
      simp
    calc
      (∑ i : Fin k, (C i j : ℝ) • a i)
          = ∑ i : Fin k, C i j • a i := by
              simp [Int.cast_smul_eq_zsmul]
      _ = ∑ i : Fin k, C i j • (aB i : E) := by
              simp_rw [haB]
      _ = (Submodule.subtype Λ) (∑ i : Fin k, C i j • aB i) := hsub.symm
      _ = (Submodule.subtype Λ) (bB j) := by
              rw [hcoordΛ]
      _ = b j := by
              simpa [Submodule.subtype_apply] using hbB j
  -- Since a and b are two bases of the same free ℤ-module, C is invertible over ℤ;
  -- hence its determinant is a unit, i.e. ±1.
  have hCdet_unit : IsUnit C.det := by
    haveI : Invertible C := by simpa [C] using (Module.Basis.invertibleToMatrix aB bB)
    exact (Matrix.isUnit_iff_isUnit_det C).mp (isUnit_of_invertible C)
  have hCdet : C.det = 1 ∨ C.det = -1 := by
    rcases hCdet_unit with ⟨u, hu⟩
    rcases Int.units_eq_one_or u with rfl | rfl
    · left
      exact hu.symm
    · right
      exact hu.symm
  -- Cast C to a real matrix.
  let M : Matrix (Fin k) (Fin k) ℝ := fun i j => (C i j : ℝ)
  have hMmap : M = ((Int.castRingHom ℝ).mapMatrix C) := by
    ext i j
    rfl
  have hMdet : M.det = (C.det : ℝ) := by
    rw [hMmap]
    exact ((Int.castRingHom ℝ).map_det C).symm
  have hMabs : |M.det| = 1 := by
    rcases hCdet with hd | hd
    · rw [hMdet, hd]
      norm_num
    · rw [hMdet, hd]
      norm_num
  -- Apply the change-of-matrix norm invariance.
  exact iMulti_norm_eq_of_det_abs_one
    (u := a) (A := M) (w := b) (hw := fun j => (hbE j).symm) (hdet := hMabs)

end

end Commons.LinearAlgebra.ExteriorPower
