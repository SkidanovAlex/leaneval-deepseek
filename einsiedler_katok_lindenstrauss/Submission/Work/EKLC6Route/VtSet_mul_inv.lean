import Mathlib
import Submission.Work.EKLC6Route.Defs

/-!
# `VtSet t` is closed under multiplication and inversion

`VtSet t = {g ∈ SL₃(ℝ) | g i j = 0 whenever t i < t j}` is the "parabolic" set `G⁰G⁺(t)` of the
EKL route (`Submission/Work/EKLComp/C6GEOM_ROUTE_LEAD.md` §3).  This file proves that it is closed
under the group operations of `SL₃(ℝ)`, i.e. that it is a subgroup.

The mathematical content is the classical step-pattern computation.

* **Multiplication.**  For `t i < t j` the `(i,j)`-entry of the product is
  `(g * h) i j = ∑_k g i k * h k j`, and every summand vanishes: if `g i k ≠ 0` then
  `¬ (t i < t k)`, so `t k ≤ t i < t j`, whence `h k j = 0`.  (Both the products and the
  non-vanishing statement are recorded here in the general `Matrix.BlockTriangular` language.)

* **Inversion.**  The inverse of `g` in `Matrix.SpecialLinearGroup` is its adjugate
  (`↑g⁻¹ = (↑g).adjugate`, `Matrix.SpecialLinearGroup.coe_inv`), and since `det g = 1` the
  adjugate is the nonsingular inverse of `↑g` (`adjugate_eq_inv_of_det_eq_one`).

Both closures are instances of the general fact that *block triangular* matrices are closed under
products (`Matrix.BlockTriangular.mul`) and under inversion
(`Matrix.blockTriangular_inv_of_blockTriangular`), once `VtSet t` is recognised as the set of
matrices that are block triangular for the weight `t` read through the dual order
(`mem_VtSet_iff_blockTriangular`).

The final statement `VtSet_mul_inv` is the aggregation of these two closure properties in the exact
form requested by the route (lemma `L1 — BIGCELL`, first conjunct).
-/

set_option linter.style.haveILetI false

namespace Work.EKLC6Route

open Work.EKLContract

/-- A matrix with determinant `1` has adjugate equal to its nonsingular inverse. -/
theorem adjugate_eq_inv_of_det_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.det = 1) : M.adjugate = M⁻¹ := by
  have h : M * M.adjugate = 1 := by rw [Matrix.mul_adjugate, hM, one_smul]
  exact (Matrix.inv_eq_right_inv h).symm

/-- `VtSet t` is the set of matrices that are block triangular for the weight `t` read through the
dual order: the condition `t i < t j → g i j = 0` is `b j < b i → g i j = 0` for
`b = OrderDual.toDual ∘ t`. -/
theorem mem_VtSet_iff_blockTriangular (t : Fin 3 → ℝ) (g : SL3) :
    g ∈ VtSet t ↔
      (g : Matrix (Fin 3) (Fin 3) ℝ).BlockTriangular (fun i => OrderDual.toDual (t i)) := by
  rw [VtSet]
  constructor
  · intro h i j hij
    exact h i j (OrderDual.toDual_lt_toDual.mp hij)
  · intro h i j hij
    exact h (OrderDual.toDual_lt_toDual.mpr hij)

theorem VtSet_mul_inv (t : Fin 3 → ℝ) :
    (∀ g h : Work.EKLContract.SL3, g ∈ Work.EKLC6Route.VtSet t →
        h ∈ Work.EKLC6Route.VtSet t → g * h ∈ Work.EKLC6Route.VtSet t) ∧
    (∀ g : Work.EKLContract.SL3, g ∈ Work.EKLC6Route.VtSet t →
        g⁻¹ ∈ Work.EKLC6Route.VtSet t) := by
  constructor
  · intro g h hg hh
    rw [mem_VtSet_iff_blockTriangular] at hg hh ⊢
    simpa using hg.mul hh
  · intro g hg
    rw [mem_VtSet_iff_blockTriangular] at hg ⊢
    haveI : Invertible (g : Matrix (Fin 3) (Fin 3) ℝ) :=
      Matrix.invertibleOfIsUnitDet _ (by rw [g.det_coe]; exact isUnit_one)
    rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_eq_inv_of_det_eq_one g.det_coe]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

end Work.EKLC6Route
