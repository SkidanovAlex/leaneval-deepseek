import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.Lat.detL_basis_gram

/-!
# A rank-`2` lattice through two independent vectors, with small determinant

Given two `ℤ`-linearly independent vectors `x y : ι → ℤ`, the `ℤ`-span
`L = span ℤ {x, y}` is a rank-`2` sublattice of `ℤ^ι` containing both of them, and its
determinant (= covolume with respect to the Euclidean structure) is at most
`‖x‖ ‖y‖`: indeed `detL L = √(‖x‖²‖y‖² - ⟨x,y⟩²) ≤ √(‖x‖²‖y‖²) = ‖x‖‖y‖` by Cauchy–Schwarz.

The basis used for the computation is `Module.Basis.span hind`, the canonical basis of the span of a
linearly independent family, indexed by `Fin 2`; `detL_basis_gram` identifies `detL` with the square
root of the determinant of the Gram matrix of that basis, which here is the explicit `2 × 2` matrix
`!![‖x‖², ⟨x,y⟩; ⟨x,y⟩, ‖y‖²]`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.Lat

open Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The covolume of the `ℤ`-span of two linearly independent integer vectors is at most the product
of their norms. -/
lemma detL_span_range_le (x y : ι → ℤ) (hind : LinearIndependent ℤ ![x, y]) :
    detL (Submodule.span ℤ (Set.range ![x, y])) ≤ eNorm x * eNorm y := by
  rw [detL_basis_gram _ (Module.Basis.span hind), Matrix.det_fin_two]
  simp only [Matrix.of_apply, Module.Basis.coe_span_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_comm]
  have hmono : Real.sqrt ((∑ k, (x k : ℝ) * (x k : ℝ)) * (∑ k, (y k : ℝ) * (y k : ℝ))
        - (∑ k, (x k : ℝ) * (y k : ℝ)) * (∑ k, (x k : ℝ) * (y k : ℝ)))
      ≤ Real.sqrt ((∑ k, (x k : ℝ) * (x k : ℝ)) * (∑ k, (y k : ℝ) * (y k : ℝ))) :=
    Real.sqrt_le_sqrt (sub_le_self _ (mul_self_nonneg _))
  have hsqrt : Real.sqrt ((∑ k, (x k : ℝ) * (x k : ℝ)) * (∑ k, (y k : ℝ) * (y k : ℝ)))
      = eNorm x * eNorm y := by
    rw [Real.sqrt_mul (Finset.sum_nonneg fun k _ => mul_self_nonneg (x k : ℝ))]
    congr 1
    · rw [eNorm]; congr 1
      exact Finset.sum_congr rfl fun k _ => by rw [pow_two]
    · rw [eNorm]; congr 1
      exact Finset.sum_congr rfl fun k _ => by rw [pow_two]
  exact le_trans hmono (le_of_eq hsqrt)

/-- The span of two linearly independent integer vectors is a rank-`2` lattice containing both,
whose determinant is bounded by the product of the norms. -/
theorem span_pair_lattice {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι → ℤ)
    (hind : LinearIndependent ℤ ![x, y]) :
    ∃ L : Submodule ℤ (ι → ℤ), Work.HP.rk L = 2 ∧ x ∈ L ∧ y ∈ L ∧
      Work.HP.detL L ≤ Work.HP.eNorm x * Work.HP.eNorm y := by
  refine ⟨Submodule.span ℤ (Set.range ![x, y]), ?_, ?_, ?_, ?_⟩
  · rw [Work.HP.rk, Module.finrank_eq_card_basis (Module.Basis.span hind)]
    simp
  · exact Submodule.subset_span ⟨0, rfl⟩
  · exact Submodule.subset_span ⟨1, rfl⟩
  · exact detL_span_range_le x y hind

end Work.HP.Lat
