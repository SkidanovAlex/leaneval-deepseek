import Mathlib
import Submission.Work.BMF.Uspt.base
import Submission.Work.BMF.vkford51_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.Uspt

open Finset
open scoped BigOperators

noncomputable section

/-- Casting the `ℤ`-valued power-sum vector `psVec` to `ℝ` gives the sum of the
`ℝ`-powers of the tuple entries. -/
lemma psVec_cast_real (k r M₁ : ℕ) (a : Fin r → Finset.Icc 1 M₁) (j : Fin k) :
    (psVec k r M₁ a j : ℝ) = ∑ i : Fin r, (((a i : ℕ) : ℝ) ^ ((j : ℕ) + 1)) := by
  rw [psVec]
  push_cast
  rfl

/-- The exponential character turns a product over a finite type into a single character
applied to the sum. -/
lemma eZ_prod_univ {ι : Type*} [Fintype ι] (φ : ι → ℝ) :
    ∏ i, Work.BMF.eZ (φ i) = Work.BMF.eZ (∑ i, φ i) := by
  rw [← eZ_sum]

theorem Yfun_pow_eq (k r M₁ : ℕ) (hr : 1 ≤ r) (hM₁ : 1 ≤ M₁) (γ : Fin k → ℝ) (b : ℕ) :
    (Work.BMF.Yfun k M₁ γ b) ^ r
      = ∑ a : Fin r → Finset.Icc 1 M₁,
          Work.BMF.eZ (∑ j : Fin k, γ j * (b : ℝ) ^ ((j : ℕ) + 1) * (Work.BMF.Uspt.psVec k r M₁ a j : ℝ)) := by
  classical
  have hY : Work.BMF.Yfun k M₁ γ b
      = ∑ a : Finset.Icc 1 M₁,
          Work.BMF.eZ (∑ j : Fin k, γ j * (((a : ℕ) : ℝ) * (b : ℝ)) ^ ((j : ℕ) + 1)) := by
    rw [Work.BMF.Yfun]
    exact (Finset.sum_coe_sort (Finset.Icc 1 M₁)
      (fun a : ℕ => Work.BMF.eZ (∑ j : Fin k, γ j * ((a : ℝ) * (b : ℝ)) ^ ((j : ℕ) + 1)))).symm
  rw [hY, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro a _
  rw [eZ_prod_univ]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc ∑ i : Fin r, γ j * (((a i : ℕ) : ℝ) * (b : ℝ)) ^ ((j : ℕ) + 1)
      = ∑ i : Fin r,
          γ j * (((a i : ℕ) : ℝ) ^ ((j : ℕ) + 1) * (b : ℝ) ^ ((j : ℕ) + 1)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_pow]
    _ = γ j * ∑ i : Fin r,
          (((a i : ℕ) : ℝ) ^ ((j : ℕ) + 1) * (b : ℝ) ^ ((j : ℕ) + 1)) := by
        rw [Finset.mul_sum]
    _ = γ j * ((∑ i : Fin r, ((a i : ℕ) : ℝ) ^ ((j : ℕ) + 1))
          * (b : ℝ) ^ ((j : ℕ) + 1)) := by
        rw [Finset.sum_mul]
    _ = γ j * (b : ℝ) ^ ((j : ℕ) + 1) * (psVec k r M₁ a j : ℝ) := by
        rw [psVec_cast_real]
        ring

end

end Work.BMF.Uspt
