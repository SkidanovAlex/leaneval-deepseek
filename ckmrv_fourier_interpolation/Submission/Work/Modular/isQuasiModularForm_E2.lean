import Mathlib
import Submission.Work.Modular.Basic

/-!
# `E₂` is a quasimodular form of weight `2` and depth `1`

The space `M_2(𝒮ℒ)` of holomorphic modular forms of weight `2` for the full modular
group is trivial, so the weight-two Eisenstein series `E₂` -- which is *not* modular,
`E₂(-1/τ) = τ² E₂(τ) - 6iτ/π` -- is a genuine depth-one quasimodular form.

The witnessing representation of `IsQuasiModularForm 2 E2` is the tautological one

  `E₂ = E₂ ^ 0 * m₀ + E₂ ^ 1 * m₁ = m₀ + E₂ * m₁`

with vanishing weight-two component `m₀ = 0` and constant weight-zero component
`m₁ = 1` (the constant function `1` as a modular form of weight `0`).  Everything is
bookkeeping: the only point requiring care is that the `j = 1` summand of
`IsQuasiModularFormDepth 1 2` has index type `ModularForm 𝒮ℒ (2 - 2 * 1)`, so the
weight-zero constant form has to be transported along the (propositional, not
definitional) equality `2 - 2 * 1 = 0` of integers.
-/

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

/-- Transporting a modular form along an equality of weights does not change the
underlying function `ℍ → ℂ`. -/
theorem coe_cast_weight {k k' : ℤ} (h : k = k') (g : ModularForm 𝒮ℒ k) :
    ⇑(h ▸ g : ModularForm 𝒮ℒ k') = ⇑g := by
  subst h
  rfl

/-- For the nonzero index `j : Fin 2`, the weight `2 - 2 j` of the `j`-th summand in
`IsQuasiModularFormDepth 1 2` is `0`.  (Stated with the orientation used for
transporting the constant modular form `1` of weight `0`.) -/
theorem zero_eq_two_sub_two_mul {j : Fin 2} (hj : (j : ℕ) ≠ 0) :
    (0 : ℤ) = 2 - 2 * (j : ℤ) := by
  have hj1 : (j : ℤ) = 1 := by
    have : (j : ℕ) = 1 := by omega
    omega
  rw [hj1]
  norm_num

theorem isQuasiModularForm_E2 : IsQuasiModularForm 2 E2 := by
  refine ⟨fun j => if h : (j : ℕ) = 0 then
      (0 : ModularForm 𝒮ℒ (2 - 2 * (j : ℤ)))
    else (zero_eq_two_sub_two_mul h) ▸ (1 : ModularForm 𝒮ℒ 0), ?_⟩
  rw [Fin.sum_univ_two]
  simp

end Work.Modular
