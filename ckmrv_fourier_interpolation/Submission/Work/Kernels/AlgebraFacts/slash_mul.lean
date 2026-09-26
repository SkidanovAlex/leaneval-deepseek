/-
# The group-algebra action `slash k r` is a *left* action: `slash k (r * s) = slash k s ∘ slash k r`

The weight-`k` action of the group algebra `R = ℂ[SL(2,ℤ)]` on functions `ℍ → ℂ` is defined by

  `slash k r F = ∑_γ c_γ · (F ∣[k] γ)`,   `r = ∑_γ c_γ γ ∈ R`

(`Work.Kernels.slash`).  This file records that it is *multiplicative*: applying the element
`r * s` of the group algebra is applying first `r` and then `s`,

  `slash k (r * s) F = slash k s (slash k r F)`.

For `r = single γ c` and `s = single δ d` this is the identity `(F ∣[k] γ) ∣[k] δ = F ∣[k] (γ*δ)`
of the slash action (`SlashAction.slash_mul`) together with the commuting of the complex
scalars `c, d`; the general case follows by bilinearity, i.e. by the induction principle
`MonoidAlgebra.induction_linear`.  Together with the `ℂ`-linearity in `r`
(`Work.Kernels.AlgebraFacts.slash_smul`) this is what makes the spaces
`Ann_k(J, 𝒫) = {F ∈ 𝒫 : (F ∣[k] r) = 0 for all r ∈ J}` of CKMRV Section 4.2 modules over
`ℂ` and gives them their right-ideal structure.
-/
import Mathlib
import Submission.Work.Kernels.GroupAlgebra

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels.AlgebraFacts

/-! ### Two elementary additivity facts for `slash` in the function variable -/

/-- The weight-`k` action of `r ∈ R` sends the zero function to zero. -/
lemma slash_mul_aux_zero (k : ℤ) (r : Work.Kernels.R) :
    Work.Kernels.slash k r (0 : ℍ → ℂ) = 0 := by
  simp [Work.Kernels.slash]

/-- The weight-`k` action of `r ∈ R` is additive in the function: it is a sum of the additive
maps `F ↦ F ∣[k] γ`. -/
lemma slash_mul_aux_add (k : ℤ) (r : Work.Kernels.R) (F G : ℍ → ℂ) :
    Work.Kernels.slash k r (F + G) = Work.Kernels.slash k r F + Work.Kernels.slash k r G := by
  simp only [Work.Kernels.slash, SlashAction.add_slash, smul_add, Finsupp.sum_add]

/-- **The group algebra acts on functions by slash operators**: applying `r * s` is applying
first `r` and then `s`,

  `slash k (r * s) F = slash k s (slash k r F)`.

This is the multiplicativity of the action `R → (ℍ → ℂ) → (ℍ → ℂ)`, `r ↦ slash k r`; since the
multiplication in `R = ℂ[SL(2,ℤ)]` is the convolution product `γ * δ`, and
`(F ∣[k] γ) ∣[k] δ = F ∣[k] (γ * δ)`, the element `r * s` acts as the composite of `r` and `s`. -/
lemma slash_mul (k : ℤ) (r s : Work.Kernels.R) (F : UpperHalfPlane → ℂ) :
    Work.Kernels.slash k (r * s) F = Work.Kernels.slash k s (Work.Kernels.slash k r F) := by
  have key : ∀ r : Work.Kernels.R, ∀ s : Work.Kernels.R, ∀ F : ℍ → ℂ,
      Work.Kernels.slash k (r * s) F = Work.Kernels.slash k s (Work.Kernels.slash k r F) := by
    intro r
    -- Bilinearity in `r`: it suffices to check `r = single γ c` and to know the statement is
    -- additive in `r`.
    induction r using MonoidAlgebra.induction_linear with
    | zero =>
      intro s F
      simp [slash_mul_aux_zero]
    | add r₁ r₂ ih₁ ih₂ =>
      intro s F
      simp only [add_mul, Work.Kernels.slash_add, slash_mul_aux_add]
      rw [ih₁ s F, ih₂ s F]
    | single γ c =>
      intro s
      -- Bilinearity in `s`, for `r = single γ c` fixed.
      induction s using MonoidAlgebra.induction_linear with
      | zero =>
        intro F
        simp
      | add s₁ s₂ ih₁ ih₂ =>
        intro F
        simp only [mul_add, Work.Kernels.slash_add]
        rw [ih₁ F, ih₂ F]
      | single δ d =>
        -- The two monomials: `single γ c * single δ d = single (γ * δ) (c * d)`, and on the
        -- other side `(F ∣[k] γ) ∣[k] δ = F ∣[k] (γ * δ)`.
        intro F
        rw [MonoidAlgebra.single_mul_single, Work.Kernels.slash_single]
        conv_rhs => rw [Work.Kernels.slash_single, Work.Kernels.slash_single, SL_smul_slash,
          ← SlashAction.slash_mul]
        rw [mul_comm c d, mul_smul]
  exact key r s F

end Work.Kernels.AlgebraFacts
