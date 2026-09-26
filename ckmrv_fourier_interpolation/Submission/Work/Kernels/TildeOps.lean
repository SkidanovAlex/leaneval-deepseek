/-
# The operators of the "tilde" ideals `𝓘̃_±`, and the `z`-variable functional equations

CKMRV (3.9) define the right ideals

  `𝓘̃_± = (T - 2I + T⁻¹ ∓ 2S)·R + (I ∓ STS)·R`,

and Proposition `prop:Kpmslashtilde` (Section 4.3) plus Lemma 4.10 assert that the kernels
satisfy `K_±^{(d)}(τ,·) ∣^{z}_{2-d/2} r = 0` for `r ∈ 𝓘̃_±`.

This file introduces the two pointwise operators computing the action of the generators of
`𝓘̃_±` at a given weight, and states the resulting annihilation of `K_±` in the `z` variable.
-/
import Mathlib
import Submission.Work.Kernels.Kernels

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels

/-- The operator `F ↦ F(·+1) - 2F + F(·-1) - 2ε·(F ∣[k] S)`, the action of the first generator
`T - 2I + T⁻¹ - 2εS` of `𝓘̃_ε` at weight `k`. -/
def TildeA (ε : ℤ) (k : ℤ) (F : ℍ → ℂ) : ℍ → ℂ :=
  fun τ => F ((1 : ℝ) +ᵥ τ) - 2 * F τ + F ((-1 : ℝ) +ᵥ τ)
    - 2 * (ε : ℂ) * (F ∣[k] ModularGroup.S) τ

/-- The operator `F ↦ F - ε·(F ∣[k] STS)`, the action of the second generator `I - εSTS` of
`𝓘̃_ε` at weight `k`. -/
def TildeB (ε : ℤ) (k : ℤ) (F : ℍ → ℂ) : ℍ → ℂ :=
  fun τ => F τ - (ε : ℂ) * (F ∣[k] (ModularGroup.S * ModularGroup.T * ModularGroup.S)) τ

/-- `φ̃_{-2}(z) = z²`. -/
def phitNeg2 : ℍ → ℂ := fun z => (z : ℂ) ^ 2

/-- `φ̃_0(z) = z²(E₂|₂S)(z) = z²E₂(z) - 6iz/π`. -/
def phit0 : ℍ → ℂ := fun z => (z : ℂ) ^ 2 * E2S z

/-- `φ̃_2(z) = z²((E₂|₂S)(z))²`. -/
def phit2 : ℍ → ℂ := fun z => (z : ℂ) ^ 2 * (E2S z) ^ 2

end Work.Kernels
