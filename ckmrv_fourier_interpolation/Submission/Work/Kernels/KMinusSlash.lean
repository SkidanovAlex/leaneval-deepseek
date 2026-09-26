/-
# The functional equations of `K_-` in group-algebra form

Bridges the pointwise statements `Work.Kernels.KernelFacts.KMinus_T2` and
`Work.Kernels.KernelFacts.KMinus_Sopm` to the group-algebra form `K_- |^τ_{d/2} r = 0`
for `r ∈ 𝓘₋`.
-/
import Mathlib
import Submission.Work.Kernels.KernelSlash
import Submission.Work.Kernels.KernelFacts.KMinus_T2
import Submission.Work.Kernels.KernelFacts.KMinus_Sopm
import Submission.Work.Kernels.KernelFacts.KPlus_S_add

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels

/-- `K_-^{(d)}` is annihilated by `(T-I)²` in the `τ` variable at weight `d/2`. -/
theorem KMinus_slash_T2 (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    slash ((d : ℤ) / 2) ((R_T - 1) ^ 2) (fun τ => KMinus ℓ d τ z) = 0 := by
  rw [slash_T2]
  exact KernelFacts.KMinus_T2 ℓ d hd z

/-- `K_-^{(d)}` is annihilated by `S-I` in the `τ` variable at weight `d/2`. -/
theorem KMinus_slash_S_sub (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    slash ((d : ℤ) / 2) (R_S - 1) (fun τ => KMinus ℓ d τ z) = 0 := by
  rw [slash_S_sub_op]
  exact KernelFacts.KMinus_Sopm ℓ d hd z


/-- `K̂ = -K|^τ_{d/2}S`: the consequence of `K_+|S = -K_+` and `K_-|S = K_-` that the paper
uses to pass between `K` and `K̂`. -/
theorem Khat_eq_neg_slash (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    (fun τ : ℍ => Khat ℓ d τ z)
      = fun σ : ℍ => - ((((fun τ : ℍ => Kfun ℓ d τ z) ∣[((d : ℤ) / 2)] ModularGroup.S) σ)) := by
  have h1' : ∀ σ : ℍ, ((fun τ : ℍ => KPlus d τ z) ∣[((d : ℤ) / 2)] ModularGroup.S) σ
      = - KPlus d σ z := by
    intro σ
    have hh := congr_fun (KernelFacts.KPlus_S_add d hd z) σ
    simp only [Sop, Pi.zero_apply] at hh
    linear_combination hh
  have h2' : ∀ σ : ℍ, ((fun τ : ℍ => KMinus ℓ d τ z) ∣[((d : ℤ) / 2)] ModularGroup.S) σ
      = KMinus ℓ d σ z := by
    intro σ
    have hh := congr_fun (KernelFacts.KMinus_Sopm ℓ d hd z) σ
    simp only [Sopm, Pi.zero_apply] at hh
    linear_combination hh
  ext σ
  have key : ((fun τ : ℍ => Kfun ℓ d τ z) ∣[((d : ℤ) / 2)] ModularGroup.S) σ
      = (2:ℂ)⁻¹ * (((fun τ : ℍ => KPlus d τ z) ∣[((d : ℤ) / 2)] ModularGroup.S) σ)
        + (2:ℂ)⁻¹ * (((fun τ : ℍ => KMinus ℓ d τ z) ∣[((d : ℤ) / 2)] ModularGroup.S) σ) := by
    have hsplit : (fun τ : ℍ => Kfun ℓ d τ z)
        = (2:ℂ)⁻¹ • ((fun τ : ℍ => KPlus d τ z) + (fun τ : ℍ => KMinus ℓ d τ z)) := by
      funext τ; simp [Kfun]; ring
    rw [hsplit, SL_smul_slash, SlashAction.add_slash]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [key, h1', h2']
  simp only [Khat]
  ring

end Work.Kernels
