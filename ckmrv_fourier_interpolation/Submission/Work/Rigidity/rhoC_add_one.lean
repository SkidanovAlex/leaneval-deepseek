import Mathlib
import Submission.Work.Rigidity.LambdaDerivDefs
import Submission.Work.Rigidity.lamC_add_one
import Submission.Work.Rigidity.lamC_neg_inv

namespace Work.Rigidity

open Work.Kernels.LogLambda
open Filter

/-- `θ₀₀` under the translation `z ↦ z + 1`: `θ₀₀ (z + 1) = θ₀₁ z` on the extension to `ℂ`.

This is the `ℂ`-level form of the `T`-law `θ₀₀(τ + 1) = θ₀₁(τ)`, obtained from the
two-variable identity `θ₂(w, τ + 1) = θ₂(w + 1/2, τ)` with `w = 0`. -/
lemma thetaC00_shift_one (z : ℂ) : thetaC00 (z + 1) = thetaC01 z := by
  show jacobiTheta (z + 1) = jacobiTheta₂ (1 / 2) z
  rw [jacobiTheta_eq_jacobiTheta₂, Work.Kernels.jacobiTheta₂_add_one_snd]
  norm_num

/-- The fourth power of `θ₀₀` under `z ↦ z + 1`, in terms of `λ`:
`θ₀₀(z + 1)⁴ = (1 - λ(z)) θ₀₀(z)⁴`.

Indeed `θ₀₀(z+1) = θ₀₁(z)` and `λ_S(z) = θ₀₁(z)⁴/θ₀₀(z)⁴ = 1 - λ(z)` by the quartic identity
`θ₀₀⁴ = θ₀₁⁴ + θ₁₀⁴` (the lemma `lamSC_eq_one_sub_lamC`). -/
lemma thetaC00_pow4_shift_one (z : ℂ) (hz : 0 < z.im) :
    thetaC00 (z + 1) ^ 4 = (1 - lamC z) * thetaC00 z ^ 4 := by
  rw [thetaC00_shift_one]
  have h00 : thetaC00 z ^ 4 ≠ 0 := pow_ne_zero 4 (thetaC00_ne_zero hz)
  have hsc : lamSC z = 1 - lamC z := lamSC_eq_one_sub_lamC z hz
  calc thetaC01 z ^ 4 = (thetaC01 z ^ 4 / thetaC00 z ^ 4) * thetaC00 z ^ 4 := by
        rw [div_mul_cancel₀ _ h00]
    _ = lamSC z * thetaC00 z ^ 4 := by rw [lamSC]
    _ = (1 - lamC z) * thetaC00 z ^ 4 := by rw [hsc]

/-- The derivative of `λ` transforms as `λ'(z + 1) = -λ'(z) / (1 - λ(z))²`.

Differentiating the transformation law `λ(z + 1) = -λ(z)/(1 - λ(z))` (valid on the open
upper half plane `U`, hence on a neighbourhood of `z ∈ U`) with the chain rule. -/
lemma deriv_lamC_shift_one (z : ℂ) (hz : 0 < z.im) :
    deriv lamC (z + 1) = -deriv lamC z / (1 - lamC z)^2 := by
  have hzU : z ∈ U := hz
  have hz1U : z + 1 ∈ U := by
    show 0 < (z + 1).im
    simpa using hz
  have hlam1 : DifferentiableAt ℂ lamC (z + 1) :=
    differentiableOn_lamC.differentiableAt (isOpen_U.mem_nhds hz1U)
  have hlam : DifferentiableAt ℂ lamC z :=
    differentiableOn_lamC.differentiableAt (isOpen_U.mem_nhds hzU)
  have h01 : thetaC01 z ≠ 0 := by
    rw [← thetaC00_shift_one z]
    exact thetaC00_ne_zero hz1U
  have hne : (1 : ℂ) - lamC z ≠ 0 := by
    have hsc : lamSC z = 1 - lamC z := lamSC_eq_one_sub_lamC z hz
    rw [← hsc, lamSC]
    exact div_ne_zero (pow_ne_zero 4 h01) (pow_ne_zero 4 (thetaC00_ne_zero hz))
  have hchain : deriv (fun w : ℂ => lamC (w + 1)) z = deriv lamC (z + 1) := by
    have hg : DifferentiableAt ℂ (fun w : ℂ => w + 1) z := by fun_prop
    change deriv (lamC ∘ fun w : ℂ => w + 1) z = deriv lamC (z + 1)
    rw [deriv_comp (x := z) (h := fun w : ℂ => w + 1) (h₂ := lamC) hlam1 hg]
    simp
  have heq : (fun w : ℂ => lamC (w + 1)) =ᶠ[nhds z]
      (fun w : ℂ => -(lamC w)/(1 - lamC w)) := by
    filter_upwards [isOpen_U.mem_nhds hzU] with w hw
    exact Work.Rigidity.lamC_add_one w hw
  have hderiv1 : deriv (fun w : ℂ => lamC (w + 1)) z
      = deriv (fun w : ℂ => -(lamC w)/(1 - lamC w)) z := Filter.EventuallyEq.deriv_eq heq
  have hquot : deriv (fun w : ℂ => -(lamC w)/(1 - lamC w)) z
      = -deriv lamC z/(1 - lamC z)^2 := by
    have hc : DifferentiableAt ℂ (fun w : ℂ => -(lamC w)) z := hlam.neg
    have hd : DifferentiableAt ℂ (fun w : ℂ => 1 - lamC w) z := hlam.const_sub 1
    change deriv ((fun w : ℂ => -(lamC w)) / (fun w : ℂ => 1 - lamC w)) z
      = -deriv lamC z/(1 - lamC z)^2
    rw [deriv_div hc hd hne]
    have e1 : deriv (fun w : ℂ => -(lamC w)) z = -deriv lamC z := deriv.neg
    have e2 : deriv (fun w : ℂ => 1 - lamC w) z = -deriv lamC z :=
      deriv_const_sub (f := lamC) (1:ℂ) (x := z)
    rw [e1, e2]
    ring
  rw [← hchain, hderiv1, hquot]

/-- **`ρ` is invariant under the translation `z ↦ z + 1`.**  Combining the transformation
laws `λ(z+1) = -λ(z)/(1-λ(z))`, `θ₀₀(z+1)⁴ = (1-λ(z)) θ₀₀(z)⁴` and
`λ'(z+1) = -λ'(z)/(1-λ(z))²` exhibits the numerator and the denominator of
`ρ(z) = λ'(z)/(λ(z)(1-λ(z))θ₀₀(z)⁴)` as transforming by the same factor. -/
theorem rhoC_add_one (z : ℂ) (hz : 0 < z.im) :
    Work.Rigidity.rhoC (z + 1) = Work.Rigidity.rhoC z := by
  have hz1 : 0 < (z + 1).im := by simpa using hz
  have h01 : thetaC01 z ≠ 0 := by
    rw [← thetaC00_shift_one z]
    exact thetaC00_ne_zero hz1
  have h1mne : (1 : ℂ) - lamC z ≠ 0 := by
    have hsc : lamSC z = 1 - lamC z := lamSC_eq_one_sub_lamC z hz
    rw [← hsc, lamSC]
    exact div_ne_zero (pow_ne_zero 4 h01) (pow_ne_zero 4 (thetaC00_ne_zero hz))
  have hlamne : lamC z ≠ 0 := lamC_ne_zero hz
  have h00 : thetaC00 z ≠ 0 := thetaC00_ne_zero hz
  have hlaw : lamC (z + 1) = -(lamC z)/(1 - lamC z) := Work.Rigidity.lamC_add_one z hz
  have h1m' : (1 : ℂ) - (-(lamC z)/(1 - lamC z)) = (1 - lamC z)⁻¹ := by
    field_simp
    ring
  have hT := thetaC00_pow4_shift_one z hz
  have hd := deriv_lamC_shift_one z hz
  simp only [rhoC]
  rw [hd, hlaw, h1m', hT]
  field_simp
  try ring

end Work.Rigidity
