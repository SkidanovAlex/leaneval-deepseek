import Mathlib
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Asymptotics.Kfun_principal_part_z_lip
import Submission.Work.Kernels.KernelGrowth

namespace Work.Asymptotics

open UpperHalfPlane
open scoped Manifold

open Work.Kernels Work.Residues

/-- The first-variable holomorphy of the cleared kernel: for fixed `z`, the function
`τ ↦ AfunFun ℓ d τ z` is holomorphic on `ℍ`.  This is the `τ`-companion of
`Work.Asymptotics.mdifferentiable_AfunFun_snd`. -/
lemma mdifferentiable_AfunFun_fst (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (z : ℍ) :
    MDiff (fun τ : ℍ => Work.Asymptotics.AfunFun ℓ d τ z) := by
  intro τ
  have h1 := Work.Residues.mdifferentiableAt_AfunPlus d hd z τ
  have h2 := Work.Residues.mdifferentiableAt_AfunMinus ℓ d hd z τ
  have h3 : (fun τ : ℍ => AfunFun ℓ d τ z)
      = fun τ : ℍ => (AfunPlus d z τ + AfunMinus ℓ d z τ) / 2 := rfl
  rw [h3]
  exact (h1.add h2).div mdifferentiableAt_const (by norm_num)

theorem differentiableOn_AfunFun_fst (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : UpperHalfPlane) :
    DifferentiableOn ℂ (fun τ : ℂ => Work.Asymptotics.AfunFun ℓ d (UpperHalfPlane.ofComplex τ) z)
      {τ : ℂ | 0 < τ.im} :=
  UpperHalfPlane.mdifferentiable_iff.mp (mdifferentiable_AfunFun_fst ℓ d hd z)

end Work.Asymptotics
