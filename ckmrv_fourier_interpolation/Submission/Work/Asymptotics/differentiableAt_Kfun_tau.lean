/-
# Holomorphy of the CKMRV kernel in `τ` off the pole divisor

The kernel `K^{(d)}(τ,z)` of CKMRV (Theorem 4.9) is a sum of products of holomorphic
functions of `τ` and of `z`, with the only singularities coming from the factors
`(j(τ) − j(z))⁻¹`.  Hence `τ ↦ K^{(d)}(τ,z)` is holomorphic at every `τ` with
`j(τ) ≠ j(z)`; this is the "a.e. `t` holomorphy" hypothesis of the parametric-integral
engine of `Work.Asymptotics.Holomorphy`.

The proof avoids any analysis of the explicit entries of the coefficient matrices `Υ_±`
of Section 4.4: by Theorem 4.9(4) (as formalised in `Work.Kernels.KernelClear_growth_tau`)
the *cleared* kernel `KfunClear` lies in `𝒫`, hence is holomorphic, and the algebra of the
clearing (the `Work.Kernels.ClearLink` lemmas) exhibits `Kfun` off the divisor as
`KfunClear` divided by the (nowhere vanishing there) prefactor
`growthPrefactor d τ z = Δ(τ)Δ(z)^e (j(τ) − j(z))`.  Dividing by a non-vanishing
holomorphic function preserves holomorphy.
-/
import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.Divisor

noncomputable section

open UpperHalfPlane Filter Topology
open scoped Manifold

namespace Work.Asymptotics

/-- **From `𝒫`-holomorphy on `ℍ` to differentiability of the composite with `ofComplex`.**
If `f` is complex differentiable on `ℍ`, then `w ↦ f (ofComplex w)` is complex differentiable
at `(τ : ℂ)`. -/
lemma differentiableAt_comp_ofComplex_of_mdiff {f : UpperHalfPlane → ℂ}
    (h : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (τ : UpperHalfPlane) :
    DifferentiableAt ℂ (fun w : ℂ => f (UpperHalfPlane.ofComplex w)) (τ : ℂ) :=
  UpperHalfPlane.mdifferentiableAt_iff.mp (h τ)

/-- The modular `j`-invariant is holomorphic on `ℍ`, hence `w ↦ j(ofComplex w)` is complex
differentiable at `(τ : ℂ)`. -/
lemma differentiableAt_jInvariantFun_comp_ofComplex (τ : UpperHalfPlane) :
    DifferentiableAt ℂ
      (fun w : ℂ => Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w)) (τ : ℂ) := by
  have hΔ : DifferentiableAt ℂ
      (fun w : ℂ => Work.Kernels.DeltaFun (UpperHalfPlane.ofComplex w)) (τ : ℂ) :=
    differentiableAt_comp_ofComplex_of_mdiff
      Work.Kernels.ClassicalFacts.DeltaFun_mem_InP.1 τ
  have hE4 : DifferentiableAt ℂ
      (fun w : ℂ => Work.Kernels.E4Fun (UpperHalfPlane.ofComplex w)) (τ : ℂ) :=
    differentiableAt_comp_ofComplex_of_mdiff
      Work.Kernels.ClassicalFacts.E4Fun_mem_InP.1 τ
  exact (hE4.pow 3).div hΔ (by simpa using Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)

/-- The growth prefactor `Δ(τ)Δ(z)^e(j(τ) − j(z))` of Theorem 4.9(4) does not vanish at
`(τ,z)` when `j(τ) ≠ j(z)` (all its factors are non-zero there). -/
lemma growthPrefactor_ne_zero (d : ℕ) {τ z : UpperHalfPlane}
    (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    Work.Kernels.growthPrefactor d τ z ≠ 0 := by
  simp only [Work.Kernels.growthPrefactor]
  exact mul_ne_zero
    (mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
      (pow_ne_zero _ (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z)))
    (sub_ne_zero.mpr h)

/-- `w ↦ growthPrefactor d (ofComplex w) z` is complex differentiable at `(τ : ℂ)`
(a product of holomorphic factors). -/
lemma differentiableAt_growthPrefactor_comp_ofComplex (d : ℕ) (τ z : UpperHalfPlane) :
    DifferentiableAt ℂ
      (fun w : ℂ => Work.Kernels.growthPrefactor d (UpperHalfPlane.ofComplex w) z)
      (τ : ℂ) := by
  have hΔ : DifferentiableAt ℂ
      (fun w : ℂ => Work.Kernels.DeltaFun (UpperHalfPlane.ofComplex w)) (τ : ℂ) :=
    differentiableAt_comp_ofComplex_of_mdiff
      Work.Kernels.ClassicalFacts.DeltaFun_mem_InP.1 τ
  have hj := differentiableAt_jInvariantFun_comp_ofComplex τ
  simp only [Work.Kernels.growthPrefactor]
  exact (hΔ.mul_const _).mul (hj.sub_const _)

/-- Off the pole divisor, the cleared kernel of Theorem 4.9(4) is the growth prefactor times
the kernel: `KfunClear = growthPrefactor · Kfun` (the `Kfun` case of the
`Work.Kernels.ClearLink` identities). -/
lemma KfunClear_eq_growthPrefactor_mul (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {τ z : UpperHalfPlane}
    (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    Work.Kernels.KfunClear ℓ d τ z
      = Work.Kernels.growthPrefactor d τ z * Work.Kernels.Kfun ℓ d τ z := by
  simp only [Work.Kernels.KfunClear, Work.Kernels.Kfun]
  rw [Work.Kernels.ClearLink.KPlusClear_eq_smul d hd τ z h,
    Work.Kernels.ClearLink.KMinusClear_eq_smul ℓ d hd τ z h]
  ring

/-- **Holomorphy of the kernel in `τ` off the pole divisor**, in the exact form needed by
`Work.Asymptotics.Holomorphy`: the function `w ↦ K^{(d)}(w,z)` (composed with
`UpperHalfPlane.ofComplex`) is complex differentiable at `τ` whenever `j(τ) ≠ j(z)`.  This is
the "a.e. `t` holomorphy" hypothesis of the parametric-integral engine, since the poles of
`τ ↦ K(τ,z)` are precisely the `SL(2,ℤ)`-orbit of `z`. -/
theorem differentiableAt_Kfun_tau {ℓ : Work.Kernels.LogLambdaData} {d : ℕ} (hd : d = 8 ∨ d = 24)
    {τ z : UpperHalfPlane} (hJ : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    DifferentiableAt ℂ (fun w : ℂ => Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex w) z)
      (τ : ℂ) := by
  -- The cleared kernel is holomorphic (Theorem 4.9(4)).
  have hclear : DifferentiableAt ℂ
      (fun w : ℂ => Work.Kernels.KfunClear ℓ d (UpperHalfPlane.ofComplex w) z) (τ : ℂ) :=
    differentiableAt_comp_ofComplex_of_mdiff
      (Work.Kernels.KernelClear_growth_tau ℓ d hd z).1.1 τ
  -- The growth prefactor is holomorphic and non-vanishing at `τ`.
  have hgp := differentiableAt_growthPrefactor_comp_ofComplex d τ z
  have hgp_ne : Work.Kernels.growthPrefactor d τ z ≠ 0 := growthPrefactor_ne_zero d hJ
  have hne : (fun w : ℂ => Work.Kernels.growthPrefactor d (UpperHalfPlane.ofComplex w) z)
      (τ : ℂ) ≠ 0 := by
    simpa using hgp_ne
  have hdiv := hclear.div hgp hne
  -- Near `τ` the kernel is the cleared kernel divided by the prefactor.
  have hj := differentiableAt_jInvariantFun_comp_ofComplex τ
  have hev : ∀ᶠ w in 𝓝 (τ : ℂ),
      Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w) ≠ Work.Kernels.jInvariantFun z :=
    hj.continuousAt.eventually_ne (by simpa using hJ)
  have heq : (fun w : ℂ => Work.Kernels.KfunClear ℓ d (UpperHalfPlane.ofComplex w) z /
      Work.Kernels.growthPrefactor d (UpperHalfPlane.ofComplex w) z)
      =ᶠ[𝓝 (τ : ℂ)] (fun w : ℂ => Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex w) z) := by
    refine hev.mono (fun w hw => ?_)
    have h1 := KfunClear_eq_growthPrefactor_mul ℓ d hd hw
    rw [div_eq_iff (growthPrefactor_ne_zero d hw), h1]
    ring
  exact hdiv.congr_of_eventuallyEq heq.symm

end Work.Asymptotics
