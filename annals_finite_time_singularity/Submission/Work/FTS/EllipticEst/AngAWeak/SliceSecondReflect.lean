/-
# Reflection `θ ↦ π/2 - θ` of the second-order angular slice data

The slice identity of `Cores.AeStep2Aux` lives on the open angular interval
`Iθ = (0, π/2)`, which is **symmetric** about `π/4`.  This file records the behaviour of the
three objects `Φ`, `sliceIntegrand` (and of the class of slices) under the reflection
`ρ θ = π/2 - θ`:

* `C²`-regularity on `(0, π/2)` is preserved: `θ ↦ f (π/2 - θ) ∈ C²`;
* the boundary function `Φ` is **anti-invariant**: `Φ (f ∘ ρ) τ = - Φ f (ρ τ)`;
* the integrand `θ ↦ σ θ f θ f'' θ` is **invariant**:
  `sliceIntegrand (f ∘ ρ) τ = sliceIntegrand f (ρ τ)`.

The reason for the two different signs is that `ρ` reverses orientation
(`deriv (f ∘ ρ) τ = - f' (ρ τ)`, `deriv (deriv (f ∘ ρ)) τ = f'' (ρ τ)`), while the weights
`sig θ = sin(2θ)^{-η}`, `sig1 θ = sin(2θ)^{-(1+η)}` satisfy `sig (ρ τ) = sig τ` and the
*cosine* factor flips: `cos (2 ρ τ) = - cos (2 τ)`.

Used to transfer the second-order slice estimate `∫ σ f f'' ≤ 0` (and its weak / a.e. versions)
from one endpoint to the other.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_second_trunc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-! ## Elementary symmetry facts about the reflection `θ ↦ π/2 - θ` -/

/-- `sin (2 (π/2 - τ)) = sin (2 τ)`: the sine of twice the angle is reflection invariant. -/
private lemma reflSinTwo (τ : ℝ) :
    Real.sin (2 * (Real.pi / 2 - τ)) = Real.sin (2 * τ) := by
  rw [show 2 * (Real.pi / 2 - τ) = Real.pi - 2 * τ by ring, Real.sin_pi_sub]

/-- `cos (2 (π/2 - τ)) = - cos (2 τ)`: the cosine of twice the angle flips sign. -/
private lemma reflCosTwo (τ : ℝ) :
    Real.cos (2 * (Real.pi / 2 - τ)) = -Real.cos (2 * τ) := by
  rw [show 2 * (Real.pi / 2 - τ) = Real.pi - 2 * τ by ring, Real.cos_pi_sub]

/-- The weight `sig θ = sin(2θ)^{-η}` is reflection invariant. -/
private lemma reflSig (τ : ℝ) :
    Work.FTS.EllipticEst.Cores.AeStep2Aux.sig (Real.pi / 2 - τ)
      = Work.FTS.EllipticEst.Cores.AeStep2Aux.sig τ := by
  simp only [Work.FTS.EllipticEst.Cores.AeStep2Aux.sig, reflSinTwo]

/-- The weight `sig1 θ = sin(2θ)^{-(1+η)}` is reflection invariant. -/
private lemma reflSig1 (τ : ℝ) :
    Work.FTS.EllipticEst.Cores.AeStep2Aux.sig1 (Real.pi / 2 - τ)
      = Work.FTS.EllipticEst.Cores.AeStep2Aux.sig1 τ := by
  simp only [Work.FTS.EllipticEst.Cores.AeStep2Aux.sig1, reflSinTwo]

/-! ## The derivatives of a reflected function

Both identities hold *unconditionally*: `deriv` is junk-valued where the derivative does not
exist, and `deriv_comp_const_sub` is exactly the chain rule for the affine reflection. -/

/-- `(f ∘ ρ)' = - (f' ∘ ρ)`. -/
private lemma reflDeriv (f : ℝ → ℝ) :
    deriv (fun θ => f (Real.pi / 2 - θ)) = fun θ => -deriv f (Real.pi / 2 - θ) := by
  funext θ
  exact deriv_comp_const_sub f (Real.pi / 2) θ

/-- `(f ∘ ρ)'' = f'' ∘ ρ` (the two sign flips cancel). -/
private lemma reflDeriv2 (f : ℝ → ℝ) :
    deriv (deriv (fun θ => f (Real.pi / 2 - θ)))
      = fun θ => deriv (deriv f) (Real.pi / 2 - θ) := by
  have h1 : deriv (fun θ : ℝ => f (Real.pi / 2 - θ))
      = fun θ : ℝ => -deriv f (Real.pi / 2 - θ) := reflDeriv f
  rw [h1]
  have h2 : (fun θ : ℝ => -deriv f (Real.pi / 2 - θ))
      = (fun θ : ℝ => (fun x : ℝ => -deriv f x) (Real.pi / 2 - θ)) := rfl
  rw [h2, reflDeriv (fun x : ℝ => -deriv f x)]
  funext θ
  have h3 : deriv (fun x : ℝ => -deriv f x) (Real.pi / 2 - θ)
      = - deriv (deriv f) (Real.pi / 2 - θ) := deriv.neg
  rw [h3]
  ring

/-! ## The reflection lemma -/

theorem SliceSecondReflect {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 2 (fun θ => f (Real.pi / 2 - θ)) (Set.Ioo 0 (Real.pi / 2)) ∧
      (∀ τ ∈ Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.Cores.AeStep2Aux.Phi (fun θ => f (Real.pi / 2 - θ)) τ
          = - Work.FTS.EllipticEst.Cores.AeStep2Aux.Phi f (Real.pi / 2 - τ)) ∧
      (∀ τ ∈ Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.Cores.AeStep2Aux.sliceIntegrand (fun θ => f (Real.pi / 2 - θ)) τ
          = Work.FTS.EllipticEst.Cores.AeStep2Aux.sliceIntegrand f (Real.pi / 2 - τ)) := by
  -- the reflection maps `Iθ = (0, π/2)` to itself
  have hsub : Set.MapsTo (fun θ : ℝ => Real.pi / 2 - θ)
      (Set.Ioo 0 (Real.pi / 2)) (Set.Ioo 0 (Real.pi / 2)) := by
    intro θ hθ
    exact ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  refine ⟨hf.comp ((contDiff_const.sub contDiff_id).contDiffOn) hsub, ?_, ?_⟩
  · intro τ _
    have hd := congrFun (reflDeriv f) τ
    simp only [Work.FTS.EllipticEst.Cores.AeStep2Aux.Phi, hd, reflSig τ, reflSig1 τ]
    rw [reflCosTwo τ]
    ring
  · intro τ _
    have hd2 := congrFun (reflDeriv2 f) τ
    simp only [Work.FTS.EllipticEst.Cores.AeStep2Aux.sliceIntegrand, hd2, reflSig τ]

end Work.FTS.EllipticEst.AngAWeak
