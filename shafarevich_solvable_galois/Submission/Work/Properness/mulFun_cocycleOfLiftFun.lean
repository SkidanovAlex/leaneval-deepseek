import Mathlib
import Submission.Work.Properness.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

-- The library is built with `autoImplicit = false`; the statement of the target lemma (written
-- by the requester) uses the anonymous universe-type binder `Universe`, so we enable
-- `autoImplicit` locally for this file to elaborate it exactly as stated.
set_option autoImplicit true

namespace Work.Properness

/-- **The two constructions `x ↦ x · ψ₀` and `ψ ↦ ψ - ψ₀` are inverse.**

The pointwise product of the `1`-cocycle `cocycleOfLiftFun ψ₀ ψ` (the "difference" of the two
lifts `ψ` and `ψ₀`, `h ↦ ψ h * (ψ₀ h)⁻¹`) with the homomorphism `ψ₀` recovers `ψ`:
`(cocycleOfLiftFun ψ₀ ψ) · ψ₀ = ψ`.  This is the elementwise form of the statement that the map
`Z¹(H, A) → {lifts}`, `x ↦ x · ψ₀`, is a bijection with inverse `ψ ↦ ψ - ψ₀`. -/
theorem mulFun_cocycleOfLiftFun {u v w : Universe} {S : Work.Properness.Setup.{u, v, w}} (ψ₀ ψ : S.Lift) (h : S.H) : S.mulFun (S.cocycleOfLiftFun ψ₀ ψ) ψ₀.1 h = (ψ : S.H → S.E) h := by
  simp only [Setup.mulFun, Setup.cocycleOfLiftFun]
  show ((ψ.1 h * (ψ₀.1 h)⁻¹) : S.E) * ψ₀.1 h = ψ.1 h
  group

end Work.Properness
