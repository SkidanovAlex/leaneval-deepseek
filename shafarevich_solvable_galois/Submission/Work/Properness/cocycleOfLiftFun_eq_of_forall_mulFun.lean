/-
# The `Z¹`-torsor action is injective on the difference map

If two lifts `ψ₀`, `ψ` differ by the pointwise product with a `1`-cocycle `x`,

`ψ h = x h * ψ₀ h`   (`Setup.mulFun x ψ₀ h`),

then the difference cocycle `Setup.cocycleOfLiftFun ψ₀ ψ` recovers `x`:
`cocycleOfLiftFun ψ₀ ψ h = x h` for every `h : H`.

This is the injectivity half of the statement that the lifts form a torsor under `Z¹(H, A)`
(`Work.Properness.Torsor`); the computation is a one-line cancellation in `E`.
-/
import Mathlib
import Submission.Work.Properness.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit true

namespace Work.Properness

theorem cocycleOfLiftFun_eq_of_forall_mulFun {u v w : Universe} {S : Work.Properness.Setup.{u, v, w}} (ψ₀ ψ : S.Lift) (x : Work.GroupCohomology.Z1 S.H (Additive S.A)) (hx : ∀ h : S.H, (ψ : S.H → S.E) h = S.mulFun x.1 ψ₀.1 h) (h : S.H) : S.cocycleOfLiftFun ψ₀ ψ h = x.1 h := by
  show Additive.ofMul ⟨ψ.1 h * (ψ₀.1 h)⁻¹, _⟩ = x.1 h
  apply Additive.ofMul.injective
  apply Subtype.ext
  show ψ.1 h * (ψ₀.1 h)⁻¹ = ((x.1 h).toMul : S.E)
  rw [hx h]
  show ((((x.1 h).toMul : S.A) : S.E) * ψ₀.1 h) * (ψ₀.1 h)⁻¹ = ((x.1 h).toMul : S.E)
  group

end Work.Properness
