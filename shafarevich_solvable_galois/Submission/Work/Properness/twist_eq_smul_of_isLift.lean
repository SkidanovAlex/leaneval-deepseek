/-
Copyright (c) 2025. All rights reserved.

# The twisted action of a lift is the canonical conjugation action

This file contains the elementary computation underlying the statement (in the header of
`Submission/Work/Properness/Defs.lean`) that the action `Setup.twistedAction ψ₀` attached to a
*homomorphism* `ψ₀ : H →* E` agrees with the canonical conjugation action `Setup.conjAction` of
`H` on the abelian kernel `A = ker π` **as soon as `ψ₀` is a lift**, i.e. `π ∘ ψ₀ = ρ`.

Concretely, `h • a` for the canonical action is conjugation by a normalized set-theoretic section
`σ` of `π`, evaluated at `ρ h`: `conjKernelMul π (σ (ρ h)) a`.  For a lift, `π (ψ₀ h) = ρ h`, so
`ψ₀ h` and `σ (ρ h)` differ by an element `u ∈ A = ker π`:

`ψ₀ h = σ (ρ h) · u`.

Since `A` is abelian, conjugation by `u` is trivial, hence

`conjKernelMul π (ψ₀ h) a = conjKernelMul π (σ (ρ h)) (conjKernelMul π u a)
                          = conjKernelMul π (σ (ρ h)) a`,

which is exactly `twist ψ₀ h a = h • a`.

## Note on universe parameters

The abstract setting `Work.Properness.Setup` is universe-polymorphic in `H`, `E`, `Q`; the theorem
below is stated with the workspace's convention (the binders `{u v w : Universe}` of the delegated
statement, elaborated with `autoImplicit` enabled, which also introduces the universe parameters
`u`, `v`, `w` used in `Setup.{u, v, w}`).
-/
import Mathlib
import Submission.Work.Properness.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe x y z

namespace Work.Properness

open Work.AbsoluteGalois (conjKernelMul conjKernelMul_mul_eq conjKernelMul_of_mem_ker)

/-- **Conjugation by a lift value is conjugation by the canonical section.**  For a lift `ψ₀` and
`h : H`, the elements `ψ₀ h` and `S.normSection (S.ρ h)` have the same image under `π`; hence they
differ by an element `c ∈ A = ker π`, and since `A` is abelian, conjugation by `c` is trivial:

`conjKernelMul π (ψ₀ h) a = conjKernelMul π (normSection (ρ h)) (conjKernelMul π c a)
                          = conjKernelMul π (normSection (ρ h)) a`.

This is the key computation behind `Setup.twist_eq_smul_of_isLift`. -/
theorem conjKernelMul_lift_eq {S : Work.Properness.Setup.{x, y, z}}
    (ψ₀ : S.Lift) (h : S.H) (a : Additive S.A) :
    conjKernelMul S.π (ψ₀.1 h) (Additive.toMul a)
      = conjKernelMul S.π (S.normSection (S.ρ h)) (Additive.toMul a) := by
  have hπ : S.π (ψ₀.1 h) = S.ρ h := by
    rw [← MonoidHom.comp_apply, ψ₀.2]
  have hc : (S.normSection (S.ρ h))⁻¹ * ψ₀.1 h ∈ S.π.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, S.normSection_spec, hπ, inv_mul_cancel]
  set c : S.π.ker := ⟨(S.normSection (S.ρ h))⁻¹ * ψ₀.1 h, hc⟩ with hc_def
  have hsplit : S.normSection (S.ρ h) * (c : S.E) = ψ₀.1 h := by
    rw [hc_def]
    group
  rw [← hsplit, conjKernelMul_mul_eq, conjKernelMul_of_mem_ker S.π S.ker_comm c]

set_option autoImplicit true in
/-- **The twisted action attached to a lift is the canonical conjugation action.**  For a lift `ψ₀`
(so that `π ∘ ψ₀ = ρ`), the action `twist ψ₀` on the abelian kernel `A` is independent of the lift
and agrees with the canonical action `conjAction` of `H` on `A`, i.e. with the conjugation action
of `Q = E/A` pulled back along `ρ`. -/
theorem twist_eq_smul_of_isLift {u v w : Universe} {S : Work.Properness.Setup.{u, v, w}} (ψ₀ : S.Lift) (h : S.H) (a : Additive S.A) : S.twist ψ₀.1 h a = h • a := by
  show Additive.ofMul (conjKernelMul S.π (ψ₀.1 h) (Additive.toMul a)) = h • a
  rw [conjKernelMul_lift_eq ψ₀ h a]
  rfl

end Work.Properness
