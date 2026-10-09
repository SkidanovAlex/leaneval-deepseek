/-
Copyright (c) 2025. All rights reserved.

# Conjugation of the torsor action `x · ψ` by an element of the abelian kernel

Let `S` be the abstract setting of an embedding problem with abelian kernel
(`Work.Properness.Setup`): `1 → A → E → Q → 1` with `A = ker π` abelian, `ρ : H ↠ Q` the map to
be lifted.  A lift `ψ` (a homomorphism `H →* E` with `π ∘ ψ = ρ`) and a `1`-cocycle
`x ∈ Z¹(H, A)` produce the lift `S.mulFun x.1 ψ.1` (`h ↦ x h · ψ h`).

The present file computes the effect of conjugating this lift by an element `a ∈ A` **inside `E`**.
Since `A` is normal in `E`, conjugation by `a` permutes the lifts; since `A` is abelian, it acts on
`A` trivially, so a conjugate of a lift of the shape `x · ψ` is again of that shape, with a
translated cocycle coordinate.  The translation is exactly the coboundary of the kernel element:

`a · (x h · ψ h) · a⁻¹ = (x + d⁰(-a)) h · ψ h`   for all `h : H`,

i.e. conjugation by `a` shifts `x` by `d⁰(-a)` (`-a` being the inverse of `a` written additively in
`Additive A`).  This is the compatibility of the torsor structure on the set of lifts with the
action of the kernel by conjugation, i.e. the statement that the natural `A`-action on the torsor
is the one induced by the `Z¹(H, A)`-torsor structure via `d⁰` — the computation used when
constraining a lift up to conjugacy.

## Proof

Write `u = x h ∈ A`, `A₀ = a ∈ E` and `p = ψ h ∈ E`.  The right hand side is

`(x + d⁰(-a)) h · p = u · (h • (-a) - a)·p = u · p · a⁻¹ · p⁻¹ · a · p`,

because `h • (-a) = -h • a` and `h • a = p a p⁻¹` is conjugation by `p`
(`Work.Properness.twist_eq_smul_of_isLift`).  Multiplying the left hand side out and using that
`A` is abelian (so that `A₀` commutes with `u` and with `p a⁻¹ p⁻¹ ∈ A`), both sides reduce to
`u · a · p · a⁻¹`.  The elementary group manipulation is isolated in the private lemma
`conj_mul_cancel`.

## Note on universe parameters

The statement uses the anonymous universe binder `{u v w : Universe}` of the requester
(`Universe` is not a Lean 4 identifier, so with `autoImplicit` enabled the binder is auto-bound and
`u v w` are dummy term variables, while the universe levels of `Setup.{u, v, w}` are the
auto-bound *levels* of the same names).  The library is built with `autoImplicit = false`, so we
enable it locally, exactly as the sibling files of this directory do.
-/
import Mathlib
import Submission.Work.Properness.Defs
import Submission.Work.Properness.twist_eq_smul_of_isLift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit true

namespace Work.Properness

open Work.AbsoluteGalois

/-- **The elementary group manipulation behind `conjLift_mulFun`.**

In a group, let `A U X P` be elements with `A` commuting with `U`, `X` commuting with `A` and
`X = P * A⁻¹ * P⁻¹`.  Then

`A * (U * P) * A⁻¹ = U * (X * A) * P`,

both sides being the word `U * A * P * A⁻¹`. -/
private lemma conj_mul_cancel {G : Type*} [Group G] (A U X P : G) (h1 : A * U = U * A)
    (h2 : X * A = A * X) (hX : X = P * A⁻¹ * P⁻¹) :
    A * (U * P) * A⁻¹ = U * (X * A) * P := by
  subst hX
  rw [h2]
  rw [← mul_assoc A U P]
  rw [h1]
  group

/-- **Conjugation by a kernel element shifts the cocycle of a lift by `d⁰`.**

For `a ∈ A = ker π`, a `1`-cocycle `x ∈ Z¹(H, A)`, a lift `ψ` and `h : H`,

`a · (x h · ψ h) · a⁻¹ = (x + d⁰(-a)) h · ψ h`,

i.e. conjugating the lift `x · ψ` by `a` inside `E` gives the lift whose `Z¹`-coordinate is
`x + d⁰(-a)`. -/
theorem conjLift_mulFun {u v w : Universe} {S : Work.Properness.Setup.{u, v, w}} (a : S.A) (x : Work.GroupCohomology.Z1 S.H (Additive S.A)) (ψ : S.Lift) (h : S.H) : (a : S.E) * S.mulFun x.1 ψ.1 h * (a : S.E)⁻¹ = S.mulFun (x + S.d0Z1 (-(Additive.ofMul a))).1 ψ.1 h := by
  -- value of the shifted cocycle at `h`
  have hcochain : (x + S.d0Z1 (-(Additive.ofMul a))).1 h
      = x.1 h + (h • (-(Additive.ofMul a)) - (-(Additive.ofMul a))) := by
    simp only [AddSubgroup.coe_add, Pi.add_apply, Setup.d0Z1_apply]
  -- the action of `h` on `-a` is conjugation by `ψ h`
  have hact : h • (-(Additive.ofMul a)) = Additive.ofMul (conjKernelMul S.π (ψ.1 h) a⁻¹) := by
    have h1 :=
      (twist_eq_smul_of_isLift (u := u) (v := v) (w := w) ψ h (-(Additive.ofMul a))).symm
    simpa [Setup.twist] using h1
  rw [Setup.mulFun, Setup.mulFun, hcochain, hact]
  simp only [toMul_add, toMul_sub, toMul_neg, toMul_ofMul, Subgroup.coe_mul, Subgroup.coe_div,
    Subgroup.coe_inv]
  rw [div_eq_mul_inv, inv_inv]
  -- `a` commutes with `x h` (both lie in the abelian kernel)
  have h1 : (a : S.E) * (↑(Additive.toMul (x.1 h)) : S.E)
      = (↑(Additive.toMul (x.1 h)) : S.E) * (a : S.E) := by
    simpa using congrArg Subtype.val (S.ker_comm a (x.1 h).toMul)
  -- `a` commutes with the conjugate `ψ h * a⁻¹ * (ψ h)⁻¹ ∈ A`
  have h2 : (↑(conjKernelMul S.π (ψ.1 h) a⁻¹) : S.E) * (a : S.E)
      = (a : S.E) * (↑(conjKernelMul S.π (ψ.1 h) a⁻¹) : S.E) := by
    simpa using congrArg Subtype.val (S.ker_comm (conjKernelMul S.π (ψ.1 h) a⁻¹) a)
  exact conj_mul_cancel (a : S.E) (↑(Additive.toMul (x.1 h)))
    (↑(conjKernelMul S.π (ψ.1 h) a⁻¹)) (↑(ψ.1 h)) h1 h2 rfl

end Work.Properness
