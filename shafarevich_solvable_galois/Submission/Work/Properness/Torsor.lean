/-
Copyright (c) 2025. All rights reserved.

# The set of solutions is a torsor under `Z¹(H, A)`, and `H¹` classifies them

This is the algebraic heart of Proposition 11 and of step 3 of Theorem 15 of

* A. Schmidt, K. Wingberg, *Šafarevič's theorem on solvable groups as Galois groups*,
  arXiv:math/9809211.

In the abstract setting `Work.Properness.Setup` (`1 → A → E → Q → 1` with abelian kernel `A` and a
surjection `ρ : H ↠ Q`), fix a lift `ψ₀` (`π ∘ ψ₀ = ρ`).  Then

* `x ↦ x · ψ₀` (`h ↦ x h * ψ₀ h`, `Setup.mulFun`) is a bijection from `Z¹(H, A)` onto the set
  `Setup.Lift` of all lifts — this is the paper's `θ = x · ψ₀`; packaging it symmetrically, for
  any two lifts `ψ, ψ'` there is a **unique** `x ∈ Z¹(H, A)` with `ψ' = x · ψ`
  (`Work.Properness.exists_unique_smulLift`): *the set of lifts is a `Z¹(H, A)`-torsor*;
* conjugating a lift by an element `a ∈ A` shifts the cocycle by the coboundary `d⁰a`
  (`Work.Properness.conjLift_mulFun`), so the orbits of the conjugation action of `A` on the
  lifts are the `B¹`-cosets;
* consequently the *classes* in `H¹(H, A)` classify the lifts up to conjugation by the kernel
  (`Work.Properness.Setup.liftClass_eq_iff`, the paper's "the space of solutions modulo
  equivalence is a principal homogeneous space over `H¹`"):

  `[x(ψ₀, ψ)] = [x(ψ₀, ψ')] ∈ H¹(H, A)  ↔  ∃ a ∈ A, ψ' = a ψ a⁻¹`.

## Main declarations

* `Work.Properness.Setup.liftClass` — the `H¹`-class of a lift relative to a base lift;
* `Work.Properness.Setup.liftClass_eq_iff` — the classification statement;
* `Work.Properness.Setup.smulLift`, `Setup.smulLift_apply` — the torsor action, and
* `Work.Properness.Setup.conjLift`, `Setup.conjLift_apply` — conjugation by the kernel;
* `Work.Properness.twist_eq_twist_of_isLift` — the twisted action does *not* depend on the lift:
  it is the canonical action `Setup.conjAction` (which factors through `ρ`).
-/
import Mathlib
import Submission.Work.Properness.Defs
import Submission.Work.Properness.cocycleOfLiftFun_mem_Z1
import Submission.Work.Properness.mulFun_cocycleOfLiftFun
import Submission.Work.Properness.cocycleOfLiftFun_eq_of_forall_mulFun
import Submission.Work.Properness.exists_lift_mulFun
import Submission.Work.Properness.exists_unique_smulLift
import Submission.Work.Properness.twist_eq_smul_of_isLift
import Submission.Work.Properness.conjLift_mulFun
import Submission.Work.Properness.liftClass_eq_iff_exists_conj
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Properness

open scoped Classical

noncomputable section

universe u v w

/-- **The class in `H¹(H, A)` of a lift**, relative to a base lift `ψ₀`: the class of the cocycle
`h ↦ ψ h * (ψ₀ h)⁻¹` (`Setup.cocycleOfLiftFun`), i.e. of the unique `x ∈ Z¹(H, A)` with
`ψ = x · ψ₀`. -/
noncomputable def Setup.liftClass {S : Setup.{u, v, w}} (ψ₀ ψ : S.Lift) :
    Work.GroupCohomology.H1 S.H (Additive S.A) :=
  Work.GroupCohomology.H1π S.H (Additive S.A)
    ⟨S.cocycleOfLiftFun ψ₀ ψ,
      cocycleOfLiftFun_mem_Z1 (Universe := Type) (u := PUnit) (v := PUnit) (w := PUnit) (S := S) ψ₀ ψ⟩

/-- **`H¹(H, A)` classifies the lifts up to conjugation by the kernel.**  For a fixed base lift
`ψ₀`, two lifts `ψ`, `ψ'` have the same class in `H¹(H, A)` if and only if they are conjugate by
an element of the abelian kernel `A`.

This is the precise form of the paper's statement that the space of solutions "modulo equivalence"
is a principal homogeneous space over `H¹(G_k, A)`: the equivalence in question is conjugation by
the kernel. -/
theorem Setup.liftClass_eq_iff {S : Setup.{u, v, w}} (ψ₀ ψ ψ' : S.Lift) :
    S.liftClass ψ₀ ψ = S.liftClass ψ₀ ψ' ↔
      ∃ a : S.A, ∀ h : S.H,
        (ψ' : S.H → S.E) h = (a : S.E) * (ψ : S.H → S.E) h * (a : S.E)⁻¹ :=
  liftClass_eq_iff_exists_conj (Universe := Type) (u := PUnit) (v := PUnit) (w := PUnit) (S := S) ψ₀ ψ ψ'

/-- **The twisted action does not depend on the lift.**  For two lifts `ψ₀`, `ψ₀'` of the same
`ρ`, the twisted actions `S.twist ψ₀.1` and `S.twist ψ₀'.1` agree pointwise; both are the
canonical conjugation action `S.conjAction` of `H` on `A`, which is defined through `ρ` alone
(`Work.Properness.twist_eq_smul_of_isLift`).  Thus the cocycles `Z¹(H, A)` of the torsor
structure depend only on the embedding problem and on `ρ`, not on the chosen solution. -/
theorem twist_eq_twist_of_isLift {S : Setup.{u, v, w}} (ψ₀ ψ₀' : S.Lift)
    (h : S.H) (a : Additive S.A) :
    S.twist ψ₀.1 h a = S.twist ψ₀'.1 h a := by
  rw [twist_eq_smul_of_isLift (Universe := Type) (u := PUnit) (v := PUnit) (w := PUnit) (S := S) ψ₀ h a,
    twist_eq_smul_of_isLift (Universe := Type) (u := PUnit) (v := PUnit) (w := PUnit) (S := S) ψ₀' h a]

/-- **The torsor action of `Z¹(H, A)` on the lifts**, realised as a function: `x • ψ` is the
(unique) lift whose underlying homomorphism is `h ↦ x h * ψ h` (`Setup.mulFun`). -/
noncomputable def Setup.smulLift {S : Setup.{u, v, w}}
    (x : Work.GroupCohomology.Z1 S.H (Additive S.A)) (ψ : S.Lift) : S.Lift :=
  Classical.choose (exists_lift_mulFun (Universe := Type) (u := PUnit) (v := PUnit) (w := PUnit) (S := S) ψ x)

/-- The computation rule for the torsor action: `(x • ψ) h = x h * ψ h`. -/
theorem Setup.smulLift_apply {S : Setup.{u, v, w}}
    (x : Work.GroupCohomology.Z1 S.H (Additive S.A)) (ψ : S.Lift) (h : S.H) :
    (S.smulLift x ψ : S.H → S.E) h = S.mulFun x.1 ψ.1 h :=
  Classical.choose_spec (exists_lift_mulFun (Universe := Type) (u := PUnit) (v := PUnit) (w := PUnit) (S := S) ψ x) h

/-- **Conjugation of a lift by an element of the kernel** is again a lift: `(a ψ a⁻¹) h =
a * ψ h * a⁻¹`; it is well defined because `A = ker π` is normal in `E`. -/
noncomputable def Setup.conjLift {S : Setup.{u, v, w}} (a : S.A)
    (ψ : S.Lift) : S.Lift :=
  ⟨{ toFun := fun h => (a : S.E) * ψ.1 h * (a : S.E)⁻¹
     map_one' := by rw [map_one, mul_one, mul_inv_cancel]
     map_mul' := fun x y => by rw [map_mul]; group },
    by
      ext h
      show S.π ((a : S.E) * ψ.1 h * (a : S.E)⁻¹) = S.ρ h
      rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp a.2, ← MonoidHom.comp_apply, ψ.2]
      simp⟩

/-- The computation rule for conjugation by the kernel. -/
theorem Setup.conjLift_apply {S : Setup.{u, v, w}} (a : S.A) (ψ : S.Lift)
    (h : S.H) :
    (S.conjLift a ψ : S.H → S.E) h = (a : S.E) * ψ.1 h * (a : S.E)⁻¹ := rfl

/-- The classification of lifts up to conjugation by `A`, in terms of `Setup.conjLift`. -/
theorem Setup.liftClass_eq_iff_exists_conjLift {S : Setup.{u, v, w}}
    (ψ₀ ψ ψ' : S.Lift) :
    S.liftClass ψ₀ ψ = S.liftClass ψ₀ ψ' ↔ ∃ a : S.A, S.conjLift a ψ = ψ' := by
  rw [Setup.liftClass_eq_iff ψ₀ ψ ψ']
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext (MonoidHom.ext fun h => by rw [Setup.conjLift_apply, ha h])⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, fun h => by rw [← ha]; rfl⟩

end

end Work.Properness
