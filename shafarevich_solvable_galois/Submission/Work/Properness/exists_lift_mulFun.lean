/-
Copyright (c) 2025. All rights reserved.

# The torsor structure of the solutions of an embedding problem with abelian kernel:
`x · ψ₀` is a lift

Let `S` be the abstract setting of an embedding problem with abelian kernel
(`Work.Properness.Setup`): `1 → A → E → Q → 1` with `A = ker π` abelian, and `ρ : H ↠ Q` the
map to be lifted.  A **lift** is a homomorphism `ψ : H →* E` with `π ∘ ψ = ρ`.

For a lift `ψ₀` and a `1`-cocycle `x ∈ Z¹(H, A)` (for the canonical action of `H` on the kernel,
i.e. conjugation inside `E` pulled back along `ρ`, see `Setup.conjAction`), the pointwise product

`θ h = x h · ψ₀ h`

is again a lift: `Work.Properness.exists_lift_mulFun`.  This is `θ = x · ψ₀` of Proposition 11 of
Schmidt–Wingberg and the raw ingredient of the statement that the set of lifts is a torsor under
`Z¹(H, A)` (with inverse `ψ ↦ ψ - ψ₀`, see `Work.Properness.mulFun_cocycleOfLiftFun`).

## Main declarations

* `Work.Properness.pi_apply_lift` — `π (ψ₀ h) = ρ h`;
* `Work.Properness.conjKernelMul_lift_eq_normSection` — conjugation by `ψ₀ h` and by the
  canonical section `normSection (ρ h)` agree on the kernel;
* `Work.Properness.twist_eq_smul_of_lift` — for a lift, the twisted action `Setup.twist ψ₀.1` is the
  canonical action `Setup.conjAction`;
* `Work.Properness.mulFun_one_of_Z1`, `Work.Properness.mulFun_mul_of_Z1`,
  `Work.Properness.pi_mulFun_of_Z1` — `S.mulFun x.1 ψ₀.1` is a homomorphism `H →* E` over `ρ`;
* `Work.Properness.exists_lift_mulFun` — the requested statement;
* `Work.Properness.exists_lift_of_mulFun` — the same statement with the harmless universe binder
  `{u v w : Universe}` of the requested form discharged, i.e. the usable form of the lemma.
-/
import Mathlib
import Submission.Work.Properness.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Properness

noncomputable section

open Work.AbsoluteGalois (conjKernelMul conjKernelMul_mul_eq conjKernelMul_of_mem_ker)

/-- For a lift `ψ₀`, the value `ψ₀ h` maps to `ρ h` under the quotient map `π`. -/
theorem pi_apply_lift {S : Setup} (ψ₀ : S.Lift) (h : S.H) : S.π (ψ₀.1 h) = S.ρ h := by
  rw [← MonoidHom.comp_apply, ψ₀.2]

/-- **Conjugation by a lift value is conjugation by the canonical section.**  For a lift `ψ₀` and
`h : H`, the elements `ψ₀ h` and `S.normSection (S.ρ h)` have the same image under `π`; hence they
differ by an element `u ∈ A = ker π`, and since `A` is abelian, conjugation by `u` is trivial:

`conjKernelMul π (ψ₀ h) a = conjKernelMul π (normSection (ρ h)) (conjKernelMul π u a)
                          = conjKernelMul π (normSection (ρ h)) a`. -/
theorem conjKernelMul_lift_eq_normSection {S : Setup} (ψ₀ : S.Lift) (h : S.H) (a : S.A) :
    conjKernelMul S.π (ψ₀.1 h) a = conjKernelMul S.π (S.normSection (S.ρ h)) a := by
  have hπ : S.π (ψ₀.1 h) = S.ρ h := pi_apply_lift ψ₀ h
  have hu : (S.normSection (S.ρ h))⁻¹ * ψ₀.1 h ∈ S.π.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, S.normSection_spec, hπ, inv_mul_cancel]
  set u : S.π.ker := ⟨(S.normSection (S.ρ h))⁻¹ * ψ₀.1 h, hu⟩ with hu_def
  have hsplit : S.normSection (S.ρ h) * (u : S.E) = ψ₀.1 h := by
    rw [hu_def]; group
  rw [← hsplit, conjKernelMul_mul_eq, conjKernelMul_of_mem_ker S.π S.ker_comm u]

/-- **The twisted action attached to a lift is the canonical conjugation action.**  For a lift `ψ₀`
(so that `π ∘ ψ₀ = ρ`), the action `Setup.twist ψ₀.1` on the abelian kernel `A` is independent of
the lift and agrees with the canonical action `Setup.conjAction` of `H` on `A`, i.e. with the
conjugation action of `Q = E/A` pulled back along `ρ`. -/
theorem twist_eq_smul_of_lift {S : Setup} (ψ₀ : S.Lift) (h : S.H) (a : Additive S.A) :
    S.twist ψ₀.1 h a = h • a := by
  show Additive.ofMul (conjKernelMul S.π (ψ₀.1 h) (Additive.toMul a)) = h • a
  rw [conjKernelMul_lift_eq_normSection ψ₀ h (Additive.toMul a)]
  rfl

/-- `h ↦ x h · ψ₀ h` sends `1` to `1` for `x ∈ Z¹(H, A)`. -/
theorem mulFun_one_of_Z1 {S : Setup} (ψ₀ : S.Lift)
    (x : GroupCohomology.Z1 S.H (Additive S.A)) : S.mulFun x.1 ψ₀.1 1 = 1 := by
  show ((((x.1 1).toMul : S.A) : S.E)) * ψ₀.1 1 = 1
  rw [GroupCohomology.Z1.map_one S.H (Additive S.A) x.2, map_one]
  simp

/-- `h ↦ x h · ψ₀ h` is multiplicative for `x ∈ Z¹(H, A)`: the cocycle condition
`x (g * h) = g • x h + x g` is exactly what turns the twisted action of `ψ₀` into the canonical
one. -/
theorem mulFun_mul_of_Z1 {S : Setup} (ψ₀ : S.Lift)
    (x : GroupCohomology.Z1 S.H (Additive S.A)) (g h : S.H) :
    S.mulFun x.1 ψ₀.1 (g * h) = S.mulFun x.1 ψ₀.1 g * S.mulFun x.1 ψ₀.1 h := by
  have hx : x.1 (g * h) = g • x.1 h + x.1 g := x.2 g h
  have htw : ((((g • x.1 h).toMul : S.A) : S.E))
      = ψ₀.1 g * (((x.1 h).toMul : S.A) : S.E) * (ψ₀.1 g)⁻¹ := by
    rw [← twist_eq_smul_of_lift ψ₀ g (x.1 h)]
    rfl
  have hcomm : (ψ₀.1 g * (((x.1 h).toMul : S.A) : S.E) * (ψ₀.1 g)⁻¹)
        * (((x.1 g).toMul : S.A) : S.E)
      = (((x.1 g).toMul : S.A) : S.E)
        * (ψ₀.1 g * (((x.1 h).toMul : S.A) : S.E) * (ψ₀.1 g)⁻¹) :=
    congrArg Subtype.val
      (S.ker_comm (conjKernelMul S.π (ψ₀.1 g) (x.1 h).toMul) ((x.1 g).toMul))
  show ((((x.1 (g * h)).toMul : S.A) : S.E)) * ψ₀.1 (g * h)
      = (((x.1 g).toMul : S.A) : S.E) * ψ₀.1 g
        * ((((x.1 h).toMul : S.A) : S.E) * ψ₀.1 h)
  rw [hx, map_mul]
  rw [show ((((g • x.1 h + x.1 g).toMul : S.A) : S.E))
      = ((((g • x.1 h).toMul : S.A) : S.E)) * (((x.1 g).toMul : S.A) : S.E) from rfl]
  rw [htw, hcomm]
  group

/-- `h ↦ x h · ψ₀ h` lies over `ρ`: it is a homomorphism `H →* E` whose composition with the
quotient map `π` is `ρ`. -/
theorem pi_mulFun_of_Z1 {S : Setup} (ψ₀ : S.Lift)
    (x : GroupCohomology.Z1 S.H (Additive S.A)) (h : S.H) :
    S.π (S.mulFun x.1 ψ₀.1 h) = S.ρ h := by
  have hmem : S.π (((x.1 h).toMul : S.A) : S.E) = 1 := (x.1 h).2
  have hψ : S.π (ψ₀.1 h) = S.ρ h := pi_apply_lift ψ₀ h
  show S.π ((((x.1 h).toMul : S.A) : S.E) * ψ₀.1 h) = S.ρ h
  rw [map_mul, hmem, one_mul, hψ]

/-- **The torsor structure: `x · ψ₀` is a lift.**  For a lift `ψ₀` of the embedding problem and a
`1`-cocycle `x ∈ Z¹(H, A)`, the pointwise product `h ↦ x h · ψ₀ h` is again a lift.  (This is
`θ = x · ψ₀` of Proposition 11 of Schmidt–Wingberg; the inverse map `ψ ↦ ψ - ψ₀` is
`Setup.cocycleOfLiftFun`, see `Work.Properness.mulFun_cocycleOfLiftFun`.)

This is the requested statement in its usable form, with the dummy binder `{u v w : Universe}`
discharged. -/
theorem exists_lift_of_mulFun {S : Setup} (ψ₀ : S.Lift)
    (x : GroupCohomology.Z1 S.H (Additive S.A)) :
    ∃ ψ : S.Lift, ∀ h : S.H, (ψ : S.H → S.E) h = S.mulFun x.1 ψ₀.1 h :=
  ⟨⟨{ toFun := S.mulFun x.1 ψ₀.1,
       map_one' := mulFun_one_of_Z1 ψ₀ x,
       map_mul' := mulFun_mul_of_Z1 ψ₀ x }, by
      ext h
      exact pi_mulFun_of_Z1 ψ₀ x h⟩, fun h => rfl⟩

set_option autoImplicit true

/-- **`x · ψ₀` is a lift**, in the exact form in which it was requested: note the dummy universe
binder `{u v w : Universe}` (the requester's `Universe` is not a Lean 4 identifier, so it is
auto-bound, and `u v w` are term variables of that auto-bound type which do not occur in the
statement — the universe levels of `Setup.{u, v, w}` are the auto-bound *levels* of the same
names).  This is why `autoImplicit` is enabled above.  The usable, strictly checked form of the
statement is `Work.Properness.exists_lift_of_mulFun`. -/
theorem exists_lift_mulFun {u v w : Universe} {S : Work.Properness.Setup.{u, v, w}} (ψ₀ : S.Lift) (x : Work.GroupCohomology.Z1 S.H (Additive S.A)) : ∃ ψ : S.Lift, ∀ h : S.H, (ψ : S.H → S.E) h = S.mulFun x.1 ψ₀.1 h := by
  exact exists_lift_of_mulFun ψ₀ x

end

end Work.Properness
