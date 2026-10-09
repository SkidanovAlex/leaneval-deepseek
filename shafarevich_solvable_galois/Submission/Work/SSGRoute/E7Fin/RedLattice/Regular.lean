import Mathlib
import Submission.Work.ArtinInduction.LatticeModp.Infra
import Submission.Work.SSGRoute.E7Fin.RedLattice.F
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The regular `𝔽_p[G]`-module

Lane `Work.SSGRoute.coker_obstruction_pt`.  The target of the arithmetic isomorphism
`Λ/pΛ ≅ 𝔽_p[Γ]^n` of Milne *ADT* I.2.11 / `(ε)` of this lane is a power of the regular module
`𝔽_p[Γ]` (the group algebra acting on itself by *left* multiplication).  This file provides that
module as `RegMod p G = G → ZMod p` with the left-regular action

  `(g • f) h = f (g⁻¹ * h)`,

i.e. the action which permutes the basis `{δ_γ}` by `δ_γ ↦ δ_{g γ}` — the convention induced by a
Galois action permuting a normal basis `{γ • β}` by `β_γ ↦ β_{g γ}`.  Together with the `𝔽_p`-module
structure (pointwise) this is the `𝔽_p[G]`-module whose powers occur in `(ε)`.

The additivity statement `ρ (𝔽_p[G]^n) = n · ρ (𝔽_p[G])` for an additive invariant `ρ` of finite
`𝔽_p[G]`-modules is the companion file `RedLattice/RegPow.lean`.

Note: `MonoidAlgebra (ZMod p) G` carries no `DistribMulAction G` instance in this pin, which is why
the action has to be given here; `RegMod` is an `abbrev`, so the `AddCommGroup`, `Module (ZMod p)`
and `Finite` instances are Mathlib's `Pi` instances.
-/

namespace Work.SSGRoute.E7Fin.RedLattice

open Work.ArtinInduction.LatticeModp

/-- The underlying type of the regular `𝔽_p[G]`-module: functions `G → 𝔽_p`. -/
abbrev RegMod (p : ℕ) (G : Type) : Type := G → ZMod p

/-- The **left regular** `G`-action: `(g • f) h = f (g⁻¹ * h)`. -/
instance instSMulRegMod (p : ℕ) (G : Type) [Group G] : SMul G (RegMod p G) :=
  ⟨fun g f => fun h => f (g⁻¹ * h)⟩

instance instDistribMulActionRegMod (p : ℕ) (G : Type) [Group G] :
    DistribMulAction G (RegMod p G) where
  smul := (instSMulRegMod p G).smul
  one_smul f := funext fun h => by show f ((1 : G)⁻¹ * h) = f h; rw [inv_one, one_mul]
  mul_smul a b f := funext fun h => by
    show f ((a * b)⁻¹ * h) = f (b⁻¹ * (a⁻¹ * h))
    rw [mul_inv_rev, mul_assoc]
  smul_zero g := rfl
  smul_add g f₁ f₂ := rfl

instance instSMulCommClassRegMod (p : ℕ) (G : Type) [Group G] :
    SMulCommClass G (ZMod p) (RegMod p G) where
  smul_comm g c f := rfl

/-- The computation rule of the regular action, in the form used by consumers. -/
lemma regMod_smul_apply (p : ℕ) (G : Type) [Group G] (g h : G) (f : RegMod p G) :
    (g • f) h = f (g⁻¹ * h) := rfl

end Work.SSGRoute.E7Fin.RedLattice
