import Mathlib
import Submission.Work.SSGRoute.PT.ClassFormation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The dévissage inclusion `M → Coind^G_U M`

The `G`-action on `Coind G U M` is `(g • f) x = f (g⁻¹ * x)` (`Coind.smul_apply`).  With that
convention the inclusion is

  `ι m = ⟨fun x => x⁻¹ • m, _⟩`    — **not** `x ↦ x • m`, which is not `G`-equivariant
  (`(g • ι m) 1 = g⁻¹ • m` while `ι (g • m) 1 = g • m`).

With `ι m = x ↦ x⁻¹ • m`:
* membership in `coindSub` is `(g * u)⁻¹ • m = u⁻¹ • (g⁻¹ • m)`, which is `mul_inv_rev` + `mul_smul`
  — **no normality of `U` needed**;
* `G`-equivariance is `(g • ι m) x = ι m (g⁻¹ * x) = (g⁻¹ * x)⁻¹ • m = x⁻¹ • (g • m)`;
* injectivity is `(ι m) 1 = m`.

Normality of `U` is needed elsewhere in the dévissage (to view `M ↪ Coind^G_U M` as the induced
object `ℤ[G/U] ⊗ M` and to apply Shapiro), not for the inclusion itself.
-/

open Classical

namespace Work.SSGRoute.PT

noncomputable section

universe u

/-- The membership identity of the dévissage inclusion. -/
theorem devissageIota_coe_mul {G : Type u} [Group G] (U : Subgroup G)
    {M : Type u} [AddCommGroup M] [DistribMulAction G M] (g : G) (u : U) (m : M) :
    (g * (u : G))⁻¹ • m = (u : G)⁻¹ • (g⁻¹ • m) := by
  rw [mul_inv_rev, mul_smul]

/-- The inclusion `M → Coind^G_U M`, `m ↦ (x ↦ x⁻¹ • m)`. -/
def devissageIota {G : Type u} [Group G] (U : Subgroup G)
    {M : Type u} [AddCommGroup M] [DistribMulAction G M] : M →+ Coind G U M where
  toFun m := ⟨fun x => x⁻¹ • m, fun g u => devissageIota_coe_mul U g u m⟩
  map_zero' := Subtype.ext (funext (fun x => by
    show x⁻¹ • (0 : M) = 0
    rw [smul_zero]))
  map_add' m n := Subtype.ext (funext (fun x => by
    show x⁻¹ • (m + n) = x⁻¹ • m + x⁻¹ • n
    rw [smul_add]))

/-- `G`-equivariance of the dévissage inclusion. -/
theorem devissageIota_equivariant {G : Type u} [Group G] (U : Subgroup G)
    {M : Type u} [AddCommGroup M] [DistribMulAction G M] :
    Work.GroupCohomology.IsEquivariant G (devissageIota U : M →+ Coind G U M) := by
  intro g m
  refine Subtype.ext (funext (fun x => ?_))
  show x⁻¹ • (g • m) = (g⁻¹ * x)⁻¹ • m
  rw [← mul_smul, mul_inv_rev, inv_inv]

/-- The dévissage inclusion is injective (evaluate at `x = 1`). -/
theorem devissageIota_injective {G : Type u} [Group G] (U : Subgroup G)
    {M : Type u} [AddCommGroup M] [DistribMulAction G M] :
    Function.Injective (devissageIota U : M →+ Coind G U M) := by
  intro m n h
  have h1 : (1 : G)⁻¹ • m = (1 : G)⁻¹ • n := congrArg (fun f : Coind G U M => f 1) h
  simpa using h1

end

end Work.SSGRoute.PT
