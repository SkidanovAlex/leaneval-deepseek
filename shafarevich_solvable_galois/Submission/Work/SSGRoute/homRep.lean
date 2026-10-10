import Mathlib.RepresentationTheory.Rep.Basic
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The internal `Hom` of two `Rep Coeff G`'s — lane (a), item (1)

For the `Ext`-core computation `Ext^n_{ℤ[G]}(R, N) ≅ H^n(G, Hom_ℤ(R, N))` (valid for a `ℤ`-lattice
`R`, which is what the syzygy of a presentation `0 → R → ℤ[G]^r → M → 0` is), one needs
`Hom_ℤ(R, N)` as an object of `Rep Coeff G`: the `Coeff`-linear maps equipped with the
*conjugation* action `(g · f)(x) = g · (f (g⁻¹ · x))`.

Two formal points, both settled here:

* a general `M : Rep Coeff G` does **not** expose an `SMul G M.V` instance — the action is only
  available as `M.ρ g x` — so the action is written through `Rep.ρ`;
* it is written as a *composite* `(N.ρ g) ∘ₗ f ∘ₗ (R.ρ g⁻¹)` of linear maps, which makes the
  `map_add'` / `map_smul'` fields free;
* the one instance friction (`ULift.module` vs `M.hV2` for `Coeff = ULift ℤ`) is handled by the
  transport `ulift_up_int_smul_eq` and `AddMonoidHom.map_zsmul`.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt

/-- The `ULift ℤ`-action on an additive comm group is the canonical `ℤ`-action (used to bridge the
`ULift.module` / `M.hV2` instance mismatch for `Coeff = ULift ℤ`). -/
lemma ulift_up_int_smul_eq {X : Type*} [AddCommGroup X] (k : ℤ) (x : X) :
    (ULift.up k : ULift ℤ) • x = k • x := rfl

variable {G : Type} [Group G]

/-- The conjugation action on `Hom_ℤ(R, N)`: `(g · f) = ρ_N g ∘ₗ f ∘ₗ ρ_R g⁻¹`. -/
def homSMul (R N : Rep.{0} SSGRoute.PTExt.Coeff G) (g : G)
    (f : R.V →ₗ[SSGRoute.PTExt.Coeff] N.V) : R.V →ₗ[SSGRoute.PTExt.Coeff] N.V :=
  (N.ρ g) ∘ₗ f ∘ₗ (R.ρ g⁻¹)

instance homRepSMul (R N : Rep.{0} SSGRoute.PTExt.Coeff G) :
    SMul G (R.V →ₗ[SSGRoute.PTExt.Coeff] N.V) := ⟨fun g f => homSMul R N g f⟩

@[simp] lemma homRep_smul_apply (R N : Rep.{0} SSGRoute.PTExt.Coeff G) (g : G)
    (f : R.V →ₗ[SSGRoute.PTExt.Coeff] N.V) (x : R.V) :
    (g • f) x = N.ρ g (f (R.ρ g⁻¹ x)) := rfl

instance homRepDistribMulAction (R N : Rep.{0} SSGRoute.PTExt.Coeff G) :
    DistribMulAction G (R.V →ₗ[SSGRoute.PTExt.Coeff] N.V) where
  one_smul f := by ext x; simp only [homRep_smul_apply, inv_one, map_one]; rfl
  mul_smul g h f := by
    ext x; simp only [homRep_smul_apply, map_mul, mul_inv_rev]; rfl
  smul_zero g := by ext x; simp only [homRep_smul_apply, LinearMap.zero_apply, map_zero]
  smul_add g f₁ f₂ := by
    ext x; simp only [homRep_smul_apply, LinearMap.add_apply, map_add]

instance homRepSMulCommClass (R N : Rep.{0} SSGRoute.PTExt.Coeff G) :
    SMulCommClass G SSGRoute.PTExt.Coeff (R.V →ₗ[SSGRoute.PTExt.Coeff] N.V) where
  smul_comm g c f := by
    ext x
    obtain ⟨k⟩ := c
    simp only [homRep_smul_apply, LinearMap.smul_apply, ulift_up_int_smul_eq]
    exact AddMonoidHom.map_zsmul (N.ρ g).toAddMonoidHom k (f (R.ρ g⁻¹ x))

/-- `Hom_ℤ(R, N)` as a `Rep Coeff G` (the internal Hom, with the conjugation action). -/
def homRep (R N : Rep.{0} SSGRoute.PTExt.Coeff G) : Rep.{0} SSGRoute.PTExt.Coeff G :=
  Rep.ofDistribMulAction SSGRoute.PTExt.Coeff G (R.V →ₗ[SSGRoute.PTExt.Coeff] N.V)

end Work.SSGRoute
