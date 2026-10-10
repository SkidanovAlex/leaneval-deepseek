import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
import Submission.Work.SSGRoute.selfdual
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

set_option maxHeartbeats 1000000 in
/-- **The `𝔽_p`-linear structure of the self-duality `E ≅ Hom(E^*, μ_p)`.**

For a finite `𝔽_p`-module `X` and a primitive `p`-th root of unity `ζu` in a domain `K`, the
pairing `(x, φ) ↦ ζ^{φ x}` (`x : X`, `φ : DualMod p X`) exhibits `X` as the `Coeff = ULift ℤ`-dual
of its own `𝔽_p`-dual: there is a `Coeff`-linear equivalence
`X ≃ₗ DualMod p X →ₗ Additive Kˣ` whose value on `(x, φ)` is `zetaPowHom ζu hζu (φ x)`.

Mathematically this is the composition of the double-dual equivalence `X ≅ (X^*)^*` with
`SelfDual.dualEquiv_zpow`, which identifies `(X^*)^*` with all additive maps `X^* → Additive Kˣ`
(every such map has image in `μ_p = zpowers ζu`); the `Coeff`-linearity is automatic because
`Coeff = ULift ℤ` acts through the underlying additive-group action, so any additive map is
`Coeff`-linear. -/
theorem dualUnits_linearEquiv (p : ℕ) [Fact p.Prime] {K : Type} [CommRing K] [IsDomain K]
    (ζu : Kˣ) (hζu : IsPrimitiveRoot ζu p) (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [Finite X] :
    ∃ e : X ≃ₗ[SSGRoute.PTExt.Coeff]
        (Work.SSGRoute.DualMod p X →ₗ[SSGRoute.PTExt.Coeff] Additive Kˣ),
      ∀ (x : X) (φ : Work.SSGRoute.DualMod p X),
        e x φ = Work.SSGRoute.SelfDual.zetaPowHom ζu hζu (φ x) := by
  classical
  -- The primitive-root map `ζ^(-) : 𝔽_p →+ Additive Kˣ` is `ℤ`-linear.
  have keyZ : ∀ (u : SSGRoute.PTExt.Coeff) (y : ZMod p),
      Work.SSGRoute.SelfDual.zetaPowHom ζu hζu (u • y)
        = u • Work.SSGRoute.SelfDual.zetaPowHom ζu hζu y := by
    intro u y
    show Work.SSGRoute.SelfDual.zetaPowHom ζu hζu (u.down • y)
      = u.down • Work.SSGRoute.SelfDual.zetaPowHom ζu hζu y
    exact AddMonoidHom.map_zsmul _ _ _
  -- The pairing is `ℤ`-linear in the first variable `x`.
  have keyX : ∀ (φ : Work.SSGRoute.DualMod p X) (u : SSGRoute.PTExt.Coeff) (x : X),
      Work.SSGRoute.SelfDual.zetaPowHom ζu hζu (φ (u • x))
        = u • Work.SSGRoute.SelfDual.zetaPowHom ζu hζu (φ x) := by
    intro φ u x
    have h : φ (u • x) = u • φ x := by
      show φ (u.down • x) = u.down • φ x
      exact AddMonoidHom.map_zsmul φ.toAddMonoidHom u.down x
    rw [h, keyZ u (φ x)]
  -- The pairing `x ↦ (φ ↦ ζ^{φ x})`.
  let inner : X → (Work.SSGRoute.DualMod p X →ₗ[SSGRoute.PTExt.Coeff] Additive Kˣ) :=
    fun x => { toFun := fun φ => Work.SSGRoute.SelfDual.zetaPowHom ζu hζu (φ x)
               map_add' := by intro φ ψ; simp [map_add]
               map_smul' := by intro u φ; rw [LinearMap.smul_apply]; exact keyZ u (φ x) }
  have inner_apply : ∀ (x : X) (φ : Work.SSGRoute.DualMod p X),
      inner x φ = Work.SSGRoute.SelfDual.zetaPowHom ζu hζu (φ x) := fun x φ => rfl
  have inner_add : ∀ (x y : X), inner (x + y) = inner x + inner y := by
    intro x y
    refine LinearMap.ext (fun φ => ?_)
    rw [LinearMap.add_apply, inner_apply, inner_apply, inner_apply]
    simp [map_add]
  have inner_smul : ∀ (u : SSGRoute.PTExt.Coeff) (x : X), inner (u • x) = u • inner x := by
    intro u x
    refine LinearMap.ext (fun φ => ?_)
    rw [show (u • (inner x)) φ = u • (inner x) φ from LinearMap.smul_apply u (inner x) φ]
    simpa only [inner_apply] using keyX φ u x
  -- The pairing, as a `Coeff`-linear map.
  let L : X →ₗ[SSGRoute.PTExt.Coeff]
      (Work.SSGRoute.DualMod p X →ₗ[SSGRoute.PTExt.Coeff] Additive Kˣ) :=
    { toFun := inner, map_add' := inner_add, map_smul' := inner_smul }
  -- The inverse of the pairing: `(X^*)^* ≅ X` (double dual) composed with the inverse of
  -- `dualEquiv_zpow` (identifying additive maps `X^* → Additive Kˣ` with `(X^*)^*`).
  let R : (Work.SSGRoute.DualMod p X →ₗ[SSGRoute.PTExt.Coeff] Additive Kˣ) → X := fun g =>
    (Module.evalEquiv (ZMod p) X).symm
      ((Work.SSGRoute.SelfDual.dualEquiv_zpow p ζu hζu (Work.SSGRoute.DualMod p X)).symm
        g.toAddMonoidHom)
  have hR_left : ∀ x, R (L x) = x := by
    intro x
    rw [show R (L x) = (Module.evalEquiv (ZMod p) X).symm
        (((Work.SSGRoute.SelfDual.dualEquiv_zpow p ζu hζu (Work.SSGRoute.DualMod p X)).symm
          (L x).toAddMonoidHom)) from rfl]
    rw [LinearEquiv.symm_apply_eq]
    rw [AddEquiv.symm_apply_eq]
    refine AddMonoidHom.ext (fun φ => ?_)
    rw [Work.SSGRoute.SelfDual.dualEquiv_zpow_apply, Module.evalEquiv_apply, Module.Dual.eval_apply]
    rfl
  have hR_right : ∀ g, L (R g) = g := by
    intro g
    have hφ : ∀ φ, φ (R g)
        = (Work.SSGRoute.SelfDual.dualEquiv_zpow p ζu hζu (Work.SSGRoute.DualMod p X)).symm
            g.toAddMonoidHom φ := by
      intro φ
      have h1 : (Module.evalEquiv (ZMod p) X) (R g)
          = (Work.SSGRoute.SelfDual.dualEquiv_zpow p ζu hζu (Work.SSGRoute.DualMod p X)).symm
              g.toAddMonoidHom := by
        rw [show R g = (Module.evalEquiv (ZMod p) X).symm
            ((Work.SSGRoute.SelfDual.dualEquiv_zpow p ζu hζu (Work.SSGRoute.DualMod p X)).symm
              g.toAddMonoidHom) from rfl]
        exact LinearEquiv.apply_symm_apply _ _
      have h2 := congrArg (fun f => f φ) h1
      rwa [Module.evalEquiv_apply, Module.Dual.eval_apply] at h2
    have hψ : Work.SSGRoute.SelfDual.dualEquiv_zpow p ζu hζu (Work.SSGRoute.DualMod p X)
        ((Work.SSGRoute.SelfDual.dualEquiv_zpow p ζu hζu (Work.SSGRoute.DualMod p X)).symm
          g.toAddMonoidHom) = g.toAddMonoidHom :=
      AddEquiv.apply_symm_apply _ _
    refine LinearMap.ext (fun φ => ?_)
    rw [show (L (R g)) φ = Work.SSGRoute.SelfDual.zetaPowHom ζu hζu (φ (R g)) from rfl]
    rw [hφ φ]
    have h4 := congrArg (fun f => f φ) hψ
    rw [Work.SSGRoute.SelfDual.dualEquiv_zpow_apply] at h4
    rw [h4]
    rfl
  refine ⟨LinearEquiv.ofBijective L ⟨fun x y h => ?_, fun g => ⟨R g, hR_right g⟩⟩, ?_⟩
  · have h := congrArg R h
    rwa [hR_left x, hR_left y] at h
  · intro x φ
    rfl

end Work.SSGRoute
