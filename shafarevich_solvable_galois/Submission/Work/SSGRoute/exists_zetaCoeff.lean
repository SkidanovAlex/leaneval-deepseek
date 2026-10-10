import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.PTDefsOmega
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- **The Kummer coefficient class `𝔽_p ⟶ Lˣ`, `1 ↦ ζ`.**  For number fields `k ⊆ L` and a primitive
`p`-th root of unity `ζ ∈ k` (`p` prime), there is a unit `u ∈ Lˣ` above `ζ` and a morphism of
`Gal(L/k)`-representations `z : 𝔽_p ⟶ Lˣ` (trivial action on `𝔽_p`) of the Kummer shape: `z` sends
`m` to the unit `ζ^m`.  (This is the coefficient class along which the Kummer push
`H²(Gal(L/k), 𝔽_p) → H²(Gal(L/k), Lˣ) = Br(L/k)` of `κ_L` is taken; both E4Ω-R1
`phi0_family_vanish_of_local` and E4Ω-R2 `zeta_idele_class_pairing` take such a `z` as a
hypothesis, and nothing in the workspace produces one at present.) -/
theorem exists_zetaCoeff (p : ℕ) [Fact p.Prime] (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] (ζ : k) (hζ : IsPrimitiveRoot ζ p) :
    ∃ u : Lˣ, (u : L) = algebraMap k L ζ ∧
      ∃ z : Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ unitsK k L,
        ∀ m : ℤ, z.hom ((m : ZMod p)) = Additive.ofMul (u ^ m) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hζne : ζ ≠ 0 := hζ.ne_zero hp0
  -- the unit `u = ζ` viewed inside `Lˣ`
  let u : Lˣ := Units.mk0 (algebraMap k L ζ) (by
    intro h
    exact hζne ((algebraMap k L).injective (by rw [h, map_zero])))
  have huval : (u : L) = algebraMap k L ζ := rfl
  have hup : u ^ p = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one, huval, ← map_pow, hζ.pow_eq_one, map_one]
  -- `u` is fixed by the Galois action, being the image of an element of `k`
  have hfix : ∀ σ : L ≃ₐ[k] L, σ • u = u := by
    intro σ
    refine Units.ext ?_
    show σ (u : L) = (u : L)
    rw [huval]
    exact σ.commutes ζ
  refine ⟨u, huval, ?_⟩
  -- The integer-indexed additive map `ℤ → Additive Lˣ`, `m ↦ u ^ m`; it kills `p` since `u ^ p = 1`,
  -- hence descends to `ZMod p`.
  let g : ℤ →+ Additive Lˣ :=
    (LinearMap.toSpanSingleton ℤ (Additive Lˣ) (Additive.ofMul u)).toAddMonoidHom
  have hg : g (p : ℤ) = 0 := by
    show (p : ℤ) • Additive.ofMul u = 0
    rw [← ofMul_zpow (p : ℤ) u, zpow_natCast, hup]
    rfl
  let fadd : ZMod p →+ Additive Lˣ := ZMod.lift p ⟨g, hg⟩
  have hfadd_coe : ∀ m : ℤ, fadd ((m : ZMod p)) = Additive.ofMul (u ^ m) := by
    intro m
    rw [ZMod.lift_coe]
    show m • Additive.ofMul u = Additive.ofMul (u ^ m)
    exact ofMul_zpow m u
  -- upgrade to a `Coeff`-linear map (the `ULift ℤ`-action is the `ℤ`-action through `.down`)
  let flin : ZMod p →ₗ[Coeff] Additive Lˣ :=
    LinearMap.mk (σ := RingHom.id Coeff) fadd.toAddHom (fun c v => by
      show fadd (c • v) = c • fadd v
      rw [ULift.smul_def, ULift.smul_def]
      exact fadd.map_zsmul c.down v)
  -- `flin` is Galois-equivariant: `u` is fixed, so all its powers are
  refine ⟨Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _ flin ?_), ?_⟩
  · intro σ v
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective v
    show flin ((m : ZMod p)) = σ • flin ((m : ZMod p))
    rw [show flin ((m : ZMod p)) = Additive.ofMul (u ^ m) from hfadd_coe m]
    rw [show σ • Additive.ofMul (u ^ m) = Additive.ofMul (σ • (u ^ m)) from rfl]
    rw [smul_zpow', hfix σ]
  · intro m
    show flin ((m : ZMod p)) = Additive.ofMul (u ^ m)
    exact hfadd_coe m

end Work.SSGRoute
