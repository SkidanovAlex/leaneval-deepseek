import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.exists_zetaCoeff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt

/-- **The Kummer coefficient class `𝔽_p ⟶ K_wˣ`, `1 ↦ ζ`.**

For `k ⊆ K` a finite Galois extension of number fields, `w` a place of `K` and `ζ ∈ K` a primitive
`p`-th root of unity fixed by the decomposition group `D_w`, there is a unit `u` of the local field
`K_w` above `ζ` and a **nonzero** morphism of `D_w`-representations
`z : 𝔽_p ⟶ K_wˣ` with `z m = u ^ m` for every `m` (in particular `z 1` is the image of `ζ`).

This is the `(z, hz)` datum demanded by the signature of `Work.SSGRoute.detectAbove_pgroup` (Z7 of the
ssg6 E7b design), and hence by Z8's step 1 (`Work.SSGRoute.vanishesAbove_base` plus the `z` supply).
It is the **local-units analogue** of the sorry-free `Work.SSGRoute.exists_zetaCoeff`, which produces
a nonzero `𝔽_p ⟶ Lˣ` — but only for `ζ` an element of the *base* field `k` (`ζ : k`).  Here `ζ` need
only be *fixed* by `D_w` (supplied at the Sylow level `k' = K^S` by
`Work.SSGRoute.pgroup_fixes_primitiveRoot`), so the proof must use:
* the unit `u := Units.mk0 (algebraMap K (localField K w) ζ)`, with `u ^ p = 1` from `hζ.pow_eq_one`;
* `D_w`-equivariance of `1 ↦ u`, from `hfix` via `NK.HassePrinciple.localAut_algebraMap` (the
  transported `D_w`-action `localUnitsEquiv` agrees with the Galois action through `localAutHom`);
* `z ≠ 0`, since `z 1 = Additive.ofMul u` and `u ≠ 0`.
The remaining bookkeeping (`ZMod.lift` descending `ℤ → Additive K_wˣ` through `ZMod p`, the
`Coeff`-linearity via `LinearMap.mk`/`fadd.map_zsmul`, and the
`Rep.ofHom`/`intertwiningMap_of_isIntertwiningMap` packaging) is verbatim the template of
`exists_zetaCoeff`, with `localUnitsEquiv` in place of the Galois action on `Lˣ`.

Note (reviewers): the statement is deliberately the *local* form; the pointwise clause
`∀ m, z.hom m = Additive.ofMul (u ^ m)` is included because it comes for free from that template. -/
theorem exists_localZetaCoeff (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (hfix : ∀ σ : SSGRoute.PTExt.decompK (k := k) w, (σ : K ≃ₐ[k] K) ζ = ζ) :
    ∃ (u : (NK.GlobalCFT.Place.localField K w)ˣ)
      (z : Rep.trivial SSGRoute.PTExt.Coeff (SSGRoute.PTExt.decompK (k := k) w) (ZMod p) ⟶
        SSGRoute.PTExt.localUnitsK (k := k) w),
      (u : NK.GlobalCFT.Place.localField K w) =
        algebraMap K (NK.GlobalCFT.Place.localField K w) ζ ∧
      z ≠ 0 ∧ ∀ m : ℤ, z.hom ((m : ZMod p)) = Additive.ofMul (u ^ m) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hζne : ζ ≠ 0 := hζ.ne_zero hp0
  -- the unit `u` of `K_w` above `ζ`
  let u : (NK.GlobalCFT.Place.localField K w)ˣ :=
    Units.mk0 (algebraMap K (NK.GlobalCFT.Place.localField K w) ζ) (by
      intro h
      exact hζne ((algebraMap K (NK.GlobalCFT.Place.localField K w)).injective
        (by rw [h, map_zero])))
  have huval : (u : NK.GlobalCFT.Place.localField K w) =
      algebraMap K (NK.GlobalCFT.Place.localField K w) ζ := rfl
  have hup : u ^ p = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one, huval, ← map_pow, hζ.pow_eq_one, map_one]
  -- `u` is fixed by the decomposition group `D_w`
  have hfixu : ∀ σ : SSGRoute.PTExt.decompK (k := k) w, σ • u = u := by
    intro σ
    refine Units.ext ?_
    show ((NK.HassePrinciple.localUnitsEquiv w σ u :
        (NK.GlobalCFT.Place.localField K w)ˣ) : NK.GlobalCFT.Place.localField K w) =
      (u : NK.GlobalCFT.Place.localField K w)
    rw [NK.HassePrinciple.coe_localUnitsEquiv, huval]
    show NK.HassePrinciple.localAut w σ
      (algebraMap K (NK.GlobalCFT.Place.localField K w) ζ) =
        algebraMap K (NK.GlobalCFT.Place.localField K w) ζ
    rw [NK.HassePrinciple.localAut_algebraMap, hfix σ]
  -- the integer-indexed additive map `ℤ → Additive K_wˣ`, `m ↦ u ^ m`; kills `p` since `u ^ p = 1`
  let g : ℤ →+ Additive (NK.GlobalCFT.Place.localField K w)ˣ :=
    (LinearMap.toSpanSingleton ℤ (Additive (NK.GlobalCFT.Place.localField K w)ˣ)
      (Additive.ofMul u)).toAddMonoidHom
  have hg : g (p : ℤ) = 0 := by
    show (p : ℤ) • Additive.ofMul u = 0
    rw [← ofMul_zpow (p : ℤ) u, zpow_natCast, hup]
    rfl
  let fadd : ZMod p →+ Additive (NK.GlobalCFT.Place.localField K w)ˣ := ZMod.lift p ⟨g, hg⟩
  have hfadd_coe : ∀ m : ℤ, fadd ((m : ZMod p)) = Additive.ofMul (u ^ m) := by
    intro m
    rw [ZMod.lift_coe]
    show m • Additive.ofMul u = Additive.ofMul (u ^ m)
    exact ofMul_zpow m u
  -- upgrade to a `Coeff`-linear map (the `ULift ℤ`-action is the `ℤ`-action through `.down`)
  let flin : ZMod p →ₗ[Coeff] Additive (NK.GlobalCFT.Place.localField K w)ˣ :=
    LinearMap.mk (σ := RingHom.id Coeff) fadd.toAddHom (fun c v => by
      show fadd (c • v) = c • fadd v
      rw [ULift.smul_def, ULift.smul_def]
      exact fadd.map_zsmul c.down v)
  -- `flin` is `D_w`-equivariant: `u` is fixed, so all its powers are
  have htw : ∀ (σ : SSGRoute.PTExt.decompK (k := k) w)
      (v : ZMod p), flin ((Rep.trivial Coeff (SSGRoute.PTExt.decompK (k := k) w)
        (ZMod p)).ρ σ v) = (SSGRoute.PTExt.localUnitsK (k := k) w).ρ σ (flin v) := by
    intro σ v
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective v
    show flin ((m : ZMod p)) = σ • flin ((m : ZMod p))
    rw [show flin ((m : ZMod p)) = Additive.ofMul (u ^ m) from hfadd_coe m]
    rw [show σ • Additive.ofMul (u ^ m) = Additive.ofMul (σ • (u ^ m)) from rfl]
    rw [smul_zpow', hfixu σ]
  let z : Rep.trivial Coeff (SSGRoute.PTExt.decompK (k := k) w) (ZMod p) ⟶
      SSGRoute.PTExt.localUnitsK (k := k) w :=
    Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _ flin htw)
  have hzval : ∀ m : ℤ, z.hom ((m : ZMod p)) = Additive.ofMul (u ^ m) := by
    intro m
    show flin ((m : ZMod p)) = Additive.ofMul (u ^ m)
    exact hfadd_coe m
  -- `u ≠ 1`, since `↑u = algebraMap ζ` with `ζ ≠ 1` (a primitive `p`-th root, `p` prime)
  have hu_ne_one : u ≠ 1 := by
    intro hu1
    have hval : (u : NK.GlobalCFT.Place.localField K w) = 1 := by rw [hu1]; rfl
    rw [huval] at hval
    exact hζ.ne_one (Fact.out : p.Prime).one_lt
      ((algebraMap K (NK.GlobalCFT.Place.localField K w)).injective
        (by rw [map_one]; exact hval))
  have hz_one : z.hom (1 : ZMod p) = Additive.ofMul u := by
    have h := hzval (1 : ℤ)
    rwa [Int.cast_one, zpow_one] at h
  refine ⟨u, z, huval, ?_, hzval⟩
  -- `z ≠ 0`, since `z 1 = Additive.ofMul u = Additive.ofMul 1 ≠ 0`
  intro hz
  have h0 : z.hom (1 : ZMod p) = 0 := hz ▸ rfl
  rw [hz_one] at h0
  exact hu_ne_one (ofMul_eq_zero.mp h0)

end Work.SSGRoute
