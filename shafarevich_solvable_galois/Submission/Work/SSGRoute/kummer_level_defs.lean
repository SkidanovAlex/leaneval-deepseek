import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Submission.Work.SSGRoute.ExtH1Iso
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.augSES_shortExact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer short exact sequence at a level

For a level `k ⊆ L` (with `L/k` finite Galois, `k` a number field) and a prime `p`, this file sets
up the short exact sequence of `Gal(L/k)`-representations

  `0 → 𝔽_p → Lˣ → (Lˣ)^p → 0`,

where the first map is a Kummer coefficient class `1 ↦ ζ` (`z`, for a primitive `p`-th root of
unity `ζ ∈ k`) and the second is the `p`-th power map on `Lˣ`.

The `p`-th powers `(Lˣ)^p` are realized as the range of the `p`-th power endomorphism of
`Additive Lˣ`, equipped with its induced `Gal`-action; `levelUnits k L` is `Lˣ` (definitionally
`unitsK k L`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt

/-- `Lˣ` as a representation of `Gal(L/k)` (definitionally `unitsK k L`). -/
noncomputable abbrev levelUnits (k : Type) [Field k] (L : Type) [Field L] [Algebra k L] :
    Rep.{0,0,0} Coeff (L ≃ₐ[k] L) := modRep (L ≃ₐ[k] L) (Additive Lˣ)

/-- The `p`-th powers `(Lˣ)^p`, as a submodule of `Additive Lˣ`. -/
noncomputable def pthSubX (L : Type) [Field L] (p : ℕ) : Submodule Coeff (Additive Lˣ) :=
  LinearMap.range ((p:ℕ) • (LinearMap.id : Additive Lˣ →ₗ[Coeff] Additive Lˣ))

theorem mem_pthSubX_iff (L : Type) [Field L] (p : ℕ) (x : Additive Lˣ) :
    x ∈ pthSubX L p ↔ ∃ u : Lˣ, (p:ℕ) • (Additive.ofMul u) = x :=
  LinearMap.mem_range

/-- `c • u` for `c : Coeff = ULift ℤ` is the `c.down`-th power. -/
theorem smul_coeff_ofMul (L : Type) [Field L] (c : Coeff) (u : Lˣ) :
    c • (Additive.ofMul u : Additive Lˣ) = Additive.ofMul (u ^ c.down) := by
  rw [ULift.smul_def]
  exact ofMul_zpow c.down u

/-- `n • u` is the `n`-th power. -/
theorem nsmul_ofMul (L : Type) [Field L] (n : ℕ) (u : Lˣ) :
    n • (Additive.ofMul u : Additive Lˣ) = Additive.ofMul (u ^ n) := by
  rw [← natCast_zsmul, ← zpow_natCast]
  exact (ofMul_zpow (n : ℤ) u).symm

/-- The `p`-th powers are stable under the Galois action: `γ • (u^p) = (γ • u)^p`. -/
theorem pthSub_mem_smulX (k : Type) [Field k] [NumberField k] (L : Type) [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (p : ℕ) (γ : L ≃ₐ[k] L)
    {x : Additive Lˣ} (hx : x ∈ pthSubX L p) :
    γ • x ∈ pthSubX L p := by
  rw [mem_pthSubX_iff] at hx ⊢
  obtain ⟨u, hu⟩ := hx
  refine ⟨γ • u, ?_⟩
  rw [← hu]
  have h2 : Additive.ofMul (γ • u) = γ • (Additive.ofMul u) := rfl
  rw [h2]
  exact (map_nsmul (DistribSMul.toAddMonoidHom (Additive Lˣ) γ) p (Additive.ofMul u)).symm

noncomputable instance instSMulPthSubX (k : Type) [Field k] [NumberField k] (L : Type) [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (p : ℕ) :
    SMul (L ≃ₐ[k] L) ↥(pthSubX L p) where
  smul γ w := ⟨γ • (w : Additive Lˣ), pthSub_mem_smulX k L p γ w.2⟩

noncomputable instance instDistribMulActionPthSubX (k : Type) [Field k] [NumberField k]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (p : ℕ) : DistribMulAction (L ≃ₐ[k] L) ↥(pthSubX L p) :=
  Function.Injective.distribMulAction
    ((Submodule.subtype (pthSubX L p) : ↥(pthSubX L p) →ₗ[Coeff] Additive Lˣ).toAddMonoidHom)
    Subtype.coe_injective
    (fun _ _ => rfl)

/-- The `p`-th powers of `Lˣ` as a representation of `Gal(L/k)`. -/
noncomputable def pthRepX (k : Type) [Field k] [NumberField k] (L : Type) [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (p : ℕ) :
    Rep.{0,0,0} Coeff (L ≃ₐ[k] L) := modRep (L ≃ₐ[k] L) ↥(pthSubX L p)

/-- The `p`-th power map `Lˣ → (Lˣ)^p` as a morphism of representations. -/
noncomputable def pthMapX (k : Type) [Field k] [NumberField k] (L : Type) [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (p : ℕ) :
    levelUnits k L ⟶ pthRepX k L p :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    { toFun := fun v => ⟨(p:ℕ) • v, LinearMap.mem_range_self _ v⟩
      map_add' := fun a b => Subtype.ext (smul_add (p:ℕ) a b)
      map_smul' := fun c v => Subtype.ext (by
        show (p:ℕ) • (c • v) = c • ((p:ℕ) • v)
        rw [ULift.smul_def, ULift.smul_def]
        simpa only [LinearMap.smul_apply, LinearMap.id_apply] using
          (map_nsmul ((c.down : ℤ) • (LinearMap.id : Additive Lˣ →ₗ[Coeff] Additive Lˣ)) p v).symm) }
    (fun γ v => Subtype.ext (by
      have h : ((levelUnits k L).ρ γ) ((p:ℕ) • v) = (p:ℕ) • (((levelUnits k L).ρ γ) v) :=
        map_nsmul ((levelUnits k L).ρ γ) p v
      have h2 : ((levelUnits k L).ρ γ) v = γ • v :=
        Rep.ofDistribMulAction_ρ_apply_apply (k := Coeff) (G := L ≃ₐ[k] L) (A := Additive Lˣ)
          γ v
      show (p:ℕ) • (γ • v) = ((levelUnits k L).ρ γ) ((p:ℕ) • v)
      exact (h.trans (congrArg (fun z => (p:ℕ) • z) h2)).symm)))

theorem pthMapX_apply (k : Type) [Field k] [NumberField k] (L : Type) [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (p : ℕ)
    (v : Additive Lˣ) :
    ((pthMapX k L p).hom v : ↥(pthSubX L p))
      = ⟨(p:ℕ) • v, LinearMap.mem_range_self _ v⟩ := rfl

theorem pthMapX_surjective (k : Type) [Field k] [NumberField k] (L : Type) [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (p : ℕ) :
    Function.Surjective (pthMapX k L p).hom := by
  intro w
  obtain ⟨u, hu⟩ := (mem_pthSubX_iff L p ((show ↥(pthSubX L p) from w) : Additive Lˣ)).mp
    (show ↥(pthSubX L p) from w).2
  refine ⟨u, ?_⟩
  apply Subtype.ext
  show (p:ℕ) • (Additive.ofMul u) = ((show ↥(pthSubX L p) from w) : Additive Lˣ)
  exact hu

/-- The unit `ζ ∈ Lˣ` obtained from `ζ : k`. -/
noncomputable def zetaUnitL (k : Type) [Field k] (L : Type) [Field L] [Algebra k L] (p : ℕ)
    [Fact p.Prime] (ζ : k) (hζ : IsPrimitiveRoot ζ p) : Lˣ :=
  Units.mk0 (algebraMap k L ζ) (by
    intro h
    exact (hζ.ne_zero (Fact.out : p.Prime).ne_zero)
      ((algebraMap k L).injective (by rw [h, map_zero])))

theorem zetaUnitL_coe (k : Type) [Field k] (L : Type) [Field L] [Algebra k L] (p : ℕ)
    [Fact p.Prime] (ζ : k) (hζ : IsPrimitiveRoot ζ p) :
    ((zetaUnitL k L p ζ hζ : Lˣ) : L) = algebraMap k L ζ := rfl

theorem zetaUnitL_pow (k : Type) [Field k] (L : Type) [Field L] [Algebra k L] (p : ℕ)
    [Fact p.Prime] (ζ : k) (hζ : IsPrimitiveRoot ζ p) :
    zetaUnitL k L p ζ hζ ^ p = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one, zetaUnitL_coe, ← map_pow, hζ.pow_eq_one,
    map_one]

/-- The value of a Kummer coefficient class at `1 : 𝔽_p`. -/
theorem z_toMul_one {k : Type} [Field k] {L : Type} [Field L] [Algebra k L] (p : ℕ)
    [Fact p.Prime] (ζ : k) (hζ : IsPrimitiveRoot ζ p)
    (z : Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ levelUnits k L)
    (hz : ((Additive.toMul (z.hom (1 : ZMod p)) : Lˣ) : L) = algebraMap k L ζ) :
    (Additive.toMul (z.hom (1 : ZMod p)) : Lˣ) = zetaUnitL k L p ζ hζ := by
  refine Units.ext ?_
  rw [zetaUnitL_coe]
  exact hz

/-- The values of a Kummer coefficient class on `ℤ`-multiples of `1`. -/
theorem z_toMul_apply {k : Type} [Field k] {L : Type} [Field L] [Algebra k L] (p : ℕ)
    [Fact p.Prime] {ζ : k} (hζ : IsPrimitiveRoot ζ p)
    {z : Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ levelUnits k L}
    (hz : ((Additive.toMul (z.hom (1 : ZMod p)) : Lˣ) : L) = algebraMap k L ζ) (m : ℤ) :
    (Additive.toMul (z.hom (m : ZMod p)) : Lˣ) = zetaUnitL k L p ζ hζ ^ m := by
  have h1 : (m : ZMod p) = (ULift.up m : Coeff) • (1 : ZMod p) := by
    simp [ULift.smul_def]
  have h2 : z.hom ((ULift.up m : Coeff) • (1 : ZMod p))
      = (ULift.up m : Coeff) • (z.hom (1 : ZMod p)) := map_smul z.hom _ _
  have hone := z_toMul_one p ζ hζ z hz
  calc (Additive.toMul (z.hom (m : ZMod p)) : Lˣ)
      = (Additive.toMul (z.hom ((ULift.up m : Coeff) • (1 : ZMod p))) : Lˣ) := by
        rw [h1]
    _ = (Additive.toMul ((ULift.up m : Coeff) • (z.hom (1 : ZMod p))) : Lˣ) :=
        congrArg (fun y => (Additive.toMul y : Lˣ)) h2
    _ = (Additive.toMul ((ULift.up m : Coeff) • (Additive.ofMul (zetaUnitL k L p ζ hζ))) : Lˣ) :=
        congrArg (fun y => (Additive.toMul ((ULift.up m : Coeff) • y) : Lˣ)) hone
    _ = (Additive.toMul (Additive.ofMul (zetaUnitL k L p ζ hζ ^ (ULift.up m : Coeff).down)) : Lˣ) :=
        congrArg (fun y => (Additive.toMul y : Lˣ)) (smul_coeff_ofMul L (ULift.up m)
          (zetaUnitL k L p ζ hζ))
    _ = zetaUnitL k L p ζ hζ ^ m := by simp

/-- The values of a Kummer coefficient class are `p`-th roots of unity. -/
theorem z_toMul_pow {k : Type} [Field k] {L : Type} [Field L] [Algebra k L] (p : ℕ)
    [Fact p.Prime] {ζ : k} (hζ : IsPrimitiveRoot ζ p)
    {z : Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ levelUnits k L}
    (hz : ((Additive.toMul (z.hom (1 : ZMod p)) : Lˣ) : L) = algebraMap k L ζ) (x : ZMod p) :
    (Additive.toMul (z.hom x) : Lˣ) ^ p = 1 := by
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective x
  rw [z_toMul_apply p hζ hz m]
  calc (zetaUnitL k L p ζ hζ ^ m) ^ p
      = (zetaUnitL k L p ζ hζ ^ m) ^ (p : ℤ) := by rw [zpow_natCast]
    _ = zetaUnitL k L p ζ hζ ^ (m * (p : ℤ)) := (zpow_mul _ _ _).symm
    _ = zetaUnitL k L p ζ hζ ^ ((p : ℤ) * m) := by rw [mul_comm]
    _ = (zetaUnitL k L p ζ hζ ^ (p : ℤ)) ^ m := zpow_mul _ _ _
    _ = 1 := by rw [zpow_natCast, zetaUnitL_pow, one_zpow]

/-- `z` is injective: `𝔽_p` is generated by `1`, whose image is a primitive `p`-th root of unity. -/
theorem z_injective {k : Type} [Field k] {L : Type} [Field L] [Algebra k L] (p : ℕ)
    [Fact p.Prime] {ζ : k} (hζ : IsPrimitiveRoot ζ p)
    {z : Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ levelUnits k L}
    (hz : ((Additive.toMul (z.hom (1 : ZMod p)) : Lˣ) : L) = algebraMap k L ζ) :
    Function.Injective z.hom := by
  have hζL : IsPrimitiveRoot (algebraMap k L ζ) p :=
    hζ.map_of_injective (algebraMap k L).injective
  have hζU : IsPrimitiveRoot (zetaUnitL k L p ζ hζ) p := by
    apply IsPrimitiveRoot.coe_units_iff.mp
    rw [zetaUnitL_coe]
    exact hζL
  intro a b hab
  have h1 : z.hom (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have h2 : a - b = 0 := by
    obtain ⟨m, hm⟩ := ZMod.intCast_surjective (a - b)
    rw [← hm] at h1 ⊢
    have h3 : (Additive.toMul (z.hom (m : ZMod p)) : Lˣ) = 1 := by
      have h4 : (Additive.toMul (z.hom (m : ZMod p)) : Lˣ)
          = (Additive.toMul (0 : ↑(levelUnits k L)) : Lˣ) :=
        congrArg (fun y => (Additive.toMul y : Lˣ)) h1
      have h5 : (Additive.toMul (0 : ↑(levelUnits k L)) : Lˣ) = 1 := by
        show (Additive.toMul (Additive.ofMul (1 : Lˣ)) : Lˣ) = 1
        rfl
      exact h4.trans h5
    rw [z_toMul_apply p hζ hz m] at h3
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd m p).mpr ((hζU.zpow_eq_one_iff_dvd m).mp h3)
  exact sub_eq_zero.mp h2

/-- The kernel of the `p`-th power map consists of the values of the Kummer coefficient class. -/
theorem ker_pthMapX_le_range_z {k : Type} [Field k] [NumberField k] {L : Type} [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (p : ℕ) [Fact p.Prime]
    {ζ : k} (hζ : IsPrimitiveRoot ζ p)
    {z : Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ levelUnits k L}
    (hz : ((Additive.toMul (z.hom (1 : ZMod p)) : Lˣ) : L) = algebraMap k L ζ)
    {x : Additive Lˣ} (hx : (pthMapX k L p).hom x = 0) :
    ∃ y : ZMod p, z.hom y = x := by
  have h0 : (p:ℕ) • x = 0 := by
    have h := congrArg (fun w : ↥(pthSubX L p) => (w : Additive Lˣ)) hx
    rw [pthMapX_apply k L p x] at h
    exact h
  have hx_pow : (Additive.toMul x : Lˣ) ^ p = 1 := by
    have hx_eq : x = Additive.ofMul (Additive.toMul x : Lˣ) :=
      (Equiv.apply_symm_apply Additive.ofMul x).symm
    have h0' : (p:ℕ) • (Additive.ofMul (Additive.toMul x : Lˣ)) = (0 : Additive Lˣ) := by
      rw [← hx_eq]
      exact h0
    rw [nsmul_ofMul] at h0'
    have h4 : (Additive.toMul (Additive.ofMul ((Additive.toMul x : Lˣ) ^ p)) : Lˣ)
        = (Additive.toMul (0 : Additive Lˣ) : Lˣ) :=
      congrArg (fun y => (Additive.toMul y : Lˣ)) h0'
    have h5 : (Additive.toMul (Additive.ofMul ((Additive.toMul x : Lˣ) ^ p)) : Lˣ)
        = (Additive.toMul x : Lˣ) ^ p := rfl
    have h6 : (Additive.toMul (0 : Additive Lˣ) : Lˣ) = 1 := by simp
    exact h5.symm.trans (h4.trans h6)
  have hζL : IsPrimitiveRoot (algebraMap k L ζ) p :=
    hζ.map_of_injective (algebraMap k L).injective
  have hx_powL : ((Additive.toMul x : Lˣ) : L) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx_pow, Units.val_one]
  obtain ⟨i, _hi, hi⟩ := hζL.eq_pow_of_pow_eq_one (ξ := ((Additive.toMul x : Lˣ) : L)) hx_powL
  refine ⟨(i : ZMod p), ?_⟩
  have hi' : zetaUnitL k L p ζ hζ ^ (i : ℤ) = Additive.toMul x := by
    rw [zpow_natCast]
    exact Units.ext hi
  have hkey : (Additive.toMul (z.hom ((i : ℤ) : ZMod p)) : Lˣ) = Additive.toMul x :=
    (z_toMul_apply p hζ hz (i : ℤ)).trans hi'
  have hcast : (i : ZMod p) = ((i : ℤ) : ZMod p) := by push_cast; rfl
  have hgoal : z.hom ((i : ℤ) : ZMod p) = x :=
    ((Equiv.apply_symm_apply Additive.ofMul (z.hom ((i : ℤ) : ZMod p))).symm.trans
      ((congrArg Additive.ofMul hkey).trans (Equiv.apply_symm_apply Additive.ofMul x)))
  rw [hcast]
  exact hgoal

/-- The composite `𝔽_p → Lˣ → (Lˣ)^p` is zero. -/
theorem z_comp_pthMapX (k : Type) [Field k] [NumberField k] (L : Type) [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (p : ℕ) [Fact p.Prime]
    {ζ : k} (hζ : IsPrimitiveRoot ζ p)
    {z : Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ levelUnits k L}
    (hz : ((Additive.toMul (z.hom (1 : ZMod p)) : Lˣ) : L) = algebraMap k L ζ) :
    z ≫ pthMapX k L p = 0 := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext ?_))
  intro x
  show (pthMapX k L p).hom (z.hom x) = 0
  refine Subtype.ext ?_
  show (p:ℕ) • (z.hom x) = 0
  have hpow : (Additive.toMul (z.hom x) : Lˣ) ^ p = 1 := z_toMul_pow p hζ hz x
  have key : (p:ℕ) • (Additive.ofMul (Additive.toMul (z.hom x) : Lˣ)) = (0 : Additive Lˣ) := by
    rw [nsmul_ofMul, hpow]
    rfl
  have step : (p:ℕ) • (z.hom x)
      = (p:ℕ) • (Additive.ofMul (Additive.toMul (z.hom x) : Lˣ)) :=
    congrArg (fun y => (p:ℕ) • y) ((Equiv.apply_symm_apply Additive.ofMul (z.hom x)).symm)
  exact step.trans key

/-- The short complex `0 → 𝔽_p → Lˣ → (Lˣ)^p → 0`. -/
noncomputable def kummerSESX (k : Type) [Field k] [NumberField k] (L : Type) [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (p : ℕ) [Fact p.Prime]
    {ζ : k} (hζ : IsPrimitiveRoot ζ p)
    (z : Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ levelUnits k L)
    (hz : ((Additive.toMul (z.hom (1 : ZMod p)) : Lˣ) : L) = algebraMap k L ζ) :
    ShortComplex (Rep.{0,0,0} Coeff (L ≃ₐ[k] L)) :=
  ShortComplex.mk z (pthMapX k L p) (z_comp_pthMapX k L p hζ hz)

/-- The Kummer short complex is short exact. -/
theorem kummerSESX_shortExact (k : Type) [Field k] [NumberField k] (L : Type) [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (p : ℕ) [Fact p.Prime]
    {ζ : k} (hζ : IsPrimitiveRoot ζ p)
    (z : Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ levelUnits k L)
    (hz : ((Additive.toMul (z.hom (1 : ZMod p)) : Lˣ) : L) = algebraMap k L ζ) :
    (kummerSESX k L p hζ z hz).ShortExact :=
  Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise
    (k := Coeff) (G := L ≃ₐ[k] L) (kummerSESX k L p hζ z hz)
    ((Rep.mono_iff_injective z).mpr (z_injective p hζ hz))
    ((Rep.epi_iff_surjective (pthMapX k L p)).mpr (pthMapX_surjective k L p))
    (fun _ hx => ker_pthMapX_le_range_z p hζ hz hx)


end Work.SSGRoute
