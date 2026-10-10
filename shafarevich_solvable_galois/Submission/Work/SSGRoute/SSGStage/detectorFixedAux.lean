import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E7cOmega.ratDivDefs
import Submission.Work.SSGRoute.E9c.TransportDefs
import Submission.Work.SSGRoute.Sha2Lib.exists_unramified_character_with_p_dvd_residueDeg

/-!
# Bookkeeping for the fixed-part case of the unramified detector

First step of `Work.SSGRoute.SSGStage.detector_of_fixedPart`
(`Submission/Work/SSGRoute/SSGStage/unramifiedDetector.lean` records the full route).

The detector class is built from the character `f : Additive G →+ ℤ/p` (killing the inertia at
`q'`, nontrivial on `D_{q'}`) and a fixed vector `m ∈ M^{G₀}`, via the scalar action

  `zmodSmulHom p m hm : ℤ/p →+ M,  z ↦ z • m`   (`hm : p • m = 0`),

and the resulting 1-cocycle `γ ↦ zmodSmulHom p m hm (f (ofMul γ))`.  This file contains the
elementary part of that bookkeeping; the class `eCoh 1 G A (H1π A z)` and its two properties are
the next steps.
-/

namespace Work.SSGRoute.SSGStage

open SSGRoute.PTExt

/-- The additive hom `ℤ →+ M`, `k ↦ k • m`. -/
def zsmulHom {M : Type} [AddCommGroup M] (m : M) : ℤ →+ M where
  toFun k := k • m
  map_zero' := by simp
  map_add' a b := by rw [add_smul]

@[simp] lemma zsmulHom_apply {M : Type} [AddCommGroup M] (m : M) (k : ℤ) :
    zsmulHom m k = k • m := rfl

/-- The additive hom `ℤ/p →+ M`, `z ↦ z • m`; well defined when `p • m = 0`. -/
noncomputable def zmodSmulHom (p : ℕ) {M : Type} [AddCommGroup M] (m : M) (hm : p • m = 0) :
    ZMod p →+ M :=
  ZMod.lift p ⟨zsmulHom m, by
    show zsmulHom m (p : ℤ) = 0
    rw [zsmulHom_apply]
    simpa using hm⟩

/-- **Values of the scalar action** on the representatives of `ℤ`: `zmodSmulHom p m hm k = k • m`. -/
lemma zmodSmulHom_coe (p : ℕ) {M : Type} [AddCommGroup M] (m : M) (hm : p • m = 0) (k : ℤ) :
    zmodSmulHom p m hm (k : ZMod p) = k • m := by
  rw [zmodSmulHom, ZMod.lift_coe]
  rfl

/-- **The image of a fixed vector is fixed**: if `m` is fixed by `G` then so is every
`zmodSmulHom p m hm z`. -/
lemma map_zmodSmulHom_of_fixed {G : Type} [Group G] (A : Rep.{0} SSGRoute.PTExt.Coeff G)
    (p : ℕ) (m : A.V) (hm : p • m = 0) (hfix : ∀ g : G, A.ρ g m = m) (g : G) (z : ZMod p) :
    A.ρ g (zmodSmulHom p m hm z) = zmodSmulHom p m hm z := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  rw [zmodSmulHom_coe, map_zsmul, hfix]

/-- **The detector cocycle.**  For an additive character `f : Additive G →+ ℤ/p` and a fixed vector
`m` of exponent dividing `p`, the function `γ ↦ zmodSmulHom p m hm (f (ofMul γ))` is a 1-cocycle
with values in `A`. -/
theorem mem_cocycles₁_zmodSmul {G : Type} [Group G] (A : Rep.{0} SSGRoute.PTExt.Coeff G)
    (p : ℕ) (m : A.V) (hm : p • m = 0) (hfix : ∀ g : G, A.ρ g m = m)
    (f : Additive G →+ ZMod p) :
    (fun γ : G => zmodSmulHom p m hm (f (Additive.ofMul γ))) ∈ groupCohomology.cocycles₁ A := by
  rw [groupCohomology.mem_cocycles₁_iff]
  intro γ δ
  show zmodSmulHom p m hm (f (Additive.ofMul (γ * δ))) =
    A.ρ γ (zmodSmulHom p m hm (f (Additive.ofMul δ))) +
      zmodSmulHom p m hm (f (Additive.ofMul γ))
  have hofmul : Additive.ofMul (γ * δ) = Additive.ofMul γ + Additive.ofMul δ := rfl
  rw [hofmul, map_add f, map_add (zmodSmulHom p m hm),
    map_zmodSmulHom_of_fixed A p m hm hfix γ (f (Additive.ofMul δ)), add_comm]

/-- **The detector class vanishes on any subgroup on which the character vanishes.**  In
particular it is unramified at `q'` when `f` kills the inertia at `q'` (the case of the fixed-part
detector, `f` coming from `exists_unramified_character_with_p_dvd_residueDeg`). -/
theorem extHRestrict_eCoh_zmodSmul_eq_zero {G : Type} [Group G] (A : Rep.{0} SSGRoute.PTExt.Coeff G)
    (p : ℕ) (m : A.V) (hm : p • m = 0) (hfix : ∀ g : G, A.ρ g m = m)
    (f : Additive G →+ ZMod p) (D : Subgroup G) (hfD : ∀ d ∈ D, f (Additive.ofMul d) = 0) :
    SSGRoute.PTExt.extHRestrict D (SSGRoute.PTExt.eCoh 1 G A
      ((groupCohomology.H1π A).hom
        ⟨fun γ => zmodSmulHom p m hm (f (Additive.ofMul γ)),
          mem_cocycles₁_zmodSmul A p m hm hfix f⟩)) = 0 := by
  refine (Work.SSGRoute.e9_caseB_cocycle A D
    ⟨fun γ => zmodSmulHom p m hm (f (Additive.ofMul γ)),
      mem_cocycles₁_zmodSmul A p m hm hfix f⟩).mpr ⟨0, ?_⟩
  intro d hd
  rw [map_zero, sub_zero]
  show zmodSmulHom p m hm (f (Additive.ofMul d)) = 0
  rw [hfD d hd, map_zero]

/-- **Detection.**  If the transported cocycle `h' ↦ φ (z (f h'))` takes a nonzero value, then the
image of the class of `z` under the coefficient change `φ` is nonzero.  (The hypothesis
`[B.IsTrivial]` makes the `1`-coboundaries of `B` vanish, so a nonzero cocycle is a nonzero
class.) -/
theorem eCoh_map_ne_zero {G H : Type} [Group G] [Group H] (f : H →* G)
    (A : Rep.{0} SSGRoute.PTExt.Coeff G) (B : Rep.{0} SSGRoute.PTExt.Coeff H) [B.IsTrivial]
    (φ : Rep.res f A ⟶ B) (z : ↥(groupCohomology.cocycles₁ A))
    (h : ∃ h₀ : H, φ ((z : G → A.V) (f h₀)) ≠ 0) :
    SSGRoute.PTExt.eCoh 1 H B ((groupCohomology.map f φ 1).hom
      ((groupCohomology.H1π A).hom z)) ≠ 0 := by
  intro hzero
  have h1 : (groupCohomology.map f φ 1).hom ((groupCohomology.H1π A).hom z) = 0 :=
    (SSGRoute.PTExt.eCoh 1 H B).injective (by rw [hzero, map_zero])
  rw [groupCohomology.H1π_comp_map_apply] at h1
  rw [groupCohomology.H1π_eq_zero_iff, groupCohomology.coboundaries₁_eq_bot_of_isTrivial,
    Submodule.mem_bot] at h1
  obtain ⟨h₀, hh₀⟩ := h
  refine hh₀ ?_
  have h2 := congrFun h1 h₀
  rw [show (groupCohomology.mapCocycles₁ f φ z : H → B.V) h₀ = φ (z (f h₀)) from rfl] at h2
  exact h2

/-- **`extHMap` along a subgroup is the composite with the coefficient map**: restricting a class
to `D` and then changing coefficients is the `extHMap` of the two. -/
theorem extHMap_eq_comp_mk₀ {G : Type} [Group G] (D : Subgroup G)
    (A : Rep.{0} SSGRoute.PTExt.Coeff G) (B : Rep.{0} SSGRoute.PTExt.Coeff D)
    (φ : Rep.res D.subtype A ⟶ B) (h : SSGRoute.PTExt.extH A 1) :
    SSGRoute.PTExt.extHMap D.subtype φ h =
      (SSGRoute.PTExt.extHRestrict D h).comp
        (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 1) := by
  rw [SSGRoute.PTExt.extHMap, SSGRoute.PTExt.extHRestrict, SSGRoute.PTExt.extHMap]
  simp only [CategoryTheory.Abelian.Ext.comp_mk₀_id]
  rw [CategoryTheory.Abelian.Ext.comp_assoc]
  omega

attribute [local instance 10000] Rep.hV2 Rep.hV1

/-- **The restriction of a trivial representation is trivial.**  (Recorded as an instance so that
the `IsTrivial` requirement of `eCoh_map_ne_zero` is discharged by synthesis.) -/
instance isTrivial_res {G H : Type} [Group G] [Group H] (f : H →* G)
    (A : Rep.{0} SSGRoute.PTExt.Coeff G) [A.IsTrivial] : (Rep.res f A).IsTrivial :=
  ⟨fun h => Representation.isTrivial_def A.ρ (f h)⟩

/-- **Restriction then coefficient change, in `eCoh` form.**  This is the bridge used by the
detection step of `detector_of_fixedPart`: it identifies the composite `(extHRestrict D h).comp
(mk₀ ν)` (the shape the level pairing consumes) with the `eCoh`-image of the transported class,
which is what `eCoh_map_ne_zero` evaluates. -/
theorem extHRestrict_comp_mk0_eq_eCoh_map {G : Type} [Group G] (D : Subgroup G)
    (A : Rep.{0} SSGRoute.PTExt.Coeff G) (B : Rep.{0} SSGRoute.PTExt.Coeff ↥D)
    (ν : Rep.res D.subtype A ⟶ B) (h : SSGRoute.PTExt.extH A 1) :
    (SSGRoute.PTExt.extHRestrict D h).comp (CategoryTheory.Abelian.Ext.mk₀ ν) (add_zero 1)
      = SSGRoute.PTExt.eCoh 1 ↥D B ((groupCohomology.map D.subtype ν 1).hom
          ((SSGRoute.PTExt.eCoh 1 G A).symm h)) := by
  rw [← extHMap_eq_comp_mk₀ D A B ν h]
  simpa using (Work.SSGRoute.eCoh_map 1 G ↥D D.subtype A B ν
    ((SSGRoute.PTExt.eCoh 1 G A).symm h)).symm

/-! ## The fixed-part detector -/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open scoped ZeroObject

/-- **Fixed-part case of the unramified detector.**  If a nonzero `D_w`-equivariant
`μ : res M → ℚ/ℤ` does not vanish on the `Gal(K/k)`-fixed part of `M`, then some finite Galois
level `L ⊇ K` carries an unramified-at-`q'` class `h` whose local restriction is not killed by `μ`. -/
theorem detector_of_fixedPart (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
            (NK.GlobalCFT.Place.ofFinite q)).subtype M ⟶
          Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K)
            (NK.GlobalCFT.Place.ofFinite q)))
    (hm : ∃ m : M, (∀ σ : K ≃ₐ[k] K, M.ρ σ m = m) ∧ μ.hom m ≠ 0) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
        (NK.GlobalCFT.Place.ofFinite q))
      (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K ↥L) M) 1),
      SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
      Nat.Coprime (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p ∧
      (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
          (NK.GlobalCFT.Place.ofFinite q')) h).comp
        (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap
          (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
            (NK.GlobalCFT.Place.ofFinite q') hq') μ)) (add_zero 1) ≠ 0 := by
  classical
  obtain ⟨m, hmfix, hmne⟩ := hm
  obtain ⟨L, hLnf, hLfd, hLgal, q', hq'lies, hram, _hfdvd, χ, hχinert, hχnon⟩ :=
    Work.SSGRoute.Sha2Lib.exists_unramified_character_with_p_dvd_residueDeg p k K Ω q
  letI : FiniteDimensional k ↥L := hLfd
  letI : IsGalois k ↥L := hLgal
  obtain ⟨σ₀, hσ₀D, hσ₀χ⟩ := hχnon
  let f : Additive (↥L ≃ₐ[k] ↥L) →+ ZMod p :=
    { toFun := fun x => (χ (Additive.toMul x)).toAdd
      map_zero' := by rw [toMul_zero, map_one, toAdd_one]
      map_add' := by intro a b; rw [toMul_add, map_mul, toAdd_mul] }
  have hfσ₀ : f (Additive.ofMul σ₀) ≠ 0 := by
    intro h0
    apply hσ₀χ
    exact Multiplicative.toAdd.injective (by rw [show (χ σ₀).toAdd = 0 from h0, toAdd_one])
  have hfinert : ∀ d : ↥L ≃ₐ[k] ↥L,
      SSGRoute.PTExt.IsInertiaAt q' d → f (Additive.ofMul d) = 0 := by
    intro d hd
    show (χ (Additive.toMul (Additive.ofMul d))).toAdd = 0
    rw [toMul_ofMul, hχinert d hd, toAdd_one]
  let j : ZMod p := (f (Additive.ofMul σ₀))⁻¹
  let f' : Additive (↥L ≃ₐ[k] ↥L) →+ ZMod p :=
    { toFun := fun x => j * f x
      map_zero' := by simp
      map_add' := by intro a b; rw [map_add, mul_add] }
  have hf'σ₀ : f' (Additive.ofMul σ₀) = 1 := inv_mul_cancel₀ hfσ₀
  have hf'inert : ∀ d : ↥L ≃ₐ[k] ↥L,
      SSGRoute.PTExt.IsInertiaAt q' d → f' (Additive.ofMul d) = 0 := by
    intro d hd
    show j * f (Additive.ofMul d) = 0
    rw [hfinert d hd, mul_zero]
  let A : Rep.{0} SSGRoute.PTExt.Coeff (↥L ≃ₐ[k] ↥L) :=
    Rep.res (SSGRoute.PTExt.galRes k K ↥L) M
  have hfixA : ∀ γ : ↥L ≃ₐ[k] ↥L, A.ρ γ m = m := fun γ => hmfix _
  let zc : (↥L ≃ₐ[k] ↥L) → A.V := fun γ => zmodSmulHom p m (hM m) (f' (Additive.ofMul γ))
  have hzc : zc ∈ groupCohomology.cocycles₁ A :=
    mem_cocycles₁_zmodSmul A p m (hM m) hfixA f'
  let z : ↥(groupCohomology.cocycles₁ A) := ⟨zc, hzc⟩
  let h : SSGRoute.PTExt.extH A 1 :=
    SSGRoute.PTExt.eCoh 1 (↥L ≃ₐ[k] ↥L) A ((groupCohomology.H1π A).hom z)
  have hlies : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
      (NK.GlobalCFT.Place.ofFinite q) := NK.GlobalCFT.Place.liesOver_ofFinite hq'lies
  refine ⟨L, hLnf, hLfd, hLgal, q', hlies, h, ?_, ?_⟩
  · intro D hD
    exact extHRestrict_eCoh_zmodSmul_eq_zero A p m (hM m) hfixA f' D
      (fun d hd => hf'inert d (hD d hd))
  · refine ⟨?_, ?_⟩
    · rw [hram]; exact Nat.coprime_one_left p
    · let fμ := Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite q') hlies
      let D : Subgroup (↥L ≃ₐ[k] ↥L) := SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q')
      let B : Rep.{0} SSGRoute.PTExt.Coeff ↥D :=
        Rep.res fμ (Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K)
          (NK.GlobalCFT.Place.ofFinite q)))
      have hres : Rep.res fμ (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
          (NK.GlobalCFT.Place.ofFinite q)).subtype M) = Rep.res D.subtype A :=
        Work.SSGRoute.decompKRestrict_res_res k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hlies M
      -- `Rep.res` is `Rep.of (·.ρ.comp ·)` definitionally, so the coefficient map can simply be
      -- typed at the restricted module; no `Eq.rec` transport is needed
      let ν : Rep.res D.subtype A ⟶ B := Rep.resMap fμ μ
      haveI : B.IsTrivial := isTrivial_res fμ _
      have hval : zc σ₀ = m := by
        show zmodSmulHom p m (hM m) (f' (Additive.ofMul σ₀)) = m
        rw [hf'σ₀]
        rw [show (1 : ZMod p) = ((1 : ℤ) : ZMod p) from (Int.cast_one (R := ZMod p)).symm,
          zmodSmulHom_coe, one_zsmul]
      have hν : ν (zc σ₀) ≠ 0 := by
        show μ.hom (zc σ₀) ≠ 0
        rw [hval]
        exact hmne
      have hkey := extHRestrict_comp_mk0_eq_eCoh_map D A B ν h
      rw [hkey]
      have hval₂ : ν (zc (D.subtype ⟨σ₀, hσ₀D⟩)) ≠ 0 := by
        rw [show (D.subtype ⟨σ₀, hσ₀D⟩ : ↥L ≃ₐ[k] ↥L) = σ₀ from rfl]
        exact hν
      have hfin := eCoh_map_ne_zero D.subtype A B ν z ⟨⟨σ₀, hσ₀D⟩, hval₂⟩
      have hsym : (SSGRoute.PTExt.eCoh 1 (↥L ≃ₐ[k] ↥L) A).symm h
          = (groupCohomology.H1π A).hom z := by simp [h]
      rw [hsym]
      exact hfin

/-! ## Summary

This module proves the **fixed-part case of the unramified detector** (`detector_of_fixedPart`,
`sorry`-free) together with the reusable core it rests on:

* `mem_cocycles₁_zmodSmul` — the detector cocycle `γ ↦ zmodSmulHom p m hm (f (ofMul γ))`;
* `extHRestrict_eCoh_zmodSmul_eq_zero` — its class is unramified wherever the character vanishes on
  the inertia (via `Work.SSGRoute.e9_caseB_cocycle`);
* `eCoh_map_ne_zero` — a nonzero value of the transported cocycle makes the class nonzero (via
  `groupCohomology.H1π_comp_map_apply` and `coboundaries₁_eq_bot_of_isTrivial`);
* `extHMap_eq_comp_mk₀` and `extHRestrict_comp_mk0_eq_eCoh_map` — the two `Ext`-level comparisons
  turning "restriction then coefficient change" into the `eCoh`-image that `eCoh_map_ne_zero`
  evaluates;
* `isTrivial_res` — `IsTrivial` for a restricted trivial representation.

The proof avoids any injectivity statement about `ℤ/p → ℚ/ℤ`: normalising the character
`f := (χ ·).toAdd` at a `σ₀ ∈ D_{q'}` with `χ σ₀ ≠ 1` gives `f' := (f σ₀)⁻¹ · f` with `f' σ₀ = 1`
(and `f'` still kills the inertia), so the detection value at `σ₀` is literally `μ m ≠ 0`.

What remains for node `C6` itself (`Work.SSGRoute.SSGStage.unramifiedDetector`) is *only* the
non-fixed case `μ(M^{G₀}) = 0`, whose analysis is recorded in that file: the local cocycle exists
iff `ker(x ↦ x ∪ e_D) ≠ 0` (true for odd `p` at `D = ℤ/p`, false for `p = 2` at `ℤ/2 × U`, first
true at `ℤ/4`), and the global realisation is the Poitou–Tate/Chebotarev input that is the genuine
missing arithmetic of the node.
-/

end Work.SSGRoute.SSGStage
