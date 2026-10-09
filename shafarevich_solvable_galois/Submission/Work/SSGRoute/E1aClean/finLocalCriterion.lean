import Mathlib
import Submission.Work.SSGRoute.E1aClean.LocalExtensionAux
import Submission.Work.SSGRoute.E1aClean.exists_localData_with_seam
import Submission.Work.SSGRoute.E1aClean.extResCompOfExtension
import Submission.Work.SSGRoute.E1cGeneric.Canonical
import Submission.Work.SSGRoute.PT.akH2Setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The finite-place local criterion of the E1a landing clause

This module proves `Work.SSGRoute.E1aClean.finLocalCriterion` (the honest finite-place crux
"CRUX-a" of the E1a node).  The route is the one recorded in `ExtChain/himgIdelesInput_fin.lean`
§"2026-10-02d":

* the `E1c`-dictionary value of a `PhiE`-generator is `β⁻¹` of the `H⁰`-class `ΨE(w)`
  (`e1cMap_Phi`), and `β⁻¹` of the class of an invariant element is represented by the *cocycle*
  `g ↦ ι⁻¹(g • n - n)` of any cochain lift `n` of it (`betaRaw`/`betaRaw_congr`); hence the
  restriction hypothesis `resH1_D (e1cMap R (PhiE R w)) = 0` unwinds *cochain-wise* to the
  existence of a `D`-invariant lift `Ψ : F → Ωˣ` of `ΨE(w)` (this is `extCochainExtension`
  `ExtChain/cruxA_proved.lean`, reproduced here without the spurious `[Finite R.V]` hypothesis,
  which is false for the canonical syzygy `R = ker (freeCover N)`);
* the local extension clause `exists_localExtension` then produces the morphism of
  `D_q`-representations `φ : Rep.res (F) ⟶ K_qˣ` compatible with `unitsToLocalUnits`
  (`localExtensionExistsNoFinite`, the `[Finite R.V]`-free form);
* `extResCompOfExtension` converts `φ` into the vanishing of the localised class.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt
open scoped Pointwise

attribute [local instance 10000] Rep.hV1 Rep.hV2

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. The local extension clause, without the spurious finiteness of `R` -/

/-- **The local extension clause of the finite-place crux.**

For a finite place `A` of `Ω` over `k` with prime `q` of `K` below it, an element
`w ∈ Ext⁰_G(R₁, Kˣ)` and a `D_A`-invariant `Ωˣ`-valued extension `Ψ` of `ΨE(w)` along the canonical
cover, there is a morphism of `D_q`-representations `φ : Rep.res_{D_q}(F) ⟶ K_qˣ` which on the
syzygy `R₁` is the localisation `w ↦ K_qˣ` of `w`.

This is `E1aClean.exists_localExtension` with the finiteness hypothesis on the carrier of `R`
removed (nothing in the construction uses it, and it is *false* for the canonical syzygy
`R = ker (freeCover N)`, whose carrier is a lattice). -/

theorem localExtensionExistsNoFinite
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (w : CategoryTheory.Abelian.Ext.{0}
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k:=k) (Ω:=Ω) (K:=K) R)
        (SSGRoute.PTExt.unitsK k K) 0)
    (Ψ : ↥(Work.AbsoluteKummer.H0 (SSGRoute.decomp k A)
        (Work.SSGRoute.ExtChain.homCoindFreeT k Ω K R.V)))
    (hΨ : ∀ x : (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k:=k) (Ω:=Ω) (K:=K) R).V,
      (Ψ : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K R.V)
          (Work.SSGRoute.ExtChain.E1cGeneric.kappa (k:=k) (Ω:=Ω) (K:=K) R x)
        = (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k:=k) (Ω:=Ω) (K:=K)
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k:=k) (Ω:=Ω) (K:=K) R) w).1 x) :
    ∃ φ : Rep.res (SSGRoute.PTExt.decompK (k:=k) (NK.GlobalCFT.Place.ofFinite q)).subtype
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k:=k) (Ω:=Ω) (K:=K) R)
        ⟶ SSGRoute.PTExt.localUnitsK (k:=k) (NK.GlobalCFT.Place.ofFinite q),
      ∀ r : (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k:=k) (Ω:=Ω) (K:=K) R).V,
        Rep.Hom.hom φ (Work.SSGRoute.ExtChain.E1cGeneric.kappa (k:=k) (Ω:=Ω) (K:=K) R r)
          = (NK.HassePrinciple.unitsToLocalUnitsHom (NK.GlobalCFT.Place.ofFinite q)).toAdditive
              (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ w) r) := by
  classical
  let Fm : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
    Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k:=k) (Ω:=Ω) (K:=K) R
  -- ===== Step 0: the local data of the place `A` =====
  obtain ⟨hLies, hcompat', _⟩ :=
    Work.SSGRoute.exists_adicCompletion_algebra_compat k Ω K A hA q hAq
  have hAq' := Submission.NeukirchUchida.primeOf_spec A hA
  have hcompat : ∀ x : k, algebraMap k (q.adicCompletion K) x =
      algebraMap (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K)
        (algebraMap k (Work.SSGRoute.localFieldAt k A hA) x) := fun x => (hcompat' x).symm
  letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
      (Work.SSGRoute.primeUnder k A hA) A hAq').toAlgebra
  letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
    (Work.SSGRoute.adicCompletionMapAt k Ω K A hA q hLies).toAlgebra
  obtain ⟨K', hfdK', hgalK', ψ, eG, Φ, e, _hΦhomeo, _hiso, hpt, h4, hψ, hseam⟩ :=
    exists_localData_with_seam 2 k Ω K A hA q hAq
  haveI : IsGalois (Work.SSGRoute.localFieldAt k A hA) (Work.SSGRoute.localClosureAt k A hA) :=
    inferInstance
  -- ===== Step 1: the seam `s : Ω →+* Ω_v` =====
  let s : Ω →+* Work.SSGRoute.localClosureAt k A hA :=
    { toFun := fun y => e (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω)
        (Work.SSGRoute.primeUnder k A hA) A y)
      map_one' := by rw [NK.NeukirchUchida.coInAdjoin_one, map_one]
      map_mul' := fun a b => by rw [NK.NeukirchUchida.coInAdjoin_mul, map_mul]
      map_zero' := by rw [NK.NeukirchUchida.coInAdjoin_zero, map_zero]
      map_add' := fun a b => by rw [NK.NeukirchUchida.coInAdjoin_add, map_add] }
  have hs_apply : ∀ y : Ω, s y = e (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω)
      (Work.SSGRoute.primeUnder k A hA) A y) := fun y => rfl
  have hs_equiv : ∀ (τ : ↥(SSGRoute.decomp k A)) (y : Ω),
      (Φ τ) (s y) = s ((τ : Ω ≃ₐ[k] Ω) y) := by
    intro τ y
    rw [hs_apply, hs_apply]
    exact hseam τ y
  have hs_inj : Function.Injective s := RingHom.injective s
  -- ===== Step 2: the additive map `ν = eAdd ∘ Ψ` =====
  let Ψa : (Fm).V →+ Additive Ωˣ := (Ψ : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K R.V)
  let eAdd : Additive Ωˣ →+ Additive (Units (Work.SSGRoute.localClosureAt k A hA)) :=
    (Units.map s.toMonoidHom).toAdditive
  let ν : (Fm).V →+ Additive (Units (Work.SSGRoute.localClosureAt k A hA)) := eAdd.comp Ψa
  let νu : (Fm).V → (Units (Work.SSGRoute.localClosureAt k A hA)) :=
    fun x => Additive.toMul (ν x)
  have νu_coe : ∀ x : (Fm).V,
      (νu x : Work.SSGRoute.localClosureAt k A hA)
        = s ((Additive.toMul (Ψa x) : Ωˣ) : Ω) := by
    intro x
    rw [show νu x = Units.map s.toMonoidHom (Additive.toMul (Ψa x)) from rfl, Units.coe_map]
    rfl
  have ν_equiv : ∀ (τ : ↥(SSGRoute.decomp k A)) (x : (Fm).V),
      (νu ((Fm).ρ (SSGRoute.res k K (τ : Ω ≃ₐ[k] Ω)) x))
        = (Φ τ) (νu x : Work.SSGRoute.localClosureAt k A hA) := by
    intro τ x
    have h1 : (Ψ : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K R.V)
        ((Fm).ρ (SSGRoute.res k K (τ : Ω ≃ₐ[k] Ω)) x)
        = τ • ((Ψ : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K R.V) x) :=
      homCoind_invariance_apply A Ψ τ x
    rw [νu_coe, νu_coe, h1]
    show s ((τ : Ω ≃ₐ[k] Ω) ((Additive.toMul (Ψa x) : Ωˣ) : Ω))
      = (Φ τ) (s ((Additive.toMul (Ψa x) : Ωˣ) : Ω))
    exact (hs_equiv τ ((Additive.toMul (Ψa x) : Ωˣ) : Ω)).symm
  -- ===== Step 3: the values of `ν` lie in `L' = k_v(s(K))` =====
  let S : Set (Work.SSGRoute.localClosureAt k A hA) := Set.range (fun y : K => s (y : Ω))
  let L' : IntermediateField (Work.SSGRoute.localFieldAt k A hA)
      (Work.SSGRoute.localClosureAt k A hA) :=
    IntermediateField.adjoin (Work.SSGRoute.localFieldAt k A hA) S
  have hS_mem : ∀ y : K, s (y : Ω) ∈ S := fun y => Set.mem_range_self y
  have hS_le : S ⊆ (L' : Set (Work.SSGRoute.localClosureAt k A hA)) :=
    IntermediateField.subset_adjoin _ _
  have hL'_mem : ∀ x : (Fm).V, (νu x : Work.SSGRoute.localClosureAt k A hA) ∈ L' := by
    intro x
    rw [← InfiniteGalois.fixedField_fixingSubgroup L', IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hfix : ∀ y : K, σ (s (y : Ω)) = s (y : Ω) := fun y =>
      (IntermediateField.mem_fixingSubgroup_iff L' σ).mp hσ (s (y : Ω)) (hS_le (hS_mem y))
    set τ : ↥(SSGRoute.decomp k A) := Φ.symm σ with hτdef
    have hΦτ : Φ τ = σ := Φ.apply_symm_apply σ
    have hres : SSGRoute.res k K (τ : Ω ≃ₐ[k] Ω) = 1 := by
      refine AlgEquiv.ext fun y => ?_
      rw [AlgEquiv.one_apply]
      refine Subtype.ext ?_
      show ((SSGRoute.res k K (τ : Ω ≃ₐ[k] Ω)) y : Ω) = (y : Ω)
      rw [AlgEquiv.restrictNormalHom_apply]
      refine hs_inj ?_
      rw [← hs_equiv τ (y : Ω), hΦτ]
      exact hfix y
    have hρ : (Fm).ρ (SSGRoute.res k K (τ : Ω ≃ₐ[k] Ω)) x = x := by
      rw [hres, map_one, Module.End.one_apply]
    have heq := ν_equiv τ x
    rw [hρ] at heq
    rw [← hΦτ]
    exact heq.symm
  have hL'K' : L' ≤ K' := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro z ⟨y, rfl⟩
    show s (algebraMap K Ω y) ∈ (K' : Set (Work.SSGRoute.localClosureAt k A hA))
    rw [hs_apply (algebraMap K Ω y), ← hψ y]
    exact (ψ.symm (algebraMap K (q.adicCompletion K) y)).2
  -- ===== Step 4: `νK : F →+ (K')ˣ` and the target map =====
  let νKf : (Fm).V → (Units ↥K') := fun x =>
    Units.mk0 (⟨(νu x : Work.SSGRoute.localClosureAt k A hA), hL'K' (hL'_mem x)⟩ : ↥K')
      (fun h => Units.ne_zero (νu x) (Subtype.ext_iff.mp h))
  have νKf_coe : ∀ x : (Fm).V, (↑(νKf x) : ↥K')
      = ⟨(νu x : Work.SSGRoute.localClosureAt k A hA), hL'K' (hL'_mem x)⟩ :=
    fun x => Units.val_mk0 ..
  have hνKf_val : ∀ z : (Fm).V,
      ((↑(νKf z) : ↥K') : Work.SSGRoute.localClosureAt k A hA)
        = (νu z : Work.SSGRoute.localClosureAt k A hA) := by
    intro z
    have h := congrArg (fun w : ↥K' => (w : Work.SSGRoute.localClosureAt k A hA)) (νKf_coe z)
    simpa using h
  have νKf_zero : νKf 0 = 1 := by
    apply Units.ext
    refine Subtype.coe_injective ?_
    show (νu (0 : (Fm).V) : Work.SSGRoute.localClosureAt k A hA) = 1
    rw [νu_coe]
    rw [show ((Additive.toMul (Ψa 0) : Ωˣ) : Ω) = 1 from by rw [map_zero]; rfl]
    rw [map_one]
  have νKf_add : ∀ x y : (Fm).V, νKf (x + y) = νKf x * νKf y := by
    intro x y
    apply Units.ext
    refine Subtype.coe_injective ?_
    show (νu (x + y) : Work.SSGRoute.localClosureAt k A hA)
        = (νu x : Work.SSGRoute.localClosureAt k A hA)
          * (νu y : Work.SSGRoute.localClosureAt k A hA)
    rw [νu_coe, νu_coe, νu_coe, map_add]
    exact map_mul s _ _
  let νK : (Fm).V →+ Additive (Units ↥K') :=
    { toFun := fun x => Additive.ofMul (νKf x)
      map_zero' := by rw [νKf_zero]; rfl
      map_add' := fun x y => by rw [νKf_add]; rfl }
  have νK_eq : ∀ x : (Fm).V, Additive.toMul (νK x) = νKf x := fun x => rfl
  let eψ : Additive (Units ↥K') →+ Additive (Units (q.adicCompletion K)) :=
    (Units.map ψ.toRingEquiv.toMulEquiv.toMonoidHom).toAdditive
  let φadd : (Fm).V →+ Additive (Units (q.adicCompletion K)) := eψ.comp νK
  let φu : (Fm).V → (Units (q.adicCompletion K)) := fun x => Additive.toMul (φadd x)
  have φu_eq : ∀ x : (Fm).V,
      φu x = Units.map ψ.toRingEquiv.toMulEquiv.toMonoidHom (νKf x) := fun x => rfl
  -- ===== Step 5: the compatibility of `Φ|_L'` with `eG` =====
  have hcompat_ΦeG : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k:=k) (NK.GlobalCFT.Place.ofFinite q)))
      (τ' : ↥(SSGRoute.decomp k A))
      (_hres : SSGRoute.res k K (τ' : Ω ≃ₐ[k] Ω) = (τ : K ≃ₐ[k] K))
      (z : Work.SSGRoute.localClosureAt k A hA) (hz : z ∈ L'),
      (Φ τ') z = ↑((eG τ) ⟨z, hL'K' hz⟩) := by
    intro τ τ' _hres z hz
    obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective
      (E := Work.SSGRoute.localClosureAt k A hA) (eG τ)
    have hg' : ∀ y : ↥K', g (y : Work.SSGRoute.localClosureAt k A hA)
        = ↑((eG τ) y) := by
      intro y
      have h := congrArg (fun e : ↥K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] ↥K' => e y) hg
      have h2 := congrArg (fun w : ↥K' => (w : Work.SSGRoute.localClosureAt k A hA)) h
      rw [AlgEquiv.restrictNormalHom_apply] at h2
      exact h2
    have hgen : ∀ w ∈ S, (Φ τ') w = g w := by
      rintro w ⟨y, rfl⟩
      dsimp only
      let y' : ↥K' := ⟨s (y : Ω), hL'K' (hS_le (hS_mem y))⟩
      have hy' : (ψ.symm (algebraMap K (q.adicCompletion K) y) : ↥K') = y' :=
        Subtype.ext (hψ y)
      have hxy : (τ' : Ω ≃ₐ[k] Ω) (y : Ω) = (τ : K ≃ₐ[k] K) y := by
        rw [show (τ' : Ω ≃ₐ[k] Ω) (y : Ω) = (SSGRoute.res k K (τ' : Ω ≃ₐ[k] Ω)) y from
          (AlgEquiv.restrictNormalHom_apply K τ' y).symm, _hres]
      calc (Φ τ') (s (y : Ω))
          = s ((τ' : Ω ≃ₐ[k] Ω) (y : Ω)) := hs_equiv τ' (y : Ω)
        _ = s ((τ : K ≃ₐ[k] K) y) := by rw [hxy]
        _ = ↑(ψ.symm (algebraMap K (q.adicCompletion K) ((τ : K ≃ₐ[k] K) y))) := (hψ _).symm
        _ = ↑((eG τ) (ψ.symm (algebraMap K (q.adicCompletion K) y))) := by
              rw [hpt, AlgEquiv.apply_symm_apply, NK.HassePrinciple.localAut_algebraMap]
        _ = ↑((eG τ) y') := by rw [hy']
        _ = g (y' : Work.SSGRoute.localClosureAt k A hA) := (hg' y').symm
        _ = g (s (y : Ω)) := rfl
    have hz' := eqOn_adjoin_of_eq S (Φ τ') g hgen z hz
    rw [hz']
    exact hg' ⟨z, hL'K' hz⟩
  -- ===== Step 6: the two properties of `φadd` =====
  let φlin : (Fm).V →ₗ[SSGRoute.PTExt.Coeff] Additive (Units (q.adicCompletion K)) :=
    { toFun := ⇑φadd
      map_add' := fun x y => φadd.map_add x y
      map_smul' := fun (n : SSGRoute.PTExt.Coeff) (x : (Fm).V) => by
        obtain ⟨z⟩ := n
        exact AddMonoidHom.map_zsmul φadd z x }
  have hint : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k:=k) (NK.GlobalCFT.Place.ofFinite q))),
      φlin.comp (((Rep.res (SSGRoute.PTExt.decompK (k:=k)
        (NK.GlobalCFT.Place.ofFinite q)).subtype Fm)).ρ τ)
        = ((SSGRoute.PTExt.localUnitsK (k:=k) (NK.GlobalCFT.Place.ofFinite q)).ρ τ).comp φlin := by
    intro τ
    apply LinearMap.ext
    intro x
    obtain ⟨τ', hτ'⟩ := exists_res_eq_of_mem_decompK k Ω K A hA q hAq τ
    have hx : ((Rep.res (SSGRoute.PTExt.decompK (k:=k)
        (NK.GlobalCFT.Place.ofFinite q)).subtype Fm)).ρ τ x
        = (Fm).ρ (SSGRoute.res k K (τ' : Ω ≃ₐ[k] Ω)) x := by
      show (Fm).ρ ((τ : K ≃ₐ[k] K)) x = (Fm).ρ (SSGRoute.res k K (τ' : Ω ≃ₐ[k] Ω)) x
      rw [← hτ']
    simp only [LinearMap.comp_apply]
    rw [hx]
    change φadd ((Fm).ρ (SSGRoute.res k K (τ' : Ω ≃ₐ[k] Ω)) x)
      = ((SSGRoute.PTExt.localUnitsK (k:=k) (NK.GlobalCFT.Place.ofFinite q)).ρ τ)
          (φadd x)
    apply Additive.ofMul.injective
    apply Units.ext
    have hL : ((Additive.toMul (φadd ((Fm).ρ (SSGRoute.res k K (τ' : Ω ≃ₐ[k] Ω)) x)) :
        (Units (q.adicCompletion K))) : q.adicCompletion K)
        = ψ (↑(νKf ((Fm).ρ (SSGRoute.res k K (τ' : Ω ≃ₐ[k] Ω)) x)) : ↥K') := by
      change (φu ((Fm).ρ (SSGRoute.res k K (τ' : Ω ≃ₐ[k] Ω)) x) : q.adicCompletion K)
        = ψ (↑(νKf ((Fm).ρ (SSGRoute.res k K (τ' : Ω ≃ₐ[k] Ω)) x)) : ↥K')
      rw [φu_eq, Units.coe_map]
      rfl
    have hR : ((Additive.toMul (((SSGRoute.PTExt.localUnitsK (k:=k)
        (NK.GlobalCFT.Place.ofFinite q)).ρ τ) (φadd x)) : (Units (q.adicCompletion K))) :
        q.adicCompletion K)
        = NK.HassePrinciple.localAutHom (NK.GlobalCFT.Place.ofFinite q) τ
            (ψ (↑(νKf x) : ↥K')) := by
      have hρu : ((SSGRoute.PTExt.localUnitsK (k:=k) (NK.GlobalCFT.Place.ofFinite q)).ρ τ
          (φadd x))
          = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K)
              (NK.GlobalCFT.Place.ofFinite q) τ (φu x)) := by
        first
          | rfl
          | (simp only [SSGRoute.PTExt.localUnitsK, NK.HassePrinciple.localUnitsRep,
              Rep.ofDistribMulAction_ρ_apply_apply]
             rfl)
      rw [hρu]
      change (↑(NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K)
          (NK.GlobalCFT.Place.ofFinite q) τ (φu x)) : q.adicCompletion K)
        = NK.HassePrinciple.localAutHom (NK.GlobalCFT.Place.ofFinite q) τ
            (ψ (↑(νKf x) : ↥K'))
      rw [NK.HassePrinciple.coe_localUnitsEquiv, φu_eq x, Units.coe_map]
      rfl
    have hval : (↑(νKf ((Fm).ρ (SSGRoute.res k K (τ' : Ω ≃ₐ[k] Ω)) x)) : ↥K')
        = (eG τ) (↑(νKf x) : ↥K') := by
      apply Subtype.ext
      rw [hνKf_val]
      have e4 : (↑(νKf x) : ↥K')
          = ⟨(νu x : Work.SSGRoute.localClosureAt k A hA), hL'K' (hL'_mem x)⟩ :=
        Subtype.ext (hνKf_val x)
      rw [e4, ← hcompat_ΦeG τ τ' hτ' (νu x) (hL'_mem x)]
      exact ν_equiv τ' x
    exact hL.trans ((congrArg ψ hval).trans (by
      rw [hpt, AlgEquiv.apply_symm_apply]
      exact hR.symm))

  refine ⟨Rep.ofHom { toLinearMap := φlin, isIntertwining' := hint }, ?_⟩
  · intro r
    have e5 : ((φu ((Work.SSGRoute.ExtChain.E1cGeneric.kappa (k:=k) (Ω:=Ω) (K:=K) R) r) :
        (q.adicCompletion K)ˣ) : q.adicCompletion K)
        = ψ (↑(νKf ((Work.SSGRoute.ExtChain.E1cGeneric.kappa (k:=k) (Ω:=Ω) (K:=K) R) r)) :
            ↥K') := by
      rw [φu_eq, Units.coe_map]
      rfl
    have hν : (↑(νKf ((Work.SSGRoute.ExtChain.E1cGeneric.kappa (k:=k) (Ω:=Ω) (K:=K) R) r)) :
        ↥K') = ψ.symm (algebraMap K (q.adicCompletion K)
          ((Additive.toMul (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ w) r) : Kˣ) : K)) := by
      have hν' : (νu ((Work.SSGRoute.ExtChain.E1cGeneric.kappa (k:=k) (Ω:=Ω) (K:=K) R) r) :
          Work.SSGRoute.localClosureAt k A hA)
          = s ((Additive.toMul (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ w) r) : Kˣ) : K) := by
        rw [νu_coe]
        rw [show (Ψa ((Work.SSGRoute.ExtChain.E1cGeneric.kappa (k:=k) (Ω:=Ω) (K:=K) R) r))
            = (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k:=k) (Ω:=Ω) (K:=K)
                (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k:=k) (Ω:=Ω) (K:=K) R) w).1 r
            from hΨ r]
        rw [Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap_apply_toCoindH0]
        rw [Work.SSGRoute.toCoindH0_apply]
        rw [toMul_ofMul]
        rw [Units.coe_map]
        rfl
      apply Subtype.ext
      rw [hνKf_val]
      rw [hψ ((Additive.toMul (Rep.Hom.hom
        (CategoryTheory.Abelian.Ext.addEquiv₀ w) r) : Kˣ) : K)]
      exact hν'
    have key : (φu ((Work.SSGRoute.ExtChain.E1cGeneric.kappa (k:=k) (Ω:=Ω) (K:=K) R) r) :
        q.adicCompletion K)
        = algebraMap K (q.adicCompletion K)
            ((Additive.toMul (Rep.Hom.hom
              (CategoryTheory.Abelian.Ext.addEquiv₀ w) r) : Kˣ) : K) := by
      rw [e5, hν, AlgEquiv.apply_symm_apply]
    exact congrArg Additive.ofMul (Units.ext key)


/-! ## 2. The cochain-level extension clause -/

/-- **The cochain-level extension clause of the finite-place crux.**

Let `R` be a representation with `ℤ`-finitely-generated carrier, `w ∈ Ext⁰_G(R₁, Kˣ)` where
`R₁ = ker (freeCover R)`, and let `D ≤ Gal(Ω/k)` be a subgroup.  If the restriction to `D` of the
`E1c`-dictionary value `e1cMap R (PhiE R w)` vanishes, then the `H⁰`-element `ΨE(w)|_D` lifts along
the canonical cover `π : Hom_ℤ(F, Ωˣ) → Hom_ℤ(R₁, Ωˣ)`, i.e. `ΨE(w)|_D` extends to a `D`-equivariant
map `F → Ωˣ`.

This is `E1aClean.exists_invariant_extension_of_resH1_e1cMap_eq_zero` with the finiteness hypothesis
on the *carrier* of `R` removed (`Finite R.V` fails for the canonical syzygy `R = ker (freeCover N)`,
which is a lattice); the proof is the `β`-form of the dictionary together with the definition of
`betaH` through `liftOf`. -/
theorem extCochainExtensionNoFinite
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (D : Subgroup (Ω ≃ₐ[k] Ω))
    (w : CategoryTheory.Abelian.Ext.{0}
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R)
        (SSGRoute.PTExt.unitsK k K) 0) :
    Work.SSGRoute.PT.H2Fin.resH1 D (Work.SSGRoute.homCoind k Ω K R)
        (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap R
          (Work.SSGRoute.ExtChain.E1cGeneric.PhiE R w)) = 0 →
      ∃ Ψ : ↥(Work.AbsoluteKummer.H0 D (Work.SSGRoute.ExtChain.homCoindFreeT k Ω K R.V)),
        ∀ x : (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R).V,
          (Ψ : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K R.V)
              (Work.SSGRoute.ExtChain.E1cGeneric.kappa R x)
            = (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
                (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) w).1 x := by
  intro h
  classical
  haveI : Fintype (K ≃ₐ[k] K) := inferInstance
  -- The `E1c` value of the generator is `β⁻¹` of the `ΨE`-image; realise it by a cocycle.
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)).comap
      (Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)).subtype)
    (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap R
      (Work.SSGRoute.ExtChain.E1cGeneric.PhiE R w))
  have hres : Work.SSGRoute.PT.H2Fin.resH1 D (Work.SSGRoute.homCoind k Ω K R)
      ((QuotientAddGroup.mk'
        ((Work.AbsoluteKummer.B1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)).comap
          (Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω)
            (Work.SSGRoute.homCoind k Ω K R)).subtype)) c) = 0 := by
    rw [hc]; exact h
  -- The `β`-form of the class.
  have hbeta : (QuotientAddGroup.mk' (Work.SSGRoute.ExtChain.E1cGeneric.piH0 R).range)
      (Work.SSGRoute.ExtChain.E1cGeneric.betaRaw R c)
      = (QuotientAddGroup.mk' (Work.SSGRoute.ExtChain.E1cGeneric.piH0 R).range)
          (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) w) := by
    have h1 := Work.SSGRoute.ExtChain.E1cGeneric.betaH_mk R c
    rw [hc, Work.SSGRoute.ExtChain.E1cGeneric.e1cMap_Phi] at h1
    rw [← Work.SSGRoute.ExtChain.E1cGeneric.betaEquiv_apply] at h1
    rw [AddEquiv.apply_symm_apply] at h1
    exact h1.symm
  -- Hence `betaRaw c - ΨE(w) = π(f)` for a `Γ`-invariant `f`.
  have hmem : Work.SSGRoute.ExtChain.E1cGeneric.betaRaw R c
      - Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) w
      ∈ (Work.SSGRoute.ExtChain.E1cGeneric.piH0 R).range := by
    have h0 : (QuotientAddGroup.mk' (Work.SSGRoute.ExtChain.E1cGeneric.piH0 R).range)
        (Work.SSGRoute.ExtChain.E1cGeneric.betaRaw R c
          - Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
              (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) w) = 0 := by
      rw [map_sub, hbeta, sub_self]
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at h0
    exact h0
  obtain ⟨f, hf⟩ := hmem
  -- The cocycle `c` is a coboundary on `D`.
  have hcB : ((Work.SSGRoute.PT.H2Fin.resZ1 D (Work.SSGRoute.homCoind k Ω K R) c :
      ↥D → Work.SSGRoute.homCoind k Ω K R)
      ∈ Work.AbsoluteKummer.B1 (↥D) (Work.SSGRoute.homCoind k Ω K R)) := by
    have h1 : Work.AbsoluteKummer.H1π (↥D) (Work.SSGRoute.homCoind k Ω K R)
        (Work.SSGRoute.PT.H2Fin.resZ1 D (Work.SSGRoute.homCoind k Ω K R) c) = 0 := by
      rw [← Work.SSGRoute.PT.H2Fin.resH1_H1π D (Work.SSGRoute.homCoind k Ω K R) c]
      exact hres
    exact (Work.AbsoluteKummer.H1π_eq_zero_iff _).mp h1
  obtain ⟨m, hm⟩ := (Work.AbsoluteKummer.mem_B1_iff
    ((Work.SSGRoute.PT.H2Fin.resZ1 D (Work.SSGRoute.homCoind k Ω K R) c :
      ↥D → Work.SSGRoute.homCoind k Ω K R))).mp hcB
  -- The adjustment `liftOf c - iotaH m` is `D`-invariant.
  have hd0 : (Work.GroupCohomology.d0 (↥D) (Work.SSGRoute.ExtChain.E1cGeneric.E1cN R))
      (Work.SSGRoute.ExtChain.E1cGeneric.liftOf R c
        - Work.SSGRoute.ExtChain.E1cGeneric.iotaH R m) = 0 := by
    have h1 : (Work.GroupCohomology.d0 (↥D) (Work.SSGRoute.ExtChain.E1cGeneric.E1cN R))
        (Work.SSGRoute.ExtChain.E1cGeneric.liftOf R c)
        = fun δ : ↥D => (Work.SSGRoute.ExtChain.E1cGeneric.iotaH R)
            ((c : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K R)
              (δ : Ω ≃ₐ[k] Ω)) := by
      funext δ
      rw [show (Work.GroupCohomology.d0 (↥D)
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cN R))
            (Work.SSGRoute.ExtChain.E1cGeneric.liftOf R c) δ
          = (Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω)
              (Work.SSGRoute.ExtChain.E1cGeneric.E1cN R))
              (Work.SSGRoute.ExtChain.E1cGeneric.liftOf R c)
              (δ : Ω ≃ₐ[k] Ω) from rfl]
      rw [congrFun (Work.SSGRoute.ExtChain.E1cGeneric.liftOf_spec R c)
        (δ : Ω ≃ₐ[k] Ω), Work.AbsoluteKummer.mapZ1_apply]
    have h2 : (Work.GroupCohomology.d0 (↥D) (Work.SSGRoute.ExtChain.E1cGeneric.E1cN R))
        (Work.SSGRoute.ExtChain.E1cGeneric.iotaH R m)
        = fun δ : ↥D => (Work.SSGRoute.ExtChain.E1cGeneric.iotaH R)
            ((c : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K R)
              (δ : Ω ≃ₐ[k] Ω)) := by
      funext δ
      rw [Work.GroupCohomology.d0_apply, Subgroup.smul_def]
      have heq := (Work.SSGRoute.ExtChain.E1cGeneric.iotaH_equivariant R
        (δ : Ω ≃ₐ[k] Ω) m).symm
      rw [heq, ← map_sub]
      congr 1
      rw [show (δ : Ω ≃ₐ[k] Ω) • m - m
          = (Work.GroupCohomology.d0 (↥D) (Work.SSGRoute.homCoind k Ω K R)) m δ from
        (Work.GroupCohomology.d0_apply _ _ _ _).symm]
      rw [congrFun hm δ]
      rfl
    rw [map_sub, h1, h2, sub_self]
  have hmem2 : (Work.SSGRoute.ExtChain.E1cGeneric.liftOf R c
      - Work.SSGRoute.ExtChain.E1cGeneric.iotaH R m)
      ∈ Work.AbsoluteKummer.H0 (↥D) (Work.SSGRoute.ExtChain.E1cGeneric.E1cN R) :=
    (Work.SSGRoute.ExtChain.E1cGeneric.d0_eq_zero_iff _).mp hd0
  -- The `Γ`-invariant `f` is `D`-invariant.
  have hmem3 : (f : Work.SSGRoute.ExtChain.E1cGeneric.E1cN R)
      ∈ Work.AbsoluteKummer.H0 (↥D) (Work.SSGRoute.ExtChain.E1cGeneric.E1cN R) := by
    rw [Work.GroupCohomology.mem_invariants]
    intro δ
    rw [Subgroup.smul_def]
    exact (Work.GroupCohomology.mem_invariants (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cN R)
      (f : Work.SSGRoute.ExtChain.E1cGeneric.E1cN R)).mp f.2 (δ : Ω ≃ₐ[k] Ω)
  have hB : (f : Work.SSGRoute.ExtChain.E1cGeneric.E1cN R)
      ∈ Work.AbsoluteKummer.H0 (↥D) (Work.SSGRoute.ExtChain.E1cGeneric.E1cN R) := hmem3
  let xA : ↥(Work.AbsoluteKummer.H0 (↥D) (Work.SSGRoute.ExtChain.E1cGeneric.E1cN R)) :=
    ⟨Work.SSGRoute.ExtChain.E1cGeneric.liftOf R c
      - Work.SSGRoute.ExtChain.E1cGeneric.iotaH R m, hmem2⟩
  let xB : ↥(Work.AbsoluteKummer.H0 (↥D) (Work.SSGRoute.ExtChain.E1cGeneric.E1cN R)) :=
    ⟨(f : Work.SSGRoute.ExtChain.E1cGeneric.E1cN R), hB⟩
  refine ⟨xA - xB, ?_⟩
  intro x
  -- Evaluate both sides through `π` on the syzygy.
  have hπ : (Work.SSGRoute.ExtChain.E1cGeneric.piH R)
      ((Work.SSGRoute.ExtChain.E1cGeneric.liftOf R c
        - Work.SSGRoute.ExtChain.E1cGeneric.iotaH R m)
        - (f : Work.SSGRoute.ExtChain.E1cGeneric.E1cN R))
      = (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) w).1 := by
    have hpif : (Work.SSGRoute.ExtChain.E1cGeneric.piH R)
        (f : Work.SSGRoute.ExtChain.E1cGeneric.E1cN R)
        = ((Work.SSGRoute.ExtChain.E1cGeneric.piH0 R) f).1 := rfl
    have hfv : ((Work.SSGRoute.ExtChain.E1cGeneric.piH0 R) f).1
        = (Work.SSGRoute.ExtChain.E1cGeneric.betaRaw R c).1
          - (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
              (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) w).1 := by
      rw [hf, AddSubgroup.coe_sub]
    have hL : (Work.SSGRoute.ExtChain.E1cGeneric.piH R)
        (Work.SSGRoute.ExtChain.E1cGeneric.liftOf R c)
        = (Work.SSGRoute.ExtChain.E1cGeneric.betaRaw R c).1 := rfl
    rw [map_sub, map_sub, Work.SSGRoute.ExtChain.E1cGeneric.piH_iotaH, sub_zero, hL, hpif, hfv,
      sub_sub_cancel]
  have hcoe2 : ((xA - xB : ↥(Work.AbsoluteKummer.H0 (↥D)
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cN R))) :
        Work.SSGRoute.ExtChain.E1cGeneric.E1cN R)
      = (Work.SSGRoute.ExtChain.E1cGeneric.liftOf R c
        - Work.SSGRoute.ExtChain.E1cGeneric.iotaH R m)
        - (f : Work.SSGRoute.ExtChain.E1cGeneric.E1cN R) := rfl
  have hpi : ((Work.SSGRoute.ExtChain.E1cGeneric.liftOf R c
        - Work.SSGRoute.ExtChain.E1cGeneric.iotaH R m)
        - (f : Work.SSGRoute.ExtChain.E1cGeneric.E1cN R))
        (Work.SSGRoute.ExtChain.E1cGeneric.kappa R x)
      = ((Work.SSGRoute.ExtChain.E1cGeneric.piH R)
          ((Work.SSGRoute.ExtChain.E1cGeneric.liftOf R c
            - Work.SSGRoute.ExtChain.E1cGeneric.iotaH R m)
            - (f : Work.SSGRoute.ExtChain.E1cGeneric.E1cN R))) x := by
    rw [Work.SSGRoute.ExtChain.E1cGeneric.piH_apply]
    rfl
  rw [hcoe2, hpi, hπ]


/-! ## 3. The statement of the extension step in its original (finite-`R.V`) form -/

/-- The `E1c`-dictionary restriction hypothesis implies the existence of a `D`-invariant extension
of `ΨE(w)` along the canonical cover; the finiteness hypothesis on `R.V` is *not* needed and is
recorded here only for compatibility with earlier consumers. -/
theorem exists_invariant_extension_of_resH1_e1cMap_eq_zero
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite R.V] [Module.Finite ℤ R.V]
    (D : Subgroup (Ω ≃ₐ[k] Ω))
    (w : CategoryTheory.Abelian.Ext.{0}
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k:=k) (Ω:=Ω) (K:=K) R)
        (SSGRoute.PTExt.unitsK k K) 0) :
    Work.SSGRoute.PT.H2Fin.resH1 D (Work.SSGRoute.homCoind k Ω K R)
        (Work.SSGRoute.ExtChain.e1cMap (k:=k) (Ω:=Ω) (K:=K) R
          (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k:=k) (Ω:=Ω) (K:=K) R w)) = 0 →
      ∃ Ψ : ↥(Work.AbsoluteKummer.H0 D
          (Work.SSGRoute.ExtChain.homCoindFreeT k Ω K R.V)),
        ∀ x : (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k:=k) (Ω:=Ω) (K:=K) R).V,
          (Ψ : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K R.V)
              (Work.SSGRoute.ExtChain.E1cGeneric.kappa (k:=k) (Ω:=Ω) (K:=K) R x)
            = (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k:=k) (Ω:=Ω) (K:=K)
                (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k:=k) (Ω:=Ω) (K:=K) R) w).1 x :=
  extCochainExtensionNoFinite k Ω K R D w

/-! ## 4. The finite-place local criterion -/

/-- **Finite-place local criterion of the E1a landing clause.**  For a finite place `A` of `Ω` over `k` with prime `q` of `K` (lying-over condition `hAq`) and a class `z : Ext¹_{Gal(K/k)}(ker (freeCover N), Kˣ)`: the vanishing of the restriction to the decomposition group `D_A = decomp k A` of the `E1c`-dictionary value `e1cEquiv z` implies that the localised class `(extRes_{D_q} z) ∘ mk₀ (unitsToLocalUnits)` vanishes.  This is the true per-place direction of the finite-place comparison square (the converse is refuted on disk), and the sole missing link between `SSGStage.resH1_e1cEquiv_eq_zero_of_akRes_e1aChainC_eq_zero` and the brick `SSGStage.extLoc_extToIdeles_e1aSyzShift_eq_zero`. -/
theorem finLocalCriterion
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    [hfin : Module.Finite ℤ ↑(CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)).V]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (z : CategoryTheory.Abelian.Ext.{0}
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))
        (SSGRoute.PTExt.unitsK k K) 1) :
    Work.SSGRoute.PT.H2Fin.resH1 (SSGRoute.decomp k A)
        (Work.SSGRoute.homCoind k Ω K
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
        (Work.SSGRoute.ExtChain.e1cEquiv
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z) = 0 →
      (SSGRoute.PTExt.extRes
          (SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofFinite q)).subtype z).comp
        (CategoryTheory.Abelian.Ext.mk₀
          (NK.HassePrinciple.unitsToLocalUnits k K (NK.GlobalCFT.Place.ofFinite q)))
        (add_zero 1) = 0 := by
  intro h
  obtain ⟨w, hw⟩ := Work.SSGRoute.ExtChain.E1cGeneric.PhiE_surjective
    (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z
  have h' : Work.SSGRoute.PT.H2Fin.resH1 (SSGRoute.decomp k A)
      (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
      (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))
        (Work.SSGRoute.ExtChain.E1cGeneric.PhiE
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) w)) = 0 := by
    rw [hw]
    exact h
  obtain ⟨Ψ, hΨ⟩ := extCochainExtensionNoFinite k Ω K
    (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) (SSGRoute.decomp k A) w h'
  obtain ⟨φ, hφ⟩ := localExtensionExistsNoFinite k Ω K A hA q hAq
    (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) w Ψ hΨ
  have hφ' := Work.SSGRoute.E1aClean.extResCompOfExtension k Ω K N
    (NK.GlobalCFT.Place.ofFinite q) w φ hφ
  rw [← hw]
  exact hφ'


end

end Work.SSGRoute.E1aClean
