import Mathlib
import Submission.Work.SSGcrux.noninvariantLevelDatum
import Submission.Work.SSGRoute.PTdualControl.C6_of_rankOneBrick
import Submission.Work.SSGRoute.PTdualControl.C6_rankOneBrick
import Submission.Work.SSGRoute.Sha2Lib.detectorInvariantCaseExtZ
import Submission.Work.E7cOmega.subsingleton_ext_one_ratRep
import Submission.Work.Sha2Lib.rankOneBrickWork
import Submission.Work.Sha2Lib.rankOneLevelCocycleRoute
import Submission.Work.E7cOmega.functional_of_ext_nonzero
import Submission.Work.SSGRoute.E7cOmega.ratDivSES
import Submission.Work.SSGRoute.SSGStage.extRatRep_vanish
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The rank-one brick of `C6` from the non-invariant datum

`Work.SSGcrux.noninvariantLevelDatum` (proved: it consumes the concentrated level data of
`Work.SSGcrux.concentratedLevelData`, itself proved) gives the level-cocycle datum for every nonzero
`D_w`-equivariant functional `μ` on the coinduced permutation module `coind_N^Γ 𝔽_p` which kills the
constant vector.

This file closes the `C6` leaf from it, by the case split that is independent of the arithmetic:

* `μ (const 1) = 0` — the datum of `Work.SSGcrux.noninvariantLevelDatum`, turned into the detector by
  the proved `PTdualControl.detectsAt_of_levelCocycleDatum`;
* `μ (const 1) ≠ 0` — the arithmetic-free invariant case
  `Sha2Lib.detectorInvariantCaseExtZ`, whose Ext-level hypothesis `(mk₀ (resMap ι)).comp φ ≠ 0` is
  derived from `μ (const 1) ≠ 0` by the connecting-map injectivity
  `ext_of_comp_extClass_eq_zero` below (the coefficient sequence `0 → ℤ → ℚ → ℚ/ℤ → 0` has
  `Ext⁰(·, ℚ) = Hom(·,ℚ) = 0` on `p`-torsion coefficients).

Then `Sha2Lib.rankOne_isUnramifiedDetector_of_coind` passes from the coinduced model to the induced
one, giving `PTdualControl.RankOneBrick`, and `PTdualControl.unramifiedDetector_of_rankOneBrick`
gives the leaf `Sha2Lib.unramifiedDetector` in its exact spelling.
-/

open CategoryTheory SSGRoute.PTExt

namespace Work.SSGcrux

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **The connecting map `δ = (· ≫ extClass)` of `0 → ℤ → ℚ → ℚ/ℤ → 0` is injective on a
`p`-torsion coefficient module.**  Proof: `ker δ = im(Ext⁰(A, ℚ) → Ext⁰(A, ℚ/ℤ))` by exactness of
the covariant sequence, and `Ext⁰(A, ℚ) = Hom(A, ℚ) = 0`
(`SSGStage.subsingleton_ext_zero_ratRep`). -/
theorem ext_of_comp_extClass_eq_zero {D : Type} [Group D] (p : ℕ) [Fact p.Prime]
    (A : Rep.{0} Coeff D) (hA : ∀ a : A, p • a = 0)
    (ν : A ⟶ Work.SSGRoute.E7cOmega.divRep D)
    (h : (Abelian.Ext.mk₀ ν).comp
        (ShortComplex.ShortExact.extClass
          (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := D)))
        (zero_add 1) = 0) :
    ν = 0 := by
  obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₃ A
    (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := D))
    (Abelian.Ext.mk₀ ν) (zero_add 1) h
  haveI : Subsingleton (Abelian.Ext A (Work.SSGRoute.E7cOmega.ratDivSES (G := D)).X₂ 0) :=
    Work.SSGRoute.SSGStage.subsingleton_ext_zero_ratRep A hA
  have h0 : y = 0 := Subsingleton.elim y 0
  rw [h0, Abelian.Ext.zero_comp] at hy
  have h2 : Abelian.Ext.mk₀ ν
      = Abelian.Ext.mk₀ (0 : A ⟶ Work.SSGRoute.E7cOmega.divRep D) := by
    rw [Abelian.Ext.mk₀_zero]
    exact hy.symm
  exact (Abelian.Ext.mk₀_bijective A (Work.SSGRoute.E7cOmega.divRep D)).1 h2

variable (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
  [Algebra k K] [FiniteDimensional k K] [IsGalois k K]

/-- The constant function `1` of the coinduced permutation module. -/
noncomputable def constCoind (N : Subgroup (K ≃ₐ[k] K)) :
    (Work.SSGRoute.PTdualControl.coindModule p k K N).V :=
  ⟨fun _ => 1, fun _ _ => rfl⟩

/-- The constant function with value `a` of the coinduced permutation module. -/
noncomputable def constElem (N : Subgroup (K ≃ₐ[k] K)) (a : ZMod p) :
    (Work.SSGRoute.PTdualControl.coindModule p k K N).V :=
  ⟨fun _ => a, fun _ _ => rfl⟩

/-- The constant vectors of the coinduced permutation module are `Γ`-fixed. -/
theorem constElem_mem_fixed (N : Subgroup (K ≃ₐ[k] K)) (σ : K ≃ₐ[k] K) (a : ZMod p) :
    (Work.SSGRoute.PTdualControl.coindModule p k K N).ρ σ (constElem p k K N a)
      = constElem p k K N a := by
  apply Subtype.ext
  funext g
  rw [Work.Sha2Lib.coind_subtype_ρ_apply]
  rfl

/-- The constant map `𝔽_p ⟶ coind_N^Γ 𝔽_p` (a morphism of trivial `Γ`-modules). -/
noncomputable def constToCoind (N : Subgroup (K ≃ₐ[k] K)) :
    Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ Work.SSGRoute.PTdualControl.coindModule p k K N :=
  Rep.ofHom
    { toLinearMap :=
        { toFun := fun a => constElem p k K N a
          map_add' := fun a b => by
            apply Subtype.ext
            funext g
            rfl
          map_smul' := fun c a => by
            apply Subtype.ext
            funext g
            rfl }
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro a
        exact (constElem_mem_fixed p k K N σ a).symm }

theorem constCoind_mem_fixed (N : Subgroup (K ≃ₐ[k] K)) (σ : K ≃ₐ[k] K) :
    (Work.SSGRoute.PTdualControl.coindModule p k K N).ρ σ (constCoind p k K N) =
      constCoind p k K N := by
  apply Subtype.ext
  funext g
  rw [Work.Sha2Lib.coind_subtype_ρ_apply]
  rfl

theorem constToCoind_apply_one (N : Subgroup (K ≃ₐ[k] K)) :
    (constToCoind p k K N).hom 1 = constCoind p k K N := rfl

/-- **The detector for the coinduced permutation module.** -/
theorem detectsAt_coind (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower k K Ω] (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (hNζ : ∀ σ ∈ N, σ ζ = ζ)
    (φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
        (Work.SSGRoute.PTdualControl.coindModule p k K N))
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1)
    (hφ : φ ≠ 0) :
    Work.SSGRoute.Sha2Lib.DetectsAt p k K Ω w q hwq
      (Work.SSGRoute.PTdualControl.coindModule p k K N) φ := by
  classical
  haveI hfin : Finite (Work.SSGRoute.PTdualControl.coindModule p k K N) :=
    Work.Sha2Lib.coindPerm_finite p k K N
  have hM : ∀ m : (Work.SSGRoute.PTdualControl.coindModule p k K N).V, p • m = 0 :=
    Work.Sha2Lib.coindPerm_psmul p k K N
  obtain ⟨μ, hμ, hφμ⟩ :=
    Work.E7cOmega.functional_of_ext_nonzero p k K
      (Work.SSGRoute.PTdualControl.coindModule p k K N) hM w φ hφ
  by_cases hc : μ.hom (constCoind p k K N) = 0
  · -- non-invariant branch: the level-cocycle datum
    have hdat : Work.SSGRoute.PTdualControl.LevelCocycleDatum p k K Ω w q hwq
        (Work.SSGRoute.PTdualControl.coindModule p k K N) μ :=
      Work.SSGcrux.noninvariantLevelDatum p k K Ω w q hwq hpq N hNI ζ hζ hNζ μ hμ hc
    have hdet := Work.SSGRoute.PTdualControl.detectsAt_of_levelCocycleDatum p k K Ω w q hwq
      (Work.SSGRoute.PTdualControl.coindModule p k K N) hM μ hdat
    rw [hφμ]
    exact hdet
  · -- invariant branch: the arithmetic-free case, via a fixed constant vector
    have hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ →
        ∀ m : (Work.SSGRoute.PTdualControl.coindModule p k K N).V,
          (Work.SSGRoute.PTdualControl.coindModule p k K N).ρ σ m = m :=
      fun σ hσ m =>
        Work.SSGRoute.PTdualControl.coindModule_inertia (p := p) (k := k) (K := K) N q hNI σ hσ m
    -- the constant map is nontrivial on the constant vector
    have hν : (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
        (constToCoind p k K N)) ≫ μ ≠ 0 := by
      intro h0
      apply hc
      have h2 : ((Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
          (constToCoind p k K N)) ≫ μ).hom 1 = 0 := by
        rw [h0, Rep.zero_hom]
        rfl
      rw [Rep.hom_comp, Representation.IntertwiningMap.comp_apply] at h2
      have h3 : (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
          (constToCoind p k K N)).hom
            (1 : (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
              (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))).V) = constCoind p k K N := by
        rw [Rep.resMap_hom_apply]
        exact constToCoind_apply_one p k K N
      rwa [h3] at h2
    have hφι : (CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
          (constToCoind p k K N))).comp φ (zero_add 1) ≠ 0 := by
      rw [hφμ]
      rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc]
      intro h0
      exact hν (ext_of_comp_extClass_eq_zero p
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
          (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)))
        (fun a => by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]) _ h0)
    exact Work.SSGRoute.Sha2Lib.detectorInvariantCaseExtZ p k K
      (Work.SSGRoute.PTdualControl.coindModule p k K N) Ω hM w q hwq hpq hI
      (constCoind p k K N) (constCoind_mem_fixed p k K N) φ hφ
      ⟨constToCoind p k K N, constToCoind_apply_one p k K N, hφι⟩

/-- **The rank-one brick of `C6`** — the detector for the permutation module `Ind_N^Γ 𝔽_p`. -/
theorem rankOneBrick_ssg (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] :
    Work.SSGRoute.PTdualControl.RankOneBrick p k Ω := by
  intro K' _ _ _ _ _ _ _ w q hwq hpq N _ hNI ζ hζ hNζ
  exact Work.Sha2Lib.rankOne_isUnramifiedDetector_of_coind p k K' Ω w q hwq N _
    (fun φ hφ => detectsAt_coind p k K' Ω w q hwq hpq N hNI ζ hζ hNζ φ hφ)

end Work.SSGcrux
