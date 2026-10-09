import Mathlib
import Submission.Work.SSGRoute.E1aClean.ArchSeam
import Submission.Work.SSGRoute.PT.e1cDelta_beta_relation_gen
import Submission.Work.SSGRoute.ExtChain.deltaH2_restriction
import Submission.Work.SSGRoute.PTdualControl.archimedeanLambda_injective_exists
import Submission.Work.SSGRoute.PTdualControl.archimedeanCruxA
import Submission.Work.SSGRoute.PTdualControl.archimedeanLocalPush
import Submission.Work.SSGRoute.PTdualControl.exists_invariant_extension_of_resH1_e1cMap_eq_zero_inf
import Submission.Work.SSGRoute.E1aClean.extResCompOfExtension
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **The archimedean local push of an invariant primitive, with the seam embedding made explicit.**

Let `K/k` be a finite Galois extension inside `Ω = k̄`, `w` an infinite place of `K` with nontrivial
decomposition group `D = D_w ≤ Gal(K/k)`, `σ ∈ Gal(Ω/k)` an involution with
`D_w ≤ (⟨σ⟩).map (res k K)`, and `φ : Ω →+* ℂ` a complex embedding extending `w.embedding` (`hφK`)
and intertwining `σ` with complex conjugation (`hlink`).  For a `ℤ`-lattice `R` with
`Gal(K/k)`-action, a `⟨σ⟩`-invariant lift `Φ` of the `E1c`-datum `(ΨE y)|_κ` pushes along the seam
to a `D_w`-equivariant lift `Φ₁ : Res_{D_w} F ⟶ K_wˣ` of `unitsToLocalUnits ∘ addEquiv₀ y`.

This is `Work.SSGRoute.PTdualControl.archimedeanLocalPush` (where `φ` is fixed to
`ComplexEmbedding.lift Ω w.embedding`) with an arbitrary seam `φ`; the proof is the same, the only
uses of the seam being `hφK` (for the `κ`-relation) and `hlink` (for the equivariance, via
`linkedSeamUnitsMap` / `localActionC`). -/
theorem localPushOfSeam
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (w : NumberField.InfinitePlace ↥K) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1)
    (φ : Ω →+* ℂ)
    (hφK : ∀ y : ↥K, φ (algebraMap ↥K Ω y) = NumberField.InfinitePlace.embedding w y)
    (hlink : ∀ x : Ω, φ (σ x) = starRingEnd ℂ (φ x))
    (hle : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) ≤
      (Subgroup.zpowers σ).map (SSGRoute.res k K))
    (hbot : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) ≠ ⊥)
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (y : CategoryTheory.Abelian.Ext
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) (SSGRoute.PTExt.unitsK k K) 0)
    (Φ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) R)
    (hΦ : Φ ∈ Work.AbsoluteKummer.H0 ↥(Subgroup.zpowers σ)
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) R))
    (hκ : Φ.comp (Work.SSGRoute.ExtChain.E1cGeneric.kappa R)
      = (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) R) y).1) :
    ∃ Φ₁ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := ↥K)
          (NK.GlobalCFT.Place.ofInfinite w)).subtype
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) R)
        ⟶ SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofInfinite w),
      ∀ x : (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
          (k := k) (Ω := Ω) (K := K) R).V,
        Rep.Hom.hom Φ₁ (Work.SSGRoute.ExtChain.E1cGeneric.kappa R x)
        = Rep.Hom.hom
            (NK.HassePrinciple.unitsToLocalUnits k ↥K (NK.GlobalCFT.Place.ofInfinite w))
            (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ y) x) := by
  classical
  have hw : w.IsComplex :=
    Work.SSGRoute.PTdualControl.isComplex_of_decompK_ofInfinite_ne_bot_aux (k := k) (K := K) w hbot
  set e : w.Completion ≃+* ℂ :=
    NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw with he
  have heK : ∀ c : ↥K, e (algebraMap ↥K w.Completion c) = w.embedding c := by
    intro c
    rw [he, NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
    simp
  have hlink' : ∀ x : Ω, φ (σ x) = starRingEnd ℂ (φ x) := hlink
  -- the computation rule of the `H0`-instance (the conjugation action on `homCoind`)
  have hlawAll : ∀ (σ' : Ω ≃ₐ[k] Ω) (hσ'mem : σ' ∈ Subgroup.zpowers σ)
      (v : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) R).V),
      σ' • (Φ ((Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) R).ρ
        (SSGRoute.res k K σ')⁻¹ v)) = Φ v := by
    intro σ' hσ'mem v
    exact congrArg (fun f : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) R =>
      f v) ((Work.GroupCohomology.mem_invariants (↥(Subgroup.zpowers σ))
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) R) Φ).mp hΦ
        ⟨σ', hσ'mem⟩)
  -- the units maps along the seam and the local identification
  set ψU : Ωˣ →* ℂˣ := Units.map φ.toMonoidHom with hψU
  set eU : (w.Completion)ˣ ≃* ℂˣ := Units.mapEquiv e.toMulEquiv with heU
  have heU_alg : ∀ u : (↥K)ˣ,
      eU (Units.map (algebraMap ↥K w.Completion) u) = Units.map w.embedding u := by
    intro u
    rw [heU]
    ext
    simp only [Units.coe_mapEquiv, Units.coe_map, RingEquiv.coe_toMulEquiv]
    exact heK (u : ↥K)
  -- the pushed additive map
  let toLoc : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) R).V
      →+ Additive (w.Completion)ˣ :=
    { toFun := fun v => Additive.ofMul (eU.symm (ψU (Additive.toMul (Φ v))))
      map_zero' := by
        show Additive.ofMul (eU.symm (ψU (Additive.toMul (Φ 0)))) = 0
        rw [map_zero, toMul_zero, map_one, map_one, ofMul_one]
      map_add' := fun a b => by
        show Additive.ofMul (eU.symm (ψU (Additive.toMul (Φ (a + b)))))
          = Additive.ofMul (eU.symm (ψU (Additive.toMul (Φ a))))
            + Additive.ofMul (eU.symm (ψU (Additive.toMul (Φ b))))
        rw [map_add, toMul_add, map_mul, map_mul, ofMul_mul] }
  have htoLoc : ∀ v : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) R).V,
      toLoc v = Additive.ofMul (eU.symm (ψU (Additive.toMul (Φ v)))) := fun v => rfl
  have htoMul_toLoc : ∀ v : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω)
      (K := K) R).V,
      Additive.toMul (toLoc v) = eU.symm (ψU (Additive.toMul (Φ v))) := fun v => rfl
  -- the `D_w`-equivariance of the pushed map
  have hInter : ∀ (γ : ↥(SSGRoute.PTExt.decompK (k := k) (K := ↥K)
        (NK.GlobalCFT.Place.ofInfinite w)))
      (v : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) R).V),
      toLoc ((Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) R).ρ
          (γ : ↥K ≃ₐ[k] ↥K) v)
        = (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
            (NK.GlobalCFT.Place.ofInfinite w)).ρ γ (toLoc v) := by
    intro γ v
    obtain ⟨σ', hσ'mem, hσ'res⟩ := Subgroup.mem_map.mp (hle γ.2)
    rcases Work.SSGRoute.PTdualControl.zpowers_involution_eq σ hσ hσ'mem with h1 | hσ'eq
    · -- the trivial element of `D_w`
      have hγ1 : (γ : ↥K ≃ₐ[k] ↥K) = 1 := by rw [← hσ'res, h1, map_one]
      have hγ1' : γ = 1 := Subtype.ext hγ1
      rw [hγ1']
      simp only [Subgroup.coe_one]
      have hF : ((Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) R).ρ
          (1 : ↥K ≃ₐ[k] ↥K)) = 1 := map_one _
      have hM : ((SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
          (NK.GlobalCFT.Place.ofInfinite w)).ρ
          (1 : ↥(SSGRoute.PTExt.decompK (k := k) (K := ↥K)
            (NK.GlobalCFT.Place.ofInfinite w)))) = 1 := map_one _
      rw [hF, hM]
      rfl
    · -- the nontrivial element: the seam computes the local action
      have hγ : (γ : ↥K ≃ₐ[k] ↥K) = SSGRoute.res k K σ := by rw [← hσ'res, hσ'eq]
      have hres : (SSGRoute.res k K) σ = (γ : ↥K ≃ₐ[k] ↥K) := hγ.symm
      have hlaw : σ • (Φ v)
          = Φ ((Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) R).ρ
              (γ : ↥K ≃ₐ[k] ↥K) v) := by
        have h2 := hlawAll σ (Subgroup.mem_zpowers σ)
          ((Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) R).ρ
            (SSGRoute.res k K σ) v)
        rw [show (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) R).ρ
              (SSGRoute.res k K σ)⁻¹
              ((Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) R).ρ
                (SSGRoute.res k K σ) v) = v from by
            simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              Module.End.one_apply]] at h2
        rw [← hγ] at h2
        exact h2
      have key : eU (Additive.toMul (toLoc ((Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k)
            (Ω := Ω) (K := K) R).ρ (γ : ↥K ≃ₐ[k] ↥K) v)))
          = Units.map (localActionC K w hw γ).toMonoidHom
              (ψU (Additive.toMul (Φ v))) := by
        rw [htoMul_toLoc, MulEquiv.apply_symm_apply]
        have h3 : Additive.toMul (Φ ((Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω)
            (K := K) R).ρ (γ : ↥K ≃ₐ[k] ↥K) v))
            = Work.SSGRoute.algEquivUnitsMapΩ k Ω σ (Additive.toMul (Φ v)) := by
          rw [← hlaw]
          exact Work.SSGRoute.addUnits_smul_toMulΩ k Ω σ (Additive.toMul (Φ v))
        rw [h3]
        exact E1aClean.linkedSeamUnitsMap K w hw γ σ hres φ hφK hlink'
          (Additive.toMul (Φ v))
      have key2 : eU (Additive.toMul ((SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
            (NK.GlobalCFT.Place.ofInfinite w)).ρ γ (toLoc v)))
          = Units.map (localActionC K w hw γ).toMonoidHom
              (ψU (Additive.toMul (Φ v))) := by
        have h4 : ((SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
              (NK.GlobalCFT.Place.ofInfinite w)).ρ γ (toLoc v))
            = Additive.ofMul ((NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K)
                (NK.GlobalCFT.Place.ofInfinite w) γ) (Additive.toMul (toLoc v))) := rfl
        rw [h4, toMul_ofMul, htoMul_toLoc, heU, he]
        rw [Work.SSGRoute.PTdualControl.localUnitsEquiv_transport (k := k) (K := K) w hw γ
          ((Units.mapEquiv
            (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).toMulEquiv).symm
              (ψU (Additive.toMul (Φ v))))]
        rw [MulEquiv.apply_symm_apply]
      apply Additive.toMul.injective
      apply eU.injective
      rw [key, key2]
  let Φ₁ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := ↥K)
        (NK.GlobalCFT.Place.ofInfinite w)).subtype
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) R)
      ⟶ SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofInfinite w) :=
    Rep.ofHom
      { toFun := fun v => toLoc v
        map_add' := fun v w => toLoc.map_add v w
        map_smul' := fun n v => by
          obtain ⟨z⟩ := n
          exact AddMonoidHom.map_zsmul toLoc z v
        isIntertwining' := fun γ => LinearMap.ext (fun v => by
          simp only [LinearMap.comp_apply]
          exact hInter γ v) }
  refine ⟨Φ₁, ?_⟩
  intro x
  rw [show (Rep.Hom.hom Φ₁ :
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := ↥K)
          (NK.GlobalCFT.Place.ofInfinite w)).subtype
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) R)).V
        → (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
          (NK.GlobalCFT.Place.ofInfinite w)).V) = ⇑toLoc from rfl]
  set z : (SSGRoute.PTExt.unitsK k ↥K).V :=
    (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ y)) x with hz
  set u : (↥K)ˣ := Additive.toMul z with hu
  have hΦκ : Additive.toMul (Φ (Work.SSGRoute.ExtChain.E1cGeneric.kappa R x))
      = Units.map (algebraMap ↥K Ω).toMonoidWithZeroHom u := by
    have h := congrArg (fun f : (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R).V
        →+ Additive Ωˣ => f x) hκ
    rw [AddMonoidHom.comp_apply] at h
    rw [h, Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap_apply_toCoindH0,
      Work.SSGRoute.toCoindH0_apply, ← hz]
    exact toMul_ofMul _
  have hψ : ψU (Units.map (algebraMap ↥K Ω).toMonoidWithZeroHom u)
      = Units.map w.embedding u := by
    rw [hψU]
    ext
    simp only [Units.coe_map]
    exact hφK (u : ↥K)
  refine Additive.toMul.injective ?_
  rw [htoMul_toLoc, hΦκ, hψ]
  rw [show (Rep.Hom.hom (NK.HassePrinciple.unitsToLocalUnits k ↥K
        (NK.GlobalCFT.Place.ofInfinite w))) z
      = Additive.ofMul (NK.HassePrinciple.unitsToLocalUnitsHom
          (NK.GlobalCFT.Place.ofInfinite w) u)
      from rfl]
  rw [toMul_ofMul]
  rw [MulEquiv.symm_apply_eq]
  exact (heU_alg u).symm

/-- **The archimedean kill clause at a *linked* involution** (the seam-based archimedean crux).

Let `K/k` be finite Galois inside `Ω = k̄`, `w` an infinite place of `K`, `σ ∈ Gal(Ω/k)` an
involution whose image `σ̄ = res k K σ` generates the decomposition group `D_w`, and let
`φ : Ω →+* ℂ` be a complex embedding extending `w.embedding` which *intertwines* `σ` with complex
conjugation, `φ (σ x) = conj (φ x)` — the *seam* (`ArchSeam.linkedInvolution_exists` constructs
`(σ, φ)` from `w` and a non-trivial `τ ∈ D_w`; this link is the archimedean analogue of the
lying-over clause `hAq` of the finite-place crux `E1aClean.finLocalCriterion`).

Then, for any `N ∈ Rep Coeff Gal(K/k)` with `N.V` finite and `R = ker (freeCover N)` the canonical
syzygy, and any `z ∈ Ext¹_{Gal(K/k)}(R, Kˣ)` (`= H¹(Gal(Ω/k), Hom_ℤ(R,Ωˣ))` through the canonical
`E1c` dictionary `e1cMap`), the vanishing of the restriction of `e1cMap R z` to the involution
`⟨σ⟩` forces the localisation of `z` at `w` to vanish:

  `(extRes_{D_w} z) ∘ mk₀ (unitsToLocalUnits) = 0`.

This is exactly the body of `PTdualControl.ArchimedeanCruxA`, with the seam data supplied explicitly
by `(φ, hφK, hlink)` rather than through the canonical embedding
`ComplexEmbedding.lift Ω w.embedding`.  The link is what makes the coefficient change
`Ωˣ → K_wˣ = ℂˣ` induced by `φ` `⟨σ⟩`-equivariant for the local action at `w`, so that the
`⟨σ⟩`-invariant primitive produced by the exactness of the dualised canonical resolution pushes
down to a `D_w`-equivariant primitive in `K_wˣ`; without it the seam does not exist
(`ArchSeam`'s counterexamples).

Suggested route (all ingredients on disk except the final assembly):
`ExtChain.E1cGeneric.PhiE_surjective` to reduce `z = PhiE R w`;
`PT.exists_extension_of_resH1_e1cMap_PhiE_eq_zero` for the `⟨σ⟩`-invariant primitive `Φ` with
`Φ ∘ κ = (PsiEMap w).1`; then the *seam* push of `Φ` along `φ` (using `hφK`, `hlink` to get
`⟨σ⟩`-equivariance and `decompK_zpowers_iso` to identify `⟨σ⟩ ≅ D_w`), the local `δ`-rule
(`PT.e1cMap_PhiE_eq_delta_gen` at `(ℝ, ℂ, ⊤)`), the injectivity of the local `E1c` dictionary
(`E1cGeneric.e1cMap_injective`), and `SSGStage.extLoc_extToIdeles_eq`/`e1aShiftEquiv_extRes` to
conclude. -/
theorem archimedeanKillClauseLinked
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (w : NumberField.InfinitePlace ↥K) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1)
    (φ : Ω →+* ℂ)
    (hφK : ∀ y : ↥K, φ (algebraMap ↥K Ω y) = NumberField.InfinitePlace.embedding w y)
    (hlink : ∀ x : Ω, φ (σ x) = starRingEnd ℂ (φ x))
    (hle : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) ≤
      (Subgroup.zpowers σ).map (SSGRoute.res k K))
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    [Module.Finite ℤ ↑(CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)).V]
    (z : CategoryTheory.Abelian.Ext.{0}
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))
        (SSGRoute.PTExt.unitsK k K) 1)
    (h : Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers σ)
        (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
        (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z) = 0) :
    (SSGRoute.PTExt.extRes (SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofInfinite w)).subtype z).comp
      (CategoryTheory.Abelian.Ext.mk₀
        (NK.HassePrinciple.unitsToLocalUnits k ↥K (NK.GlobalCFT.Place.ofInfinite w)))
      (add_zero 1) = 0 := by
  classical
  by_cases hbot : SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofInfinite w) = ⊥
  · -- the decomposition group is trivial: the localised class vanishes unconditionally
    exact Work.SSGRoute.PTdualControl.extRes_comp_eq_zero_of_decompK_eq_bot
      (k := k) (Ω := Ω) K w N z hbot
  · -- main case: `D_w ≠ ⊥`
    haveI hFintypeG : Fintype (K ≃ₐ[k] K) := inferInstance
    haveI hFintypeD : Fintype ↥(SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofInfinite w)) := Fintype.ofFinite _
    -- write `z` as a `PhiE`-generator
    obtain ⟨y, hy⟩ := Work.SSGRoute.ExtChain.E1cGeneric.PhiE_surjective
      (k := k) (Ω := Ω) (K := K)
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z
    rw [← hy] at h ⊢
    -- the `⟨σ⟩`-invariant primitive over `Ωˣ`
    obtain ⟨Φ, hΦ, hκ⟩ :=
      Work.SSGRoute.PTdualControl.exists_invariant_extension_of_resH1_e1cMap_eq_zero_inf
        (k := k) (Ω := Ω) (K := K)
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))
        (Subgroup.zpowers σ) y h
    -- the local primitive over `K_wˣ`, by the seam
    obtain ⟨Φ₁, hΦ₁⟩ := localPushOfSeam k Ω K w σ hσ φ hφK hlink hle hbot
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) y Φ hΦ hκ
    -- the `δ`-step: a local lift kills the localised class
    refine Work.SSGRoute.E1aClean.extRes_PhiEgen_comp_mk₀_eq_zero
      (f := (SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofInfinite w)).subtype)
      (M := CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))
      (R := SSGRoute.PTExt.unitsK k K)
      (Z := SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
        (NK.GlobalCFT.Place.ofInfinite w))
      (ι := NK.HassePrinciple.unitsToLocalUnits k ↥K (NK.GlobalCFT.Place.ofInfinite w))
      (w := y) (φ := Φ₁) ?_
    intro r
    exact hΦ₁ r

end

end Work.SSGRoute.E1aClean
