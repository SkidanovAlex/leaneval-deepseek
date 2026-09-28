import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.ratSerrePairComparison
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.serreE0Range
import Submission.Work.Serre.relCoh_concentrated_of_ratAcyclic
import Submission.Work.Stems.product_ratH_vanishing
import Submission.Work.StemsB.RelChainsR
import Submission.Work.StemsB.Rat.collarSuspClassAuxRat
import Submission.Work.Thom.CohMap_oneH
import Submission.Work.Serre.exists_ratCup_iso_zero
import Submission.Work.Serre.serreRangeEMVanAll
import Submission.Work.Serre.DiscPair.ratH_of_contractible_base
import Submission.Work.Serre.DiscPair.cylPair_concentrated

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## Auxiliary facts used in the assembly -/

/-- **Pullback fixes the unit class `1 ∈ H⁰(−;ℚ)`.**  The `ℚ`-coefficient version of
`Work.Thom.CohMap_oneH` (the proof is ring-generic). -/
theorem CohMap_oneH_rat {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    (Work.Thom.CohMap f ℚ 0).hom (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of Y)))
      = Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of X)) := by
  change (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.dualChainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) 0))
      (Work.Cohomology.cohomologyClassOf ℚ (TopCat.toSSet.obj (TopCat.of Y))
        (Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj (TopCat.of Y)))
        (Work.Cohomology.cochainDiff_unitCochain ℚ (TopCat.toSSet.obj (TopCat.of Y))))
    = Work.Cohomology.cohomologyClassOf ℚ (TopCat.toSSet.obj (TopCat.of X))
        (Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj (TopCat.of X)))
        (Work.Cohomology.cochainDiff_unitCochain ℚ (TopCat.toSSet.obj (TopCat.of X)))
  rw [Work.Cohomology.singularCohomologyMap_classOf (X := TopCat.of X) (Y := TopCat.of Y) ℚ
      (TopCat.ofHom f) (n := 0) (Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj (TopCat.of Y)))
      (Work.Cohomology.cochainDiff_unitCochain ℚ (TopCat.toSSet.obj (TopCat.of Y)))]
  exact Work.Cohomology.cohomologyClassOf_congr ℚ (TopCat.toSSet.obj (TopCat.of X))
    (Work.Thom.chainComplexMap_unitCochain (R := ℚ) (TopCat.toSSet.map (TopCat.ofHom f))) _ _

/-- **A weakly contractible path connected space is rationally acyclic.** -/
theorem ratAcyclic_of_weaklyContractible_base {B : Type} [TopologicalSpace B] (b₀ : B)
    (hB : PathConnectedSpace B)
    (hBc : ∀ i : ℕ, Subsingleton (HomotopyGroup (Fin i) B b₀)) :
    Work.Serre.RatAcyclic B := by
  have hvan : ∀ i : ℕ, 0 < i → IsZero (Work.Serre.ratH (TopCat.of B) i) :=
    fun i hi => Work.Serre.serreE0Range B b₀ i (fun k _ => hBc k) i hi (by omega)
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact Work.Serre.isIso_ratHomologyMap_toPoint_zero_of_subsingleton_pi0 B (Classical.arbitrary B)
      (Work.Serre.subsingleton_pi0_of_pathConnectedSpace B _)
  · exact IsZero.isIso (hvan n hn)
      (Work.Cohomology.homologyContractible_ring ℚ (X := TopCat.of PUnit) n hn) _

/-- **A linear map between zero modules is an isomorphism.** -/
theorem isIso_ofHom_of_subsingleton {V W : Type} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] [Subsingleton V] [Subsingleton W] (φ : V →ₗ[ℚ] W) :
    IsIso (ModuleCat.ofHom φ) := by
  rw [CategoryTheory.ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ b⟩⟩

/-- **A nonzero linear map between `ℚ`-lines is an isomorphism.** -/
theorem isIso_ofHom_of_linearEquiv_rat {V W : Type} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (e₁ : V ≃ₗ[ℚ] ℚ) (e₂ : W ≃ₗ[ℚ] ℚ) (φ : V →ₗ[ℚ] W) (hφ : φ ≠ 0) :
    IsIso (ModuleCat.ofHom φ) := by
  set ψ : ℚ →ₗ[ℚ] ℚ := e₂.toLinearMap.comp (φ.comp e₁.symm.toLinearMap) with hψ
  have hψne : ψ ≠ 0 := by
    intro h0
    refine hφ (LinearMap.ext fun v => ?_)
    have h1 : ψ (e₁ v) = 0 := by rw [h0]; rfl
    simp only [hψ, LinearMap.comp_apply, LinearEquiv.coe_coe] at h1
    rw [e₁.symm_apply_apply] at h1
    exact e₂.injective (by simpa using h1)
  haveI : IsIso (ModuleCat.ofHom ψ) := Work.Serre.ratCupAux_isIso_ofHom_rat_ne_zero ψ hψne
  have hbij : Function.Bijective ψ :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective (ModuleCat.ofHom ψ)).mp ‹IsIso _›
  rw [CategoryTheory.ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro x y hxy
    have hxy' : φ x = φ y := hxy
    have h2 : ψ (e₁ x) = ψ (e₁ y) := by
      show e₂ (φ (e₁.symm (e₁ x))) = e₂ (φ (e₁.symm (e₁ y)))
      rw [e₁.symm_apply_apply, e₁.symm_apply_apply, hxy']
    exact e₁.injective (hbij.1 h2)
  · intro w
    obtain ⟨q, hq⟩ := hbij.2 (e₂ w)
    refine ⟨e₁.symm q, ?_⟩
    refine e₂.injective ?_
    have h3 : ψ q = e₂ (φ (e₁.symm q)) := rfl
    rw [h3] at hq
    exact hq


theorem thomCylAt_of_contractible {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (b₀ : B) (r N : ℕ) (hr : 1 ≤ r)
    (hq : Work.StemsB.IsSerreFibration q)
    (hB : PathConnectedSpace B)
    (hBc : ∀ i : ℕ, Subsingleton (HomotopyGroup (Fin i) B b₀))
    (hX : PathConnectedSpace X)
    (hpc : PathConnectedSpace (Work.StemsB.fibre q b₀))
    (hvan : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b₀)) t))
    (hgen : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b₀)) r ≅ ModuleCat.of ℚ ℚ)) :
    Work.Serre.ThomCylAt r N q := by
  classical
  rcases Nat.lt_or_ge N r with hNr | hrN
  · exact ⟨0, fun m hm => by exfalso; omega⟩
  obtain ⟨hXvan, hXgen⟩ :=
    ratH_of_contractible_base q b₀ r N hr hrN hq hB hBc hX hpc hvan hgen
  have hBacyc : Work.Serre.RatAcyclic B := ratAcyclic_of_weaklyContractible_base b₀ hB hBc
  obtain ⟨hMvan, hMgen⟩ := cylPair_concentrated q r N hr hBacyc hX hXvan hXgen
  obtain ⟨eU⟩ := hMgen
  let U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)) :=
    eU.inv.hom 1
  have hUne : U ≠ 0 := by
    intro hU0
    have h1 : eU.hom.hom U = 1 := by
      have h := congrArg
        (fun (g : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℚ) => ModuleCat.Hom.hom g (1 : ℚ))
        (Iso.inv_hom_id eU)
      simpa [U, ModuleCat.hom_comp] using h
    rw [hU0, map_zero] at h1
    exact one_ne_zero h1.symm
  have cast_ne : ∀ {a b : ℕ} (h : a = b) (x : Work.Thom.RelCoh ℚ a (Work.Serre.cyl q)
      (Set.range (Work.Serre.cylIncl q))), x ≠ 0 → (h ▸ x) ≠ 0 := by
    intro a b h x hx
    cases h
    exact hx
  refine ⟨U, fun m hm => ?_⟩
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hgen0 : Nonempty (Work.Thom.RelCoh ℚ (0 + (r + 1)) (Work.Serre.cyl q)
        (Set.range (Work.Serre.cylIncl q)) ≅ ModuleCat.of ℚ ℚ) :=
      ⟨eqToIso (congrArg (fun n => Work.Thom.RelCoh ℚ n (Work.Serre.cyl q)
        (Set.range (Work.Serre.cylIncl q))) (Nat.zero_add (r + 1))) ≪≫ eU⟩
    have hB0 : Nonempty (Work.Thom.Coh ℚ 0 B ≅ ModuleCat.of ℚ ℚ) :=
      (Work.Serre.ratCoh_ratH_iso_rat (TopCat.of B) 0).mpr
        (Work.Serre.ratH_zero_of_pathConnected B)
    have hφne : (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl q)) 0 (r + 1)).flip U) ∘ₗ
        (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ 0).hom) ≠ 0 := by
      intro h0
      have hh0 : ((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl q)) 0 (r + 1)).flip U)
          ((Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ 0).hom
            (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of B)))) = 0 :=
        LinearMap.congr_fun h0 _
      rw [CohMap_oneH_rat (Work.Serre.cylRetract q)] at hh0
      have hh1 : (Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl q)) 0 (r + 1))
          (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of (Work.Serre.cyl q)))) U = 0 := hh0
      rw [Work.StemsB.Rat.mixedCupC_oneH_zeroQ (Set.range (Work.Serre.cylIncl q)) (r + 1) U] at hh1
      exact cast_ne (Nat.zero_add (r + 1)).symm U hUne hh1
    exact isIso_ofHom_of_linearEquiv_rat
      (V := ↥(Work.Thom.Coh ℚ 0 B))
      (W := ↥(Work.Thom.RelCoh ℚ (0 + (r + 1)) (Work.Serre.cyl q)
        (Set.range (Work.Serre.cylIncl q))))
      (Classical.choice hB0).toLinearEquiv (Classical.choice hgen0).toLinearEquiv
      (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl q)) 0 (r + 1)).flip U) ∘ₗ
        (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ 0).hom) hφne
  · have hz1 : IsZero (Work.Thom.Coh ℚ m B) :=
      Work.Serre.isZero_ratCoh_of_isZero_ratH
        (Work.Serre.serreE0Range B b₀ m (fun k _ => hBc k) m hmpos (by omega))
    have hz2 : IsZero (Work.Thom.RelCoh ℚ (m + (r + 1)) (Work.Serre.cyl q)
        (Set.range (Work.Serre.cylIncl q))) :=
      hMvan (m + (r + 1)) (by omega) (by omega)
    haveI := ModuleCat.subsingleton_of_isZero hz1
    haveI := ModuleCat.subsingleton_of_isZero hz2
    exact isIso_ofHom_of_subsingleton _

end

end Work.Serre.DiscPair
