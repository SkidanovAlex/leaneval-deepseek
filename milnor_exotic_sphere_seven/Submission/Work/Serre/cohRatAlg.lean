import Mathlib
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Cohomology.uctDefs
import Submission.Work.Serre.moduleCatLeftHomologyMap_mkQ

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The dual (cochain) side of a chain map, over a field

This file proves the algebraic core of `Work.Serre.cohMapIsoOfRatHomologyIso`: for a chain map
`φ : C ⟶ D` of chain complexes of vector spaces over a field `F`, if `φ` induces an isomorphism on
homology in degree `k`, then its transpose (the map on the dual cochain complexes) induces an
isomorphism on cohomology in degree `k`.

The proof is the universal coefficient theorem over a field (`Work.StemsB.fdPsi`/`fdMiddle`),
together with its *naturality*: the comparison map `Ψ : ker dⁿ ⟶ Hom(Hₙ, F)` commutes with the
maps induced by a chain map.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits
open Work.Cohomology

namespace Work.Serre

noncomputable section

variable {F : Type} [Field F]

/-! ## Notation -/

/-- The three-term chain complex `C_{k+1} → C_k → C_{k-1}`, with the map induced by a chain
map. -/
abbrev chainScHom (C D : ChainComplex (ModuleCat.{0,0} F) ℕ) (φ : C ⟶ D) (k : ℕ) :
    C.sc' (k + 1) k (k - 1) ⟶ D.sc' (k + 1) k (k - 1) :=
  (HomologicalComplex.shortComplexFunctor' (ModuleCat.{0,0} F) (ComplexShape.down ℕ)
    (k + 1) k (k - 1)).map φ

/-- The three-term cochain complex `K^{k-1} → K^k → K^{k+1}` of the dual complexes, with the map
induced by the transpose of a chain map. -/
abbrev dualScHom (C D : ChainComplex (ModuleCat.{0,0} F) ℕ) (φ : C ⟶ D) (k : ℕ) :
    (dualComplex F D).sc' (k - 1) k (k + 1) ⟶ (dualComplex F C).sc' (k - 1) k (k + 1) :=
  (HomologicalComplex.shortComplexFunctor' (ModuleCat.{0,0} F) (ComplexShape.up ℕ)
    (k - 1) k (k + 1)).map (dualComplexMap F C D φ)

/-- The map induced by a chain map on `Hₖ`, in the explicit "cycles modulo boundaries" model. -/
abbrev fdZMap (C D : ChainComplex (ModuleCat.{0,0} F) ℕ) (φ : C ⟶ D) (k : ℕ) :
    ModuleCat.of F (↥(Work.StemsB.fdZ F C k) ⧸ Work.StemsB.fdH F C k) ⟶
      ModuleCat.of F (↥(Work.StemsB.fdZ F D k) ⧸ Work.StemsB.fdH F D k) :=
  ShortComplex.leftHomologyMap' (chainScHom C D φ k)
    (C.sc' (k + 1) k (k - 1)).moduleCatLeftHomologyData
    (D.sc' (k + 1) k (k - 1)).moduleCatLeftHomologyData

/-- The map induced by the transpose of a chain map on `Hᵏ`, in the explicit "cocycles modulo
coboundaries" model. -/
abbrev dualHMap (C D : ChainComplex (ModuleCat.{0,0} F) ℕ) (φ : C ⟶ D) (k : ℕ) :
    ModuleCat.of F (↥(LinearMap.ker ((dualComplex F D).d k (k + 1)).hom) ⧸
        Work.StemsB.fdPre F D k) ⟶
      ModuleCat.of F (↥(LinearMap.ker ((dualComplex F C).d k (k + 1)).hom) ⧸
        Work.StemsB.fdPre F C k) :=
  ShortComplex.leftHomologyMap' (dualScHom C D φ k)
    ((dualComplex F D).sc' (k - 1) k (k + 1)).moduleCatLeftHomologyData
    ((dualComplex F C).sc' (k - 1) k (k + 1)).moduleCatLeftHomologyData

/-! ## The identifications with the `moduleCatLeftHomologyData` model -/

lemma fdZ_eq_ker_scMap (C : ChainComplex (ModuleCat.{0,0} F) ℕ) (k : ℕ) :
    Work.StemsB.fdZ F C k = LinearMap.ker ((C.sc' (k + 1) k (k - 1)).g.hom) := rfl

lemma fdH_eq_range_scMap (C : ChainComplex (ModuleCat.{0,0} F) ℕ) (k : ℕ) :
    Work.StemsB.fdH F C k = (C.sc' (k + 1) k (k - 1)).moduleCatToCycles.range := rfl

lemma fdPre_eq_range_scMap (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ) :
    Work.StemsB.fdPre F E n =
      ((dualComplex F E).sc' (n - 1) n (n + 1)).moduleCatToCycles.range := rfl

/-! ## The concrete maps on cycles, cocycles and their quotients -/

lemma chainMap_mem_fdZ (C D : ChainComplex (ModuleCat.{0,0} F) ℕ) (φ : C ⟶ D) (k : ℕ)
    {x : ↑(C.X k)} (hx : x ∈ Work.StemsB.fdZ F C k) :
    φ.f k x ∈ Work.StemsB.fdZ F D k := by
  rw [Work.StemsB.fdZ, LinearMap.mem_ker]
  have hx' : (C.d k (k - 1)).hom x = 0 := LinearMap.mem_ker.mp hx
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.comm k (k - 1))) x
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h
  rw [h, hx', map_zero]

lemma dualMap_mem_ker (C D : ChainComplex (ModuleCat.{0,0} F) ℕ) (φ : C ⟶ D) (k : ℕ)
    {w : ↑((dualComplex F D).X k)}
    (hw : w ∈ LinearMap.ker ((dualComplex F D).d k (k + 1)).hom) :
    ((dualComplexMap F C D φ).f k).hom w ∈
      LinearMap.ker ((dualComplex F C).d k (k + 1)).hom := by
  rw [LinearMap.mem_ker]
  have hw' : ((dualComplex F D).d k (k + 1)).hom w = 0 := LinearMap.mem_ker.mp hw
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    ((dualComplexMap F C D φ).comm k (k + 1))) w
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h
  rw [h, hw', map_zero]

/-- The restriction of the transpose of a chain map to the cocycles. -/
def cocycleMap (C D : ChainComplex (ModuleCat.{0,0} F) ℕ) (φ : C ⟶ D) (k : ℕ) :
    ↥(LinearMap.ker ((dualComplex F D).d k (k + 1)).hom) →ₗ[F]
      ↥(LinearMap.ker ((dualComplex F C).d k (k + 1)).hom) :=
  ((((dualComplexMap F C D φ).f k).hom).comp
      (LinearMap.ker ((dualComplex F D).d k (k + 1)).hom).subtype).codRestrict
    (LinearMap.ker ((dualComplex F C).d k (k + 1)).hom)
    (fun m => dualMap_mem_ker C D φ k m.2)

/-- `cocycleMap` applies the transpose on representatives. -/
lemma cocycleMap_coe (C D : ChainComplex (ModuleCat.{0,0} F) ℕ) (φ : C ⟶ D) (k : ℕ)
    (m : ↥(LinearMap.ker ((dualComplex F D).d k (k + 1)).hom)) :
    ((cocycleMap C D φ k m : ↥(LinearMap.ker ((dualComplex F C).d k (k + 1)).hom)) :
        ↑((dualComplex F C).X k))
      = ((dualComplexMap F C D φ).f k).hom (m : ↑((dualComplex F D).X k)) := rfl

/-- Elementwise description of the chain-side map on cycles modulo boundaries. -/
lemma fdZMap_mkQ (C D : ChainComplex (ModuleCat.{0,0} F) ℕ) (φ : C ⟶ D) (k : ℕ)
    (x : ↥(Work.StemsB.fdZ F C k)) :
    (fdZMap C D φ k).hom ((Work.StemsB.fdH F C k).mkQ x) =
      (Work.StemsB.fdH F D k).mkQ ⟨φ.f k x, chainMap_mem_fdZ C D φ k x.2⟩ := by
  change (ShortComplex.leftHomologyMap' (chainScHom C D φ k)
      (C.sc' (k + 1) k (k - 1)).moduleCatLeftHomologyData
      (D.sc' (k + 1) k (k - 1)).moduleCatLeftHomologyData).hom
    ((C.sc' (k + 1) k (k - 1)).moduleCatToCycles.range.mkQ x) =
      (D.sc' (k + 1) k (k - 1)).moduleCatToCycles.range.mkQ
        ⟨φ.f k x, chainMap_mem_fdZ C D φ k x.2⟩
  exact Work.Serre.moduleCatLeftHomologyMap_mkQ (chainScHom C D φ k) x

/-- Elementwise description of the cochain-side map on cocycles modulo coboundaries. -/
lemma dualHMap_mkQ (C D : ChainComplex (ModuleCat.{0,0} F) ℕ) (φ : C ⟶ D) (k : ℕ)
    (w : ↥(LinearMap.ker ((dualComplex F D).d k (k + 1)).hom)) :
    (dualHMap C D φ k).hom ((Work.StemsB.fdPre F D k).mkQ w) =
      (Work.StemsB.fdPre F C k).mkQ (cocycleMap C D φ k w) := by
  change (ShortComplex.leftHomologyMap' (dualScHom C D φ k)
      ((dualComplex F D).sc' (k - 1) k (k + 1)).moduleCatLeftHomologyData
      ((dualComplex F C).sc' (k - 1) k (k + 1)).moduleCatLeftHomologyData).hom
    (((dualComplex F D).sc' (k - 1) k (k + 1)).moduleCatToCycles.range.mkQ w) =
      ((dualComplex F C).sc' (k - 1) k (k + 1)).moduleCatToCycles.range.mkQ
        ⟨((dualComplexMap F C D φ).f k).hom (w : ↑((dualComplex F D).X k)),
          dualMap_mem_ker C D φ k w.2⟩
  exact Work.Serre.moduleCatLeftHomologyMap_mkQ (dualScHom C D φ k) w

/-! ## Evaluation of the universal-coefficient isomorphism -/

lemma fdMiddle_apply (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ)
    (w : ↥(LinearMap.ker ((dualComplex F E).d n (n + 1)).hom))
    (x : ↥(Work.StemsB.fdZ F E n)) :
    Work.StemsB.fdMiddle F E n ((Work.StemsB.fdPre F E n).mkQ w)
      ((Work.StemsB.fdH F E n).mkQ x) = (Work.StemsB.fdVal F E n w) x := by
  rw [show Work.StemsB.fdMiddle F E n ((Work.StemsB.fdPre F E n).mkQ w)
      = Work.StemsB.fdPsi F E n w from ?_]
  · rw [Work.StemsB.fdPsi_apply]
  · rw [Work.StemsB.fdMiddle]
    simp only [LinearEquiv.trans_apply, Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk]

/-! ## Naturality of the comparison map `Ψ`, and the square -/

/-- **Naturality of `Ψ`**: the comparison map from the cocycles of the dual complex to the dual of
the homology commutes with the maps induced by a chain map. -/
lemma fdPsi_naturality (C D : ChainComplex (ModuleCat.{0,0} F) ℕ) (φ : C ⟶ D) (k : ℕ)
    (w : ↥(LinearMap.ker ((dualComplex F D).d k (k + 1)).hom)) :
    Work.StemsB.fdPsi F C k (cocycleMap C D φ k w) =
      (LinearMap.dualMap ((fdZMap C D φ k).hom)) (Work.StemsB.fdPsi F D k w) := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := (Work.StemsB.fdH F C k).mkQ_surjective y
  rw [Work.StemsB.fdPsi_apply, LinearMap.dualMap_apply, fdZMap_mkQ C D φ k x,
    Work.StemsB.fdPsi_apply]
  rfl

/-- **The square**: the transport of the chain-side map on `Hₖ` by the universal coefficient
isomorphisms is the map induced on `Hᵏ` by the transpose. -/
theorem fdMiddle_square (C D : ChainComplex (ModuleCat.{0,0} F) ℕ) (φ : C ⟶ D) (k : ℕ) :
    (Work.StemsB.fdMiddle F C k).toLinearMap.comp ((dualHMap C D φ k).hom) =
      (LinearMap.dualMap ((fdZMap C D φ k).hom)).comp
        (Work.StemsB.fdMiddle F D k).toLinearMap := by
  apply LinearMap.ext
  intro y
  obtain ⟨w, rfl⟩ := (Work.StemsB.fdPre F D k).mkQ_surjective y
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (Work.StemsB.fdH F C k).mkQ_surjective x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.dualMap_apply,
    dualHMap_mkQ C D φ k w, fdZMap_mkQ C D φ k x]
  show Work.StemsB.fdMiddle F C k ((Work.StemsB.fdPre F C k).mkQ (cocycleMap C D φ k w))
      ((Work.StemsB.fdH F C k).mkQ x)
    = Work.StemsB.fdMiddle F D k ((Work.StemsB.fdPre F D k).mkQ w)
      ((Work.StemsB.fdH F D k).mkQ ⟨φ.f k x, chainMap_mem_fdZ C D φ k x.2⟩)
  rw [fdMiddle_apply C k (cocycleMap C D φ k w) x,
    fdMiddle_apply D k w ⟨φ.f k x, chainMap_mem_fdZ C D φ k x.2⟩]
  rfl

/-- **The dual map is an isomorphism whenever the chain-side map on `Hₖ` is.**  This is the
transport of `fdMiddle_square` across the universal-coefficient isomorphisms. -/
theorem isIso_dualHMap_of_isIso_fdZMap {C D : ChainComplex (ModuleCat.{0,0} F) ℕ} (φ : C ⟶ D)
    (k : ℕ) (h : IsIso (fdZMap C D φ k)) : IsIso (dualHMap C D φ k) := by
  haveI := h
  have hbij : Function.Bijective ⇑(fdZMap C D φ k).hom :=
    ConcreteCategory.bijective_of_isIso (fdZMap C D φ k)
  have hdual : Function.Bijective ⇑(LinearMap.dualMap (fdZMap C D φ k).hom) :=
    ⟨LinearMap.dualMap_injective_of_surjective hbij.2,
      LinearMap.dualMap_surjective_of_injective hbij.1⟩
  have hfun : ⇑(dualHMap C D φ k).hom =
      (⇑(Work.StemsB.fdMiddle F C k).symm) ∘
        ((⇑(LinearMap.dualMap (fdZMap C D φ k).hom)) ∘ ⇑(Work.StemsB.fdMiddle F D k)) := by
    funext y
    have hsq := LinearMap.congr_fun (fdMiddle_square C D φ k) y
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hsq
    simp only [Function.comp_apply]
    apply (Work.StemsB.fdMiddle F C k).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hsq
  rw [ConcreteCategory.isIso_iff_bijective, hfun]
  exact (Work.StemsB.fdMiddle F C k).symm.bijective.comp
    (hdual.comp (Work.StemsB.fdMiddle F D k).bijective)

end

end Work.Serre
