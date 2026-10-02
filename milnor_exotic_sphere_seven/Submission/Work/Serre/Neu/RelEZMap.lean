-- PORTED COPY (neutral island) of `Submission/Work/Serre/relEZMap.lean`.
-- The only changes are: the imports of ratShuffle-island modules are redirected to the
-- copies in `Submission/Work/Serre/Neu/`, and the abbrev `singSSet` is renamed to
-- `singSSetN` (same body) so that this module can coexist with `Work.Serre.E0Defs`,
-- which declares the same name.  Declarations and proofs are unchanged.
import Mathlib
import Submission.Work.Serre.Neu.Defs
import Submission.Work.Serre.relEZ_main
import Submission.Work.Serre.relEZ_homology_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative Eilenberg–Zilber chain map, with its value on shuffle cycles

`Work.Serre.relEZ_homology_iso` shows that the Koszul tensor product
`C_*(W) ⊗_ℤ C_*(P,Q)` and the relative chain complex `C_*(W × P, W × Q)` have isomorphic
homology.  Here we exhibit a *chain map* realising this, whose value on the cross product of a
cycle of `W` with a cycle of `(P,Q)` is the relative chain class of the Eilenberg–Zilber shuffle
of representatives.

The construction is the one of the five-lemma proof: the tensor product of the pair sequence
`0 → C_*(Q) → C_*(P) → C_*(P,Q) → 0` with the degreewise flat complex `C_*(W)` is short exact,

`S : 0 ⟶ tpC C C_*(Q) ⟶ tpC C C_*(P) ⟶ tpC C C_*(P,Q) ⟶ 0`,

and the Eilenberg–Zilber shuffle induces a morphism of short exact sequences from `S` to the pair
sequence `S₂ : 0 ⟶ C_*(W × Q) ⟶ C_*(W × P) ⟶ C_*(W × P, W × Q) ⟶ 0` of the product.  Its third
component is a quasi-isomorphism by the five lemma (`quasiIso_τ₃`), and it is the required chain
map `EZ`.  Its value on the shuffle cycle is the second commutation square, which is exactly the
`Abelian.comp_epiDesc` computation rule of the descent along the epimorphism
`tpMap C C C_*(P) (cokernel f0) (𝟙 C) (cokernel.π f0)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct MonoidalCategory

namespace Work.Serre

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

theorem relEZMap (W : Type) [TopologicalSpace W] (P : Type) [TopologicalSpace P] (Q : Set P) :
    ∃ EZ : Work.Serre.tpCWQ W P Q ⟶ Work.Serre.relBBA W P Q,
      (∀ n, CategoryTheory.IsIso (HomologicalComplex.homologyMap EZ n)) ∧
      (∀ (m q : ℕ) (u : ↥((Work.Cohomology.singularChains ℤ (TopCat.of W)).cycles m))
         (v : ↥((Work.Cohomology.relChains (TopCat.of P) Q).cycles q))
         (vt : (Work.Cohomology.singularChains ℤ (TopCat.of P)).X q)
         (hvt : ((Work.Cohomology.relChainsProj (TopCat.of P) Q).f q).hom vt
                 = ((Work.Cohomology.relChains (TopCat.of P) Q).iCycles q) v),
        (EZ.f (m + q)) (((Work.Serre.tpCWQ W P Q).iCycles (m + q)).hom
            (Work.Serre.crossCycTensElem W P Q m q u v))
          = ((Work.Cohomology.relChainsProj (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q}).f (m + q)).hom
              (Work.Serre.ezShufChain W P m q (((Work.Cohomology.singularChains ℤ
                (TopCat.of W)).iCycles m).hom u) vt)) := by
  let X : TopCat := TopCat.of W
  let Y : TopCat := TopCat.of P
  let Q' : TopCat := TopCat.of ↥Q
  let Z : TopCat := TopCat.of (W × P)
  let WQ : Set (W × P) := {x : W × P | x.2 ∈ Q}
  let C : ChainComplex (ModuleCat ℤ) ℕ := Work.Cohomology.singularChains ℤ X
  let CY : ChainComplex (ModuleCat ℤ) ℕ := Work.Cohomology.singularChains ℤ Y
  let CQ : ChainComplex (ModuleCat ℤ) ℕ := Work.Cohomology.singularChains ℤ Q'
  let f0 : CQ ⟶ CY := Work.Cohomology.inclChains Y Q
  have hflat : ∀ k, Module.Flat ℤ ↥(C.X k) := fun k => flat_singularChains X k
  have hf0 : ∀ k, Function.Injective ((f0.f k).hom) := fun k => inclChains_component_injective Y Q k
  have hf0s : ∀ k, Function.Surjective (((cokernel.π f0).f k).hom) :=
    fun k => cokernelπ_component_surjective f0 k
  let Dtp : Work.Kunneth.tpC C CQ ⟶ Work.Kunneth.tpC C CY := Work.Kunneth.tpMap C C CQ CY (𝟙 C) f0
  let DtpD : Work.Kunneth.tpC C CY ⟶ Work.Kunneth.tpC C (cokernel f0) :=
    Work.Kunneth.tpMap C C CY (cokernel f0) (𝟙 C) (cokernel.π f0)
  let S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk Dtp DtpD (by
      rw [Work.Kunneth.tpMap_comp, Category.id_comp, cokernel.condition, tpMap_zero_left])
  have hS : S.ShortExact := tpMap_relChains_shortExact C hflat f0 hf0 hf0s
  haveI hEpiDtpD : Epi DtpD := hS.epi_g
  let S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) := Work.Cohomology.hPairShort Z WQ
  have hS₂ : S₂.ShortExact := Work.Cohomology.hPairShort_shortExact Z WQ
  let τ₁ : S.X₁ ⟶ S₂.X₁ := Work.Kunneth.ezMapT X Q' ≫
    Work.Cohomology.chainMap ℤ (TopCat.of (W × ↥Q)) (TopCat.of ↥WQ) (prodSubtypeTopIso W P Q).hom
  let τ₂ : S.X₂ ⟶ S₂.X₂ := Work.Kunneth.ezMapT X Y
  have hcomm₁₂ : τ₁ ≫ S₂.f = S.f ≫ τ₂ := by
    have hnat := relEZ_ezMapT_naturality X Q' X Y (𝟙 X) (Work.Cohomology.subtypeIncl Y Q)
    rw [chainMap_id_eq X] at hnat
    have hL : τ₁ ≫ S₂.f = Work.Kunneth.ezMapT X Q' ≫
        SSet.chainComplexMap (TopCat.toSSet.map (MonoidalCategoryStruct.tensorHom (𝟙 X)
          (Work.Cohomology.subtypeIncl Y Q))) Work.Kunneth.zz := by
      dsimp only [τ₁, S₂, Work.Cohomology.hPairShort, Work.Cohomology.inclChains]
      rw [Category.assoc, ← Work.Cohomology.chainMap_comp', ← tensorHom_id_incl_eq W P Q]
      rfl
    have hR : S.f ≫ τ₂ = Work.Kunneth.tpMap (Work.Kunneth.sChain (TopCat.toSSet.obj X))
        (Work.Kunneth.sChain (TopCat.toSSet.obj X)) (Work.Kunneth.sChain (TopCat.toSSet.obj Q'))
        (Work.Kunneth.sChain (TopCat.toSSet.obj Y)) (𝟙 (Work.Cohomology.singularChains ℤ X))
        (SSet.chainComplexMap (TopCat.toSSet.map (Work.Cohomology.subtypeIncl Y Q))
          Work.Kunneth.zz) ≫ Work.Kunneth.ezMapT X Y := rfl
    rw [hL, hR]
    exact hnat.symm
  have hb : S.f ≫ (τ₂ ≫ S₂.g) = 0 := by
    rw [← Category.assoc, ← hcomm₁₂, Category.assoc, S₂.zero, comp_zero]
  have hg : kernel.ι DtpD ≫ (τ₂ ≫ S₂.g) = 0 :=
    ShortComplex.Exact.comp_eq_zero hS.exact (a := kernel.ι DtpD) (kernel.condition DtpD) hb
  let EZ : S.X₃ ⟶ S₂.X₃ := Abelian.epiDesc DtpD (τ₂ ≫ S₂.g) hg
  have hEZq : QuasiIso EZ := by
    let Φ : S ⟶ S₂ :=
      { τ₁ := τ₁
        τ₂ := τ₂
        τ₃ := EZ
        comm₁₂ := hcomm₁₂
        comm₂₃ := (Abelian.comp_epiDesc DtpD (τ₂ ≫ S₂.g) hg).symm }
    have hφ1 : QuasiIso Φ.τ₁ := by
      haveI : QuasiIso (Work.Kunneth.ezMapT X Q') := quasiIso_ezMapT X Q'
      haveI : QuasiIso (Work.Cohomology.chainMap ℤ (TopCat.of (W × ↥Q)) (TopCat.of ↥WQ)
          (prodSubtypeTopIso W P Q).hom) := inferInstance
      show QuasiIso (Work.Kunneth.ezMapT X Q' ≫ Work.Cohomology.chainMap ℤ
        (TopCat.of (W × ↥Q)) (TopCat.of ↥WQ) (prodSubtypeTopIso W P Q).hom)
      infer_instance
    have hφ2 : QuasiIso Φ.τ₂ := by
      show QuasiIso (Work.Kunneth.ezMapT X Y)
      exact quasiIso_ezMapT X Y
    exact HomologicalComplex.HomologySequence.quasiIso_τ₃ Φ hS hS₂ hφ1 hφ2
  refine ⟨EZ, ?_, ?_⟩
  · intro n
    haveI : QuasiIso EZ := hEZq
    exact inferInstance
  · intro m q u v vt hvt
    let a : (C).X m := ((C).iCycles m).hom u
    let a₀ : (Work.Kunneth.tpC C CY).X (m + q) :=
      Work.Kunneth.tpLof C CY (m + q) ⟨(m, q), rfl⟩ (a ⊗ₜ[ℤ] vt)
    have hvt' : (ModuleCat.Hom.hom ((cokernel.π f0).f q)) vt
        = (ModuleCat.Hom.hom (iCycles (cokernel f0) q)) v := hvt
    have hcross : ((Work.Serre.tpCWQ W P Q).iCycles (m + q)).hom
        (Work.Serre.crossCycTensElem W P Q m q u v)
        = Work.Kunneth.tpLof C (cokernel f0) (m + q) ⟨(m, q), rfl⟩
            (a ⊗ₜ[ℤ] (((cokernel f0).iCycles q).hom v)) :=
      Work.Kunneth.iCycles_crossCycTens_tmul C (cokernel f0) (m + q) m q rfl u v
    have ha₀ : (DtpD.f (m + q)).hom a₀
        = Work.Kunneth.tpLof C (cokernel f0) (m + q) ⟨(m, q), rfl⟩
            (a ⊗ₜ[ℤ] (((cokernel f0).iCycles q).hom v)) := by
      have h := Work.Kunneth.tpMap_tmul C C CY (cokernel f0) (𝟙 C) (cokernel.π f0)
        (m + q) ⟨(m, q), rfl⟩ a vt
      have hid : ModuleCat.Hom.hom (HomologicalComplex.Hom.f (𝟙 C) m) a = a := by
        rw [HomologicalComplex.id_f C m]
        rfl
      rw [h, hid, hvt']
    have hcomp := congrArg
      (fun (G : (Work.Kunneth.tpC C CY) ⟶ S₂.X₃) => (G.f (m + q)).hom a₀)
      (Abelian.comp_epiDesc DtpD (τ₂ ≫ S₂.g) hg)
    rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hcomp
    rw [hcross, ← ha₀]
    exact hcomp

end

end Work.Serre
