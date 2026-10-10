import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E1aClean.finPlaceSquare
import Submission.Work.SSGRoute.E1aClean.levelTwoCocycleAgrees
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `E1c`-dictionary glue of obligation (2) of `finPlaceDict_holds`

`Work.SSGRoute.LeadNatWit.FinPlaceDict` (and hence `E1aClean.localDictionary_natural_family_arch`)
has, at each finite place `(A,q)`, three clauses: naturality, the comparison square with
`globalDictionaryCanon`, and the unramified clause.  The **square** itself is filed and staffed
elsewhere (`E1aClean/LeadPhiUnr/phiCan_square.lean`, with its route in
`E1aClean/LeadPhiUnr/NOTE_phiCan_square_route.md`); its mathematical heart is the transcription
target of `E1aClean/NOTE_finPlaceSquare_glue_WIP.txt`, proved **here**.

Contents:

* `levelChangeTransfer_e1cMap_eq_hensel` — the glue: the level-change transfer
  `E1aClean.levelChangeTransfer` of the level-`1` `E1c`-dictionary of a lifted cocycle is the
  level-`2` `E1c`-dictionary of its base-changed cocycle.  Four lines: the level-`1` and level-`2`
  cocycle formulas (`ExtChain.E1cGeneric.e1cMap_eq_H1π_of_cocycle_lift`,
  `E1aClean.e1cMap_hensel_cocycle_formula`), the `H¹` level change `E1aClean.levelChangeTransfer_H1π`,
  and the pointwise (BC) identification `E1aClean.LevelTwoCocycleTarget` plus the interface `(α)`
  `E1aClean.fixingSubgroupEquiv_symm_coe_eq_restrictScalars` (and `(β)`
  `E1aClean.levelTwoCoeff_eq_rep_res`, a `rfl`).

**No property of the push `θ` of `phiCan` is used**: this is the `θ`-free half of the square, so it
is reusable whichever way the square's prover settles the arbitrary-`θ` interface question raised in
`NOTE_phiCan_square_route.md` §5.
-/

namespace Work.SSGRoute.PT.E1aFinBox

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

noncomputable section

attribute [local instance 10000] Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [NumberField K]

/-- **The glue of the comparison square**: the level-change transport of the level-`1`
`E1c`-dictionary value of the cocycle `c₁` (lifted by `ñ ∈ E1cN X`, cocycle class `y`) is the
level-`2` `E1c`-dictionary value of the base-changed cocycle `c₂` (lifted by `levelTwoLift … X ñ`,
cocycle class `y₂`), the two cocycles being related pointwise by `(BC)`
(`LevelTwoCocycleTarget`).

Proof: rewrite the left side by the level-`1` cocycle formula
(`ExtChain.E1cGeneric.e1cMap_eq_H1π_of_cocycle_lift`), apply the level change at the level of `H¹`
(`E1aClean.levelChangeTransfer_H1π`), identify the resulting cocycle with `c₂` pointwise using
`(BC)` and the interface `(α)` `fixingSubgroupEquiv_symm_coe_eq_restrictScalars`, and rewrite the
right side by the level-`2` cocycle formula (`E1aClean.e1cMap_hensel_cocycle_formula`). -/
theorem levelChangeTransfer_e1cMap_eq_hensel
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hAq : ∀ x : NumberField.RingOfIntegers ↥K,
      x ∈ q.asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1)
    [hNorm : Normal ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
      ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)]
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) ≃ₐ[
          ↥(Work.SSGRoute.E1aClean.decompField k Ω A)]
        ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)))
    (he : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (x : K),
        ((e τ) ⟨(x : Ω), Work.SSGRoute.E1aClean.le_henselField k Ω K A x.2⟩ : Ω)
          = ((τ : K ≃ₐ[k] K) x : Ω))
    (hφres : ∀ g : Ω ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] Ω,
      Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e
          (SSGRoute.res ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
            (Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) g)
        = SSGRoute.res k K (AlgEquiv.restrictScalars k g))
    (X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ X.V]
    [instA : IsAlgClosure ↥(Work.SSGRoute.E1aClean.decompField k Ω A) Ω]
    [instF : FiniteDimensional ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
      ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)]
    [instG : IsGalois ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
      ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)]
    (c₁ : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K X)))
    (ñ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) X)
    (hñ : ∀ g : Ω ≃ₐ[k] Ω,
      Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) X (c₁.1 g)
        = Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω)
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) X) ñ g)
    (c₂ : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] Ω)
      (Work.SSGRoute.homCoind ↥(Work.SSGRoute.E1aClean.decompField k Ω A) Ω
        (Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
        (Work.SSGRoute.E1aClean.levelTwoCoeff k Ω K A hA q hAq e X))))
    (hñ₂ : ∀ g : Ω ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] Ω,
      Work.SSGRoute.ExtChain.E1cGeneric.iotaH
          (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
          (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
          (Work.SSGRoute.E1aClean.levelTwoCoeff k Ω K A hA q hAq e X) (c₂.1 g)
        = Work.GroupCohomology.d0
            (Ω ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] Ω)
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cN
              (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
              (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
              (Work.SSGRoute.E1aClean.levelTwoCoeff k Ω K A hA q hAq e X))
            (Work.SSGRoute.E1aClean.levelTwoLift k Ω K A hA q hAq e X ñ) g)
    (y : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) X)
      (SSGRoute.PTExt.unitsK k K) 0)
    (hy : (Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) X ñ
            : Work.SSGRoute.homCoind k Ω K
              (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) X))
        = ↑(Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := k) (Ω := Ω) (K := K)
              (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) X) y))
    (y₂ : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
        (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
        (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
        (Rep.res (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) X))
      (SSGRoute.PTExt.unitsK ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
        ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)) 0)
    (hy₂ : (Work.SSGRoute.ExtChain.E1cGeneric.piH
              (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
              (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
              (Rep.res (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) X)
              (Work.SSGRoute.E1aClean.levelTwoLift k Ω K A hA q hAq e X ñ)
            : Work.SSGRoute.homCoind ↥(Work.SSGRoute.E1aClean.decompField k Ω A) Ω
                (Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
                (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
                  (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
                  (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
                  (Rep.res (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) X)))
        = ↑(Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
              (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
              (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
              (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
                (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
                (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
                (Rep.res (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) X)) y₂))
    (hBC : Work.SSGRoute.E1aClean.LevelTwoCocycleTarget k Ω K A hA q hAq e he X c₁ ñ hñ c₂ hñ₂) :
    Work.SSGRoute.E1aClean.levelChangeTransfer A X
        (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) hφres
        (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K) X
          (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) X y))
      = Work.SSGRoute.ExtChain.E1cGeneric.e1cMap
          (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
          (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
          (Rep.res (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) X)
          (Work.SSGRoute.ExtChain.E1cGeneric.PhiE
            (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
            (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
            (Rep.res (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) X) y₂) := by
  have hψc : Continuous (fun g : Ω ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] Ω =>
      AlgEquiv.restrictScalars k g) :=
    Work.SSGRoute.E1aClean.restrictScalars_decompField_continuous A
  -- (BC) + interface (α): the level-change cocycle is `c₂`
  have hZ1 : (⟨fun g : Ω ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] Ω =>
        c₁.1 (AlgEquiv.restrictScalars k g),
      Work.SSGRoute.E1aClean.levelChange_mem_Z1 A X
        (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) hφres hψc c₁⟩
      : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] Ω)
          (Work.SSGRoute.homCoind ↥(Work.SSGRoute.E1aClean.decompField k Ω A) Ω
            (Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
            (Rep.res (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) X)))) = c₂ := by
    refine Subtype.ext (funext fun g => ?_)
    show c₁.1 (AlgEquiv.restrictScalars k g) = c₂.1 g
    rw [hBC g]
    exact (congrArg (fun σ : Ω ≃ₐ[k] Ω => c₁.1 σ)
      (Work.SSGRoute.E1aClean.fixingSubgroupEquiv_symm_coe_eq_restrictScalars A g)).symm
  -- (1) the level-1 cocycle formula, inside the transfer
  rw [Work.SSGRoute.ExtChain.E1cGeneric.e1cMap_eq_H1π_of_cocycle_lift
    (k := k) (Ω := Ω) (K := K) X c₁ ñ hñ y hy]
  -- (2) the level change at the level of `H¹`
  rw [Work.SSGRoute.E1aClean.levelChangeTransfer_H1π A X
    (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) hφres hψc c₁]
  -- (3)+(4) the cocycle is `c₂` and the level-2 cocycle formula reads the other end
  exact (congrArg (fun z : ↥(Work.AbsoluteKummer.Z1
        (Ω ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] Ω)
        (Work.SSGRoute.homCoind ↥(Work.SSGRoute.E1aClean.decompField k Ω A) Ω
          (Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
          (Rep.res (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) X))) =>
      Work.AbsoluteKummer.H1π (Ω ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] Ω)
        (Work.SSGRoute.homCoind ↥(Work.SSGRoute.E1aClean.decompField k Ω A) Ω
          (Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
          (Rep.res (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) X)) z) hZ1).trans
    (Work.SSGRoute.E1aClean.e1cMap_hensel_cocycle_formula A X
      (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) c₂
      (Work.SSGRoute.E1aClean.levelTwoLift k Ω K A hA q hAq e X ñ) hñ₂ y₂ hy₂).symm
/-- **The glue with (BC) discharged**: same statement as
`levelChangeTransfer_e1cMap_eq_hensel`, but the pointwise base-change hypothesis is produced
internally by `E1aClean.levelTwoCocycle_agrees` from the lift data (`ñ`, `hñ`, `ñ₂ = levelTwoLift …`,
`hñ₂`).  This is the form in which the comparison square consumes the glue: it removes the need to
choose between the two parallel developments of (BC)
(`E1aClean.levelTwoCocycle_agrees` and `E1aClean.levelTwo_cocycle_agrees`). -/
theorem levelChangeTransfer_e1cMap_eq_hensel_of_lift
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hAq : ∀ x : NumberField.RingOfIntegers ↥K,
      x ∈ q.asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1)
    [hNorm : Normal ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
      ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)]
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) ≃ₐ[
          ↥(Work.SSGRoute.E1aClean.decompField k Ω A)]
        ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)))
    (he : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (x : K),
        ((e τ) ⟨(x : Ω), Work.SSGRoute.E1aClean.le_henselField k Ω K A x.2⟩ : Ω)
          = ((τ : K ≃ₐ[k] K) x : Ω))
    (hφres : ∀ g : Ω ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] Ω,
      Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e
          (SSGRoute.res ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
            (Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) g)
        = SSGRoute.res k K (AlgEquiv.restrictScalars k g))
    (X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ X.V]
    [instA : IsAlgClosure ↥(Work.SSGRoute.E1aClean.decompField k Ω A) Ω]
    [instF : FiniteDimensional ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
      ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)]
    [instG : IsGalois ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
      ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)]
    (c₁ : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K X)))
    (ñ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) X)
    (hñ : ∀ g : Ω ≃ₐ[k] Ω,
      Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) X (c₁.1 g)
        = Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω)
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) X) ñ g)
    (c₂ : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] Ω)
      (Work.SSGRoute.homCoind ↥(Work.SSGRoute.E1aClean.decompField k Ω A) Ω
        (Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
        (Work.SSGRoute.E1aClean.levelTwoCoeff k Ω K A hA q hAq e X))))
    (hñ₂ : ∀ g : Ω ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] Ω,
      Work.SSGRoute.ExtChain.E1cGeneric.iotaH
          (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
          (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
          (Work.SSGRoute.E1aClean.levelTwoCoeff k Ω K A hA q hAq e X) (c₂.1 g)
        = Work.GroupCohomology.d0
            (Ω ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] Ω)
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cN
              (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
              (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
              (Work.SSGRoute.E1aClean.levelTwoCoeff k Ω K A hA q hAq e X))
            (Work.SSGRoute.E1aClean.levelTwoLift k Ω K A hA q hAq e X ñ) g)
    (y : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) X)
      (SSGRoute.PTExt.unitsK k K) 0)
    (hy : (Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) X ñ
            : Work.SSGRoute.homCoind k Ω K
              (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) X))
        = ↑(Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := k) (Ω := Ω) (K := K)
              (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) X) y))
    (y₂ : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
        (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
        (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
        (Rep.res (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) X))
      (SSGRoute.PTExt.unitsK ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
        ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)) 0)
    (hy₂ : (Work.SSGRoute.ExtChain.E1cGeneric.piH
              (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
              (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
              (Rep.res (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) X)
              (Work.SSGRoute.E1aClean.levelTwoLift k Ω K A hA q hAq e X ñ)
            : Work.SSGRoute.homCoind ↥(Work.SSGRoute.E1aClean.decompField k Ω A) Ω
                (Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
                (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
                  (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
                  (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
                  (Rep.res (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) X)))
        = ↑(Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
              (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
              (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
              (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
                (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
                (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
                (Rep.res (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) X)) y₂))
    :
    Work.SSGRoute.E1aClean.levelChangeTransfer A X
        (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) hφres
        (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K) X
          (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) X y))
      = Work.SSGRoute.ExtChain.E1cGeneric.e1cMap
          (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
          (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
          (Rep.res (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) X)
          (Work.SSGRoute.ExtChain.E1cGeneric.PhiE
            (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
            (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
            (Rep.res (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) X) y₂)   :=
  levelChangeTransfer_e1cMap_eq_hensel (k := k) (Ω := Ω) (K := K)
    A hA q hAq e he hφres X c₁ ñ hñ c₂ hñ₂ y hy y₂ hy₂
    (Work.SSGRoute.E1aClean.levelTwoCocycle_agrees (k := k) (Ω := Ω) (K := K)
      A hA q hAq e he X c₁ ñ hñ c₂ hñ₂)

#print axioms Work.SSGRoute.PT.E1aFinBox.levelChangeTransfer_e1cMap_eq_hensel
#print axioms Work.SSGRoute.PT.E1aFinBox.levelChangeTransfer_e1cMap_eq_hensel_of_lift

end

end Work.SSGRoute.PT.E1aFinBox
