import Mathlib
import Submission.Work.Cohomology.Endgame.cappedTransferClean
import Submission.Work.Cohomology.RelCupTransfer
import Submission.Work.Cohomology.RelCup
import Submission.Work.Cohomology.relCochainDual
import Submission.Work.Cohomology.dualComplexMap_quasiIso
import Submission.Work.Cohomology.relChainsMap_quasiIso
import Submission.Work.Cohomology.isIso_homologyMap_tau1
import Submission.Work.Cohomology.collarInclCohomologyIsIso
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Milnor.CollarHomotopy
import Submission.Work.Endgame.capRelAuxClean

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

/-!
# The pair map `ιX : (Vk(-2), Mk(-2)) → (X, A)` is an isomorphism on relative cohomology

The statement and the strategy are described in the docstring of `cappedTransferIso` below.

This is the *clean* version of `Work.Cohomology.capRelMap_isIso`: it concerns
`Work.Cohomology.Endgame.CappedTransfer.capRelMap D hU`, the copy of the transfer map whose import
closure avoids `Submission.Work.Cohomology.dualZ` and `Submission.Work.Cohomology.prodSphereAux`.
The generalities about `relComplexMap` and the cochain-level excision are in
`Submission/Work/Endgame/capRelAuxClean.lean` (namespace
`Work.Cohomology.Endgame.CapAux`), a copy of `Submission/Work/Cohomology/capRelAux.lean` with the
poisoned import removed.
-/

namespace Work.Endgame
open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Work.Cohomology
open Work.Cohomology.Endgame.CappedTransfer
open Work.Cohomology.Endgame.CapAux

noncomputable section

/-- **The pair map `ιX : (Vk(-2), Mk(-2)) → (X, A)` is an isomorphism on relative cohomology**
(for the *clean* copy of the transfer machinery).

`Work.Cohomology.Endgame.CappedTransfer.capRelMap D hU` is the map of relative cochain complexes
induced by the open embedding `D.ιX : Vk (-2) → X = cappedSpace D`, where `A = Set.range D.ιY` is
the cap.  It is the copy, in the namespace `Work.Cohomology.Endgame.CappedTransfer`, of the map
used by `Work.Cohomology.capRelMap`, whose import closure is *clean* (it avoids
`Submission.Work.Cohomology.dualZ` and `Submission.Work.Cohomology.prodSphereAux`).

The map factors as

`(Vk(-2), Mk(-2)) --incl--> (Vk(-2), collar(-2)) --≅--> (range D.ιX, A ∩ range D.ιX) --incl--> (X, A)`

and each of the three pieces is an isomorphism on relative cohomology: the first is the inclusion
of a deformation retract (`Work.Milnor.collar_homotopyEquiv_Mk` + the five lemma), the second is an
isomorphism of pairs, and the third is an excision.  Hence `capRelMap D hU` induces an isomorphism
`H^n(Vk(-2), Mk(-2)) ≅ H^n(X, A)` in every degree `n`.

Only degrees `4` and `8` are needed for the Milnor assembly, but the statement is degreewise.

**Compatibility constraint**: this module and its whole import closure must NOT contain
`Submission.Work.Cohomology.dualZ` or `Submission.Work.Cohomology.prodSphereAux`. -/
theorem cappedTransferIso (D : Work.Milnor.CapData) (hU : D.U = Work.Milnor.collar (-2)) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.Endgame.CappedTransfer.capRelMap D hU) n) := by
  classical
  let V : TopCat := TopCat.of (Submission.Milnor.Vk (-2))
  let S : Set V := Set.range (Work.Milnor.mkToVkFun (-2))
  let K : Set V := Work.Milnor.collar (-2)
  let X : TopCat := Work.Milnor.glueX D
  let U : Set X := Work.Milnor.glueU D
  let A : Set X := Work.Milnor.glueV D
  let Arel : Set (TopCat.of U) := {y : U | (y : X) ∈ A}
  let φ : V ≅ TopCat.of U := TopCat.isoOfHomeo (eU D)
  -- `Mk (-2) ⊆ collar (-2)`
  have hKS : ∀ x ∈ S, (𝟙 V) x ∈ K := by
    intro x hx
    obtain ⟨q, rfl⟩ := hx
    exact Work.Milnor.mem_collar.mpr (Work.Milnor.one_lt_fibreNorm_mkToVkFun (-2) q)
  -- the open embedding `fU D : Vk (-2) → U` carries `collar (-2)` into `A ∩ U`
  have hfK : ∀ x ∈ K, fU D x ∈ Arel := by
    intro x hx
    have hxU : x ∈ D.U := by rw [hU]; exact hx
    change ((eU D x : ↥(Work.Milnor.glueU D)) : Work.Milnor.cappedSpace D) ∈ A
    rw [eU_apply_coe D x]
    exact ⟨D.φ x, (D.ιX_eq_ιY_iff.mpr ⟨hxU, rfl⟩).symm⟩
  have hf : ∀ x ∈ S, fU D x ∈ Arel := fun x hx => hfK x (hKS x hx)
  -- the inverse of `fU D` carries `A ∩ U` into `collar (-2)`
  have hInv : ∀ y ∈ Arel, φ.inv y ∈ K := by
    intro y hy
    have hyA : (y : X) ∈ A := hy
    obtain ⟨p, hp⟩ := y.2
    have hsub : y = φ.hom p := by
      apply Subtype.ext
      change (y : Work.Milnor.cappedSpace D) =
        ((eU D p : ↥(Work.Milnor.glueU D)) : Work.Milnor.cappedSpace D)
      rw [eU_apply_coe D p]
      exact hp.symm
    rw [hsub, TopCat.hom_inv_id_apply]
    have hpA : D.ιX p ∈ A := by rw [hp]; exact hyA
    obtain ⟨z, hz⟩ := hpA
    have hpU : p ∈ D.U := (D.ιY_eq_ιX_iff.mp hz).choose
    rwa [hU] at hpU
  -- the inclusion `A ∩ U ⊆ A`
  have hRestr : ∀ y ∈ Arel, (subtypeIncl X U) y ∈ A := fun y hy => hy
  have hFinal : ∀ x ∈ S, (fU D ≫ subtypeIncl X U) x ∈ A :=
    fun x hx => hRestr (fU D x) (hf x hx)
  -- the excision step
  have h₂ : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relComplexMap ℤ Arel A (subtypeIncl X U) hRestr) n) :=
    capRel_excision_isIso X U A (Work.Milnor.isOpen_glueU D) (Work.Milnor.isOpen_glueV D)
      (Work.Milnor.glueU_union_glueV D) n hRestr
  -- the homeomorphism-of-pairs and collar steps
  have h₁ : CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (relComplexMap ℤ S Arel (fU D) hf) n) := by
    have hMid : ∀ x ∈ S, (𝟙 V ≫ fU D) x ∈ Arel := fun x hx => hfK ((𝟙 V) x) (hKS x hx)
    have heq : relComplexMap ℤ S Arel (fU D) hf
        = relComplexMap ℤ S Arel (𝟙 V ≫ fU D) hMid :=
      capRel_relComplexMap_congr ℤ S Arel (Category.id_comp (fU D)).symm hf hMid
    rw [heq, capRel_relComplexMap_comp ℤ S K Arel (𝟙 V) (fU D) hKS hfK,
      HomologicalComplex.homologyMap_comp]
    haveI hK : CategoryTheory.IsIso
        (HomologicalComplex.homologyMap (relComplexMap ℤ K Arel (fU D) hfK) n) :=
      capRel_relComplexMap_iso_of_isIso_pairs ℤ K Arel (fU D) hfK φ.inv hInv
        (Iso.hom_inv_id φ) (Iso.inv_hom_id φ) n
    haveI hSth : CategoryTheory.IsIso
        (HomologicalComplex.homologyMap (relComplexMap ℤ S K (𝟙 V) hKS) n) :=
      capRel_collar_isIso n hKS
    infer_instance
  -- the factorisation of `capRelMap` through the identity of `Vk (-2)`
  have hmap : capRelMap D hU = relComplexMap ℤ S A (fU D ≫ subtypeIncl X U) hFinal := by
    unfold capRelMap
    exact capRel_relComplexMap_congr ℤ S A (fU_comp_subtypeIncl D).symm
      (capPairMap_mem D hU) hFinal
  rw [hmap]
  exact capRel_isIso_relComplexMap_comp ℤ S Arel A (fU D) (subtypeIncl X U) hf hRestr n
    hFinal h₂ h₁


end

end Work.Endgame
