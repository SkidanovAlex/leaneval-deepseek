import Mathlib
import Submission.Work.Serre.relCohMV_les_rat
import Submission.Work.Serre.MVCohRatDefs
import Submission.Work.Serre.MVShift.ShQ
import Submission.Work.Serre.MVShift.HonestCup
import Submission.Work.Serre.MVShift.relMapLM_mixedRelStar
import Submission.Work.Serre.MVShift.shKZeroRat
import Submission.Work.Cohomology.relIncl_relCupH
import Submission.Work.Serre.MVGlue.mvSetup

/-!
# The cup product with a relative cocycle on the pieces of an open cover

This file collects the *honest* chain-level cup maps used in the proof of the `δ`-derivation of
the rational Mayer–Vietoris connecting map (`Work.Serre.mvDeltaCupMixedAux`):

* the restrictions of a relative cocycle `t ∈ C^{n₀}(X,A;ℚ)` to `(U, A∩U)` and `(U∩V, A∩U∩V)`;
* the chain maps `cupTop`, `cupTopU`, `cupTopV`, `cupTopUV` (cup with those restrictions, as chain
  maps into the degree-`n₀` shift of the corresponding relative cochain complex);
* the biproduct `cupMid` of the two middle maps.

These are the components of the "honest cup morphism" `Smv X ∅ U V ⟶ shS (Smv X A U V) n₀`.

The file also records the elementary biproduct/shift calculus (`shMap` is additive, the two
factorisations of a biproduct lift) that is used to assemble the morphism of short complexes.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Serre

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

/-! ## §1. The restrictions of the cocycle to the cover pieces -/

/-- The restriction of a relative cocycle on `(X,A)` to the pair `(U, A ∩ U)`. -/
noncomputable def cupTgtU (X : TopCat) (A : Set X) (U : Set X) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ X A n₀) :
    Work.Cohomology.relKern ℚ (TopCat.of ↥U) (Work.Cohomology.interAU A U) n₀ :=
  Work.Cohomology.relMapLM (R := ℚ) (X₁ := TopCat.of ↥U) (X₂ := X)
    (Work.Cohomology.interAU A U) A (Work.Cohomology.subtypeIncl X U)
    (Work.Cohomology.interAU_incl_subtypeIncl X A U) n₀ t

theorem cupTgtU_cocycle (X : TopCat) (A : Set X) (U : Set X) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ X A n₀)
    (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0) :
    Work.Cohomology.relDiffLM ℚ (TopCat.of ↥U) (Work.Cohomology.interAU A U) n₀
      (cupTgtU X A U n₀ t) = 0 :=
  Work.Cohomology.relDiffLM_relMapLM (R := ℚ) (X₁ := TopCat.of ↥U) (X₂ := X)
    (A₁ := Work.Cohomology.interAU A U) (A₂ := A) (f := Work.Cohomology.subtypeIncl X U)
    (h := Work.Cohomology.interAU_incl_subtypeIncl X A U) (n := n₀) t ht

/-- The further restriction of `cupTgtU X A U n₀ t` to the overlap `(U ∩ V, A ∩ U ∩ V)`. -/
noncomputable def cupTgtUV (X : TopCat) (A : Set X) (U : Set X) (V : Set X) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ X A n₀) :
    Work.Cohomology.relKern ℚ (TopCat.of ↥(U ∩ V))
      (Work.Cohomology.interAU A (U ∩ V)) n₀ :=
  Work.Cohomology.relMapLM (R := ℚ) (X₁ := TopCat.of ↥(U ∩ V)) (X₂ := TopCat.of ↥U)
    (Work.Cohomology.interAU A (U ∩ V)) (Work.Cohomology.interAU A U)
    (Work.Cohomology.pdIncl U (U ∩ V) Set.inter_subset_left)
    (Work.Cohomology.interAU_incl_pdIncl_U X A U V) n₀ (cupTgtU X A U n₀ t)

theorem cupTgtUV_cocycle (X : TopCat) (A : Set X) (U : Set X) (V : Set X) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ X A n₀)
    (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0) :
    Work.Cohomology.relDiffLM ℚ (TopCat.of ↥(U ∩ V))
      (Work.Cohomology.interAU A (U ∩ V)) n₀ (cupTgtUV X A U V n₀ t) = 0 :=
  Work.Cohomology.relDiffLM_relMapLM (R := ℚ) (X₁ := TopCat.of ↥(U ∩ V))
    (X₂ := TopCat.of ↥U) (A₁ := Work.Cohomology.interAU A (U ∩ V))
    (A₂ := Work.Cohomology.interAU A U)
    (f := Work.Cohomology.pdIncl U (U ∩ V) Set.inter_subset_left)
    (h := Work.Cohomology.interAU_incl_pdIncl_U X A U V) (n := n₀) (cupTgtU X A U n₀ t)
    (cupTgtU_cocycle X A U n₀ t ht)

/-! ## §2. The four chain maps -/

/-- The cup with the restriction of the cocycle to `(X,A)`. -/
noncomputable def cupTop (X : TopCat) (A : Set X) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ X A n₀)
    (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0) :
    Work.Cohomology.relComplex ℚ X (∅ : Set X) ⟶
      MVShift.shK (Work.Cohomology.relComplex ℚ X A) n₀ :=
  cupRelChain X A n₀ t ht

/-- The cup with the restriction of the cocycle to `(U, A ∩ U)`. -/
noncomputable def cupTopU (X : TopCat) (A : Set X) (U : Set X) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ X A n₀)
    (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0) :
    Work.Cohomology.relComplex ℚ (TopCat.of ↥U) (Work.Cohomology.interAU (∅ : Set X) U) ⟶
      MVShift.shK (Work.Cohomology.relComplex ℚ (TopCat.of ↥U)
        (Work.Cohomology.interAU A U)) n₀ :=
  cupRelChain (TopCat.of ↥U) (Work.Cohomology.interAU A U) n₀
    (cupTgtU X A U n₀ t) (cupTgtU_cocycle X A U n₀ t ht)

/-- The cup with the restriction of the cocycle to `(V, A ∩ V)`. -/
noncomputable def cupTopV (X : TopCat) (A : Set X) (V : Set X) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ X A n₀)
    (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0) :
    Work.Cohomology.relComplex ℚ (TopCat.of ↥V) (Work.Cohomology.interAU (∅ : Set X) V) ⟶
      MVShift.shK (Work.Cohomology.relComplex ℚ (TopCat.of ↥V)
        (Work.Cohomology.interAU A V)) n₀ :=
  cupRelChain (TopCat.of ↥V) (Work.Cohomology.interAU A V) n₀
    (cupTgtU X A V n₀ t) (cupTgtU_cocycle X A V n₀ t ht)

/-- The cup with the restriction of the cocycle to `(U ∩ V, A ∩ U ∩ V)`. -/
noncomputable def cupTopUV (X : TopCat) (A : Set X) (U : Set X) (V : Set X) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ X A n₀)
    (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0) :
    Work.Cohomology.relComplex ℚ (TopCat.of ↥(U ∩ V))
      (Work.Cohomology.interAU (∅ : Set X) (U ∩ V)) ⟶
      MVShift.shK (Work.Cohomology.relComplex ℚ (TopCat.of ↥(U ∩ V))
        (Work.Cohomology.interAU A (U ∩ V))) n₀ :=
  cupRelChain (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) n₀
    (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)

/-- The middle component: the biproduct of the two cups with the restrictions of the cocycle. -/
noncomputable def cupMid (X : TopCat) (A : Set X) (U : Set X) (V : Set X) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ X A n₀)
    (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0) :
    (Work.Cohomology.relComplex ℚ (TopCat.of ↥U) (Work.Cohomology.interAU (∅ : Set X) U) ⊞
        Work.Cohomology.relComplex ℚ (TopCat.of ↥V)
          (Work.Cohomology.interAU (∅ : Set X) V)) ⟶
      MVShift.shK (Work.Cohomology.relComplex ℚ (TopCat.of ↥U)
          (Work.Cohomology.interAU A U) ⊞
        Work.Cohomology.relComplex ℚ (TopCat.of ↥V)
          (Work.Cohomology.interAU A V)) n₀ :=
  biprod.desc
    (cupTopU X A U n₀ t ht ≫ MVShift.shMap
      (biprod.inl : Work.Cohomology.relComplex ℚ (TopCat.of ↥U)
          (Work.Cohomology.interAU A U) ⟶
        (Work.Cohomology.relComplex ℚ (TopCat.of ↥U) (Work.Cohomology.interAU A U) ⊞
          Work.Cohomology.relComplex ℚ (TopCat.of ↥V)
            (Work.Cohomology.interAU A V))) n₀)
    (cupTopV X A V n₀ t ht ≫ MVShift.shMap
      (biprod.inr : Work.Cohomology.relComplex ℚ (TopCat.of ↥V)
          (Work.Cohomology.interAU A V) ⟶
        (Work.Cohomology.relComplex ℚ (TopCat.of ↥U) (Work.Cohomology.interAU A U) ⊞
          Work.Cohomology.relComplex ℚ (TopCat.of ↥V)
            (Work.Cohomology.interAU A V))) n₀)

/-! ## §3. Elementary shift/biproduct calculus -/

theorem shMap_add {K L : CochainComplex (ModuleCat ℚ) ℕ} (f g : K ⟶ L) (n : ℕ) :
    MVShift.shMap (f + g) n = MVShift.shMap f n + MVShift.shMap g n := by
  apply HomologicalComplex.hom_ext
  intro i
  rfl

theorem shMap_neg {K L : CochainComplex (ModuleCat ℚ) ℕ} (f : K ⟶ L) (n : ℕ) :
    MVShift.shMap (-f) n = -MVShift.shMap f n := by
  apply HomologicalComplex.hom_ext
  intro i
  rfl

end

end Work.Serre
