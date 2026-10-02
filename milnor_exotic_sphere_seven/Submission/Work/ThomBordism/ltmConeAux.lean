import Submission.Work.ThomBordism.localThom_iUnion_aux
import Submission.Work.ThomBordism.chartDescentEngine

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# Auxiliaries for `localThomMap_bijective_of_coneData`

This module collects the small lemmas about the class/coboundary dictionary of
`Work.ThomBordism.localThom_iUnion_aux` that the cone-to-quasi-isomorphism argument
(`Work.ThomBordism.localThomMap_bijective_of_coneData`) needs:

* `pdCohMap_preim_self` — the restriction of a piece class to the piece itself is the identity;
* `totShiftD_eq_zero_of_relDiffLM` — a relative cocycle is a `totShiftD`-cycle;
* `psiAbs_relDiff_zero` — `psiAbs` of a base cocycle is a relative cocycle;
* `relClassOf_eq_of_sub_eq_d` — two relative cocycles whose difference is a differential have
  the same class.
-/

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

namespace Work.ThomBordism

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **The restriction of a piece class to the piece itself is the identity.** -/
theorem pdCohMap_preim_self (Z : RealBundle B F ι) (n : ℕ) (U : Set B)
    (τ : Work.Thom.PieceCoh Z U n) :
    (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
      (Z.proj ⁻¹' U) (Z.proj ⁻¹' U) (Set.preimage_mono (fun x hx => hx)) n).hom τ = τ :=
  pdCohMap_self (X := TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' U)
    (Set.preimage_mono (fun x hx => hx)) n τ

/-- A relative cocycle is a `totShiftD`-cycle. -/
theorem totShiftD_eq_zero_of_relDiffLM (Z : RealBundle B F ι) (W : Set B) (n m : ℕ)
    (x : TotC Z W (m + n))
    (h : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (m + n) x = 0) :
    totShiftD Z n W m x = 0 := by
  rw [totShiftD_eq_relDiffLM, h]
  exact totC_cast_zero Z W _

/-- **`psiAbs` of a base cocycle is a relative cocycle.** -/
theorem psiAbs_relDiff_zero (Z : RealBundle B F ι) (n : ℕ) (U : Set B)
    (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U) (m : ℕ) (a : BaseC W m)
    (ha : cochainDiff ℤ (baseSSet W) a = 0) :
    relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (m + n)
      (psiAbs Z n U τ W hW m a) = 0 := by
  have h := psiAbs_relDiff Z n U τ W hW m a
  rw [ha] at h
  rw [show psiAbs Z n U τ W hW (m + 1) (0 : BaseC W (m + 1)) = 0 from
    map_zero (psiAbsLM Z n U τ W hW (m + 1))] at h
  exact h.trans (totC_cast_zero Z W (Nat.add_right_comm m 1 n))

/-- **Two relative cocycles whose difference is a differential have the same class.**

This is the "class" half of the class/coboundary dictionary in the indexing of the cone: if
`z - z'` is the differential `C.d i j` of `w`, then the classes of `z` and `z'` agree.  (The
existing lemmas `exists_totShiftD_of_relClass_eq` and friends only run in the *other* direction,
from an equality of classes to a primitive.) -/
theorem relClassOf_eq_of_sub_eq_d (Z : RealBundle B F ι) (W : Set B) (i j : ℕ)
    (z z' : TotC Z W j) (w : TotC Z W i)
    (hz : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) j z = 0)
    (hz' : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) j z' = 0)
    (h : z - z' = ((TotComplex Z W).d i j).hom w) :
    relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz
      = relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z' hz' := by
  have hsub : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) j (z - z') = 0 := by
    rw [map_sub, hz, hz', sub_self]
  have hcyc : relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (z - z') hsub
      = (relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)).toCycles i j w := by
    apply iCycles_injective_K (relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)) j
    rw [iCycles_relCocycleOf, iCycles_toCycles', h]
    rfl
  have hzero : relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (z - z') hsub = 0 := by
    rw [relClassOf_eq_homologyπ' Z W j (z - z') hsub, hcyc]
    exact cochain_homologyπ_toCycles_eq_zero
      (C := relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)) i j w
  have hsubcyc : relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (z - z') hsub
      = relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz
        - relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z' hz' := by
    apply iCycles_injective_K (relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)) j
    rw [map_sub, iCycles_relCocycleOf, iCycles_relCocycleOf, iCycles_relCocycleOf]
  have h1 : relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz
        - relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z' hz'
      = relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (z - z') hsub := by
    rw [relClassOf_eq_homologyπ' Z W j z hz, relClassOf_eq_homologyπ' Z W j z' hz',
      relClassOf_eq_homologyπ' Z W j (z - z') hsub, ← map_sub, hsubcyc]
  exact sub_eq_zero.mp (by rw [h1, hzero])

end

end Work.ThomBordism
