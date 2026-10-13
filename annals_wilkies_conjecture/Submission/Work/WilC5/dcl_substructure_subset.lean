import Mathlib
import Submission.Work.WilC5.ExpLog
import Submission.Work.WilC5.Reduct
import Submission.Work.WilC5.ReductEmb
import Submission.Work.WilC2.Dcl
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilC5.dcl_image_of_elementary

namespace Work.WilC5

open FirstOrder Language

set_option linter.style.haveILetI false

/-- **A model of `TE` is closed under definable closure in its `rexp`-reduct.**

Let `F ⊆ K` be an `LEc`-substructure of a model `K ⊨ TE` which is itself a model of `TE`
(hypothesis `hF`).  Then the `LRc`-definable closure of `F` inside the `rexp`-reduct
`reductStruct K` contains no point outside `F`.

The proof has three ingredients:
* the inclusion `F → K` is an `LEc`-embedding, hence (by `ReductEmb`) an `LRc`-embedding of the
  `rexp`-reducts;
* both `rexp`-reducts are models of `TR` (`reduct_model_TR`), so model completeness of `TR`
  (`hMCr`) makes that embedding *elementary*;
* an elementary embedding preserves closure under definable closure
  (`dcl_image_of_elementary`), applied to the trivially `dcl`-closed set `univ ⊆ F`.  The image of
  `univ` is exactly the carrier `F ⊆ K`. -/
theorem dcl_substructure_subset
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    {K : Type} [WilkiesDesign.CG.LEc.Structure K]
    (hK : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (F : WilkiesDesign.CG.LEc.Substructure K) (hF : (F : Type) ⊨ WilkiesDesign.CG.TE) :
    @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) (F : Set K) ⊆ (F : Set K) := by
  -- The inclusion `F ↪ K` of `LEc`-structures, transported to the `rexp`-reducts.
  obtain ⟨fR, hfR⟩ := ReductEmb (M := F) (N := K) hF hK (Substructure.subtype F)
  -- Name the `LRc`-structures on `F` and `K` so that the instances line up with `hMCr`.
  letI : WilkiesDesign.CG.LRc.Structure F := reductStruct F
  letI : WilkiesDesign.CG.LRc.Structure K := reductStruct K
  haveI hFTR := reduct_model_TR F hF
  haveI hKTR := reduct_model_TR K hK
  -- Model completeness of `TR` promotes the inclusion to an elementary embedding.
  let helem : @ElementaryEmbedding WilkiesDesign.CG.LRc F K
      (reductStruct F) (reductStruct K) :=
    { toFun := (fR : F → K)
      map_formula' := fun _ φ x => hMCr (M := F) (N := K) fR φ x }
  -- An elementary embedding preserves `dcl`-closedness; `univ` is trivially `dcl`-closed.
  have hsub : @Work.WilC2.Dcl K (reductStruct K)
      ((⇑helem : F → K) '' (Set.univ : Set F)) ⊆ (⇑helem : F → K) '' (Set.univ : Set F) :=
    @dcl_image_of_elementary F K (reductStruct F) (reductStruct K) helem (Set.univ : Set F)
      (fun _ _ => Set.mem_univ _)
  -- The image of `univ` under the inclusion is the carrier `F`.
  have himg : (⇑helem : F → K) '' (Set.univ : Set F) = (F : Set K) := by
    have h1 : (⇑helem : F → K) = (fR : F → K) := rfl
    rw [h1, hfR, Substructure.coe_subtype, Subtype.coe_image_univ]
  rwa [himg] at hsub

end Work.WilC5
