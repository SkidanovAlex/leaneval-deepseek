import Mathlib
import Submission.Work.WilC5.S4StepNewSetup
import Submission.Work.WilC5.DclExtension
import Submission.Work.WilC5.DclExtensionCast

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- The `LRc`-structure synthesised by Mathlib from the ordered-field data, written with the
*explicit* ring part `Ring.CompatibleRing.toStructure`.  This is the structure at which
`Work.WilC5.DclExtension` and the whole cut/o-minimality chain of area C5 are stated. -/
abbrev canonTS (K : Type) [LEc.Structure K] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Ring.CompatibleRing K] : LRc.Structure K :=
  @Language.withConstantsStructure LR K
    (@Language.sumStructure Language.ring rexpL K
      (Ring.CompatibleRing.toStructure (self := (inferInstance : Ring.CompatibleRing K)))
      (inferInstance : rexpL.Structure K))
    ℝ (inferInstance : (constantsOn ℝ).Structure K)

/-- The statement of `DclExtensionReduct` with the alignment hypothesis that the statement as
requested is missing: the `rexp`-reduct must be recognised as the canonical structure. -/
theorem DclExtensionReductAlign
    {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    (hstrK : (Work.WilC5.reductStruct K : LRc.Structure K) = canonTS K)
    (hstrL : (Work.WilC5.reductStruct L : LRc.Structure L) = canonTS L)
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels)
    (hKTR : K ⊨ WilkiesDesign.CG.TR) (hLTR : L ⊨ WilkiesDesign.CG.TR)
    (F : WilkiesDesign.CG.LRc.Substructure K) (hF : ↥F ⊨ WilkiesDesign.CG.TR)
    (hFdcl : @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) (F : Set K) ⊆ (F : Set K))
    (σ : WilkiesDesign.CG.LRc.Embedding ↥F L) {x : K} {y : L}
    (hcut : (∀ f : ↥F, ((f : K) < x ↔ (σ f : L) < y)) ∧
      (∀ f : ↥F, (x < (f : K) ↔ y < (σ f : L)))) :
    ∃ (S : WilkiesDesign.CG.LRc.Substructure K)
      (hS : (S : Set K) = @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) ((F : Set K) ∪ {x}))
      (hSdcl : @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) (S : Set K) ⊆ (S : Set K))
      (hle : F ≤ S) (hxS : x ∈ (S : Set K)),
      ∃ σ' : WilkiesDesign.CG.LRc.Embedding ↥S L,
        (∀ f : ↥F, σ' ⟨(f : K), hle f.2⟩ = σ f) ∧ σ' ⟨x, hxS⟩ = y := by
  classical
  have hK : (Work.WilC5.reductStruct K : LRc.Structure K) = canonTS K := hstrK
  have hL : (Work.WilC5.reductStruct L : LRc.Structure L) = canonTS L := hstrL
  let F' : @LRc.Substructure K (canonTS K) :=
    SubCast (Work.WilC5.reductStruct K) (canonTS K) hK F
  have hF' : @Theory.Model LRc ↥F' (@Substructure.inducedStructure LRc K (canonTS K) F') TR := by
    rw [induced_SubCast (Work.WilC5.reductStruct K) (canonTS K) hK F]
    exact hF
  have hFdcl' : @Work.WilC2.Dcl K (canonTS K) (F' : Set K) ⊆ (F' : Set K) := by
    intro z hz
    have hz' : z ∈ @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) (F : Set K) := by
      rw [Dcl_congr hK (F : Set K)]
      exact hz
    exact hFdcl hz'
  let σ' : @Embedding LRc ↥F' L (@Substructure.inducedStructure LRc K (canonTS K) F')
      (canonTS L) :=
    EmbCast (@Substructure.inducedStructure LRc K (canonTS K) F')
      (@Substructure.inducedStructure LRc K (Work.WilC5.reductStruct K) F)
      (canonTS L) (Work.WilC5.reductStruct L)
      (induced_SubCast (Work.WilC5.reductStruct K) (canonTS K) hK F)
      hL.symm σ
  have hcut' : (∀ f : ↥F', ((f : K) < x ↔ (σ' f : L) < y)) ∧
      (∀ f : ↥F', (x < (f : K) ↔ y < (σ' f : L))) :=
    ⟨fun f => hcut.1 f, fun f => hcut.2 f⟩
  haveI hKcanon : @Theory.Model LRc K (canonTS K) TR := by rw [← hK]; exact hKTR
  haveI hLcanon : @Theory.Model LRc L (canonTS L) TR := by rw [← hL]; exact hLTR
  obtain ⟨S', hS', hSdcl', hle', hxS', σ'', hσ''F, hσ''x⟩ :=
    DclExtension (K := K) (L := L) hMCr hOM F' hF' hFdcl' σ' hcut'
  refine ⟨SubCast (canonTS K) (Work.WilC5.reductStruct K) hK.symm S', ?_, ?_, ?_, ?_, ?_⟩
  · calc (SubCast (canonTS K) (Work.WilC5.reductStruct K) hK.symm S' : Set K)
        = (S' : Set K) := rfl
      _ = @Work.WilC2.Dcl K (canonTS K) ((F' : Set K) ∪ {x}) := hS'
      _ = @Work.WilC2.Dcl K (canonTS K) ((F : Set K) ∪ {x}) := rfl
      _ = @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) ((F : Set K) ∪ {x}) :=
            (Dcl_congr hK ((F : Set K) ∪ {x})).symm
  · intro z hz
    have hz' : z ∈ @Work.WilC2.Dcl K (canonTS K) (S' : Set K) := by
      rw [← Dcl_congr hK (S' : Set K)]
      exact hz
    exact hSdcl' hz'
  · exact hle'
  · exact hxS'
  · refine ⟨EmbCast (@Substructure.inducedStructure LRc K (Work.WilC5.reductStruct K)
        (SubCast (canonTS K) (Work.WilC5.reductStruct K) hK.symm S'))
      (@Substructure.inducedStructure LRc K (canonTS K) S')
      (Work.WilC5.reductStruct L) (canonTS L)
      (induced_SubCast (canonTS K) (Work.WilC5.reductStruct K) hK.symm S')
      hL σ'', ?_, ?_⟩
    · intro f
      exact hσ''F f
    · exact hσ''x

end Work.WilC5
