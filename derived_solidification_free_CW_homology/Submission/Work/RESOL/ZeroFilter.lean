/-
AREA RESOL — the column filtration argument: `Zero.eps : Zero.R ⟶ 𝟭 Cpx` is a
quasi-isomorphism on bounded-above complexes.

For a complex `B` bounded above (`B.X q = 0` for `q > b`) the augmentation
`Zero.eps.app B : Zero.totFull B ⟶ B` of the total complex of the column-wise resolutions is
compared with the *column filtration*

`0 ⟶ totCut j B ⟶ totCut (j-1) B ⟶ colCpx (j-1) B ⟶ 0`

(`RESOL/ZeroCutJ.lean` for the `j`-indexed inclusion `cutJ` and its retraction `cutRetrJ`) and
the target-side stupid truncation sequence `truncShortComplex B j`
(`RESOL/solidCofibrant_trunc.lean`), the vertical maps being the degreewise augmentations
`epsCutFam j` (the columns `q ≥ j` onto the truncation `trunc j B`) and the augmentation of the
`(j-1)`-st column `colAugFam (j-1)`.

The main steps:

* `Zero.srcSES_shortExact`: the source-side sequence is short exact (in fact split in every
  degree, with the explicit retraction `cutRetrJ` and section `colSectFam`);
* `Zero.phiJ`: the morphism of short complexes
  `(totCut j → totCut (j-1) → colCpx (j-1)) ⟶ (trunc j → trunc (j-1) → single (j-1) B.X(j-1))`
  with components `epsCut j`, `epsCut (j-1)`, `colAug (j-1)` (the two commuting squares are
  `zPhiComm12` and `zPhiComm23`);
* `Zero.quasiIso_epsCutCh_of_ge`: the base case `j ≥ b+1`, where both complexes have all terms
  zero;
* `Zero.quasiIso_epsCutCh_le`: the descending induction, using the five lemma
  (`quasiIso_middle_of_shortExact`) and the quasi-isomorphism `colAug (j-1)`;
* `Zero.quasiIso_eps_of_boundedAbove`: the comparison of `epsCut k` with `eps` through the
  inclusions `cutTop k : totCut k B ⟶ totFull B` and `truncToSelf k : trunc k B ⟶ B`, both of
  which are isomorphisms on homology in degrees `≥ k+1`.
-/
import Mathlib
import Submission.Work.RESOL.ZeroCutJ
import Submission.Work.RESOL.zCutIncComm
import Submission.Work.RESOL.zCutColProjComm
import Submission.Work.RESOL.zCutSplittingData
import Submission.Work.RESOL.zCutInclTopFamComm
import Submission.Work.RESOL.zEpsCutFamComm
import Submission.Work.RESOL.zColAug
import Submission.Work.RESOL.zIsIsoCutInclTopFam
import Submission.Work.RESOL.zCutEpsComm
import Submission.Work.RESOL.zIsZeroCutX
import Submission.Work.RESOL.zPhiComm12
import Submission.Work.RESOL.zPhiComm23
import Submission.Work.RESOL.quasiIso_middle_of_shortExact
import Submission.Work.RESOL.solidCofibrant_trunc

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Work.RESOL

namespace Zero

variable (F : LightCondAb ⥤ LightCondAb) [F.PreservesZeroMorphisms] (π : F ⟶ 𝟭 LightCondAb)
  (hπ : ∀ M, Epi (π.app M))

/-! ## The chain maps of the filtration step -/

/-- The inclusion of the columns `q ≥ j` into the columns `q ≥ j-1`, as a chain map. -/
def cutJCh (j : ℤ) (B : Cpx) : totCut F π hπ j B ⟶ totCut F π hπ (j - 1) B where
  f n := cutJ F π hπ j B n
  comm' i m him := cutJ_comm F π hπ j B him

/-- The projection onto the `k`-th column, as a chain map. -/
def colProjCh (k : ℤ) (B : Cpx) : totCut F π hπ k B ⟶ colCpx F π hπ k B where
  f n := colProjFam F π hπ k B n
  comm' i m him := zCutColProjComm F π hπ k B i m him

/-- The augmentation of the columns `q ≥ k` onto the truncation, as a chain map. -/
def epsCutCh (k : ℤ) (B : Cpx) : totCut F π hπ k B ⟶ trunc k B where
  f n := epsCutFam F π hπ k B n
  comm' i m him := zEpsCutFamComm F π hπ k B him

/-- The inclusion of the columns `q ≥ k` into all the columns, as a chain map. -/
def cutTopCh (k : ℤ) (B : Cpx) : totCut F π hπ k B ⟶ totFull F π hπ B where
  f n := cutInclTopFam F π hπ k B n
  comm' i m him := zCutInclTopFamComm F π hπ k B him

/-- The augmentation of the `k`-th column, as a chain map (the chain map whose existence is
`zColAug`). -/
noncomputable def colAugCh (k : ℤ) (B : Cpx) : colCpx F π hπ k B ⟶
    (HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) k).obj (B.X k) :=
  (zColAug F π hπ k B).choose

/-- The degreewise components of `colAugCh` are the components `colAugFam`. -/
lemma colAugCh_f (k : ℤ) (B : Cpx) (n : ℤ) :
    (colAugCh F π hπ k B).f n = colAugFam F π hπ k B n :=
  (zColAug F π hπ k B).choose_spec.1 n

/-- The augmentation of a column is a quasi-isomorphism. -/
theorem quasiIso_colAugCh (k : ℤ) (B : Cpx) : QuasiIso (colAugCh F π hπ k B) :=
  (zColAug F π hπ k B).choose_spec.2

/-! ## The source-side short exact sequence -/

/-- The source-side filtration step `0 ⟶ totCut j B ⟶ totCut (j-1) B ⟶ colCpx (j-1) B ⟶ 0`. -/
def srcSES (j : ℤ) (B : Cpx) : ShortComplex Cpx :=
  ShortComplex.mk (cutJCh F π hπ j B) (colProjCh F π hπ (j - 1) B)
    (HomologicalComplex.hom_ext _ _ (fun n => by
      rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
      exact cutJ_comp_colProjFam F π hπ j B n))

/-- The source-side filtration step is short exact: it is split in every degree, with retraction
`cutRetrJ` of the inclusion `cutJ` and section `colSectFam` of the projection `colProjFam`. -/
theorem srcSES_shortExact (j : ℤ) (B : Cpx) : (srcSES F π hπ j B).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => ?_)
  refine ShortComplex.Splitting.shortExact (S := (srcSES F π hπ j B).map
    (HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) n)) ?_
  refine ShortComplex.Splitting.mk (cutRetrJ F π hπ j B n) (colSectFam F π hπ (j - 1) B n)
    ?_ ?_ ?_
  · show CategoryTheory.CategoryStruct.comp (cutJ F π hπ j B n) (cutRetrJ F π hπ j B n)
      = 𝟙 ((totCut F π hπ j B).X n)
    exact cutJ_comp_cutRetrJ F π hπ j B n
  · show CategoryTheory.CategoryStruct.comp (colSectFam F π hπ (j - 1) B n)
        (colProjFam F π hπ (j - 1) B n) = 𝟙 ((colCpx F π hπ (j - 1) B).X n)
    exact colSectFam_comp_colProjFam F π hπ (j - 1) B n
  · show CategoryTheory.CategoryStruct.comp (cutRetrJ F π hπ j B n) (cutJ F π hπ j B n)
        + CategoryTheory.CategoryStruct.comp (colProjFam F π hπ (j - 1) B n)
          (colSectFam F π hπ (j - 1) B n) = 𝟙 ((totCut F π hπ (j - 1) B).X n)
    exact cutRetrJ_comp_cutJ_add F π hπ j B n

/-! ## The morphism of short exact sequences -/

/-- The morphism of short complexes comparing the column filtration step with the truncation
step: `totCut j B ⟶ trunc j B`, `totCut (j-1) B ⟶ trunc (j-1) B` and
`colCpx (j-1) B ⟶ single (j-1) (B.X (j-1))`. -/
noncomputable def phiJ (j : ℤ) (B : Cpx) :
    srcSES F π hπ j B ⟶ truncShortComplex B j where
  τ₁ := epsCutCh F π hπ j B
  τ₂ := epsCutCh F π hπ (j - 1) B
  τ₃ := colAugCh F π hπ (j - 1) B
  comm₁₂ := HomologicalComplex.hom_ext _ _ (fun n => by
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    exact zPhiComm12 F π hπ j B n)
  comm₂₃ := HomologicalComplex.hom_ext _ _ (fun n => by
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, colAugCh_f]
    exact zPhiComm23 F π hπ j B n)

/-! ## The base case and the induction -/

/-- **Base case.** If `B.X q = 0` for all `q > b` and `j ≥ b+1`, then both `totCut j B` and
`trunc j B` have all their terms zero, hence `epsCut j` is a quasi-isomorphism. -/
theorem quasiIso_epsCutCh_of_ge (B : Cpx) (b j : ℤ) (hj : b + 1 ≤ j)
    (hB : ∀ q : ℤ, b < q → IsZero (B.X q)) : QuasiIso (epsCutCh F π hπ j B) := by
  obtain ⟨hcut, htrunc⟩ := zIsZeroCutX F π hπ B b j hj hB
  rw [quasiIso_iff]
  intro n
  refine quasiIsoAt_of_isIso_f _ n ?_ ?_ ?_
  · exact IsZero.isIso (hcut _) (htrunc _) _
  · exact IsZero.isIso (hcut _) (htrunc _) _
  · exact IsZero.isIso (hcut _) (htrunc _) _

/-- **Induction step.** If `epsCut j` is a quasi-isomorphism, then so is `epsCut (j-1)`: this is
the five lemma applied to the morphism `phiJ j` of short exact sequences, whose first and third
vertical maps are quasi-isomorphisms. -/
theorem quasiIso_epsCutCh_pred (B : Cpx) (j : ℤ) (h : QuasiIso (epsCutCh F π hπ j B)) :
    QuasiIso (epsCutCh F π hπ (j - 1) B) :=
  quasiIso_middle_of_shortExact (srcSES_shortExact F π hπ j B)
    (truncShortComplex_shortExact B j) (phiJ F π hπ j B) h
    (quasiIso_colAugCh F π hπ (j - 1) B)

/-- **The filtration.** For `B` vanishing above `b` and every `j ≤ b+1`, the augmentation
`epsCut j : totCut j B ⟶ trunc j B` is a quasi-isomorphism. -/
theorem quasiIso_epsCutCh_le (B : Cpx) (b j : ℤ) (hj : j ≤ b + 1)
    (hB : ∀ q : ℤ, b < q → IsZero (B.X q)) : QuasiIso (epsCutCh F π hπ j B) := by
  have hmain : ∀ m : ℕ, QuasiIso (epsCutCh F π hπ (b + 1 - ((m : ℕ) : ℤ)) B) := by
    intro m
    induction m with
    | zero =>
      have h0 : b + 1 - (((0 : ℕ) : ℤ)) = b + 1 := by omega
      rw [h0]
      exact quasiIso_epsCutCh_of_ge F π hπ B b (b + 1) le_rfl hB
    | succ m ih =>
      have h1 : b + 1 - (((m : ℕ) : ℤ)) - 1 = b + 1 - (((m + 1 : ℕ)) : ℤ) := by omega
      rw [← h1]
      exact quasiIso_epsCutCh_pred F π hπ B (b + 1 - (((m : ℕ)) : ℤ)) ih
  have hnonneg : (0 : ℤ) ≤ b + 1 - j := by omega
  have hm : ((((b + 1 - j).toNat : ℕ)) : ℤ) = b + 1 - j := Int.toNat_of_nonneg hnonneg
  have hjm : b + 1 - ((((b + 1 - j).toNat : ℕ)) : ℤ) = j := by omega
  rw [← hjm]
  exact hmain _

/-- **The filtration, all cuts.** For `B` vanishing above `b`, every cut augmentation
`epsCut j : totCut j B ⟶ trunc j B` is a quasi-isomorphism. -/
theorem quasiIso_epsCutCh (B : Cpx) (b : ℤ) (hB : ∀ q : ℤ, b < q → IsZero (B.X q))
    (j : ℤ) : QuasiIso (epsCutCh F π hπ j B) := by
  by_cases hj : b + 1 ≤ j
  · exact quasiIso_epsCutCh_of_ge F π hπ B b j hj hB
  · exact quasiIso_epsCutCh_le F π hπ B b j (by omega) hB

/-- **The comparison at the top.** The inclusion `cutTop k : totCut k B ⟶ totFull B` is an
isomorphism on homology in all degrees `≥ k+1`. -/
theorem quasiIsoAt_cutTopCh (k : ℤ) (B : Cpx) {n : ℤ} (hn : k + 1 ≤ n) :
    QuasiIsoAt (cutTopCh F π hπ k B) n :=
  quasiIsoAt_of_isIso_f _ n
    (zIsIsoCutInclTopFam F π hπ k B (n - 1) (by omega))
    (zIsIsoCutInclTopFam F π hπ k B n (by omega))
    (zIsIsoCutInclTopFam F π hπ k B (n + 1) (by omega))

/-- The square comparing the augmentation `eps` of the total complex with the cut at `k`:
restricting `eps` to the columns `q ≥ k` is the augmentation of the cut followed by the inclusion
of the truncation into `B`. -/
theorem cutTopCh_comp_eps (k : ℤ) (B : Cpx) :
    cutTopCh F π hπ k B ≫ (eps F π hπ).app B = epsCutCh F π hπ k B ≫ truncToSelf k B :=
  HomologicalComplex.hom_ext _ _ (fun n => by
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, truncToSelf_f]
    exact zCutEpsComm F π hπ k B n)

/-- **`eps` is a quasi-isomorphism on bounded-above complexes.** -/
theorem quasiIso_eps_of_boundedAbove (B : Cpx) (hB : IsBoundedAbove B) :
    QuasiIso ((eps F π hπ).app B) := by
  obtain ⟨b, hb⟩ := hB
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hcut := quasiIso_epsCutCh F π hπ B b hb (n - 1)
  rw [quasiIso_iff] at hcut
  have hsq := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (cutTopCh_comp_eps F π hπ (n - 1) B)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq
  haveI h1 : IsIso (HomologicalComplex.homologyMap (cutTopCh F π hπ (n - 1) B) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).mp
      (quasiIsoAt_cutTopCh F π hπ (n - 1) B (by omega))
  haveI h3 : IsIso (HomologicalComplex.homologyMap (truncToSelf (n - 1) B) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).mp
      (quasiIsoAt_truncToSelf (n - 1) B (by omega))
  haveI h2 : IsIso (HomologicalComplex.homologyMap (epsCutCh F π hπ (n - 1) B) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).mp (hcut n)
  haveI hcomp : IsIso (HomologicalComplex.homologyMap (cutTopCh F π hπ (n - 1) B) n
      ≫ HomologicalComplex.homologyMap ((eps F π hπ).app B) n) := by
    rw [hsq]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (HomologicalComplex.homologyMap (cutTopCh F π hπ (n - 1) B) n)
    (HomologicalComplex.homologyMap ((eps F π hπ).app B) n)

end Zero

end Work.RESOL

end
