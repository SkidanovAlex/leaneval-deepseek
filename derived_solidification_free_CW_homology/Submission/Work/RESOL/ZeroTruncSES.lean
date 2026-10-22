/-
AREA RESOL — the truncation step of the filtration induction and the degree comparisons.

* `Zero.truncShortComplex_shortExact` : the target-side short exact sequence
  `0 ⟶ trunc j B ⟶ trunc (j-1) B ⟶ single (j-1) (B.X (j-1)) ⟶ 0` of the brutal truncation
  (`solidCofibrant_trunc.lean`), short exact because it is split in every degree;
* `Zero.quasiIsoAt_truncIncl` : `trunc j B ⟶ B` is a quasi-isomorphism in degrees `≥ j`;
* `Zero.cutInclTopFam`, `Zero.cutInclTop` : the inclusion of the columns `≥ k` into all columns
  and `Zero.quasiIsoAt_cutInclTop` : it is a quasi-isomorphism in degrees `≥ k + 1`;
* `Zero.epsCutFam`, `Zero.epsCut` : the degreewise augmentation `totCut k B ⟶ trunc k B`.

The chain-map properties `Zero.cutInclTopFam_comm` and `Zero.epsCutFam_comm` are stated in the
form of degreewise component identities, so that the statements are about the component families
(which are plain `Sigma.desc`/`Sigma.ι` expressions without proofs).
-/
import Mathlib
import Submission.Work.RESOL.ZeroCut
import Submission.Work.RESOL.solidCofibrant_trunc
import Submission.Work.RESOL.exists_windowTower
import Submission.Work.RESOL.isIso_sigmaDesc_of_zero_complement
import Submission.Work.RESOL.TruncBounded

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

/-! ## The target-side short exact sequence -/

/-- The truncation step `0 ⟶ trunc j B ⟶ trunc (j-1) B ⟶ single (j-1) (B.X (j-1)) ⟶ 0` is short
exact. -/
theorem truncShortComplex_shortExact (B : Cpx) (j : ℤ) :
    (truncShortComplex B j).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (truncSplitting B j n).shortExact)

/-- **The target-side comparison.**  The inclusion `trunc j B ⟶ B` induces an isomorphism on
homology in all degrees `≥ j + 1`. -/
theorem quasiIsoAt_truncIncl (B : Cpx) (j : ℤ) {n : ℤ} (hn : j + 1 ≤ n) :
    QuasiIsoAt (truncIncl B j) n :=
  quasiIsoAt_of_isIso_f (truncIncl B j) n
    (isIso_truncIncl_f B j (by omega)) (isIso_truncIncl_f B j (by omega))
    (isIso_truncIncl_f B j (by omega))

/-! ## The inclusion of the columns `≥ k` into all the columns -/

/-- The differential of the total complex of all the columns in adjacent degrees. -/
theorem totFull_d_eq (B : Cpx) (n : ℤ) :
    (totFull F π hπ B).d n (n + 1) = totDc F π hπ topP topP_step B n := by
  rw [show (totFull F π hπ B).d n (n + 1) = dite (n + 1 = n + 1)
    (fun h => totD F π hπ topP topP_step B n (n + 1) h) (fun _ => 0) from rfl,
    dite_eq_left rfl]
  rfl

/-- The inclusion of the columns `≥ k` into all the columns, in degree `n`. -/
def cutInclTopFam (k : ℤ) (B : Cpx) (n : ℤ) :
    (totCut F π hπ k B).X n ⟶ (totFull F π hπ B).X n :=
  Sigma.desc (fun x : TotIdx (geP k) n =>
    Sigma.ι (totFam F π hπ topP B n) ⟨x.1, ⟨x.2.1, trivial⟩⟩)

/-- The component formula for `cutInclTopFam`. -/
lemma cutInclTopFam_ι (k : ℤ) (B : Cpx) (n : ℤ) (x : TotIdx (geP k) n) :
    Sigma.ι (totFam F π hπ (geP k) B n) x ≫ cutInclTopFam F π hπ k B n
      = Sigma.ι (totFam F π hπ topP B n) ⟨x.1, ⟨x.2.1, trivial⟩⟩ :=
  Sigma.ι_comp_desc _ x

/-! ## The augmentation `totCut k B ⟶ trunc k B` -/

/-- The degreewise augmentation of the columns `≥ k` onto the brutal truncation, in degree `n`:
the summands with resolution degree `0` are augmented, the others are killed. -/
def epsCutFam (k : ℤ) (B : Cpx) (n : ℤ) :
    (totCut F π hπ k B).X n ⟶ (trunc k B).X n :=
  Sigma.desc (fun x : TotIdx (geP k) n =>
    if h : x.1.2 = 0 then
      (((Rco F π hπ).obj (B.X x.1.1)).XIsoOfEq h).hom
        ≫ aug0 F π hπ (B.X x.1.1)
        ≫ eqToHom (by
            have h2 : x.1.1 = n := by have h3 := x.2.1; omega
            exact (trunc_X_of_le B k x.2.2).symm.trans
              (congrArg (fun m => (trunc k B).X m) h2))
    else 0)

/-- The component formula for `epsCutFam`. -/
lemma epsCutFam_ι (k : ℤ) (B : Cpx) (n : ℤ) (x : TotIdx (geP k) n) :
    Sigma.ι (totFam F π hπ (geP k) B n) x ≫ epsCutFam F π hπ k B n
      = (if h : x.1.2 = 0 then
          (((Rco F π hπ).obj (B.X x.1.1)).XIsoOfEq h).hom
            ≫ aug0 F π hπ (B.X x.1.1)
            ≫ eqToHom (by
                have h2 : x.1.1 = n := by have h3 := x.2.1; omega
                exact (trunc_X_of_le B k x.2.2).symm.trans
                  (congrArg (fun m => (trunc k B).X m) h2))
        else 0) :=
  Sigma.ι_comp_desc _ x

end Zero

end Work.RESOL

end
