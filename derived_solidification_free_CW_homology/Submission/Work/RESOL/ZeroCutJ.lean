/-
AREA RESOL — the column filtration step in the `j`-indexed form.

The filtration induction proving that `Zero.totFull B ⟶ B` is a quasi-isomorphism for `B`
bounded above compares the column cut

`0 ⟶ totCut j B ⟶ totCut (j-1) B ⟶ colCpx (j-1) B ⟶ 0`

(the columns `q ≥ j` inside the columns `q ≥ j-1`, the quotient being the `(j-1)`-st column)
with the target-side sequence `truncShortComplex B j` (`RESOL/solidCofibrant_trunc.lean`), whose
terms are `trunc j B`, `trunc (j-1) B` and `single (j-1) (B.X (j-1))`.

`Zero.cutIncFam k` (the inclusion of the columns `q ≥ k+1` into the columns `q ≥ k`,
`RESOL/ZeroCut.lean`) is indexed so that its *source* is `totCut (k+1) B`, which is not
syntactically `totCut j B`: `k + 1` and `j` are only propositionally equal, and `(k+1) - 1` is
not syntactically `k`.  To avoid transporting along integer equalities in every statement of the
induction, this file provides the same inclusion re-indexed by `j`:

* `Zero.cutJ j B : totCut j B ⟶ totCut (j-1) B` (the inclusion of the columns `q ≥ j`) with its
  retraction `Zero.cutRetrJ j B` (which kills the `(j-1)`-st column), their component formulas,
  the chain-map property `Zero.cutJ_comm` of `cutJ`, and the two splitting identities of the
  filtration step that involve them (`cutJ_comp_cutRetrJ`, `cutRetrJ_comp_cutJ_add`,
  `cutJ_comp_colProjFam`; the third splitting identity
  `colSectFam k ≫ colProjFam k = 𝟙` is `Zero.colSectFam_comp_colProjFam` at `k = j-1`).

The proofs are the exact analogues of `RESOL/zCutIncComm.lean` (chain-map property) and
`RESOL/zCutSplittingData.lean` (splitting identities), with `geP (k+1)` replaced by `geP j` and
`geP k` by `geP (j-1)`.

Finally, `Zero.truncToSelf k B : trunc k B ⟶ B` is the inclusion of the stupid truncation into
the original complex; its components are the components of `loId` (`loT`), the inclusion
constructed in `RESOL/exists_windowTower.lean`, so that
`Work.RESOL.quasiIsoAt_loId` gives its quasi-isomorphism property in high degrees.
-/
import Mathlib
import Submission.Work.RESOL.ZeroCut
import Submission.Work.RESOL.solidCofibrant_trunc
import Submission.Work.RESOL.exists_windowTower

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RESOL

/-- The identity of a coproduct is the `Sigma.desc` of its inclusions. -/
lemma sigma_desc_id {ι : Type*} {Y : ι → LightCondAb} [HasCoproduct Y] :
    Sigma.desc (fun i => Sigma.ι Y i) = 𝟙 (∐ Y) := by
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_comp_desc, Category.comp_id]

namespace Zero

variable (F : LightCondAb ⥤ LightCondAb) [F.PreservesZeroMorphisms] (π : F ⟶ 𝟭 LightCondAb)
  (hπ : ∀ M, Epi (π.app M))

/-! ## The inclusion of the columns `q ≥ j` into the columns `q ≥ j - 1` -/

/-- The index of `totCut j B` seen as an index of `totCut (j-1) B`. -/
def cutJIdx {j n : ℤ} (x : TotIdx (geP j) n) : TotIdx (geP (j - 1)) n :=
  ⟨x.1, x.2.1, by have h : j ≤ x.1.1 := x.2.2; omega⟩

/-- The inclusion of the columns `q ≥ j` into the columns `q ≥ j - 1`, in degree `n`. -/
def cutJ (j : ℤ) (B : Cpx) (n : ℤ) :
    (totCut F π hπ j B).X n ⟶ (totCut F π hπ (j - 1) B).X n :=
  Sigma.desc (fun x : TotIdx (geP j) n => Sigma.ι (totFam F π hπ (geP (j - 1)) B n) (cutJIdx x))

/-- The component formula for `cutJ`. -/
lemma cutJ_ι (j : ℤ) (B : Cpx) (n : ℤ) (x : TotIdx (geP j) n) :
    Sigma.ι (totFam F π hπ (geP j) B n) x ≫ cutJ F π hπ j B n
      = Sigma.ι (totFam F π hπ (geP (j - 1)) B n) (cutJIdx x) :=
  Sigma.ι_comp_desc _ x

/-- The index of `totCut (j-1) B` in a column `> j - 1`, seen as an index of `totCut j B`. -/
def cutRetrJIdx {j n : ℤ} (x : TotIdx (geP (j - 1)) n) (h : j - 1 < x.1.1) : TotIdx (geP j) n :=
  ⟨x.1, x.2.1, by have h' : j - 1 ≤ x.1.1 := x.2.2; omega⟩

/-- The retraction of `cutJ`, killing the `(j-1)`-st column, in degree `n`. -/
def cutRetrJ (j : ℤ) (B : Cpx) (n : ℤ) :
    (totCut F π hπ (j - 1) B).X n ⟶ (totCut F π hπ j B).X n :=
  Sigma.desc (fun x : TotIdx (geP (j - 1)) n =>
    if h : j - 1 < x.1.1 then
      Sigma.ι (totFam F π hπ (geP j) B n) (cutRetrJIdx x h)
    else 0)

/-- The component formula for `cutRetrJ`. -/
lemma cutRetrJ_ι (j : ℤ) (B : Cpx) (n : ℤ) (x : TotIdx (geP (j - 1)) n) :
    Sigma.ι (totFam F π hπ (geP (j - 1)) B n) x ≫ cutRetrJ F π hπ j B n
      = if h : j - 1 < x.1.1 then
          Sigma.ι (totFam F π hπ (geP j) B n) (cutRetrJIdx x h)
        else 0 :=
  Sigma.ι_comp_desc _ x

/-! ## The chain-map property of `cutJ` -/

/-- The vertical part of the differential of `totCut (j-1) B` agrees with the vertical part of
the differential of `totCut j B` after the inclusion `cutJ`: on a column `q ≥ j` and resolution
degree `p` both are the differential of the resolution `Rco.obj (B.X q)`. -/
lemma cutJ_V (j : ℤ) (B : Cpx) (i : ℤ) (x : TotIdx (geP j) i) :
    totVpart F π hπ (geP j) B i x ≫ cutJ F π hπ j B (i + 1)
      = totVpart F π hπ (geP (j - 1)) B i (cutJIdx x) := by
  rw [totVpart, totVpart, Category.assoc, cutJ_ι]
  rfl

/-- The horizontal part of the differential of `totCut (j-1) B` agrees with the horizontal part
of the differential of `totCut j B` after the inclusion `cutJ`. -/
lemma cutJ_H (j : ℤ) (B : Cpx) (i : ℤ) (x : TotIdx (geP j) i) :
    totHpart F π hπ (geP j) (geP_step j) B i x ≫ cutJ F π hπ j B (i + 1)
      = totHpart F π hπ (geP (j - 1)) (geP_step (j - 1)) B i (cutJIdx x) := by
  rw [totHpart, totHpart, Linear.units_smul_comp, Category.assoc, cutJ_ι]
  rfl

/-- The inclusion `cutJ` is a chain map for the canonical differentials `totDc`. -/
lemma cutJ_Dc (j : ℤ) (B : Cpx) (i : ℤ) :
    cutJ F π hπ j B i ≫ totDc F π hπ (geP (j - 1)) (geP_step (j - 1)) B i
      = totDc F π hπ (geP j) (geP_step j) B i ≫ cutJ F π hπ j B (i + 1) := by
  apply Sigma.hom_ext
  intro x
  conv_lhs => rw [← Category.assoc, cutJ_ι, totDc_apply]
  conv_rhs => rw [← Category.assoc, totDc_apply, Preadditive.add_comp]
  rw [cutJ_V, cutJ_H]

/-- The chain-map property of the inclusion of the columns `q ≥ j` into the columns `q ≥ j - 1`,
in the form of a component identity. -/
theorem cutJ_comm (j : ℤ) (B : Cpx) {i m : ℤ} (him : (ComplexShape.up ℤ).Rel i m) :
    cutJ F π hπ j B i ≫ (totCut F π hπ (j - 1) B).d i m
      = (totCut F π hπ j B).d i m ≫ cutJ F π hπ j B m := by
  have hm : i + 1 = m := (ComplexShape.up_Rel ℤ i m).mp him
  subst hm
  rw [totCut_d_eq, totCut_d_eq]
  exact cutJ_Dc F π hπ j B i

/-! ## The splitting data of the filtration step -/

/-- The inclusion of the columns `q ≥ j` followed by the retraction which kills the
`(j-1)`-st column is the identity of `totCut j B`. -/
theorem cutJ_comp_cutRetrJ (j : ℤ) (B : Cpx) (n : ℤ) :
    cutJ F π hπ j B n ≫ cutRetrJ F π hπ j B n = 𝟙 ((totCut F π hπ j B).X n) := by
  apply Sigma.hom_ext
  intro x
  have hx : j - 1 < x.1.1 := by have h := x.2.2; omega
  simp only [← Category.assoc, cutJ_ι, cutRetrJ_ι, cutJIdx, cutRetrJIdx, dif_pos hx]
  rfl

/-- The retraction followed by the inclusion, plus the projection onto the `(j-1)`-st column
followed by its section, is the identity of `totCut (j-1) B`. -/
theorem cutRetrJ_comp_cutJ_add (j : ℤ) (B : Cpx) (n : ℤ) :
    cutRetrJ F π hπ j B n ≫ cutJ F π hπ j B n
      + colProjFam F π hπ (j - 1) B n ≫ colSectFam F π hπ (j - 1) B n
      = 𝟙 ((totCut F π hπ (j - 1) B).X n) := by
  apply Sigma.hom_ext
  intro x
  by_cases h : j - 1 < x.1.1
  · have hk : ¬ (x.1.1 = j - 1) := by omega
    simp only [Preadditive.comp_add, ← Category.assoc, cutRetrJ_ι, cutJ_ι, colProjFam_ι,
      dif_pos h, dif_neg hk, cutJIdx, cutRetrJIdx, zero_comp, add_zero]
    rfl
  · have hq : x.1.1 = j - 1 := by omega
    have hp : x.1.2 = n - (j - 1) := by have := x.2.1; omega
    have hx : x = colSectIdx (j - 1) n := by
      apply Subtype.ext
      exact Prod.ext hq hp
    subst hx
    simp only [Preadditive.comp_add, ← Category.assoc, cutRetrJ_ι, colProjFam_ι, colSectFam,
      colSectIdx, cutRetrJIdx, dif_neg (by omega : ¬ j - 1 < j - 1), dif_pos trivial, zero_comp,
      zero_add, Category.id_comp, Category.comp_id]
    rfl

/-- The inclusion of the columns `q ≥ j` followed by the projection onto the `(j-1)`-st column
vanishes. -/
theorem cutJ_comp_colProjFam (j : ℤ) (B : Cpx) (n : ℤ) :
    cutJ F π hπ j B n ≫ colProjFam F π hπ (j - 1) B n = 0 := by
  apply Sigma.hom_ext
  intro x
  rw [← Category.assoc, cutJ_ι, colProjFam_ι]
  rw [dif_neg]
  · rw [comp_zero]
  · intro h
    have hv : (cutJIdx x).1.1 = x.1.1 := rfl
    rw [hv] at h
    have hx := x.2.2
    omega

/-! ## The inclusion of the stupid truncation into the complex -/

/-- The component of `loT` is the transport of the truncation `trunc k K` into `K`, transported
along the definitional identification of the terms of `trunc k K` and `loX k K`. -/
lemma loT_eq_trunc (k : ℤ) (K : Cpx) (i : ℤ) (h : k ≤ i) :
    loT k K i = eqToHom (trunc_X_of_le K k h) := by
  rw [loT_eq k K i h]

/-- The inclusion `trunc k K ⟶ K` of the stupid truncation (the terms in degrees `≥ k`) into the
original complex.  Its components are the components of the inclusion `loId k` of
`RESOL/exists_windowTower.lean`. -/
def truncToSelf (k : ℤ) (K : Cpx) : trunc k K ⟶ K where
  f n := loT k K n
  comm' i j hij := by
    have hj : i + 1 = j := (ComplexShape.up_Rel ℤ i j).mp hij
    subst hj
    by_cases h : k ≤ i
    · have h' : k ≤ i + 1 := by omega
      rw [trunc_d_eq K (m := k) (i := i) (n := i + 1) rfl h h', loT_eq_trunc k K i h,
        loT_eq_trunc k K (i + 1) h']
      simp only [Category.assoc, eqToHom_comp_eqToHom_self, Category.comp_id, Category.id_comp]
    · rw [trunc_d_eq_zero K (m := k) (i := i) (n := i + 1) rfl h, zero_comp, loT_eq_zero k K i h,
        zero_comp]

/-- The component formula for `truncToSelf`. -/
lemma truncToSelf_f (k : ℤ) (K : Cpx) (n : ℤ) : (truncToSelf k K).f n = loT k K n := rfl

/-- The inclusion of the stupid truncation is a quasi-isomorphism in all degrees `≥ k + 1`. -/
theorem quasiIsoAt_truncToSelf (k : ℤ) (K : Cpx) {n : ℤ} (hn : k + 1 ≤ n) :
    QuasiIsoAt (truncToSelf k K) n := by
  refine quasiIsoAt_of_isIso_f _ n ?_ ?_ ?_
  · rw [truncToSelf_f]; exact isIso_loT k K (by omega)
  · rw [truncToSelf_f]; exact isIso_loT k K (by omega)
  · rw [truncToSelf_f]; exact isIso_loT k K (by omega)

end Zero

end Work.RESOL

end
