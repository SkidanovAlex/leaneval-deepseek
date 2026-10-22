/-
AREA RESOL — the column filtration of the total resolution complex.

For a cochain complex `B` and `k : ℤ`, `Zero.totCut k B` is the total complex of the columns
`q ≥ k` of the resolution bicomplex (`Zero.totCpx` with the predicate `q ≥ k`), and
`Zero.colCpx k B` is the `k`-th column alone, seen as a complex (the resolution of `B.X k`,
re-indexed so that its resolution degree `0` sits in cochain degree `k`).

The short exact sequence
`0 ⟶ totCut (k+1) B ⟶ totCut k B ⟶ colCpx k B ⟶ 0`
(the `k`-th column is the quotient of the columns `≥ k` by the columns `≥ k+1`) is the basic
step of the filtration induction proving that `totFull B ⟶ B` is a quasi-isomorphism for `B`
bounded above.

The maps are `cutInc` (the inclusion), `colProj` (the projection onto the `k`-th column),
`cutRetr`/`colSect` (the degreewise splitting data).  The degreewise components of all these
maps are defined here, together with their component formulas; the chain-map properties and
the splitting identities are proved in `RESOL/ZeroCutSES.lean`.

Conventions: an index of `TotIdx P n` is a pair `(q, p)` with `q` the *column* (degree in `B`)
and `p` the *resolution degree*, `p + q = n`.
-/
import Submission.Work.RESOL.ZeroRes

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RESOL

namespace Zero

variable (F : LightCondAb ⥤ LightCondAb) [F.PreservesZeroMorphisms] (π : F ⟶ 𝟭 LightCondAb)
  (hπ : ∀ M, Epi (π.app M)) (B : Cpx)

/-! ## The columns `≥ k` -/

/-- The predicate "the column is at least `k`". -/
abbrev geP (k : ℤ) : ℤ → Prop := fun q => k ≤ q

theorem geP_step (k : ℤ) : ∀ q : ℤ, geP k q → geP k (q + 1) := fun q h => by omega

/-- The total complex of the columns `q ≥ k`. -/
abbrev totCut (k : ℤ) (B : Cpx) : Cpx := totCpx F π hπ (geP k) (geP_step k) B

theorem totCut_X (k : ℤ) (B : Cpx) (n : ℤ) :
    (totCut F π hπ k B).X n = totX F π hπ (geP k) B n := rfl

theorem totCut_d_eq (k : ℤ) (B : Cpx) (n : ℤ) :
    (totCut F π hπ k B).d n (n + 1) = totDc F π hπ (geP k) (geP_step k) B n := by
  rw [show (totCut F π hπ k B).d n (n + 1) = dite (n + 1 = n + 1)
    (fun h => totD F π hπ (geP k) (geP_step k) B n (n + 1) h) (fun _ => 0) from rfl,
    dite_eq_left rfl]
  rfl

/-- The index of `totCut k B` obtained from an index of `totCut (k+1) B`. -/
def cutIdx {k n : ℤ} (x : TotIdx (geP (k + 1)) n) : TotIdx (geP k) n :=
  ⟨x.1, x.2.1, by have h : k + 1 ≤ x.1.1 := x.2.2; omega⟩

/-- The index of `totCut (k+1) B` obtained from an index of `totCut k B` in a column `> k`. -/
def cutRetrIdx {k n : ℤ} (x : TotIdx (geP k) n) (h : k < x.1.1) : TotIdx (geP (k + 1)) n :=
  ⟨x.1, x.2.1, by have h' : k ≤ x.1.1 := x.2.2; omega⟩

/-- The index of the `k`-th column of `totCut k B` in degree `n`. -/
def colSectIdx (k n : ℤ) : TotIdx (geP k) n :=
  ⟨(k, n - k), ⟨by omega, le_refl k⟩⟩

lemma cutIdx_val {k n : ℤ} (x : TotIdx (geP (k + 1)) n) : (cutIdx x).1 = x.1 := rfl

lemma cutRetrIdx_val {k n : ℤ} (x : TotIdx (geP k) n) (h : k < x.1.1) :
    (cutRetrIdx x h).1 = x.1 := rfl

lemma colSectIdx_val (k n : ℤ) : (colSectIdx k n).1 = (k, n - k) := rfl

/-! ## The degreewise components of the inclusion `totCut (k+1) B ⟶ totCut k B` -/

/-- The inclusion of the columns `≥ k+1` into the columns `≥ k`, in degree `n`. -/
def cutIncFam (k : ℤ) (B : Cpx) (n : ℤ) :
    (totCut F π hπ (k + 1) B).X n ⟶ (totCut F π hπ k B).X n :=
  Sigma.desc (fun x : TotIdx (geP (k + 1)) n =>
    Sigma.ι (totFam F π hπ (geP k) B n) (cutIdx x))

/-- The retraction of `cutIncFam`, killing the `k`-th column, in degree `n`. -/
def cutRetrFam (k : ℤ) (B : Cpx) (n : ℤ) :
    (totCut F π hπ k B).X n ⟶ (totCut F π hπ (k + 1) B).X n :=
  Sigma.desc (fun x : TotIdx (geP k) n =>
    if h : k < x.1.1 then
      Sigma.ι (totFam F π hπ (geP (k + 1)) B n) (cutRetrIdx x h)
    else 0)

lemma cutIncFam_ι (k : ℤ) (B : Cpx) (n : ℤ) (x : TotIdx (geP (k + 1)) n) :
    Sigma.ι (totFam F π hπ (geP (k + 1)) B n) x ≫ cutIncFam F π hπ k B n
      = Sigma.ι (totFam F π hπ (geP k) B n) (cutIdx x) :=
  Sigma.ι_comp_desc _ x

lemma cutRetrFam_ι (k : ℤ) (B : Cpx) (n : ℤ) (x : TotIdx (geP k) n) :
    Sigma.ι (totFam F π hπ (geP k) B n) x ≫ cutRetrFam F π hπ k B n
      = if h : k < x.1.1 then
          Sigma.ι (totFam F π hπ (geP (k + 1)) B n) (cutRetrIdx x h)
        else 0 :=
  Sigma.ι_comp_desc _ x

/-! ## The `k`-th column as a complex -/

/-- The embedding of complex shapes `n ↦ n - k` (the re-indexing which moves the `k`-th column
into the total degree of the total complex). -/
def shiftEmb (k : ℤ) : ComplexShape.Embedding (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ComplexShape.Embedding.mk' _ _ (fun n => n - k)
    (fun a b h => by
      have h2 : a - k = b - k := h
      have h3 : a - k + k = b - k + k := by rw [h2]
      simpa using h3)
    (fun a b => by
      show (a + 1 = b) ↔ ((a - k) + 1 = b - k)
      constructor <;> intro h <;> omega)

instance instIsRelIffShiftEmb (k : ℤ) : (shiftEmb k).IsRelIff where
  rel' a b h := by
    show a + 1 = b
    have h2 : a - k + 1 = b - k := h
    omega

/-- The `k`-th column of the resolution bicomplex, as a cochain complex in the total degree of
the total complex: its resolution degree `p` sits in cochain degree `p + k`. -/
abbrev colCpx (k : ℤ) (B : Cpx) : Cpx :=
  ((Rco F π hπ).obj (B.X k)).restriction (shiftEmb k)

theorem colCpx_X (k : ℤ) (B : Cpx) (n : ℤ) :
    (colCpx F π hπ k B).X n = ((Rco F π hπ).obj (B.X k)).X (n - k) := rfl

theorem colCpx_d (k : ℤ) (B : Cpx) (n m : ℤ) :
    (colCpx F π hπ k B).d n m = ((Rco F π hπ).obj (B.X k)).d (n - k) (m - k) := rfl

/-- The comparison of the summand of `totCut k B` in the `k`-th column with the `k`-th column
itself. -/
lemma totFam_eq_colCpx {k n : ℤ} (x : TotIdx (geP k) n) (h : x.1.1 = k) :
    totFam F π hπ (geP k) B n x = (colCpx F π hπ k B).X n := by
  show ((Rco F π hπ).obj (B.X x.1.1)).X x.1.2 = ((Rco F π hπ).obj (B.X k)).X (n - k)
  rw [h]
  congr 1
  omega

/-- The projection onto the `k`-th column, in degree `n`. -/
def colProjFam (k : ℤ) (B : Cpx) (n : ℤ) :
    (totCut F π hπ k B).X n ⟶ (colCpx F π hπ k B).X n :=
  Sigma.desc (fun x : TotIdx (geP k) n =>
    if h : x.1.1 = k then
      eqToHom (totFam_eq_colCpx F π hπ B x h)
    else 0)

lemma colProjFam_ι (k : ℤ) (B : Cpx) (n : ℤ) (x : TotIdx (geP k) n) :
    Sigma.ι (totFam F π hπ (geP k) B n) x ≫ colProjFam F π hπ k B n
      = if h : x.1.1 = k then
          eqToHom (totFam_eq_colCpx F π hπ B x h)
        else 0 :=
  Sigma.ι_comp_desc _ x

/-- The inclusion of the `k`-th column, in degree `n`. -/
def colSectFam (k : ℤ) (B : Cpx) (n : ℤ) :
    (colCpx F π hπ k B).X n ⟶ (totCut F π hπ k B).X n :=
  Sigma.ι (totFam F π hπ (geP k) B n) (colSectIdx k n)

/-- The re-indexed single complex: the object `M` concentrated in cochain degree `k`. -/
abbrev singleShift (k : ℤ) (M : LightCondAb) : Cpx :=
  ((HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).obj M).restriction (shiftEmb k)

theorem singleShift_X (k : ℤ) (M : LightCondAb) (n : ℤ) :
    (singleShift k M).X n = ((HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).obj
      M).X (n - k) := rfl

/-- The augmentation of the `k`-th column, as a morphism of complexes (the `k`-th column is a
resolution of `B.X k`, concentrated in total degree `k`). -/
def colAugRestr (k : ℤ) (B : Cpx) : colCpx F π hπ k B ⟶ singleShift k (B.X k) :=
  HomologicalComplex.restrictionMap ((augSingle F π hπ).app (B.X k)) (shiftEmb k)

/-- The degreewise components of the augmentation of the `k`-th column, with values in the
single complex `(single k).obj (B.X k)`. -/
def colAugFam (k : ℤ) (B : Cpx) (n : ℤ) :
    (colCpx F π hπ k B).X n ⟶
      ((HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) k).obj (B.X k)).X n :=
  if h : n = k then
    (((Rco F π hπ).obj (B.X k)).XIsoOfEq (by omega : n - k = 0)).hom
      ≫ aug0 F π hπ (B.X k)
      ≫ eqToHom (by
          rw [h]
          exact (HomologicalComplex.single_obj_X_self (ComplexShape.up ℤ) k (B.X k)).symm)
  else 0

lemma colAugRestr_f (k : ℤ) (B : Cpx) (n : ℤ) :
    (colAugRestr F π hπ k B).f n = ((augSingle F π hπ).app (B.X k)).f (n - k) := rfl

end Zero

end Work.RESOL
