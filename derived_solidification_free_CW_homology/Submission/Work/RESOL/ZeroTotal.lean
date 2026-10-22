/-
AREA RESOL — the (hand-rolled) total complex of the column-wise resolution of a complex.

For a cochain complex `B : Cpx` (of light condensed abelian groups) and a resolution functor
`Rco` whose values are concentrated in cochain degrees `≤ 0`, the resolution of `B` is the total
complex

`(totCpx P B)^n = ∐_{(q,p) : p + q = n, P q} (Rco.obj (B.X q)).X p`

with differential: the resolution differential
`(Rco.obj (B.X q)).X p ⟶ (Rco.obj (B.X q)).X (p + 1)` plus `(-1)^p` times the differential
`(Rco.obj (B.X q)).X p ⟶ (Rco.obj (B.X (q + 1))).X p` induced by `B.d q (q + 1)`.

The index predicate `P` (with `P q → P (q + 1)`) allows us to cut the complex at a column `k`
(`P q := k ≤ q`), which is what the filtration argument for `totCpx ⊤ B ⟶ B` needs.
-/
import Submission.Work.RESOL.ZeroSetup

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RESOL

namespace Zero

variable (F : LightCondAb ⥤ LightCondAb) [F.PreservesZeroMorphisms] (π : F ⟶ 𝟭 LightCondAb)
  (hπ : ∀ M, Epi (π.app M))

/-! ## Signs -/

/-- The sign `(-1)^k`, as a unit of `ℤ`. -/
def sgn (k : ℤ) : ℤˣ := (ComplexShape.up ℤ).ε k

lemma sgn_succ (k : ℤ) : sgn (k + 1) = -sgn k :=
  ComplexShape.ε_succ (ComplexShape.up ℤ) ((ComplexShape.up_Rel (ℤ) k (k + 1)).mpr rfl)

/-! ## The total complex -/

/-- The index set of the summands of the total complex in total degree `n`: pairs `(q, p)` with
`p + q = n` (so that the summand `(Rco.obj (B.X q)).X p` sits in degree `n`) and `P q`. -/
abbrev TotIdx (P : ℤ → Prop) (n : ℤ) : Type := {x : ℤ × ℤ // x.2 + x.1 = n ∧ P x.1}

/-- The family of objects indexed by `TotIdx P n`. -/
abbrev totFam (P : ℤ → Prop) (B : Cpx) (m : ℤ) : TotIdx P m → LightCondAb :=
  fun y => ((Rco F π hπ).obj (B.X y.1.1)).X y.1.2

/-- The degree `m` part of the total complex. -/
abbrev totX (P : ℤ → Prop) (B : Cpx) (m : ℤ) : LightCondAb := ∐ (totFam F π hπ P B m)

/-- The index of the summand reached by the *vertical* part of the differential. -/
def totVIdx {P : ℤ → Prop} {n : ℤ} (x : TotIdx P n) : TotIdx P (n + 1) :=
  ⟨(x.1.1, x.1.2 + 1), by
    obtain ⟨h1, h2⟩ := x.2
    exact ⟨by omega, h2⟩⟩

/-- The index of the summand reached by the *horizontal* part of the differential. -/
def totHIdx {P : ℤ → Prop} {n : ℤ} (hP : ∀ q, P q → P (q + 1)) (x : TotIdx P n) :
    TotIdx P (n + 1) :=
  ⟨(x.1.1 + 1, x.1.2), by
    obtain ⟨h1, h2⟩ := x.2
    exact ⟨by omega, hP x.1.1 h2⟩⟩

/-- The vertical part of the differential, on a summand. -/
def totVpart (P : ℤ → Prop) (B : Cpx) (n : ℤ) (y : TotIdx P n) :
    ((Rco F π hπ).obj (B.X y.1.1)).X y.1.2 ⟶ totX F π hπ P B (n + 1) :=
  ((Rco F π hπ).obj (B.X y.1.1)).d y.1.2 (y.1.2 + 1)
    ≫ Sigma.ι (totFam F π hπ P B (n + 1)) (totVIdx y)

/-- The horizontal part of the differential, on a summand. -/
def totHpart (P : ℤ → Prop) (hP : ∀ q, P q → P (q + 1)) (B : Cpx) (n : ℤ)
    (y : TotIdx P n) :
    ((Rco F π hπ).obj (B.X y.1.1)).X y.1.2 ⟶ totX F π hπ P B (n + 1) :=
  sgn y.1.2 • (((Rco F π hπ).map (B.d y.1.1 (y.1.1 + 1))).f y.1.2
    ≫ Sigma.ι (totFam F π hπ P B (n + 1)) (totHIdx hP y))

/-- The canonical differential of the total complex, from degree `n` to degree `n + 1`. -/
def totDc (P : ℤ → Prop) (hP : ∀ q, P q → P (q + 1)) (B : Cpx) (n : ℤ) :
    totX F π hπ P B n ⟶ totX F π hπ P B (n + 1) :=
  Sigma.desc (fun x => totVpart F π hπ P B n x + totHpart F π hπ P hP B n x)

/-- The differential of the total complex, from degree `n` to degree `m = n + 1`. -/
def totD (P : ℤ → Prop) (hP : ∀ q, P q → P (q + 1)) (B : Cpx) (n m : ℤ)
    (hm : m = n + 1) : totX F π hπ P B n ⟶ totX F π hπ P B m :=
  hm.symm ▸ totDc F π hπ P hP B n

lemma totDc_apply (P : ℤ → Prop) (hP : ∀ q, P q → P (q + 1)) (B : Cpx) (n : ℤ)
    (y : TotIdx P n) :
    Sigma.ι (totFam F π hπ P B n) y ≫ totDc F π hπ P hP B n
      = totVpart F π hπ P B n y + totHpart F π hπ P hP B n y :=
  Sigma.ι_comp_desc _ y

/-! ## The components of `Rco.map` in the unfolded form

The `map` field of `Rco` is `HomologicalComplex.extendMap`, and the elaborator unfolds it, so the
lemmas below are stated in the unfolded form (which is what goals contain). -/

lemma Rco_map_f_eq {M N : LightCondAb} (f : M ⟶ N) (n : ℤ) :
    ((Rco F π hπ).map f).f n
      = (HomologicalComplex.extendMap ((LR F π hπ).chainComplexMap f)
          ComplexShape.embeddingDownNat).f n :=
  rfl

/-- The chain map property of the components of `Rco.map`, in the unfolded form. -/
lemma Rco_map_f_comm {M N : LightCondAb} (f : M ⟶ N) (i j : ℤ) :
    (HomologicalComplex.extendMap ((LR F π hπ).chainComplexMap f)
        ComplexShape.embeddingDownNat).f i
      ≫ ((Rco F π hπ).obj N).d i j
      = ((Rco F π hπ).obj M).d i j
        ≫ (HomologicalComplex.extendMap ((LR F π hπ).chainComplexMap f)
            ComplexShape.embeddingDownNat).f j :=
  HomologicalComplex.Hom.comm ((Rco F π hπ).map f) i j

/-- The index reached by first moving vertically and then horizontally agrees with the index
reached by first moving horizontally and then vertically. -/
lemma totHIdx_totVIdx {P : ℤ → Prop} (hP : ∀ q, P q → P (q + 1)) {n : ℤ}
    (x : TotIdx P n) :
    totHIdx hP (totVIdx (n := n) x) = totVIdx (n := n + 1) (totHIdx hP x) :=
  Subtype.ext rfl

/-- Test: the two composite indices are definitionally equal. -/
example (P : ℤ → Prop) (hP : ∀ q, P q → P (q + 1)) (B : Cpx) (n : ℤ) (x : TotIdx P n) :
    (Sigma.ι (totFam F π hπ P B ((n + 1) + 1))
        (totHIdx hP (totVIdx (n := n) x)) :
      totFam F π hπ P B ((n + 1) + 1) (totHIdx hP (totVIdx (n := n) x))
        ⟶ ∐ (totFam F π hπ P B ((n + 1) + 1)))
      = Sigma.ι (totFam F π hπ P B ((n + 1) + 1))
          (totVIdx (n := n + 1) (totHIdx hP x)) :=
  rfl

lemma ztotVV_eq_zero (P : ℤ → Prop) (B : Cpx) (n : ℤ)
    (x : TotIdx P n) :
    ((Rco F π hπ).obj (B.X x.1.1)).d x.1.2 (x.1.2 + 1)
      ≫ totVpart F π hπ P B (n + 1) ⟨(x.1.1, x.1.2 + 1), ⟨by omega, x.2.2⟩⟩ = 0 := by
  rw [totVpart]
  simp only [totVIdx, Subtype.coe_mk]
  rw [← Category.assoc, HomologicalComplex.d_comp_d, zero_comp]

/-- The "horizontal then horizontal" term vanishes: the horizontal part of the differential is
`Rco.map` applied to `d_B`, and consecutive differentials of `B` compose to zero. -/
lemma ztotHH_eq_zero (P : ℤ → Prop) (hP : ∀ q, P q → P (q + 1)) (B : Cpx) (n : ℤ)
    (x : TotIdx P n) :
    sgn x.1.2 • (((Rco F π hπ).map (B.d x.1.1 (x.1.1 + 1))).f x.1.2
      ≫ totHpart F π hπ P hP B (n + 1)
          ⟨(x.1.1 + 1, x.1.2), ⟨by omega, hP x.1.1 x.2.2⟩⟩) = 0 := by
  rw [totHpart]
  show sgn x.1.2 • (((Rco F π hπ).map (B.d x.1.1 (x.1.1 + 1))).f x.1.2
    ≫ (sgn x.1.2 • (((Rco F π hπ).map (B.d (x.1.1 + 1) ((x.1.1 + 1) + 1))).f x.1.2
      ≫ Sigma.ι (totFam F π hπ P B (n + 1 + 1))
          ⟨(x.1.1 + 1 + 1, x.1.2), ⟨by omega, hP (x.1.1 + 1) (hP x.1.1 x.2.2)⟩⟩))) = 0
  have hcomp : ((Rco F π hπ).map (B.d x.1.1 (x.1.1 + 1))).f x.1.2
      ≫ ((Rco F π hπ).map (B.d (x.1.1 + 1) ((x.1.1 + 1) + 1))).f x.1.2 = 0 := by
    rw [← HomologicalComplex.comp_f, ← Functor.map_comp, HomologicalComplex.d_comp_d,
      Functor.map_zero, HomologicalComplex.zero_f]
  rw [Linear.comp_units_smul, ← Category.assoc, hcomp, zero_comp, smul_zero, smul_zero]

/-- The two "mixed" terms (horizontal after vertical, and vertical after horizontal) cancel:
this is the chain-map property of `Rco.map (B.d q (q+1))`, together with `sgn (p+1) = -sgn p`. -/
lemma ztotVH_add_totHV (P : ℤ → Prop) (hP : ∀ q, P q → P (q + 1)) (B : Cpx) (n : ℤ)
    (x : TotIdx P n) :
    ((Rco F π hπ).obj (B.X x.1.1)).d x.1.2 (x.1.2 + 1)
        ≫ totHpart F π hπ P hP B (n + 1) ⟨(x.1.1, x.1.2 + 1), ⟨by omega, x.2.2⟩⟩
      + sgn x.1.2 • (((Rco F π hπ).map (B.d x.1.1 (x.1.1 + 1))).f x.1.2
        ≫ totVpart F π hπ P B (n + 1)
            ⟨(x.1.1 + 1, x.1.2), ⟨by omega, hP x.1.1 x.2.2⟩⟩) = 0 := by
  rw [totHpart, totVpart]
  show ((Rco F π hπ).obj (B.X x.1.1)).d x.1.2 (x.1.2 + 1)
      ≫ (sgn (x.1.2 + 1) • (((Rco F π hπ).map (B.d x.1.1 (x.1.1 + 1))).f (x.1.2 + 1)
        ≫ Sigma.ι (totFam F π hπ P B (n + 1 + 1))
            ⟨(x.1.1 + 1, x.1.2 + 1), ⟨by omega, hP x.1.1 x.2.2⟩⟩))
    + sgn x.1.2 • (((Rco F π hπ).map (B.d x.1.1 (x.1.1 + 1))).f x.1.2
      ≫ (((Rco F π hπ).obj (B.X (x.1.1 + 1))).d x.1.2 (x.1.2 + 1)
        ≫ Sigma.ι (totFam F π hπ P B (n + 1 + 1))
            ⟨(x.1.1 + 1, x.1.2 + 1), ⟨by omega, hP x.1.1 x.2.2⟩⟩)) = 0
  rw [Linear.comp_units_smul, ← Category.assoc, ← Category.assoc,
    HomologicalComplex.Hom.comm ((Rco F π hπ).map (B.d x.1.1 (x.1.1 + 1))) x.1.2 (x.1.2 + 1),
    sgn_succ, Units.neg_smul]
  rw [neg_add_cancel]

/-- The vertical component of the differential, followed by the differential in degree `n+1`,
distributed over the two components in degree `n+1`. -/
lemma ztotVpart_comp (P : ℤ → Prop) (hP : ∀ q, P q → P (q + 1)) (B : Cpx) (n : ℤ)
    (x : TotIdx P n) :
    totVpart F π hπ P B n x ≫ totDc F π hπ P hP B (n + 1)
      = ((Rco F π hπ).obj (B.X x.1.1)).d x.1.2 (x.1.2 + 1)
            ≫ totVpart F π hπ P B (n + 1) ⟨(x.1.1, x.1.2 + 1), ⟨by omega, x.2.2⟩⟩
        + ((Rco F π hπ).obj (B.X x.1.1)).d x.1.2 (x.1.2 + 1)
            ≫ totHpart F π hπ P hP B (n + 1)
                ⟨(x.1.1, x.1.2 + 1), ⟨by omega, x.2.2⟩⟩ := by
  rw [totVpart]
  show ((Rco F π hπ).obj (B.X x.1.1)).d x.1.2 (x.1.2 + 1)
      ≫ Sigma.ι (totFam F π hπ P B (n + 1)) ⟨(x.1.1, x.1.2 + 1), ⟨by omega, x.2.2⟩⟩
      ≫ totDc F π hπ P hP B (n + 1)
      = ((Rco F π hπ).obj (B.X x.1.1)).d x.1.2 (x.1.2 + 1)
            ≫ totVpart F π hπ P B (n + 1) ⟨(x.1.1, x.1.2 + 1), ⟨by omega, x.2.2⟩⟩
        + ((Rco F π hπ).obj (B.X x.1.1)).d x.1.2 (x.1.2 + 1)
            ≫ totHpart F π hπ P hP B (n + 1)
                ⟨(x.1.1, x.1.2 + 1), ⟨by omega, x.2.2⟩⟩
  rw [totDc, Sigma.ι_comp_desc, Preadditive.comp_add]

/-- The horizontal component of the differential, followed by the differential in degree `n+1`,
distributed over the two components in degree `n+1`. -/
lemma ztotHpart_comp (P : ℤ → Prop) (hP : ∀ q, P q → P (q + 1)) (B : Cpx) (n : ℤ)
    (x : TotIdx P n) :
    totHpart F π hπ P hP B n x ≫ totDc F π hπ P hP B (n + 1)
      = sgn x.1.2 • (((Rco F π hπ).map (B.d x.1.1 (x.1.1 + 1))).f x.1.2
            ≫ totVpart F π hπ P B (n + 1)
                ⟨(x.1.1 + 1, x.1.2), ⟨by omega, hP x.1.1 x.2.2⟩⟩)
        + sgn x.1.2 • (((Rco F π hπ).map (B.d x.1.1 (x.1.1 + 1))).f x.1.2
            ≫ totHpart F π hπ P hP B (n + 1)
                ⟨(x.1.1 + 1, x.1.2), ⟨by omega, hP x.1.1 x.2.2⟩⟩) := by
  rw [totHpart]
  show (sgn x.1.2 • (((Rco F π hπ).map (B.d x.1.1 (x.1.1 + 1))).f x.1.2
          ≫ Sigma.ι (totFam F π hπ P B (n + 1))
              ⟨(x.1.1 + 1, x.1.2), ⟨by omega, hP x.1.1 x.2.2⟩⟩))
        ≫ totDc F π hπ P hP B (n + 1)
      = sgn x.1.2 • (((Rco F π hπ).map (B.d x.1.1 (x.1.1 + 1))).f x.1.2
            ≫ totVpart F π hπ P B (n + 1)
                ⟨(x.1.1 + 1, x.1.2), ⟨by omega, hP x.1.1 x.2.2⟩⟩)
        + sgn x.1.2 • (((Rco F π hπ).map (B.d x.1.1 (x.1.1 + 1))).f x.1.2
            ≫ totHpart F π hπ P hP B (n + 1)
                ⟨(x.1.1 + 1, x.1.2), ⟨by omega, hP x.1.1 x.2.2⟩⟩)
  rw [Linear.units_smul_comp, Category.assoc, totDc, Sigma.ι_comp_desc,
    Preadditive.comp_add, smul_add]

/-- The square of the (canonical) differential of the total complex vanishes. -/
theorem totDc_comp (P : ℤ → Prop) (hP : ∀ q, P q → P (q + 1)) (B : Cpx) (n : ℤ) :
    totDc F π hπ P hP B n ≫ totDc F π hπ P hP B (n + 1) = 0 := by
  apply Sigma.hom_ext
  intro x
  rw [← Category.assoc, comp_zero]
  have h1 : Sigma.ι (totFam F π hπ P B n) x ≫ totDc F π hπ P hP B n
      = totVpart F π hπ P B n x + totHpart F π hπ P hP B n x := by
    rw [totDc, Sigma.ι_comp_desc]
  rw [h1, Preadditive.add_comp, ztotVpart_comp F π hπ P hP B n x,
    ztotHpart_comp F π hπ P hP B n x, ztotVV_eq_zero F π hπ P B n x,
    ztotHH_eq_zero F π hπ P hP B n x, zero_add, add_zero,
    ztotVH_add_totHV F π hπ P hP B n x]

/-- The square of the differential of the total complex vanishes. -/
theorem totD_comp (P : ℤ → Prop) (hP : ∀ q, P q → P (q + 1)) (B : Cpx) (n : ℤ) :
    totD F π hπ P hP B n (n + 1) rfl ≫ totD F π hπ P hP B (n + 1) ((n + 1) + 1) rfl = 0 :=
  totDc_comp F π hπ P hP B n

/-- The complex structure on the total complex. -/
def totCpx (P : ℤ → Prop) (hP : ∀ q, P q → P (q + 1)) (B : Cpx) : Cpx where
  X n := totX F π hπ P B n
  d n m := if h : m = n + 1 then totD F π hπ P hP B n m h else 0
  shape n m hnm := by
    rw [dif_neg]
    rw [ComplexShape.up_Rel] at hnm
    omega
  d_comp_d' i j k hij hjk := by
    rw [ComplexShape.up_Rel] at hij hjk
    subst hij
    subst hjk
    rw [dif_pos rfl, dif_pos rfl]
    exact totD_comp F π hπ P hP B i

/-- The index predicate selecting all columns. -/
abbrev topP : ℤ → Prop := fun _ => True

lemma topP_step : ∀ q : ℤ, topP q → topP (q + 1) := fun _ _ => trivial

/-- The resolution of a complex: the total complex of all columns. -/
abbrev totFull (B : Cpx) : Cpx := totCpx F π hπ topP topP_step B

/-- The functoriality map of the total complex, on degree `n`. -/
def totMapFam {B B' : Cpx} (f : B ⟶ B') (n : ℤ) :
    (totFull F π hπ B).X n ⟶ (totFull F π hπ B').X n :=
  Sigma.desc (fun x : TotIdx topP n =>
    ((Rco F π hπ).map (f.f x.1.1)).f x.1.2 ≫ Sigma.ι (totFam F π hπ topP B' n) x)

/-- The component of the augmentation `R B ⟶ B`. -/
def epsFam (B : Cpx) (n : ℤ) : (totFull F π hπ B).X n ⟶ B.X n :=
  Sigma.desc (fun x : TotIdx topP n =>
    if h : x.1.2 = 0 then
      eqToHom (congrArg (fun t => ((Rco F π hπ).obj (B.X x.1.1)).X t) h)
        ≫ aug0 F π hπ (B.X x.1.1) ≫ eqToHom (congrArg B.X (by
        obtain ⟨h1, h2⟩ := x.2
        omega))
    else 0)

end Zero

end Work.RESOL
