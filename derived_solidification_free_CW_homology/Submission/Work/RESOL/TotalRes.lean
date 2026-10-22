/-
AREA RESOL — the augmentation `ε : R ⟶ 𝟭` of the resolution by the total complex of the
column-wise resolutions.

`R : Cpx ⤳ Cpx` is the total complex of the bicomplex whose `p`-th column is the resolution
`X.obj (B.X p)` of the `p`-th term of `B` (see `Submission/Work/RESOL/Bicomplex.lean`).  Here we
construct the comparison map `ε : R ⟶ 𝟭 Cpx`: in degree `n`, the summand
`(X.obj (B.X p)).X q` of `(R.obj B).X n` (with `p - q = n`) is mapped to `B.X n` by the
augmentation `augRes (B.X p) : (X.obj (B.X p)).X 0 ⟶ B.X p` when `q = 0`, and by zero otherwise.

All statements are phrased in terms of the graded-object description of the total complex
(`GradedObject.mapObj`), which is definitionally the total complex.
-/
import Mathlib
import Submission.Work.RESOL.Bicomplex

open CategoryTheory Limits LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open HomologicalComplex

noncomputable section

namespace Work.RESOL

attribute [local instance 2000] Sheaf.instHasColimitsOfShape

attribute [local instance] Classical.propDecidable

set_option allowUnsafeReducibility true

attribute [local reducible] HomologicalComplex₂.total HomologicalComplex₂.toGradedObject
  HomologicalComplex₂.ιTotal HomologicalComplex₂.ιTotalOrZero GradedObject.mapObj
  GradedObject.ιMapObj GradedObject.ιMapObjOrZero bicomplexObj ComplexShape.π
  ComplexShape.ε₁ ComplexShape.ε₂ Work.RESOL.totalComplexShape

/-- The total degree of the summand `(X.obj (B.X p)).X q` of the resolution of `B`. -/
abbrev tshape : ℤ × ℕ → ℤ :=
  ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.down ℕ) (ComplexShape.up ℤ)

/-- The total complex shape is the expected function of `(p,q)`. -/
lemma tshape_eq (p : ℤ) (q : ℕ) : tshape (p, q) = p - (q : ℤ) := rfl

/-- The `n`-th term of the total complex of the resolution bicomplex of `B`, in the
graded-object form. -/
abbrev totX (B : Cpx) (n : ℤ) : LightCondAb :=
  (bicomplexObj B).toGradedObject.mapObj
    (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.down ℕ) (ComplexShape.up ℤ)) n

/-! ## The augmentation of the degreewise resolution -/

/-- The augmentation `(X.obj M).X 0 ⟶ M` of the resolution of a light condensed abelian
group. -/
def augRes (M : LightCondAb) : (LR.chainComplex M).X 0 ⟶ M :=
  (LR.chainComplexXZeroIso M).hom ≫ LR.π.app M

lemma augRes_comp_d (M : LightCondAb) : (LR.chainComplex M).d 1 0 ≫ augRes M = 0 := by
  have hd : (LR.chainComplex M).d 1 0 =
      (LR.chainComplexXOneIso M).hom ≫ LR.π.app (kernel (LR.π.app M))
        ≫ kernel.ι (LR.π.app M) ≫ (LR.chainComplexXZeroIso M).inv := by
    simpa using CategoryTheory.Abelian.LeftResolution.map_chainComplex_d_1_0 (Λ := LR) (X := M)
  rw [hd, augRes]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [kernel.condition]
  simp only [comp_zero]

lemma augRes_naturality {M N : LightCondAb} (f : M ⟶ N) :
    (LR.chainComplexMap f).f 0 ≫ augRes N = augRes M ≫ f := by
  have hnat : LR.F.map f ≫ LR.π.app N = LR.π.app M ≫ f := by
    simpa using LR.π_naturality (f := f)
  rw [CategoryTheory.Abelian.LeftResolution.chainComplexMap_f_0, augRes, augRes]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hnat]

/-! ## The comparison map in degree `n` -/

/-- The component of the comparison map attached to the summand `(X.obj (B.X p)).X q`: the
augmentation of the resolution of `B.X p` when `q = 0`, and zero otherwise. -/
def augComp (B : Cpx) (p : ℤ) (q : ℕ) :
    (bicomplexObj B).toGradedObject (p, q) ⟶ B.X (tshape (p, q)) :=
  if hq : q = 0 then
    (((LR.chainComplex (B.X p)).XIsoOfEq hq).hom) ≫ augRes (B.X p)
      ≫ (B.XIsoOfEq (by rw [tshape_eq, hq]; omega)).hom
  else 0

@[simp] lemma bicomplexObj_X (B : Cpx) (p : ℤ) :
    (bicomplexObj B).X p = LR.chainComplex (B.X p) := rfl

@[simp] lemma bicomplexObj_d (B : Cpx) (p p' : ℤ) :
    (bicomplexObj B).d p p' = LR.chainComplexMap (B.d p p') := rfl

variable (B : Cpx)

/-- The comparison map `(R.obj B).X n ⟶ B.X n` in degree `n` (in the graded-object form of the
total complex). -/
def epsFam (n : ℤ) : totX B n ⟶ B.X n :=
  HomologicalComplex₂.totalDesc (bicomplexObj B)
    (fun (p : ℤ) (q : ℕ)
      (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.down ℕ) (ComplexShape.up ℤ)
        (p, q) = n) => augComp B p q ≫ (B.XIsoOfEq h).hom)

lemma epsFam_comp_ιTotal (n : ℤ) (p : ℤ) (q : ℕ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.down ℕ) (ComplexShape.up ℤ)
      (p, q) = n) :
    (HomologicalComplex₂.ιTotal (bicomplexObj B) (ComplexShape.up ℤ) p q n h) ≫ epsFam B n
      = augComp B p q ≫ (B.XIsoOfEq h).hom := by
  simp only [epsFam, HomologicalComplex₂.ι_totalDesc]

lemma epsFam_comp_ιMapObj (n : ℤ) (p : ℤ) (q : ℕ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.down ℕ) (ComplexShape.up ℤ)
      (p, q) = n) :
    (bicomplexObj B).toGradedObject.ιMapObj
        (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.down ℕ) (ComplexShape.up ℤ))
        (p, q) n h ≫ epsFam B n
      = augComp B p q ≫ (B.XIsoOfEq h).hom :=
  epsFam_comp_ιTotal B n p q h

lemma epsFam_comp_ιMapObj_assoc (n : ℤ) (p : ℤ) (q : ℕ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.down ℕ) (ComplexShape.up ℤ)
      (p, q) = n)
    {A : LightCondAb} (f : B.X n ⟶ A) :
    (bicomplexObj B).toGradedObject.ιMapObj
        (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.down ℕ) (ComplexShape.up ℤ))
        (p, q) n h ≫ (epsFam B n ≫ f)
      = (augComp B p q ≫ (B.XIsoOfEq h).hom) ≫ f := by
  conv_lhs => rw [← Category.assoc, epsFam_comp_ιMapObj B n p q h]

/-- The signs of the total complex shape are the expected ones. -/
lemma eps₁_val (p : ℤ) (q : ℕ) :
    ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (p, q)
      = 1 := rfl

lemma eps₂_val (p : ℤ) (q : ℕ) :
    ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (p, q)
      = Int.negOnePow p := rfl

/-- The comparison map is a morphism of complexes: it commutes with the horizontal and the
vertical parts of the differential of the total complex. -/
theorem epsFam_comm {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) :
    epsFam B i ≫ B.d i j
      = (HomologicalComplex₂.D₁ (bicomplexObj B) (ComplexShape.up ℤ) i j
          + HomologicalComplex₂.D₂ (bicomplexObj B) (ComplexShape.up ℤ) i j) ≫ epsFam B j := by
  have hj : i + 1 = j := (ComplexShape.up_Rel ℤ i j).mp hij
  rw [← hj]
  rw [Preadditive.add_comp]
  apply GradedObject.mapObj_ext (X := (bicomplexObj B).toGradedObject)
    (p := ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.down ℕ) (ComplexShape.up ℤ))
  intro pq hpq
  obtain ⟨p, q⟩ := pq
  have hpq' : p - (q : ℤ) = i := hpq
  simp only [epsFam_comp_ιMapObj_assoc, Category.assoc, HomologicalComplex.XIsoOfEq_hom_comp_d]
  rw [Preadditive.comp_add]
  rw [← Category.assoc, HomologicalComplex₂.ι_D₁, ← Category.assoc, HomologicalComplex₂.ι_D₂]
  by_cases hq : q = 0
  · -- the summand `(p,0)` contributes to the horizontal differential only
    subst hq
    -- the left hand side
    rw [augComp, dif_pos rfl]
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
    simp only [Category.assoc, HomologicalComplex.XIsoOfEq_hom_comp_d]
    -- the vertical part of the right hand side vanishes
    rw [HomologicalComplex₂.d₂_eq_zero (K := bicomplexObj B) (c₁₂ := ComplexShape.up ℤ)
      (i₁ := p) (i₂ := 0) (i₁₂ := i + 1)
      (by
        rw [ComplexShape.next_eq_self']
        · simp [ComplexShape.down_Rel]
        · intro k hk
          rw [ComplexShape.down_Rel] at hk
          omega), zero_comp, add_zero]
    -- the horizontal part of the right hand side
    rw [HomologicalComplex₂.d₁_eq (K := bicomplexObj B) (c₁₂ := ComplexShape.up ℤ)
      (h := (ComplexShape.up_Rel ℤ p (p + 1)).mpr rfl) (i₂ := 0) (i₁₂ := i + 1)
      (h' := by show p + 1 - ((0 : ℕ) : ℤ) = i + 1; omega)]
    rw [eps₁_val, one_smul, Category.assoc, epsFam_comp_ιMapObj, augComp, dif_pos rfl]
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
    simp only [Category.assoc]
    rw [HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom, ← Category.assoc, augRes_naturality,
      Category.assoc, HomologicalComplex.d_comp_XIsoOfEq_hom]
  · -- the summand `(p,q)` contributes to the vertical differential only
    rw [augComp, dif_neg hq, zero_comp]
    rw [HomologicalComplex₂.d₁_eq (K := bicomplexObj B) (c₁₂ := ComplexShape.up ℤ)
      (h := (ComplexShape.up_Rel ℤ p (p + 1)).mpr rfl) (i₂ := q) (i₁₂ := i + 1)
      (h' := by show p + 1 - ((q : ℕ) : ℤ) = i + 1; omega)]
    rw [eps₁_val, one_smul, Category.assoc, epsFam_comp_ιMapObj]
    simp only [augComp, dite_eq_right hq, zero_comp, comp_zero, zero_add]
    rw [HomologicalComplex₂.d₂_eq (K := bicomplexObj B) (c₁₂ := ComplexShape.up ℤ) (i₁ := p)
      (i₂' := q - 1) (h := by rw [ComplexShape.down_Rel]; omega) (i₁₂ := i + 1)
      (h' := by
        show p - (((q - 1 : ℕ)) : ℤ) = i + 1
        have h1 : (1 : ℕ) ≤ q := by omega
        rw [Nat.cast_sub h1, Nat.cast_one]
        omega)]
    rw [Linear.units_smul_comp, Category.assoc, epsFam_comp_ιMapObj]
    by_cases hq1 : q = 1
    · subst hq1
      rw [augComp, dif_pos rfl]
      simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp, Nat.reduceSub,
        Nat.cast_zero, sub_zero]
      simp only [Category.assoc]
      rw [← Category.assoc, augRes_comp_d, zero_comp, smul_zero]
    · rw [augComp, dif_neg (by omega : ¬ (q - 1 = 0)), zero_comp, comp_zero, smul_zero]

/-- The comparison map `R.obj B ⟶ B` as a chain map of cochain complexes. -/
noncomputable def epsHom (B : Cpx) : R.obj B ⟶ B where
  f := epsFam B
  comm' := fun i j hij => epsFam_comm B hij

@[simp] lemma epsHom_f (B : Cpx) (n : ℤ) : (epsHom B).f n = epsFam B n := rfl

end Work.RESOL
