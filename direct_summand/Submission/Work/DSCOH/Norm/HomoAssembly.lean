/-
Area DSCOH (curric-46) — the normalization comparison: the categorical assembly of the homotopy.

This file contains the categorical part of the proof that the "degenerate simplices" homotopy
`Work.DSCOH.Norm.semiHom` connects `𝟙` with `ordProj ≫ ordIncl` on the semi-ordered Čech
complex:

* `semiD_comp` : the component formula for the semi-ordered differential;
* `Dterm`/`Hterm` : the individual terms of the two differentials, at a fixed component `y`;
* `lhs_eq_sum` : the expansion of the `y`-component of `dh + hd` as the sum of the `Dterm`s and
  the `Hterm`s;
* `ordProj_ordIncl_comp` / `rhs_comp` : the component formula for `ordProj ≫ ordIncl`;
* `canonical_comp_eq` : the comparison of two canonical composites with the same read index;
* `Dterm_castSucc_add_succ` : the cancellation of the two middle terms of the first differential;
* the `ℕ`-indexed versions `DtermN`/`HtermN` of the terms and the conversion lemmas
  `sum_Dterm`/`sum_Hterm`, used to split the sums at the threshold `frA`.
-/
import Mathlib
import Submission.Work.DSCOH.Norm.HomoStruct
import Submission.Work.DSCOH.Struct.frV_eq_of_between
import Submission.Work.DSCOH.Struct.frV_lt_of_gt
import Submission.Work.DSCOH.Struct.lt_of_lt_le_frA
import Submission.Work.DSCOH.Struct.readD_lt
import Submission.Work.DSCOH.Struct.readD_gt
import Submission.Work.DSCOH.Struct.readD_mid
import Submission.Work.DSCOH.Struct.readH_eq

namespace Work.DSCOH.Norm

open CategoryTheory Limits Opposite TopologicalSpace
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

universe u v w

variable {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
variable {ι : Type w} [LinearOrder ι] [Fintype ι]

/-- Any two canonical maps (i.e. `P.map` of morphisms of opens with the same source and target)
between two sections of `P` over opens of tuples are equal: the hom-sets of `Opens X` are
subsingletons. -/
lemma tupleMod_map_eq {P : (Opens X)ᵒᵖ ⥤ ModuleCat A} {V W : (Opens X)ᵒᵖ} (f g : V ⟶ W) :
    P.map f = P.map g := by
  rw [Subsingleton.elim f g]

/-- Two composites of canonical maps with the same source and target are equal. -/
lemma tupleMod_comp_eq {P : (Opens X)ᵒᵖ ⥤ ModuleCat A} {V W Z : (Opens X)ᵒᵖ}
    (f f' : V ⟶ W) (g g' : W ⟶ Z) : P.map f ≫ P.map g = P.map f' ≫ P.map g' := by
  rw [← P.map_comp, ← P.map_comp]
  exact tupleMod_map_eq _ _

section
variable [HasProducts (ModuleCat A)] (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)

/-- The component formula for the semi-ordered Čech differential. -/
lemma semiD_comp (n : ℕ) (y : SemiIdx ι (n + 1)) :
    semiD P U n ≫ Pi.π (fun w : SemiIdx ι (n + 1) => tupleMod P U w.val) y =
      ∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) •
        (Pi.π (fun w : SemiIdx ι n => tupleMod P U w.val)
            ⟨del y.val b, monotone_del y.val b y.property⟩ ≫ resDel P U y.val b) :=
  Pi.lift_comp_π _ _

/-- The `b`-th term of the first differential, as a morphism into the `y`-component. -/
noncomputable def Dterm (k : ℕ) (y : SemiIdx ι (k + 1)) (b : Fin (k + 2)) :
    semiTerm P U (k + 1) ⟶ tupleMod P U y.val :=
  (-1 : ℤ) ^ (b : ℕ) •
    (semiHomComp P U k ⟨del y.val b, monotone_del y.val b y.property⟩ ≫ resDel P U y.val b)

/-- The `c`-th term of the second differential, as a morphism into the `y`-component. -/
noncomputable def Hterm (k : ℕ) (y : SemiIdx ι (k + 1)) (c : Fin (k + 3)) :
    semiTerm P U (k + 1) ⟶ tupleMod P U y.val :=
  if hy : StrictMono y.val then 0
  else (-1 : ℤ) ^ ((frA y.val y.property hy : ℕ) + (c : ℕ)) •
    (Pi.π (fun w : SemiIdx ι (k + 1) => tupleMod P U w.val)
        ⟨del (dup y.val (frA y.val y.property hy).castSucc) c,
          monotone_del _ _ (monotone_dup y.property _)⟩
      ≫ (resDel P U (dup y.val (frA y.val y.property hy).castSucc) c
          ≫ isoDup P U y.val (frA y.val y.property hy).castSucc))

/-- The `y`-component of the two differential terms of the homotopy identity, expanded into the
individual terms `Dterm` and `Hterm`. -/
lemma lhs_eq_sum (k : ℕ) (y : SemiIdx ι (k + 1)) :
    ((semiHom P U k ≫ semiD P U k) + (semiD P U (k + 1) ≫ semiHom P U (k + 1)))
        ≫ Pi.π (fun w : SemiIdx ι (k + 1) => tupleMod P U w.val) y =
      (∑ b : Fin (k + 2), Dterm P U k y b) + (∑ c : Fin (k + 3), Hterm P U k y c) := by
  rw [Preadditive.add_comp]
  congr 1
  · rw [Category.assoc, semiD_comp, Preadditive.comp_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [Linear.comp_smul, Dterm]
    rw [← Category.assoc, semiHom_comp]
  · by_cases hy : StrictMono y.val
    · rw [Category.assoc, semiHom_comp, semiHomComp_of_strictMono P U hy, comp_zero]
      simp only [Hterm, dif_pos hy, Finset.sum_const_zero]
    · rw [Category.assoc, semiHom_comp, semiHomComp_of_not_strictMono P U hy]
      rw [Linear.comp_smul, ← Category.assoc, semiD_comp, Preadditive.sum_comp]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      simp only [Hterm, dif_neg hy]
      rw [Linear.smul_comp, Category.assoc, smul_smul, ← pow_add]
      congr 1

end

variable [HasProducts (ModuleCat A)] (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)

lemma ordProj_comp (k : ℕ) (z : OrdIdx ι (k + 1)) :
    ordProj P U (k + 1) ≫ Pi.π (fun w : OrdIdx ι (k + 1) => tupleMod P U w.val) z =
      Pi.π (fun w : SemiIdx ι (k + 1) => tupleMod P U w.val) ⟨z.val, z.property.monotone⟩ :=
  Pi.lift_comp_π _ _

lemma ordIncl_comp (k : ℕ) (y : SemiIdx ι (k + 1)) :
    ordIncl P U (k + 1) ≫ Pi.π (fun w : SemiIdx ι (k + 1) => tupleMod P U w.val) y =
      (if h : StrictMono y.val then
        (Pi.π (fun w : OrdIdx ι (k + 1) => tupleMod P U w.val) ⟨y.val, h⟩ :
          ordTerm P U (k + 1) ⟶ tupleMod P U y.val) else 0) :=
  Pi.lift_comp_π _ _

lemma ordProj_ordIncl_comp (k : ℕ) (y : SemiIdx ι (k + 1)) :
    (ordProj P U (k + 1) ≫ ordIncl P U (k + 1)) ≫
        Pi.π (fun w : SemiIdx ι (k + 1) => tupleMod P U w.val) y
      = (if h : StrictMono y.val then
          Pi.π (fun w : SemiIdx ι (k + 1) => tupleMod P U w.val) y else 0) := by
  rw [Category.assoc, ordIncl_comp]
  split_ifs with h
  · rw [ordProj_comp]
  · rw [comp_zero]

lemma rhs_comp (k : ℕ) (y : SemiIdx ι (k + 1)) :
    (𝟙 (semiTerm P U (k + 1)) - ordProj P U (k + 1) ≫ ordIncl P U (k + 1)) ≫
        Pi.π (fun w : SemiIdx ι (k + 1) => tupleMod P U w.val) y
      = (if h : StrictMono y.val then 0 else
          Pi.π (fun w : SemiIdx ι (k + 1) => tupleMod P U w.val) y) := by
  rw [Preadditive.sub_comp, Category.id_comp, ordProj_ordIncl_comp]
  by_cases h : StrictMono y.val <;> simp [h]

section pairing
variable [HasProducts (ModuleCat A)] (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)

/-- The `ℕ`-indexed version of the first differential's terms. -/
noncomputable def DtermN (k : ℕ) (y : SemiIdx ι (k + 1)) (i : ℕ) :
    semiTerm P U (k + 1) ⟶ tupleMod P U y.val :=
  if h : i < k + 2 then Dterm P U k y ⟨i, h⟩ else 0

/-- The `ℕ`-indexed version of the second differential's terms. -/
noncomputable def HtermN (k : ℕ) (y : SemiIdx ι (k + 1)) (i : ℕ) :
    semiTerm P U (k + 1) ⟶ tupleMod P U y.val :=
  if h : i < k + 3 then Hterm P U k y ⟨i, h⟩ else 0

lemma DtermN_eq {k : ℕ} (y : SemiIdx ι (k + 1)) (i : Fin (k + 2)) :
    DtermN P U k y i.1 = Dterm P U k y i := by
  rw [DtermN, dif_pos i.isLt]

lemma HtermN_eq {k : ℕ} (y : SemiIdx ι (k + 1)) (i : Fin (k + 3)) :
    HtermN P U k y i.1 = Hterm P U k y i := by
  rw [HtermN, dif_pos i.isLt]

lemma sum_Dterm {k : ℕ} (y : SemiIdx ι (k + 1)) :
    (∑ b : Fin (k + 2), Dterm P U k y b) =
      ∑ i ∈ Finset.range (k + 2), DtermN P U k y i := by
  rw [← Fin.sum_univ_eq_sum_range (DtermN P U k y) (k + 2)]
  exact Finset.sum_congr rfl (fun i _ => (DtermN_eq P U y i).symm)

lemma sum_Hterm {k : ℕ} (y : SemiIdx ι (k + 1)) :
    (∑ c : Fin (k + 3), Hterm P U k y c) =
      ∑ i ∈ Finset.range (k + 3), HtermN P U k y i := by
  rw [← Fin.sum_univ_eq_sum_range (HtermN P U k y) (k + 3)]
  exact Finset.sum_congr rfl (fun i _ => (HtermN_eq P U y i).symm)

end pairing

section pairing2
variable [HasProducts (ModuleCat A)] (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)

/-- Two canonical composites whose read indices agree (up to the corresponding transport of the
index) are equal. -/
lemma canonical_comp_eq {k : ℕ} {u₁ u₂ : SemiIdx ι k} (hu : u₁ = u₂) {W : (Opens X)ᵒᵖ}
    {α₁ : op (tupleOp U u₁.val) ⟶ W} {α₂ : op (tupleOp U u₂.val) ⟶ W} :
    P.map α₁ = eqToHom (congrArg (fun v : SemiIdx ι k => tupleMod P U v.val) hu) ≫ P.map α₂ := by
  rw [← eqToHom_map P (p := congrArg (fun v : SemiIdx ι k => op (tupleOp U v.val)) hu)]
  rw [← P.map_comp]
  exact tupleMod_map_eq α₁ (eqToHom _ ≫ α₂)
variable [HasProducts (ModuleCat A)] (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)

/-- The two middle terms of the first differential cancel each other: deleting the first or the
second copy of the first repeated value gives the same tuple. -/
lemma Dterm_castSucc_add_succ {k : ℕ} (y : SemiIdx ι (k + 1)) (hy : Monotone y.val)
    (hh : ¬ StrictMono y.val) :
    Dterm P U k y (frA y.val hy hh).castSucc + Dterm P U k y (frA y.val hy hh).succ = 0 := by
  have hdel : del y.val (frA y.val hy hh).castSucc = del y.val (frA y.val hy hh).succ :=
    del_castSucc_eq_del_succ y.val _ (firstRepeat_spec y.val hy hh)
  by_cases h1 : StrictMono (del y.val (frA y.val hy hh).castSucc)
  · have h2 : StrictMono (del y.val (frA y.val hy hh).succ) := by rwa [hdel] at h1
    rw [Dterm, Dterm, semiHomComp_of_strictMono P U h1, semiHomComp_of_strictMono P U h2]
    simp only [zero_comp, smul_zero, add_zero]
  · have h2 : ¬ StrictMono (del y.val (frA y.val hy hh).succ) := by rwa [hdel] at h1
    rw [Dterm, Dterm, semiHomComp_of_not_strictMono P U h1, semiHomComp_of_not_strictMono P U h2]
    simp only [Linear.smul_comp, Category.assoc, smul_smul]
    set fr1 := firstRepeat (del y.val (frA y.val hy hh).castSucc)
      (monotone_del y.val (frA y.val hy hh).castSucc y.property) h1 with hfr1
    set fr2 := firstRepeat (del y.val (frA y.val hy hh).succ)
      (monotone_del y.val (frA y.val hy hh).succ y.property) h2 with hfr2
    have hfr : fr1 = fr2 := by rw [hfr1, hfr2]; simp only [hdel]
    have hu : (⟨dup (del y.val (frA y.val hy hh).castSucc) fr1.castSucc,
        monotone_dup (monotone_del y.val (frA y.val hy hh).castSucc y.property) _⟩ :
        SemiIdx ι (k + 1))
        = ⟨dup (del y.val (frA y.val hy hh).succ) fr2.castSucc,
        monotone_dup (monotone_del y.val (frA y.val hy hh).succ y.property) _⟩ :=
      Subtype.ext (by simp only [hdel, hfr])
    have hX1 : isoDup P U (del y.val (frA y.val hy hh).castSucc) fr1.castSucc
          ≫ resDel P U y.val (frA y.val hy hh).castSucc
        = P.map ((opDup U (del y.val (frA y.val hy hh).castSucc) fr1.castSucc).op
            ≫ (homOfLE (leOfHom (opDel U y.val (frA y.val hy hh).castSucc))).op) := by
      rw [isoDup, resDel, ← P.map_comp]
    have hX2 : isoDup P U (del y.val (frA y.val hy hh).succ) fr2.castSucc
          ≫ resDel P U y.val (frA y.val hy hh).succ
        = P.map ((opDup U (del y.val (frA y.val hy hh).succ) fr2.castSucc).op
            ≫ (homOfLE (leOfHom (opDel U y.val (frA y.val hy hh).succ))).op) := by
      rw [isoDup, resDel, ← P.map_comp]
    have key := canonical_comp_eq P U hu
      (α₁ := (opDup U (del y.val (frA y.val hy hh).castSucc) fr1.castSucc).op
          ≫ (homOfLE (leOfHom (opDel U y.val (frA y.val hy hh).castSucc))).op)
      (α₂ := (opDup U (del y.val (frA y.val hy hh).succ) fr2.castSucc).op
          ≫ (homOfLE (leOfHom (opDel U y.val (frA y.val hy hh).succ))).op)
    rw [hX1, hX2, key, ← Category.assoc,
      Pi.π_comp_eqToHom (f := fun v : SemiIdx ι (k + 1) => tupleMod P U v.val) hu]
    have hc : (-1 : ℤ) ^ ((frA y.val hy hh).castSucc : ℕ) * (-1 : ℤ) ^ (fr1 : ℕ)
        = -((-1 : ℤ) ^ ((frA y.val hy hh).succ : ℕ) * (-1 : ℤ) ^ (fr2 : ℕ)) := by
      rw [hfr, Fin.val_succ, Fin.val_castSucc]
      ring
    rw [hc, neg_smul]
    abel

end pairing2

end Work.DSCOH.Norm
