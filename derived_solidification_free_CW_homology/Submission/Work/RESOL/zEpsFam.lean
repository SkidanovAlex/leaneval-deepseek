/-
AREA RESOL — the augmentation `ε : R ⟶ 𝟭` of the resolution is a morphism of complexes
and is natural in the complex.

For a cochain complex `B` of light condensed abelian groups, `totFull B` is the total complex
of the column-wise resolution of `B` (all columns, see `RESOL/ZeroTotal.lean`), `epsFam B n` is
the degree `n` component of the augmentation `R B ⟶ B` (it augments the summands
`(Rco.obj (B.X q)).X 0` with `q = n` and kills the others), and `totMapFam f n` is the degree
`n` component of `R f` for a morphism of complexes `f`.

The theorem `Work.RESOL.zEpsFam` below is the conjunction of the two componentwise identities
from which the chain-map and naturality properties of `ε` follow:

* `epsFam B i ≫ B.d i j = (totFull B).d i j ≫ epsFam B j` (commutation with the differentials);
* `totMapFam f n ≫ epsFam B' n = epsFam B n ≫ f.f n` (naturality).

The proof is a computation with the coproduct summands of the total complex.  The auxiliary
lemmas `zEpsFam_vert` and `zEpsFam_horz` compute the two summands of the differential of the
total complex followed by `epsFam`, and `zEpsFam_kill` / `zEpsFam_aug0_map` supply the
inputs `aug0_comp_d` / `aug0_naturality` of the degreewise resolution.
-/
import Mathlib
import Submission.Work.RESOL.ZeroTotal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.RESOL

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

namespace Zero

variable (F : LightCondAb ⥤ LightCondAb) [F.PreservesZeroMorphisms] (π : F ⟶ 𝟭 LightCondAb)
  (hπ : ∀ M, Epi (π.app M))

/-! ## The components of the augmentation -/

/-- The component of `epsFam` on the summand with index `x` of the total complex. -/
lemma zEpsFam_ι (B : Cpx) (n : ℤ) (x : TotIdx topP n) :
    Sigma.ι (totFam F π hπ topP B n) x ≫ epsFam F π hπ B n
      = (if h : x.1.2 = 0 then
          (((Rco F π hπ).obj (B.X x.1.1)).XIsoOfEq h).hom
            ≫ aug0 F π hπ (B.X x.1.1)
            ≫ (B.XIsoOfEq (by obtain ⟨h1, h2⟩ := x.2; omega)).hom
         else 0) := by
  rw [epsFam, Sigma.ι_comp_desc]
  rfl

/-- The (unfolded) total index reached by the vertical part of the differential. -/
lemma zEpsFam_totVIdx_snd {P : ℤ → Prop} {n : ℤ} (x : TotIdx P n) :
    (totVIdx x).1.2 = x.1.2 + 1 := rfl

/-- The (unfolded) total index reached by the horizontal part of the differential. -/
lemma zEpsFam_totHIdx_snd {P : ℤ → Prop} {n : ℤ} (hP : ∀ q, P q → P (q+1)) (x : TotIdx P n) :
    (totHIdx hP x).1.2 = x.1.2 := rfl

/-! ## The two summands of the differential, followed by the augmentation -/

/-- The vertical part of the differential, followed by the augmentation: only the summands with
`p = -1` survive, and there the resolution differential meets `aug0`. -/
lemma zEpsFam_vert (B : Cpx) (n : ℤ) (x : TotIdx topP n) :
    totVpart F π hπ topP B n x ≫ epsFam F π hπ B (n+1)
      = (if h : x.1.2 + 1 = 0 then
           ((Rco F π hπ).obj (B.X x.1.1)).d x.1.2 (x.1.2 + 1)
             ≫ (((Rco F π hπ).obj (B.X x.1.1)).XIsoOfEq h).hom
             ≫ aug0 F π hπ (B.X x.1.1)
             ≫ (B.XIsoOfEq (by omega)).hom
         else 0) := by
  rw [totVpart, Category.assoc, zEpsFam_ι]
  by_cases h : x.1.2 + 1 = 0
  · rw [dite_eq_left (show (totVIdx x).1.2 = 0 by rw [zEpsFam_totVIdx_snd]; exact h)]
    rw [dite_eq_left h]
    rfl
  · rw [dite_eq_right (show ¬ ((totVIdx x).1.2 = 0) by rw [zEpsFam_totVIdx_snd]; exact h)]
    rw [dite_eq_right h, comp_zero]

/-- The horizontal part of the differential, followed by the augmentation: only the summands
with `p = 0` survive, and there the augmentation is natural. -/
lemma zEpsFam_horz (B : Cpx) (n : ℤ) (x : TotIdx topP n) :
    totHpart F π hπ topP topP_step B n x ≫ epsFam F π hπ B (n+1)
      = sgn x.1.2 • (((Rco F π hπ).map (B.d x.1.1 (x.1.1+1))).f x.1.2
          ≫ (if h : x.1.2 = 0 then
               (((Rco F π hπ).obj (B.X (x.1.1+1))).XIsoOfEq h).hom
                 ≫ aug0 F π hπ (B.X (x.1.1+1))
                 ≫ (B.XIsoOfEq (by omega)).hom
             else 0)) := by
  rw [totHpart, Linear.units_smul_comp, Category.assoc, zEpsFam_ι]
  by_cases h : x.1.2 = 0
  · rw [dite_eq_left (show (totHIdx topP_step x).1.2 = 0 by rw [zEpsFam_totHIdx_snd]; exact h)]
    rw [dite_eq_left h]
    rfl
  · rw [dite_eq_right (show ¬ ((totHIdx topP_step x).1.2 = 0) by
      rw [zEpsFam_totHIdx_snd]; exact h)]
    rw [dite_eq_right h, comp_zero, smul_zero]

/-! ## Auxiliary identities for `aug0` -/

/-- In degree `-1` the differential of the resolution is followed by `aug0` by zero. -/
lemma zEpsFam_aug0_d (M : LightCondAb) {W : LightCondAb} {g : M ⟶ W} :
    ((Rco F π hπ).obj M).d (-1) 0 ≫ (aug0 F π hπ M ≫ g) = 0 := by
  rw [← Category.assoc, aug0_comp_d, zero_comp]

/-- Transporting the differential of a complex along a proof `p = -1`. -/
lemma zEpsFam_d_eq (K : Cpx) {p j : ℤ} {W : LightCondAb} {f : K.X j ⟶ W} (h : p = -1) :
    K.d p j ≫ f = (K.XIsoOfEq h).hom ≫ (K.d (-1) j ≫ f) := by
  rw [← Category.assoc, HomologicalComplex.XIsoOfEq_hom_comp_d]

/-- The composite `d ≫ (eqToHom ≫ aug0)` of a resolution vanishes when the source index is `-1`
and the target index of the transported differential is `0`. -/
lemma zEpsFam_kill (M : LightCondAb) {i j : ℤ} {W : LightCondAb} {f : M ⟶ W}
    (h1 : i = -1) (h2 : j = 0) :
    ((Rco F π hπ).obj M).d i j ≫ (((Rco F π hπ).obj M).XIsoOfEq h2).hom
      ≫ (aug0 F π hπ M ≫ f) = 0 := by
  rw [← Category.assoc, HomologicalComplex.d_comp_XIsoOfEq_hom]
  rw [zEpsFam_d_eq (K := (Rco F π hπ).obj M) (j := 0) (W := W) (f := aug0 F π hπ M ≫ f) h1]
  rw [zEpsFam_aug0_d]
  rw [comp_zero]

/-- The vertical part of the differential, followed by the augmentation, in the case where the
source index is `-1`: this summand contributes zero. -/
lemma zEpsFam_vert_zero (B : Cpx) (n : ℤ) (x : TotIdx topP n) (h : x.1.2 + 1 = 0) :
    totVpart F π hπ topP B n x ≫ epsFam F π hπ B (n+1) = 0 := by
  rw [zEpsFam_vert]
  rw [dite_eq_left h]
  exact zEpsFam_kill (F := F) (π := π) (hπ := hπ) (M := B.X x.1.1) (i := x.1.2)
    (j := x.1.2 + 1) (W := B.X (n+1)) (f := (B.XIsoOfEq (by omega)).hom)
    (h1 := (show x.1.2 = -1 by omega)) h

/-- The naturality of `aug0`, in the form needed for the horizontal summands. -/
lemma zEpsFam_aug0_map (M N : LightCondAb) (f : M ⟶ N) {W : LightCondAb} {g : N ⟶ W} :
    ((Rco F π hπ).map f).f 0 ≫ (aug0 F π hπ N ≫ g) = aug0 F π hπ M ≫ (f ≫ g) := by
  rw [← Category.assoc, aug0_naturality, Category.assoc]

/-- The naturality of the index transport `XIsoOfEq` under a morphism of complexes, in the form
needed for the horizontal summands. -/
lemma zEpsFam_map_smooth {K L : Cpx} (φ : K ⟶ L) {n n' : ℤ} {W : LightCondAb} {f : L.X n' ⟶ W}
    (h : n = n') :
    φ.f n ≫ ((L.XIsoOfEq h).hom ≫ f) = (K.XIsoOfEq h).hom ≫ (φ.f n' ≫ f) := by
  rw [← Category.assoc, HomologicalComplex.XIsoOfEq_hom_naturality, Category.assoc]

/-! ## The two identities -/

/-- The augmentation `R B ⟶ B` commutes with the differentials. -/
lemma zEpsFam_comm (B : Cpx) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    epsFam F π hπ B i ≫ B.d i j = (totFull F π hπ B).d i j ≫ epsFam F π hπ B j := by
  have hij' : i + 1 = j := (ComplexShape.up_Rel ℤ i j).mp hij
  subst hij'
  have hd : (totFull F π hπ B).d i (i+1) = totDc F π hπ topP topP_step B i := by
    show (totCpx F π hπ topP topP_step B).d i (i+1) = _
    simp only [totCpx, totD]
    exact dite_eq_left trivial
  rw [hd]
  apply Sigma.hom_ext
  intro x
  obtain ⟨hsum, -⟩ := x.2
  rw [← Category.assoc, zEpsFam_ι]
  rw [← Category.assoc, totDc_apply, Preadditive.add_comp]
  by_cases hp0 : x.1.2 = 0
  · rw [dite_eq_left hp0]
    rw [zEpsFam_vert, zEpsFam_horz]
    rw [dite_eq_right (show ¬ (x.1.2 + 1 = 0) by omega)]
    rw [dite_eq_left hp0]
    rw [zero_add]
    have hsgn : sgn (x.1.2) = 1 := by rw [sgn, hp0, ComplexShape.ε_zero]
    rw [hsgn, one_smul]
    simp only [Category.assoc]
    rw [HomologicalComplex.XIsoOfEq_hom_comp_d]
    rw [zEpsFam_map_smooth, zEpsFam_aug0_map, HomologicalComplex.d_comp_XIsoOfEq_hom]
  · rw [dite_eq_right hp0]
    by_cases hp1 : x.1.2 + 1 = 0
    · rw [zEpsFam_vert_zero (F := F) (π := π) (hπ := hπ) (h := hp1), zEpsFam_horz]
      rw [dite_eq_right hp0]
      simp only [zero_comp, comp_zero, smul_zero, add_zero]
    · rw [zEpsFam_vert, zEpsFam_horz]
      rw [dite_eq_right hp1, dite_eq_right hp0]
      simp only [zero_comp, comp_zero, smul_zero, add_zero]

/-- The augmentation `R B ⟶ B` is natural in the complex. -/
lemma zEpsFam_naturality {B B' : Cpx} (f : B ⟶ B') (n : ℤ) :
    totMapFam F π hπ f n ≫ epsFam F π hπ B' n = epsFam F π hπ B n ≫ f.f n := by
  apply Sigma.hom_ext
  intro x
  obtain ⟨hsum, -⟩ := x.2
  rw [← Category.assoc, totMapFam, Sigma.ι_comp_desc, Category.assoc]
  rw [zEpsFam_ι]
  rw [← Category.assoc, zEpsFam_ι]
  by_cases hp0 : x.1.2 = 0
  · rw [dite_eq_left hp0, dite_eq_left hp0]
    simp only [Category.assoc]
    rw [zEpsFam_map_smooth, zEpsFam_aug0_map, HomologicalComplex.XIsoOfEq_hom_naturality]
  · rw [dite_eq_right hp0, dite_eq_right hp0]
    simp only [zero_comp, comp_zero]

end Zero

end

/-- The augmentation `ε : R ⟶ 𝟭` of the resolution of a complex is a morphism of complexes
(commutation with the differentials) and is natural in the complex. -/
theorem zEpsFam (F : CategoryTheory.Functor LightCondAb LightCondAb)
    [F.PreservesZeroMorphisms] (π : F ⟶ CategoryTheory.Functor.id LightCondAb)
    (hπ : ∀ M, CategoryTheory.Epi (π.app M)) :
    (∀ (B : Work.RESOL.Cpx) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j),
        CategoryTheory.CategoryStruct.comp (Work.RESOL.Zero.epsFam F π hπ B i) (B.d i j)
          = CategoryTheory.CategoryStruct.comp ((Work.RESOL.Zero.totFull F π hπ B).d i j)
              (Work.RESOL.Zero.epsFam F π hπ B j))
    ∧ (∀ (B B' : Work.RESOL.Cpx) (f : B ⟶ B') (n : ℤ),
        CategoryTheory.CategoryStruct.comp (Work.RESOL.Zero.totMapFam F π hπ f n)
            (Work.RESOL.Zero.epsFam F π hπ B' n)
          = CategoryTheory.CategoryStruct.comp (Work.RESOL.Zero.epsFam F π hπ B n) (f.f n)) :=
  ⟨fun B i j hij => Zero.zEpsFam_comm F π hπ B i j hij,
   fun B B' f n => Zero.zEpsFam_naturality F π hπ f n⟩

end Work.RESOL
