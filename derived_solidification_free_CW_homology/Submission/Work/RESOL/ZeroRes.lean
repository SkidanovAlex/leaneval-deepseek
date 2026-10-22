/-
AREA RESOL — the resolution functor `R` on complexes and its augmentation `ε : R ⟶ 𝟭`.

`R B` is the total complex of the column-wise resolution of `B` (all columns, see
`RESOL/ZeroTotal.lean`), and `ε B : R B ⟶ B` is induced by the degreewise augmentation
`aug0` of `Rco` (see `RESOL/ZeroSetup.lean`).

The definition of `R` (as a functor) and of `ε` (as a natural transformation) is assembled from
the componentwise lemmas `totMapFam_id`, `totMapFam_comp`, `totMapFam_comm`, `epsFam_comm` and
`epsFam_naturality` below.
-/
import Submission.Work.RESOL.ZeroTotal
import Submission.Work.RESOL.zTotMapFam
import Submission.Work.RESOL.zEpsFam

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RESOL

namespace Zero

variable (F : LightCondAb ⥤ LightCondAb) [F.PreservesZeroMorphisms] (π : F ⟶ 𝟭 LightCondAb)
  (hπ : ∀ M, Epi (π.app M))

/-- The functoriality map is the identity on the identity. -/
theorem totMapFam_id (B : Cpx) (n : ℤ) : totMapFam F π hπ (𝟙 B) n = 𝟙 _ :=
  (zTotMapFam F π hπ).1 B n

/-- The functoriality map is compatible with composition. -/
theorem totMapFam_comp {B B' B'' : Cpx} (f : B ⟶ B') (g : B' ⟶ B'') (n : ℤ) :
    totMapFam F π hπ (f ≫ g) n = totMapFam F π hπ f n ≫ totMapFam F π hπ g n :=
  (zTotMapFam F π hπ).2.1 B B' B'' f g n

/-- The functoriality map is a chain map. -/
theorem totMapFam_comm {B B' : Cpx} (f : B ⟶ B') {i j : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) :
    totMapFam F π hπ f i ≫ (totFull F π hπ B').d i j
      = (totFull F π hπ B).d i j ≫ totMapFam F π hπ f j :=
  (zTotMapFam F π hπ).2.2 B B' f i j hij

/-- The augmentation is a chain map. -/
theorem epsFam_comm (B : Cpx) {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) :
    epsFam F π hπ B i ≫ B.d i j
      = (totFull F π hπ B).d i j ≫ epsFam F π hπ B j :=
  (zEpsFam F π hπ).1 B i j hij

/-- The augmentation is natural. -/
theorem epsFam_naturality {B B' : Cpx} (f : B ⟶ B') (n : ℤ) :
    totMapFam F π hπ f n ≫ epsFam F π hπ B' n = epsFam F π hπ B n ≫ f.f n :=
  (zEpsFam F π hπ).2 B B' f n

/-- **The resolution functor**: the total complex of the column-wise resolution. -/
def R : Cpx ⥤ Cpx where
  obj B := totFull F π hπ B
  map {B B'} f :=
    { f := totMapFam F π hπ f
      comm' := fun i j hij => totMapFam_comm F π hπ f hij }
  map_id B := HomologicalComplex.hom_ext _ _ (fun n => totMapFam_id F π hπ B n)
  map_comp {B B' B''} f g :=
    HomologicalComplex.hom_ext _ _ (fun n => totMapFam_comp F π hπ f g n)

/-- **The augmentation** `R B ⟶ B`. -/
def eps : R F π hπ ⟶ 𝟭 Cpx where
  app B := { f := epsFam F π hπ B, comm' := fun i j hij => epsFam_comm F π hπ B hij }
  naturality {B B'} f :=
    HomologicalComplex.hom_ext _ _ (fun n => by
      simp only [HomologicalComplex.comp_f, Functor.id_map]
      change totMapFam F π hπ f n ≫ epsFam F π hπ B' n = epsFam F π hπ B n ≫ f.f n
      exact epsFam_naturality F π hπ f n)

end Zero

end Work.RESOL
