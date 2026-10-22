/-
AREA RESOL — the comparison map `ε : R ⟶ 𝟭 Cpx`.

`R : Cpx ⤳ Cpx` is the total complex of the column-wise resolutions
(`Submission/Work/RESOL/Bicomplex.lean`), and `epsHom B : R.obj B ⟶ B` is the augmentation
(`Submission/Work/RESOL/TotalRes.lean`, where the chain-map property is proved).  Here we
assemble these components into a natural transformation `ε : R ⟶ 𝟭 Cpx`, using the naturality of
the components (`Work.RESOL.epsFamNaturality`).
-/
import Mathlib
import Submission.Work.RESOL.TotalRes
import Submission.Work.RESOL.epsFamNaturality

open CategoryTheory Limits LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open HomologicalComplex

noncomputable section

namespace Work.RESOL

attribute [local instance 2000] Sheaf.instHasColimitsOfShape

attribute [local instance] Classical.propDecidable

/-- Naturality of `epsHom` at the level of morphisms of cochain complexes. -/
theorem epsHom_naturality {B B' : Cpx} (f : B ⟶ B') : epsHom B ≫ f = R.map f ≫ epsHom B' := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, epsHom_f]
  exact epsFamNaturality f n

/-- **The comparison map** `ε : R ⟶ 𝟭 Cpx`, whose component at `B` is the augmentation
`epsHom B : R.obj B ⟶ B`. -/
noncomputable def eps : R ⟶ 𝟭 Cpx where
  app B := epsHom B
  naturality {B B'} f := (epsHom_naturality f).symm

@[simp] lemma eps_app (B : Cpx) : (eps.app B) = epsHom B := rfl

end Work.RESOL
