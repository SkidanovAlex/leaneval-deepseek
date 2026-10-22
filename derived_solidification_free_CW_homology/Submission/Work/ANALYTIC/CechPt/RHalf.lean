import Mathlib
import Submission.Work.ANALYTIC.CechPt.SolidChain
import Submission.Work.ANALYTIC.CechPt.Bridge
import Submission.Work.ANALYTIC.CechPt.binaryExp_epi
import Submission.Work.ANALYTIC.CechPt.IntervalAug
import Submission.Work.TOOLKIT.Main

/-!
# The Čech resolution of the interval, in the `cechTerm` model

`Work.ANALYTIC.CechPt.cech_descent` (`CechPt/Bridge.lean`) proves that the augmentation of the
Čech complex `cechComplex β` of the binary expansion is a quasi-isomorphism.  This module
transports that statement to the explicit model `Rchain`/`Rcpx` of `CechPt/SolidChain.lean`, whose
terms are `ℤ[cechTerm p]` and whose differentials are the alternating sums of the face maps
`cechFace p i`: the level isomorphism `dRLvlIso` of `CechPt/dR_comp.lean` is a chain map by
`dR_eq_level`, hence gives an isomorphism of complexes `Rcpx ≅ cechComplex β`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace Work.ANALYTIC.CechPt

open Work.ATOM

/-! ## The level isomorphism is a chain map -/

/-- The level isomorphism, landing in `dRLvlChain.X p` (rather than in the extension of
`dRLvlChain`, which is propositionally, but not definitionally, the same object). -/
noncomputable def dRLvlIso' (p : ℕ) : zfree (cechTerm p) ≅ dRLvlChain.X p :=
  dRLvlIso p ≪≫ dRLvlExtIso p

/-- The differential of `Rchain` is the differential of `dRLvlChain`, conjugated by the level
isomorphisms `dRLvlIso'`. -/
theorem dR_eq_level' (p : ℕ) :
    dR p = (dRLvlIso' (p+1)).hom ≫ dRLvlChain.d (p+1) p ≫ (dRLvlIso' p).inv := by
  rw [dR_eq_level p]
  change (dRLvlIso (p+1)).hom ≫ (cechComplex beta).d (-(p+1:ℤ)) (-(p:ℤ)) ≫
      (dRLvlIso p).inv = _
  rw [dRLvlExtIso_d p]
  simp only [dRLvlIso', Iso.trans_hom, Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc]

/-- The isomorphism `Rchain ⟶ dRLvlChain` whose components are the level isomorphisms
`dRLvlIso'`. -/
noncomputable def chainIsoHom : Rchain ⟶ dRLvlChain where
  f p := (dRLvlIso' p).hom
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    simp only [Rchain, ChainComplex.of_d]
    rw [dR_eq_level' j]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The inverse of `chainIsoHom`. -/
noncomputable def chainIsoInv : dRLvlChain ⟶ Rchain where
  f p := (dRLvlIso' p).inv
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    simp only [Rchain, ChainComplex.of_d]
    rw [dR_eq_level' j, Iso.inv_hom_id_assoc]

/-- **The Čech complex in the `cechTerm` model is the Čech complex of the nerve.** -/
noncomputable def chainIso : Rchain ≅ dRLvlChain where
  hom := chainIsoHom
  inv := chainIsoInv
  hom_inv_id := by
    apply HomologicalComplex.hom_ext
    intro p
    exact Iso.hom_inv_id _
  inv_hom_id := by
    apply HomologicalComplex.hom_ext
    intro p
    exact Iso.inv_hom_id _

/-- The induced isomorphism of cochain complexes `Rcpx ≅ cechComplex β`. -/
noncomputable def cpxIso : Rcpx ≅ cechComplex beta :=
  (ComplexShape.embeddingDownNat.extendFunctor LightCondAb).mapIso chainIso

/-! ## The augmentation -/

/-- The augmentation of the free Čech complex of the binary expansion, in the `cechTerm` model:
`Rcpx ⟶ ℤ[[0,1]]` (placed in degree `0`). -/
noncomputable def cechAugR : Rcpx ⟶
    (HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).obj
      ((free ℤ).obj intervalCond) :=
  cpxIso.hom ≫ cechAug beta

/-- `cechAugR` is a quasi-isomorphism, because it is the conjugate (by the isomorphism of
complexes `cpxIso`) of the Čech augmentation `cechAug β`, which is one by
`Work.ANALYTIC.CechPt.quasiIso_cechAug`. -/
theorem quasiIso_cechAugR : QuasiIso cechAugR := by
  have hβ : QuasiIso (cechAug beta) := quasiIso_cechAug beta beta_epi
  haveI : IsIso (DerivedCategory.Q.map (cechAug beta)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso LightCondAb (cechAug beta)).mpr hβ
  have h : IsIso (DerivedCategory.Q.map cechAugR) := by
    show IsIso (DerivedCategory.Q.map (cpxIso.hom ≫ cechAug beta))
    rw [Functor.map_comp]
    infer_instance
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso LightCondAb cechAugR).mp h

/-- **The free Čech complex of the Cantor cover resolves `ℤ[[0,1]]`**, as a solid-equivalence. -/
theorem solidEquiv_cechAugR :
    Submission.Blueprint.SolidEquiv (DerivedCategory.Q.map cechAugR) :=
  (Work.TOOLKIT.toolkit_prop).of_iso _
    ((DerivedCategory.isIso_Q_map_iff_quasiIso LightCondAb cechAugR).mpr quasiIso_cechAugR)

end Work.ANALYTIC.CechPt
