import Mathlib
import Submission.Work.ANALYTIC.CechPt.DualComplex
import Submission.Work.ANALYTIC.CechPt.cechCompare_isIso

/-!
# The Čech differential `dR` squares to zero

`dR p = ∑ i, (-1)^i ℤ[cechFace p i]` (`DualComplex`) is the alternating sum of the face maps of
the Čech nerve of the binary expansion `beta : C = {0,1}^ℕ ⟶ [0,1]`, presented on the light
profinite sets `cechTerm p` of `(p+1)`-tuples of points of the Cantor set with a common binary
expansion (`CechTermDefs`, `LevelModelDefs`).

Rather than checking the simplicial identities for `cechFace` directly by hand, we use the level
model: `ℤ[cechTerm p]` is isomorphic to the degree `-p` piece of the Čech cochain complex
`cechComplex beta` (`Nerve`), and under this isomorphism `dR p` is the differential `d` of that
complex.  Then `dR (p+1) ≫ dR p = 0` follows by telescoping the isomorphisms and using
`HomologicalComplex.d_comp_d` (`d ≫ d = 0`).

The comparison `ℤ[cechTerm p] ≅ (cechComplex beta).X (-p)` is built from the comparison map
`cechCompare p : cechTerm p ⟶ C^•_[0,1](p)` of `LevelModelDefs`, which is an isomorphism by
`cechCompare_isIso`, together with the fact that the complex is the extension of its `ℕ`-graded
part.  The naturality of `cechCompare` with respect to the face maps is proved here directly
from the universal property of the wide pullback (these lemmas are the ones used in the module
`cechComplexLevelModel`, which cannot be imported here because its import
`Submission.Work.ANALYTIC.CechPt.Contraction` clashes with
`Submission.Work.ANALYTIC.CechPt.cech_acyclic_type`, both of them declaring
`Work.ANALYTIC.CechPt.nerve_δ_π`).
-/

open CategoryTheory Limits LightProfinite LightCondensed AlgebraicTopology
open scoped Simplicial
open _root_.LightCondensed _root_.LightCondensed.Solid Work.ATOM

namespace Work.ANALYTIC.CechPt

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

/-! ## The face maps of the Čech nerve, on the projections of the wide pullback -/

/-- The `j`-th projection of the face map `δ i` of the Čech nerve of `beta` is the
`i.succAbove j`-th projection. -/
lemma dRNerve_delta_π (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) :
    SimplicialObject.δ (cechNerve beta) i ≫
      Limits.WidePullback.π (fun _ : Fin (n + 1) => beta) j =
      Limits.WidePullback.π (fun _ : Fin (n + 2) => beta) (Fin.succAbove i j) := by
  simp only [SimplicialObject.δ_def]
  unfold cechNerve
  rw [CategoryTheory.Arrow.cechNerve_map]
  simp only [CategoryTheory.Arrow.mk_hom]
  rw [Limits.WidePullback.lift_π]
  rfl

/-- The base of the face map `δ i` of the Čech nerve of `beta` is the base. -/
lemma dRNerve_delta_base (n : ℕ) (i : Fin (n + 2)) :
    SimplicialObject.δ (cechNerve beta) i ≫
      Limits.WidePullback.base (fun _ : Fin (n + 1) => beta) =
      Limits.WidePullback.base (fun _ : Fin (n + 2) => beta) := by
  simp only [SimplicialObject.δ_def]
  unfold cechNerve
  erw [CategoryTheory.Arrow.cechNerve_map]
  erw [Limits.WidePullback.lift_base]
  rfl

/-- The comparison maps `cechCompare p` are natural for the face maps `δ i` of the Čech nerve
of `beta` and the face maps `cechFace p i` of `cechTerm`. -/
theorem dRCompare_naturality (p : ℕ) (i : Fin (p + 2)) :
    CategoryTheory.CategoryStruct.comp (cechCompare (p + 1))
      (SimplicialObject.δ (cechNerve beta) i) =
    CategoryTheory.CategoryStruct.comp
      (lightProfiniteToLightCondSet.map (cechFace p i))
      (cechCompare p) := by
  apply Limits.WidePullback.hom_ext (arrows := fun _ : Fin (p + 1) => beta)
  · intro j
    erw [Category.assoc, dRNerve_delta_π, cechCompare_π,
      Category.assoc, cechCompare_π, ← Functor.map_comp, cechFace_cechProj]
  · erw [Category.assoc, dRNerve_delta_base, cechCompare_base,
      Category.assoc, cechCompare_base,
      ← Category.assoc, ← Functor.map_comp, cechFace_cechProj]
    exact (cechProj_beta_eq (p + 1) (i.succAbove 0)).symm

/-! ## The level model of the Čech complex -/

/-- The alternating face map complex of the free Čech nerve, in `ℕ`-grading. -/
abbrev dRLvlChain : ChainComplex LightCondAb ℕ :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj (cechFree beta)

/-- The Čech complex in degree `-p` is the `p`-th term of the chain complex `dRLvlChain`. -/
noncomputable def dRLvlExtIso (p : ℕ) : (cechComplex beta).X (-(p:ℤ)) ≅ dRLvlChain.X p :=
  HomologicalComplex.extendXIso dRLvlChain ComplexShape.embeddingDownNat
    (ComplexShape.embeddingDownNat_f p)

/-- The differential of the Čech complex, expressed through the differential of `dRLvlChain`. -/
lemma dRLvlExtIso_d (p : ℕ) : (cechComplex beta).d (-(p+1:ℤ)) (-(p:ℤ)) =
    (dRLvlExtIso (p+1)).hom ≫ dRLvlChain.d (p+1) p ≫ (dRLvlExtIso p).inv :=
  HomologicalComplex.extend_d_eq dRLvlChain ComplexShape.embeddingDownNat
    (ComplexShape.embeddingDownNat_f (p+1)) (ComplexShape.embeddingDownNat_f p)

/-- The comparison map `ℤ[cechTerm p] ≅ ℤ[C^•_[0,1](p)]` induced by the coordinate
projections. -/
noncomputable def dRFreeIso (p : ℕ) : zfree (cechTerm p) ≅ dRLvlChain.X p :=
  (free ℤ).mapIso (@asIso _ _ _ _ (cechCompare p) (cechCompare_isIso p))

/-- The level model: `ℤ[cechTerm p] ≅ (cechComplex beta).X (-p)`. -/
noncomputable def dRLvlIso (p : ℕ) : zfree (cechTerm p) ≅ (cechComplex beta).X (-(p:ℤ)) :=
  dRFreeIso p ≪≫ (dRLvlExtIso p).symm

lemma dRLvlIso_hom (p : ℕ) :
    (dRLvlIso p).hom = (free ℤ).map (cechCompare p) ≫ (dRLvlExtIso p).inv := by
  change (dRFreeIso p ≪≫ (dRLvlExtIso p).symm).hom =
    (free ℤ).map (cechCompare p) ≫ (dRLvlExtIso p).inv
  rw [Iso.trans_hom, Iso.symm_hom]
  rfl

lemma dRLvlIso_inv (p : ℕ) :
    (dRLvlIso p).inv =
      (dRLvlExtIso p).hom ≫
        (free ℤ).map ((@asIso _ _ _ _ (cechCompare p) (cechCompare_isIso p)).inv) := by
  change (dRFreeIso p ≪≫ (dRLvlExtIso p).symm).inv =
    (dRLvlExtIso p).hom ≫
      (free ℤ).map ((@asIso _ _ _ _ (cechCompare p) (cechCompare_isIso p)).inv)
  rw [Iso.trans_inv, Iso.symm_inv]
  rfl

/-- The inverse of the comparison isomorphism is a left inverse of the comparison map. -/
lemma dRAsIsoCancel (p : ℕ) :
    cechCompare p ≫ (@asIso _ _ _ _ (cechCompare p) (cechCompare_isIso p)).inv = 𝟙 _ := by
  change (@asIso _ _ _ _ (cechCompare p) (cechCompare_isIso p)).hom ≫
    (@asIso _ _ _ _ (cechCompare p) (cechCompare_isIso p)).inv = 𝟙 _
  exact Iso.hom_inv_id _

/-- The face maps of the nerve correspond to the face maps `cechFace` of `cechTerm`, after
inverting the comparison map. -/
lemma dRInner (p : ℕ) (i : Fin (p + 2)) :
    cechCompare (p+1) ≫ SimplicialObject.δ (cechNerve beta) i ≫
        (@asIso _ _ _ _ (cechCompare p) (cechCompare_isIso p)).inv =
      lightProfiniteToLightCondSet.map (cechFace p i) := by
  rw [← Category.assoc, dRCompare_naturality p i, Category.assoc, dRAsIsoCancel p,
    Category.comp_id]

/-- Each summand of the Čech differential is the alternating sum of the maps `ℤ[cechFace p i]`. -/
lemma dRSummand (p : ℕ) (i : Fin (p + 2)) :
    (free ℤ).map (cechCompare (p+1)) ≫ (cechFree beta).δ i ≫
        (free ℤ).map ((@asIso _ _ _ _ (cechCompare p) (cechCompare_isIso p)).inv) =
      zmap (cechFace p i) := by
  rw [show (cechFree beta).δ i = (free ℤ).map ((cechNerve beta).δ i) from rfl]
  rw [← Functor.map_comp, ← Functor.map_comp]
  rw [dRInner p i]
  rfl

/-! ## `dR` is the differential of the Čech complex -/

/-- `dR p` is the Čech differential `d` of `cechComplex beta`, conjugated by the level models
`dRLvlIso`. -/
theorem dR_eq_level (p : ℕ) :
    dR p = (dRLvlIso (p+1)).hom ≫
      (cechComplex beta).d (-(p+1:ℤ)) (-(p:ℤ)) ≫
      (dRLvlIso p).inv := by
  rw [show dR p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • zmap (cechFace p i) from rfl]
  rw [dRLvlIso_hom, dRLvlIso_inv, dRLvlExtIso_d]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [show dRLvlChain.d (p + 1) p =
      ∑ i : Fin (p + 2), (-1:ℤ)^(i:ℕ) • (cechFree beta).δ i from
    (alternatingFaceMapComplex_obj_d (cechFree beta) p).trans rfl]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [dRSummand p i]

/-- **The Čech differential squares to zero.** -/
theorem dR_comp (p : ℕ) :
    CategoryTheory.CategoryStruct.comp (Work.ANALYTIC.CechPt.dR (p+1)) (Work.ANALYTIC.CechPt.dR p) = 0 := by
  rw [dR_eq_level (p+1), dR_eq_level p]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  -- the two consecutive differentials now sit in consecutive degrees (the casts are
  -- propositionally, hence definitionally, equal)
  show (dRLvlIso (p+1+1)).hom ≫
      (cechComplex beta).d (-(↑(p+1) + 1)) (-(↑(p+1))) ≫
      (cechComplex beta).d (-(↑(p+1))) (-(↑p)) ≫ (dRLvlIso p).inv = 0
  rw [HomologicalComplex.d_comp_d_assoc]
  simp

end

end Work.ANALYTIC.CechPt
