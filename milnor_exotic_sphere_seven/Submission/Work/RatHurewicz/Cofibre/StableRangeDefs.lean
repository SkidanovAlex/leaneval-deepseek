import Mathlib
import Submission.Work.RatHurewicz.Cofibre.BMInstantiate
import Submission.Work.RatHurewicz.Cofibre.Maps
import Submission.Work.RatHurewicz.Cofibre.compressRel_cofibre_range_zero
import Submission.Work.RatHurewicz.relPiVanishing_of_isHurewiczFibration
import Submission.Work.Serre.Assembly.serreK2IntSharp
import Submission.Work.Serre.bijective_piMapN_of_joined

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Vocabulary for the cofibre computation of Serre's stable range

This file fixes the objects used in the proof of
`Work.RatHurewicz.fibrationPairMap_injective_stableRange`:

* `collarPt ι y` — the point `[y, 1/4]` of the cofibre, an element of `cofibreU ι ∩ cofibreV ι`;
* `collarRaise ι` — the map `F → ↥(cofibreU ι ∩ cofibreV ι)`, `y ↦ collarPt ι y`;
* `collarBase ι` — the map `↥(cofibreU ι ∩ cofibreV ι) → F`, the "base" of a cone point;
* `coneImage ι` — the image of the cone in the cofibre (the closed cone `⊆ cofibre ι`);
* `thetaMap ι` — the map of relative chain complexes `C_*(E, F) → C_*(cofibre ι, coneImage ι)`;
* `psiMap` — the map of relative chain complexes `C_*(cofibre ι, coneImage ι) → C_*(B, {b₀})`.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.RatHurewicz

noncomputable section

variable {E F B : Type} [TopologicalSpace E] [TopologicalSpace F]

/-- The height `1/4`, used to build the collar point inside `cofibreU ι ∩ cofibreV ι`. -/
def collarStub : unitInterval := ⟨1 / 4, by norm_num⟩

theorem collarStub_pos : (0 : unitInterval) < collarStub := by
  change (0 : ℝ) < (1 / 4 : ℝ); norm_num

theorem collarStub_lt_half : collarStub < cofibreHalf := by
  change (1 / 4 : ℝ) < (1 / 2 : ℝ); norm_num

/-- **The collar point over `y`**: the cone point of height `1/4` over `y`, as an element of
`cofibreU ι ∩ cofibreV ι`. -/
def collarPt (ι : C(F, E)) (y : F) : ↥(cofibreU ι ∩ cofibreV ι) :=
  ⟨cofibreInclCone ι (coneMk (F := F) (y, collarStub)),
    (mem_cofibreU_coneIncl_iff ι _).mpr (by rw [coneHeight_coneMk]; exact collarStub_lt_half),
    (mem_cofibreV_coneIncl_iff ι _).mpr (by rw [coneHeight_coneMk]; exact collarStub_pos)⟩

@[simp]
theorem collarPt_val (ι : C(F, E)) (y : F) :
    ((collarPt ι y : ↥(cofibreU ι ∩ cofibreV ι)) : cofibre ι)
      = cofibreInclCone ι (coneMk (F := F) (y, collarStub)) := rfl

theorem collarPt_mem_U (ι : C(F, E)) (y : F) :
    ((collarPt ι y : ↥(cofibreU ι ∩ cofibreV ι)) : cofibre ι) ∈ cofibreU ι :=
  (collarPt ι y).2.1

theorem collarPt_mem_V (ι : C(F, E)) (y : F) :
    ((collarPt ι y : ↥(cofibreU ι ∩ cofibreV ι)) : cofibre ι) ∈ cofibreV ι :=
  (collarPt ι y).2.2

/-- **The "raise" map `F → cofibreU ι ∩ cofibreV ι`**, `y ↦ [y, 1/4]`. -/
def collarRaise (ι : C(F, E)) : C(F, ↥(cofibreU ι ∩ cofibreV ι)) where
  toFun := collarPt ι
  continuous_toFun := by
    change Continuous (fun y : F => (⟨cofibreInclCone ι (coneMk (F := F) (y, collarStub)),
      (mem_cofibreU_coneIncl_iff ι _).mpr (by rw [coneHeight_coneMk]; exact collarStub_lt_half),
      (mem_cofibreV_coneIncl_iff ι _).mpr (by rw [coneHeight_coneMk]; exact collarStub_pos)⟩ :
        ↥(cofibreU ι ∩ cofibreV ι)))
    exact Continuous.subtype_mk ((cofibreInclCone ι).continuous.comp
      ((continuous_quotient_mk').comp (Continuous.prodMk continuous_id continuous_const))) _

@[simp]
theorem collarRaise_apply (ι : C(F, E)) (y : F) : collarRaise ι y = collarPt ι y := rfl

/-- **The image of the cone in the cofibre** — the closed cone `CF ⊆ E ∪_F CF`. -/
def coneImage (ι : C(F, E)) : Set (cofibre ι) := Set.range (cofibreInclCone ι)

theorem mem_coneImage (ι : C(F, E)) (y : Work.Stems.Cone F) :
    cofibreInclCone ι y ∈ coneImage ι := ⟨y, rfl⟩

theorem cofibreIncl_mem_coneImage (ι : C(F, E)) (y : F) :
    cofibreIncl ι (ι y) ∈ coneImage ι :=
  ⟨Work.Stems.coneIncl y, (cofibreIncl_coneIncl ι y).symm⟩

/-! ## The map of pairs `(E, F) → (cofibre ι, coneImage ι)` -/

theorem coneImageSec_mem (ι : C(F, E)) (a : ↥(Set.range ⇑ι)) :
    cofibreIncl ι a.1 ∈ coneImage ι := by
  have hmem : ∃ y : F, ι y = (a : E) := Set.mem_range.mp a.2
  refine ⟨Work.Stems.coneIncl hmem.choose, ?_⟩
  rw [← cofibreIncl_coneIncl, hmem.choose_spec]

theorem continuous_coneImageSecFun (ι : C(F, E)) :
    Continuous fun a : ↥(Set.range ⇑ι) => cofibreIncl ι a.1 :=
  (cofibreIncl ι).continuous.comp continuous_subtype_val

/-- The map `↥(Set.range ι) → ↥(coneImage ι)` used as the second component of the pair map
`(E, range ι) → (cofibre ι, coneImage ι)`. -/
def coneImageSec (ι : C(F, E)) : C(↥(Set.range ⇑ι), ↥(coneImage ι)) where
  toFun a := ⟨cofibreIncl ι a.1, coneImageSec_mem ι a⟩
  continuous_toFun := Continuous.subtype_mk (continuous_coneImageSecFun ι)
    (fun a => coneImageSec_mem ι a)

/-- **The map of relative chain complexes `C_*(E, F) → C_*(cofibre ι, coneImage ι)`** induced by
the pair map `(id, incl)`. -/
def thetaMap (ι : C(F, E)) :
    Work.Cohomology.relChains (TopCat.of E) (Set.range ⇑ι) ⟶
      Work.Cohomology.relChains (TopCat.of (cofibre ι)) (coneImage ι) :=
  Work.Cohomology.relChainsMapOf (TopCat.of E) (TopCat.of (cofibre ι)) (Set.range ⇑ι)
    (coneImage ι) (TopCat.ofHom (cofibreIncl ι)) (TopCat.ofHom (coneImageSec ι))
    (by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro a
      rfl)

end

end Work.RatHurewicz
