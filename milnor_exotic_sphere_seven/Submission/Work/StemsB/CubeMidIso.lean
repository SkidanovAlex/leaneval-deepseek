import Submission.Work.StemsB.CubeMidHomeo
import Submission.Work.Cohomology.relChainsMapOf_isIso
import Submission.Work.Cohomology.exists_relComplexMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The middle slab and `Iⁿ × (1/4,3/4) × Y` have the same relative homology

The canonical homeomorphism `Work.StemsB.midHomeo` of the middle slab with `Iⁿ × (1/4,3/4) × Y`
(`Submission/Work/StemsB/CubeMidHomeo.lean`) maps the boundary part of the middle slab onto the
boundary `∂Iⁿ × (1/4,3/4) × Y`.  This file draws the homological conclusion: the two *pairs* have
isomorphic relative homology, by the five lemma applied to the map of short exact sequences of the
pairs.

* `Work.StemsB.midMap`, `Work.StemsB.midMapInv` — the homeomorphism as morphisms of `TopCat`;
* `Work.StemsB.isIso_midMapHomology` — it induces homology isomorphisms;
* `Work.StemsB.midRelIso` — the induced isomorphism of relative homology groups.
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

namespace Work.StemsB

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

/-- The canonical homeomorphism of the middle slab with `Iⁿ × (1/4,3/4) × Y`, as a morphism. -/
def midMap (n : ℕ) : TopCat.of ↥(slabMid (Y := Y) n) ⟶ TopCat.of (CubeP (midParam Y) n) :=
  TopCat.ofHom ⟨midTo n, continuous_midTo n⟩

/-- Its inverse. -/
def midMapInv (n : ℕ) : TopCat.of (CubeP (midParam Y) n) ⟶ TopCat.of ↥(slabMid (Y := Y) n) :=
  TopCat.ofHom ⟨midFrom n, continuous_midFrom n⟩

@[simp] theorem midMap_apply (n : ℕ) (z : ↥(slabMid (Y := Y) n)) : midMap n z = midTo n z := rfl

@[simp] theorem midMapInv_apply (n : ℕ) (w : CubeP (midParam Y) n) : midMapInv n w = midFrom n w :=
  rfl

theorem midMap_midMapInv (n : ℕ) : midMap n ≫ midMapInv n = 𝟙 (TopCat.of ↥(slabMid (Y := Y) n)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  show midFrom n (midTo n z) = z
  exact midFrom_midTo n z

theorem midMapInv_midMap (n : ℕ) :
    midMapInv n ≫ midMap n = 𝟙 (TopCat.of (CubeP (midParam Y) n)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro w
  show midTo n (midFrom n w) = w
  exact midTo_midFrom n w

/-- **The canonical homeomorphism induces isomorphisms on singular homology.** -/
theorem isIso_midMapHomology (n : ℕ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of ↥(slabMid (Y := Y) n))
        (TopCat.of (CubeP (midParam Y) n)) (midMap n)) k) := by
  have h1 : TopCat.Homotopy (midMap n ≫ midMapInv n)
      (𝟙 (TopCat.of ↥(slabMid (Y := Y) n))) := by
    rw [midMap_midMapInv]
    exact ContinuousMap.Homotopy.refl _
  have h2 : TopCat.Homotopy (midMapInv n ≫ midMap n)
      (𝟙 (TopCat.of (CubeP (midParam Y) n))) := by
    rw [midMapInv_midMap]
    exact ContinuousMap.Homotopy.refl _
  exact Work.Cohomology.homologyEquiv ℤ (TopCat.of ↥(slabMid (Y := Y) n))
    (TopCat.of (CubeP (midParam Y) n)) (midMap n) (midMapInv n) h1 h2 k

/-- The restriction of the canonical homeomorphism to the boundary parts, as a morphism. -/
def midRelMap (n : ℕ) :
    TopCat.of (slabMidi (Y := Y) n) ⟶ TopCat.of (cubeBdryK (midParam Y) n) :=
  Work.Cohomology.relMapSub (slabMidi (Y := Y) n) (cubeBdryK (midParam Y) n) (midMap n)
    (fun x hx => midTo_mem_bdry n hx)

/-- The restriction in the other direction. -/
def midRelMapInv (n : ℕ) :
    TopCat.of (cubeBdryK (midParam Y) n) ⟶ TopCat.of (slabMidi (Y := Y) n) :=
  Work.Cohomology.relMapSub (cubeBdryK (midParam Y) n) (slabMidi (Y := Y) n) (midMapInv n)
    (fun x hx => midFrom_mem_bdry n hx)

theorem midRelMap_comp (n : ℕ) :
    midRelMap n ≫ midRelMapInv n = 𝟙 (TopCat.of (slabMidi (Y := Y) n)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  show (⟨midFrom n (midTo n x.1), _⟩ : ↥(slabMidi (Y := Y) n)) = x
  exact Subtype.ext (midFrom_midTo n x.1)

theorem midRelMapInv_comp (n : ℕ) :
    midRelMapInv n ≫ midRelMap n = 𝟙 (TopCat.of (cubeBdryK (midParam Y) n)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  show (⟨midTo n (midFrom n x.1), _⟩ : ↥(cubeBdryK (midParam Y) n)) = x
  exact Subtype.ext (midTo_midFrom n x.1)

/-- **The restricted homeomorphism induces isomorphisms on singular homology.** -/
theorem isIso_midRelMapHomology (n : ℕ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (slabMidi (Y := Y) n))
        (TopCat.of (cubeBdryK (midParam Y) n)) (midRelMap n)) k) := by
  have h1 : TopCat.Homotopy (midRelMap n ≫ midRelMapInv n)
      (𝟙 (TopCat.of (slabMidi (Y := Y) n))) := by
    rw [midRelMap_comp]
    exact ContinuousMap.Homotopy.refl _
  have h2 : TopCat.Homotopy (midRelMapInv n ≫ midRelMap n)
      (𝟙 (TopCat.of (cubeBdryK (midParam Y) n))) := by
    rw [midRelMapInv_comp]
    exact ContinuousMap.Homotopy.refl _
  exact Work.Cohomology.homologyEquiv ℤ (TopCat.of (slabMidi (Y := Y) n))
    (TopCat.of (cubeBdryK (midParam Y) n)) (midRelMap n) (midRelMapInv n) h1 h2 k

/-- **The relative homology of the middle slab is that of `Iⁿ × (1/4,3/4) × Y`.** -/
theorem midRelIso (n : ℕ) (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of ↥(slabMid (Y := Y) n))
        (slabMidi (Y := Y) n)).homology m) ≅
      ((Work.Cohomology.relChains (TopCat.of (CubeP (midParam Y) n))
        (cubeBdryK (midParam Y) n)).homology m)) := by
  have hw : CategoryTheory.CategoryStruct.comp
      (Work.Cohomology.subtypeIncl (TopCat.of ↥(slabMid (Y := Y) n)) (slabMidi (Y := Y) n))
        (midMap n)
      = CategoryTheory.CategoryStruct.comp (midRelMap n)
        (Work.Cohomology.subtypeIncl (TopCat.of (CubeP (midParam Y) n))
          (cubeBdryK (midParam Y) n)) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    show midTo n x.1 = midTo n x.1
    rfl
  haveI := Work.Cohomology.relChainsMapOf_isIso
    (X := TopCat.of ↥(slabMid (Y := Y) n)) (Y := TopCat.of (CubeP (midParam Y) n))
    (slabMidi (Y := Y) n) (cubeBdryK (midParam Y) n)
    (midMap n) (midRelMap n) hw m (isIso_midMapHomology (Y := Y) n)
    (isIso_midRelMapHomology (Y := Y) n)
  exact ⟨asIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf
    (TopCat.of ↥(slabMid (Y := Y) n)) (TopCat.of (CubeP (midParam Y) n)) (slabMidi (Y := Y) n)
    (cubeBdryK (midParam Y) n) (midMap n) (midRelMap n) hw) m)⟩

end

end Work.StemsB
