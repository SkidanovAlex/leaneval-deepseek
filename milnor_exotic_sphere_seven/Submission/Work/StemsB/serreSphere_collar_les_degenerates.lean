import Mathlib
import Submission.Work.StemsB.SerreSphereCollar
import Submission.Work.StemsB.SerreSphereStep
import Submission.Work.StemsB.serreSphere_contract_big
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.homotopyEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The collar pair `(sphLoopBig b × Y, sphLoopCollar b × Y)` has a degenerate long exact sequence

The pair is the model of the disc pair `(D^b × Y, S^{b-1} × Y)`:

* `sphLoopBig b = {|v|_∞ < 3/2}` is a **contractible** open cube,
* `sphLoopCollar b = {|x|_∞ > 1/2}` inside it is a collar of the cube boundary `S^{b-1}`.

Because the cube is contractible, the projection `sphLoopBig b × Y → Y` is a homotopy equivalence,
and so is the "zero section" `y ↦ (shell point, y)`; the latter is the composite
`Y → sphLoopCollar b × Y → sphLoopBig b × Y` of the section of the collar with the inclusion.

This file proves that the long exact sequence of the pair degenerates:

* `Work.StemsB.serreSphere_collar_restriction_injective` — the restriction
  `H^n(sphLoopBig b × Y) → H^n(sphLoopCollar b × Y)` is injective in every degree;
* `Work.StemsB.serreSphere_collar_delta_surjective` — the connecting map
  `H^n(sphLoopCollar b × Y) → H^{n+1}(sphLoopBig b × Y, sphLoopCollar b × Y)` is surjective in
  every degree;
* `Work.StemsB.serreSphere_collar_les_degenerates` — the two together, the requested form.

Consequently the pair LES breaks up into short exact sequences, i.e. the "Künneth splitting"
`H^{n+1}(A) ≅ H^{n+1}(X) ⊕ H^{n+1}(X,A)`, which (with the collar isomorphism
`Work.StemsB.cohomology_collar_iso`, `H^{n+1}(X,A) ≅ H^{n+1-b}(Y)`) is the geometric input of the
derivation property of the Wang transgression (`D2_PLAN.md` §2, items 3–4).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Work.StemsB

noncomputable section

variable {Y : Type} [TopologicalSpace Y]
variable {R : Type} [CommRing R]

/-- The shell point lies in the inner cube. -/
theorem sphShellPt_mem_sphLoopBig (b : ℕ) (hb : 1 ≤ b) : sphShellPt b ∈ sphLoopBig b :=
  (sphShellPt_mem_sphLoopCollar b hb).2

/-- The shell point, as a point of the inner cube. -/
def collarShellPt (b : ℕ) (hb : 1 ≤ b) : ↥(sphLoopBig b) :=
  Subtype.mk (sphShellPt b) (sphShellPt_mem_sphLoopBig b hb)

/-- The "zero section" of the collar product: `y ↦ (shell point, y)`. -/
def collarSection (b : ℕ) (hb : 1 ≤ b) : ContinuousMap Y ↥(sphLoopCollarProd b Y) :=
  ContinuousMap.mk (fun y : Y =>
      Subtype.mk ((collarShellPt b hb, y) : ↥(sphLoopBig b) × Y)
        (sphShellPt_mem_sphLoopCollar b hb)) (by fun_prop)

/-- The same section, composed with the inclusion of the collar into the inner cube. -/
def collarSectionIncl (b : ℕ) (hb : 1 ≤ b) :
    ContinuousMap Y (↥(sphLoopBig b) × Y) :=
  ContinuousMap.mk (fun y : Y => ((collarShellPt b hb, y) : ↥(sphLoopBig b) × Y)) (by fun_prop)

/-- The projection `sphLoopBig b × Y → Y`. -/
def collarProdSnd (b : ℕ) : ContinuousMap (↥(sphLoopBig b) × Y) Y :=
  ContinuousMap.mk (fun q => q.2) (by fun_prop)

@[simp] theorem collarSectionIncl_apply (b : ℕ) (hb : 1 ≤ b) (y : Y) :
    collarSectionIncl (Y := Y) b hb y = ((collarShellPt b hb, y) : ↥(sphLoopBig b) × Y) := rfl

@[simp] theorem collarProdSnd_apply (b : ℕ) (q : ↥(sphLoopBig b) × Y) :
    collarProdSnd (Y := Y) b q = q.2 := rfl

/-- **The section `y ↦ (shell point, y)` is a homotopy equivalence** (into the inner cube times
`Y`): the contraction `serreSphere_contract_big` of the cube to the shell point supplies the two
homotopies. -/
theorem isIso_collarSectionIncl (b : ℕ) (hb : 1 ≤ b) (n : ℕ) :
    IsIso (Work.Cohomology.singularCohomologyMap R (TopCat.of Y)
      (TopCat.of (↥(sphLoopBig b) × Y)) (TopCat.ofHom (collarSectionIncl (Y := Y) b hb)) n) := by
  obtain ⟨c, hc0, hc1, -⟩ := serreSphere_contract_big b hb (sphShellPt_mem_sphLoopBig b hb)
  have hsym : TopCat.Homotopy (𝟙 (TopCat.of (↥(sphLoopBig b) × Y)))
      (TopCat.ofHom (collarProdSnd (Y := Y) b) ≫
        TopCat.ofHom (collarSectionIncl (Y := Y) b hb)) :=
    ContinuousMap.Homotopy.mk
      ⟨fun p : unitInterval × (↥(sphLoopBig b) × Y) => (c (p.2.1, p.1), p.2.2), by fun_prop⟩
      (fun q => by
        apply Prod.ext
        · exact hc0 q.1
        · rfl)
      (fun q => by
        apply Prod.ext
        · exact hc1 q.1
        · rfl)
  have hH : TopCat.Homotopy
      (TopCat.ofHom (collarProdSnd (Y := Y) b) ≫
        TopCat.ofHom (collarSectionIncl (Y := Y) b hb))
      (𝟙 (TopCat.of (↥(sphLoopBig b) × Y))) := hsym.symm
  have hH' : TopCat.Homotopy
      (TopCat.ofHom (collarSectionIncl (Y := Y) b hb) ≫
        TopCat.ofHom (collarProdSnd (Y := Y) b))
      (𝟙 (TopCat.of Y)) :=
    ContinuousMap.Homotopy.mk
      ⟨fun p : unitInterval × Y => p.2, by fun_prop⟩
      (fun y => rfl) (fun y => rfl)
  exact Work.Cohomology.homotopyEquiv R (TopCat.of Y) (TopCat.of (↥(sphLoopBig b) × Y))
    (TopCat.ofHom (collarSectionIncl (Y := Y) b hb)) (TopCat.ofHom (collarProdSnd (Y := Y) b))
    hH' hH n

/-- The section of the collar, composed with the inclusion, is the section of the inner cube. -/
theorem collarSection_comp_subtypeIncl (b : ℕ) (hb : 1 ≤ b) :
    TopCat.ofHom (collarSection (Y := Y) b hb) ≫
        Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig b) × Y))
          (sphLoopCollarProd b Y) =
      TopCat.ofHom (collarSectionIncl (Y := Y) b hb) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  rfl

/-- **The restriction `H^n(sphLoopBig b × Y) → H^n(sphLoopCollar b × Y)` is injective.** -/
theorem serreSphere_collar_restriction_injective (b : ℕ) (hb : 1 ≤ b) (n : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap
      (Work.Cohomology.restr R (TopCat.of (↥(sphLoopBig b) × Y))
        (sphLoopCollarProd b Y)) n).hom := by
  haveI hiso := isIso_collarSectionIncl (R := R) (Y := Y) b hb n
  have hinj : Function.Injective
      (Work.Cohomology.singularCohomologyMap R (TopCat.of Y)
        (TopCat.of (↥(sphLoopBig b) × Y))
        (TopCat.ofHom (collarSectionIncl (Y := Y) b hb)) n).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hcomp := Work.Cohomology.singularCohomologyMap_comp R
    (TopCat.ofHom (collarSection (Y := Y) b hb))
    (Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)) n
  rw [collarSection_comp_subtypeIncl (Y := Y) b hb] at hcomp
  rw [hcomp] at hinj
  exact Function.Injective.of_comp hinj

/-- **The connecting map of the collar pair is surjective.**  By the exactness of the pair sequence
at `H^{n+1}(sphLoopBig b × Y)`, this is equivalent to the injectivity of the restriction in degree
`n + 1` (`serreSphere_collar_restriction_injective`). -/
theorem serreSphere_collar_delta_surjective (b : ℕ) (hb : 1 ≤ b) (n : ℕ) :
    Function.Surjective (Work.Cohomology.pairδ R (TopCat.of (↥(sphLoopBig b) × Y))
      (sphLoopCollarProd b Y) n).hom := by
  have hex1 : Function.Exact (Work.Cohomology.pairδ R (TopCat.of (↥(sphLoopBig b) × Y))
        (sphLoopCollarProd b Y) n).hom
      (HomologicalComplex.homologyMap
        (Work.Cohomology.relIncl R (TopCat.of (↥(sphLoopBig b) × Y))
          (sphLoopCollarProd b Y)) (n + 1)).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (Work.Cohomology.pair_exact₁ R (TopCat.of (↥(sphLoopBig b) × Y))
        (sphLoopCollarProd b Y) n)
  have hex2 : Function.Exact (HomologicalComplex.homologyMap
        (Work.Cohomology.relIncl R (TopCat.of (↥(sphLoopBig b) × Y))
          (sphLoopCollarProd b Y)) (n + 1)).hom
      (HomologicalComplex.homologyMap
        (Work.Cohomology.restr R (TopCat.of (↥(sphLoopBig b) × Y))
          (sphLoopCollarProd b Y)) (n + 1)).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (Work.Cohomology.pair_exact₂ R (TopCat.of (↥(sphLoopBig b) × Y))
        (sphLoopCollarProd b Y) (n + 1))
  have hinj := serreSphere_collar_restriction_injective (R := R) (Y := Y) b hb (n + 1)
  -- the inclusion of the relative cohomology in the absolute one is zero in degree `n + 1`
  have hrel : (HomologicalComplex.homologyMap
      (Work.Cohomology.relIncl R (TopCat.of (↥(sphLoopBig b) × Y))
        (sphLoopCollarProd b Y)) (n + 1)).hom = 0 := by
    apply LinearMap.ext
    intro x
    have hx : (HomologicalComplex.homologyMap
        (Work.Cohomology.restr R (TopCat.of (↥(sphLoopBig b) × Y))
          (sphLoopCollarProd b Y)) (n + 1)).hom
        ((HomologicalComplex.homologyMap
          (Work.Cohomology.relIncl R (TopCat.of (↥(sphLoopBig b) × Y))
            (sphLoopCollarProd b Y)) (n + 1)).hom x) = 0 :=
      (hex2 ((HomologicalComplex.homologyMap
        (Work.Cohomology.relIncl R (TopCat.of (↥(sphLoopBig b) × Y))
          (sphLoopCollarProd b Y)) (n + 1)).hom x)).mpr ⟨x, rfl⟩
    have hf : (HomologicalComplex.homologyMap
        (Work.Cohomology.restr R (TopCat.of (↥(sphLoopBig b) × Y))
          (sphLoopCollarProd b Y)) (n + 1)).hom
        ((HomologicalComplex.homologyMap
          (Work.Cohomology.relIncl R (TopCat.of (↥(sphLoopBig b) × Y))
            (sphLoopCollarProd b Y)) (n + 1)).hom x) =
        (HomologicalComplex.homologyMap
          (Work.Cohomology.restr R (TopCat.of (↥(sphLoopBig b) × Y))
            (sphLoopCollarProd b Y)) (n + 1)).hom
          (0 : ↥(HomologicalComplex.homology
            (Work.Cohomology.singularCochainComplex R (TopCat.of (↥(sphLoopBig b) × Y)))
            (n + 1))) :=
      hx.trans (map_zero _).symm
    exact hinj hf
  intro y
  have hy : (HomologicalComplex.homologyMap
      (Work.Cohomology.relIncl R (TopCat.of (↥(sphLoopBig b) × Y))
        (sphLoopCollarProd b Y)) (n + 1)).hom y = 0 := by rw [hrel]; rfl
  exact (hex1 y).mp hy

/-- **The long exact sequence of the collar pair degenerates** (the requested statement). -/
theorem serreSphere_collar_les_degenerates (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (n : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap
        (Work.Cohomology.restr R (TopCat.of (↥(sphLoopBig b) × Y))
          (sphLoopCollarProd b Y)) n).hom ∧
      Function.Surjective (Work.Cohomology.pairδ R (TopCat.of (↥(sphLoopBig b) × Y))
        (sphLoopCollarProd b Y) n).hom :=
  ⟨serreSphere_collar_restriction_injective b hb n,
    serreSphere_collar_delta_surjective b hb n⟩

end

end Work.StemsB
