import Mathlib
import Submission.Work.Drive.endTripleRegDesign
import Submission.Work.Drive.blockPlaneInvariant
import Submission.Work.Drive.classTripleAssemblyLiftFree

/-!
# The *unrestricted* rows-1/2 producer: `EndTripleReg` of the plane class maps from `Meet3Hyp`

`Work.Drive.endTripleReg_of_meet3Hyp_sweeps` produces the class-level end data `EndTripleReg` of
three plane presentations from the design's own `Meet3Hyp` of the three radial sweeps, but only at
**common-class triples of plane parameters in the closed unit square** (the reason: the level lift
`exists_sweepTriple_of_commonClass` lands in the box, and `Meet3Hyp.trans` is only available there).

The consumer `Work.Drive.EndTripleReg` quantifies over *all* of `ℝ²`, so this file removes the
restriction, at the price of the **affine invariance** of the presentations:

* `Work.Drive.exists_affRep_mem_unitBox` — every plane parameter has an affine representative
  `x ↦ (ε i * x i + 2 m i)` with `ε i = ±1` inside the unit square;
* `Work.Drive.transfer_mfderiv_class_of_affRep` — the range and the injectivity of the manifold
  derivative of the class map `y ↦ [P y]` are invariant under such a representative, whenever `P` is;
* `Work.Drive.endTripleReg_of_meet3Hyp_sweeps_unrestricted` — the unrestricted producer;
* `Work.Drive.endTripleReg_blockPlane_of_designMeet3_unrestricted` — its instance at the design's own
  presentations (`Work.Drive.blockPlane Ξ Q u τ k`), whose invariance is
  `Work.Drive.blockPlane_affRep`.

The mathematical mechanism is the *folding* of the disk presentations: `diskPlane Q = Q ∘ sqDisk ∘
foldBox` with `foldFun x = (1 - cos (π x))/2` of period `2`, so the class map of the plane is
invariant under `x ↦ x + 2m` and under `x ↦ -x` — exactly the two operations that move a parameter
into `[0,1]`.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace
attribute [local instance] Work.Drive.projCharted
local instance instIsManifoldProjChartU :
    IsManifold (𝓡 3) Work.Drive.Ctop (Projectivization ℝ (Eucl 3)) :=
  Work.Drive.isManifold_projCharted 3

/-! ## 1. The affine representative inside the unit square -/

/-- **Every plane parameter has an affine representative in the unit square**: a translation by an
even integer per coordinate and an independent reflection per coordinate
(`Work.Drive.exists_foldRep'`). -/
lemma exists_affRep_mem_unitBox (y : EuclideanSpace ℝ (Fin 2)) :
    ∃ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) ∧
      ∀ i, e i * y i + 2 * (mm i : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  choose e mm h using fun i : Fin 2 => exists_foldRep' (y i)
  exact ⟨e, mm, fun i => (h i).1, fun i => (h i).2⟩

/-- The affine representative of such a parameter lies in the unit box. -/
lemma affRep_mem_unitBox {e : Fin 2 → ℝ} {mm : Fin 2 → ℤ} {y : EuclideanSpace ℝ (Fin 2)}
    (h : ∀ i, e i * y i + 2 * (mm i : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    affRep e mm y ∈ Submission.Drive.unitBox 1 := by
  simp only [Submission.Drive.unitBox, Set.mem_setOf_eq]
  intro i
  simpa only [affRep_apply] using h i

/-! ## 2. Transfer of the class derivative along an affine symmetry -/

/-- **The manifold derivative of the class map of an affinely invariant presentation transfers
along the affine symmetry.**  If `P (affRep e mm y) = P y` for all `y`, then the injectivity of
`mfderiv (planeClassMap P)` and its range are the same at `y` and at `affRep e mm y`.

Proof: in the preferred projective chart at the (common) class, the intrinsic derivative is the
Fréchet derivative of the charted class map; the charted class map is invariant under the affine
symmetry (a bijection of `𝔼²` with linear part `Work.Drive.diagEps e`), and invariance under an
invertible linear operation transfers injectivity and range by the chain rule
(`Work.Drive.fderiv_transfer_of_comp_eq`). -/
theorem transfer_mfderiv_class_of_affRep
    (P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hP : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop P)
    (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ) (he : ∀ i, e i = 1 ∨ e i = -1)
    (hinv : ∀ y : EuclideanSpace ℝ (Fin 2), P (affRep e mm y) = P y)
    (y : EuclideanSpace ℝ (Fin 2)) :
    (Function.Injective (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap P) (affRep e mm y))
        ↔ Function.Injective (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap P) y)) ∧
      (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap P) y).range
        = (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap P) (affRep e mm y)).range := by
  have hval : Work.Drive.planeClassMap P (affRep e mm y) = Work.Drive.planeClassMap P y :=
    congrArg (fun p => (Work.Drive.cappingSpaceHomeoProj p).2) (hinv y)
  have hcls : ContMDiffAt (𝓡 2) (𝓡 3) Work.Drive.Ctop (Work.Drive.planeClassMap P) y :=
    contMDiffAt_cls_of_contMDiff hP y
  have hcls' : ContMDiffAt (𝓡 2) (𝓡 3) Work.Drive.Ctop
      (Work.Drive.planeClassMap P) (affRep e mm y) :=
    contMDiffAt_cls_of_contMDiff hP _
  have hchart : (@chartAt (EuclideanSpace ℝ (Fin 3)) _
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
      (Work.Drive.projCharted 3) (Work.Drive.planeClassMap P y) :
      OpenPartialHomeomorph (Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
        (EuclideanSpace ℝ (Fin 3)))
      = Work.Drive.projChart (Work.Drive.projChartIndexOf (Work.Drive.planeClassMap P y)) :=
    Work.Drive.projCharted_chartAt_eq_projChart _
  have hchart' : (@chartAt (EuclideanSpace ℝ (Fin 3)) _
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
      (Work.Drive.projCharted 3) (Work.Drive.planeClassMap P (affRep e mm y)) :
      OpenPartialHomeomorph (Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
        (EuclideanSpace ℝ (Fin 3)))
      = Work.Drive.projChart (Work.Drive.projChartIndexOf (Work.Drive.planeClassMap P y)) := by
    rw [hval]
    exact hchart
  have hfy : fderiv ℝ (fun z => Work.Drive.projChartMap
        (Work.Drive.projChartIndexOf (Work.Drive.planeClassMap P y))
        (Work.Drive.planeClassMap P z)) y
      = mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap P) y :=
    Work.Drive.fderiv_projChartMap_of_chartAt_eq (Work.Drive.planeClassMap P) y hcls _ hchart
  have hfy' : fderiv ℝ (fun z => Work.Drive.projChartMap
        (Work.Drive.projChartIndexOf (Work.Drive.planeClassMap P y))
        (Work.Drive.planeClassMap P z)) (affRep e mm y)
      = mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap P) (affRep e mm y) :=
    Work.Drive.fderiv_projChartMap_of_chartAt_eq (Work.Drive.planeClassMap P) (affRep e mm y)
      hcls' _ hchart'
  have hcomp : ∀ z, (fun w => Work.Drive.projChartMap
        (Work.Drive.projChartIndexOf (Work.Drive.planeClassMap P y))
        (Work.Drive.planeClassMap P w)) (affRep e mm z)
      = (fun w => Work.Drive.projChartMap
        (Work.Drive.projChartIndexOf (Work.Drive.planeClassMap P y))
        (Work.Drive.planeClassMap P w)) z := by
    intro z
    simp only [Work.Drive.planeClassMap]
    rw [hinv z]
  have hG : DifferentiableAt ℝ (fun w => Work.Drive.projChartMap
      (Work.Drive.projChartIndexOf (Work.Drive.planeClassMap P y))
      (Work.Drive.planeClassMap P w)) (affRep e mm y) := by
    have hgoal : DifferentiableAt ℝ (fun w => Work.Drive.projChartMap
        (Work.Drive.projChartIndexOf (Work.Drive.planeClassMap P y))
        ((Work.Drive.cappingSpaceHomeoProj (P w)).2)) (affRep e mm y) := by
      refine differentiableAt_projChartMap_cls P hP (affRep e mm y) _ ?_
      rw [show (Work.Drive.cappingSpaceHomeoProj (P (affRep e mm y))).2
          = (Work.Drive.cappingSpaceHomeoProj (P y)).2 from hval]
      exact Work.Drive.projChartIndexOf_spec (Work.Drive.planeClassMap P y)
    exact hgoal
  have hkey := fderiv_transfer_of_comp_eq
    (G := fun w => Work.Drive.projChartMap
      (Work.Drive.projChartIndexOf (Work.Drive.planeClassMap P y))
      (Work.Drive.planeClassMap P w))
    (φ := affRep e mm) (D := diagEps e) (y := y)
    hcomp (hasFDerivAt_affRep e mm y) (diagEps_injective he) (diagEps_surjective he) hG
  rw [hfy', hfy] at hkey
  exact hkey

/-! ## 3. The unrestricted producer -/

/-- **The rows-1/2 producer at an arbitrary (not necessarily box-resident) triple**: if the plane
presentations are invariant under the affine symmetries `x ↦ (ε i * x i + 2 m i)` and their levels
are above `c 0`, then `Meet3Hyp` of the three radial sweeps gives the `EndTripleReg` conclusion at
**every** common-class triple of plane parameters.

(Reduction to `Work.Drive.endTripleReg_of_meet3Hyp_sweeps`: move the three parameters into the unit
square by an affine symmetry, where the box producer applies; the classes, the levels and the
conclusion are unaffected, by `Work.Drive.transfer_mfderiv_class_of_affRep`.) -/
theorem endTripleReg_unrestricted_aux
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (hcpos : ∀ k, 0 < c k) (hc10 : c 1 < c 0) (hc20 : c 2 < c 0)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0) (hcont : ContinuousOn ψ (Set.Icc 0 1))
    (hanti : StrictAntiOn ψ (Set.Icc 0 1))
    (hinv : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), P k (affRep e mm y) = P k y)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < Work.Drive.levelOf (P k y))
    (hmeet : Meet3Hyp Work.Drive.CappingSpace
      (fun k => Work.Drive.clampedSweep (c k) ψ (P k)))
    (Y : Fin 3 → EuclideanSpace ℝ (Fin 2)) (hY : Work.Drive.CommonClass P Y) :
    (∀ k, Function.Injective
        (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P k)) (Y k))) ∧
      ((mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P 0)) (Y 0)).range ⊓
        (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P 1)) (Y 1)).range ⊓
        (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P 2)) (Y 2)).range = ⊥) := by
  have hrep : ∀ k : Fin 3, ∃ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ),
      (∀ i, e i = 1 ∨ e i = -1) ∧
        ∀ i, e i * Y k i + 2 * (mm i : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    fun k => exists_affRep_mem_unitBox (Y k)
  choose e mm hrep' using hrep
  let Y' : Fin 3 → EuclideanSpace ℝ (Fin 2) := fun k => affRep (e k) (mm k) (Y k)
  have hsymm : ∀ k : Fin 3, Work.Drive.planeClassMap (P k) (Y' k)
      = Work.Drive.planeClassMap (P k) (Y k) :=
    fun k => congrArg (fun p => (Work.Drive.cappingSpaceHomeoProj p).2)
      (hinv (e k) (mm k) (hrep' k).1 k (Y k))
  have hbox : ∀ k, Y' k ∈ Submission.Drive.unitBox 1 :=
    fun k => affRep_mem_unitBox (hrep' k).2
  have hcls : Work.Drive.CommonClass P Y' := by
    intro k
    rw [hsymm k, hsymm 0]
    exact hY k
  have hbig := endTripleReg_of_meet3Hyp_sweeps c ψ P hψ hP hcpos hc10 hc20 hψ0 hψ1 hcont hanti
    hlev hmeet Y' hbox hcls
  have htr : ∀ k : Fin 3,
      (Function.Injective (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P k))
          (affRep (e k) (mm k) (Y k)))
        ↔ Function.Injective
            (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P k)) (Y k))) ∧
      (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P k)) (Y k)).range
        = (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P k))
            (affRep (e k) (mm k) (Y k))).range :=
    fun k => transfer_mfderiv_class_of_affRep (P k) (hP k) (e k) (mm k) (hrep' k).1
      (fun y => hinv (e k) (mm k) (hrep' k).1 k y) (Y k)
  refine ⟨?_, ?_⟩
  · intro k
    fin_cases k
    · exact (htr 0).1.mp hbig.1
    · exact (htr 1).1.mp hbig.2.1
    · exact (htr 2).1.mp hbig.2.2.1
  · rw [(htr 0).2, (htr 1).2, (htr 2).2]
    exact hbig.2.2.2

/-- **The unrestricted rows-1/2 producer**: the class-level end data `Work.Drive.EndTripleReg` of the
three plane presentations, at **every** common-class triple of plane parameters, from `Meet3Hyp` of
the three radial sweeps and the affine invariance of the presentations. -/
theorem endTripleReg_of_meet3Hyp_sweeps_unrestricted
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (hcpos : ∀ k, 0 < c k) (hc10 : c 1 < c 0) (hc20 : c 2 < c 0)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0) (hcont : ContinuousOn ψ (Set.Icc 0 1))
    (hanti : StrictAntiOn ψ (Set.Icc 0 1))
    (hinv : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), P k (affRep e mm y) = P k y)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < Work.Drive.levelOf (P k y))
    (hmeet : Meet3Hyp Work.Drive.CappingSpace
      (fun k => Work.Drive.clampedSweep (c k) ψ (P k))) :
    Work.Drive.EndTripleReg (Work.Drive.planeClassMap (P 0))
      (Work.Drive.planeClassMap (P 1)) (Work.Drive.planeClassMap (P 2)) := by
  intro y₀ y₁ y₂ h01 h02
  have hclsY : Work.Drive.CommonClass P
      (![y₀, y₁, y₂] : Fin 3 → EuclideanSpace ℝ (Fin 2)) := by
    intro k
    fin_cases k
    · simp
    · simpa using h01.symm
    · simpa using h02.symm
  have hmain := endTripleReg_unrestricted_aux c ψ P hψ hP hcpos hc10 hc20 hψ0 hψ1 hcont hanti
    hinv hlev hmeet (![y₀, y₁, y₂] : Fin 3 → EuclideanSpace ℝ (Fin 2)) hclsY
  exact ⟨hmain.1 0, hmain.1 1, hmain.1 2, hmain.2⟩

/-! ## 4. The design's instance -/

/-- **The design's unrestricted rows-1/2 producer**: `EndTripleReg` of the three perturbed design
planes at every common-class triple of plane parameters, from the design's own `Meet3Hyp` of the
three radial sweeps.  The affine invariance is `Work.Drive.blockPlane_affRep`. -/
theorem endTripleReg_blockPlane_of_designMeet3_unrestricted
    (Ξ : EuclideanSpace ℝ (Fin 4) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace)
    (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin 4)) (cblk : Fin 3 → ℝ)
    (hΞsm : ∀ s : EuclideanSpace ℝ (Fin 4),
      ContMDiff (𝓡 4) (𝓡 4) Work.Drive.Ctop (fun p : Work.Drive.CappingSpace => Ξ s p))
    (hQ : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (Work.Drive.diskPlane Q))
    (hcpos : ∀ k, 0 < cblk k) (hc10 : cblk 1 < cblk 0) (hc20 : cblk 2 < cblk 0)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      cblk 0 < Work.Drive.levelOf (Work.Drive.blockPlane Ξ Q u τ k y))
    (hmeet : Meet3Hyp Work.Drive.CappingSpace (Work.Drive.designSweep Ξ Q u τ cblk)) :
    Work.Drive.EndTripleReg (Work.Drive.planeClassMap (Work.Drive.blockPlane Ξ Q u τ 0))
      (Work.Drive.planeClassMap (Work.Drive.blockPlane Ξ Q u τ 1))
      (Work.Drive.planeClassMap (Work.Drive.blockPlane Ξ Q u τ 2)) :=
  endTripleReg_of_meet3Hyp_sweeps_unrestricted cblk (fun t : ℝ => 1 - t)
    (fun k => Work.Drive.blockPlane Ξ Q u τ k)
    contDiff_designCutoff (fun k => contMDiff_blockPlane Ξ hΞsm Q u τ k hQ) hcpos hc10 hc20
    (by norm_num) (by norm_num) continuousOn_designCutoff strictAntiOn_designCutoff
    (fun e mm he k y => blockPlane_affRep he mm Ξ Q u τ k y) hlev hmeet

end

end Work.Drive
