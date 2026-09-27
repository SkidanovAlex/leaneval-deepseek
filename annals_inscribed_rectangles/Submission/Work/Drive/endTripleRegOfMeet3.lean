import Mathlib
import Submission.Work.Drive.sweepTripleLift
import Submission.Work.Drive.classRegOfSweeps
import Submission.Work.Drive.planeClassDeriv_eq_mfderiv
import Submission.Work.Drive.encodedEndData

/-!
# The row-1 producer of the ends clause: `EndTripleReg` of the plane class maps from `Meet3Hyp`

The ends clause of the design (`NOTES_LEAD_hodd_blockT6.md` §3, row 1) needs the *class-level* end data
`Work.Drive.EndTripleReg` of the three plane presentations from the design's own `Meet3Hyp` of the three
*radial sweeps*.  This file provides it (in the box-restricted form that the sweeps' transversality can
actually supply, see the note at the end):

* `Work.Drive.endTripleReg_of_meet3Hyp_sweeps` — the class-level regularity of a common-class triple of
  plane parameters **lying in the closed unit square**, whose planes have levels strictly above the
  truncation level `c 0` (which is the largest), from `Meet3Hyp`.
* `Work.Drive.endTripleReg_box_of_meet3Hyp_sweeps` — the same in the `y₀ y₁ y₂`-shape of
  `EndTripleReg`.

The route is the composition of the three bricks

1. `Work.Drive.exists_sweepTriple_of_commonClass` — the level lift: a common-class triple of plane
   parameters in the square becomes a *triple point* of the three sweeps (block `0` on its radial face,
   the other two lifted along their radial coordinate);
2. `Work.Drive.classReg_of_sweepTransverse_planeClassDeriv` — the sweep transversality at that triple
   point is transported to the plane class derivatives (`Meet3Hyp.trans` → `TripleTransverse` →
   charted block form → `Work.Drive.inj_inf_of_tripleTransverseE_of_blocks`);
3. `Work.Drive.planeClassDeriv_injective_iff` / `planeClassDeriv_range_generalPosition_iff` — the
   charted class derivative is the intrinsic `mfderiv` of the plane class map.
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
local instance instIsManifoldProjChart :
    IsManifold (𝓡 3) Work.Drive.Ctop (Projectivization ℝ (Eucl 3)) :=
  Work.Drive.isManifold_projCharted 3

/-! ## 1. The class maps of smooth plane presentations are chart-differentiable

This is the local `hclass` of `Work.Drive.tripleTransverse_clampedSweeps_of_contMDiff`, extracted as a
stand-alone lemma so that the *converse* extraction can use it too. -/

lemma differentiableAt_projChartMap_cls {n : ℕ}
    (Q : EuclideanSpace ℝ (Fin n) → Work.Drive.CappingSpace)
    (hQ : ContMDiff (𝓡 n) (𝓡 4) Work.Drive.Ctop Q) (z : EuclideanSpace ℝ (Fin n)) (i : Fin 4)
    (hzi : (Work.Drive.cappingSpaceHomeoProj (Q z)).2 ∈ Work.Drive.projChartSource i) :
    DifferentiableAt ℝ (fun y => Work.Drive.projChartMap i
      ((Work.Drive.cappingSpaceHomeoProj (Q y)).2)) z := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    Work.Drive.halfLineProjectiveCharted
  have hG : ContMDiffAt (𝓡 n) (𝓡 4) Work.Drive.Ctop
      (fun w => Work.Drive.cappingSpaceHomeoProj (Q w)) z := by
    have hiff := Work.Drive.chartedStructure_contMDiffWithinAt
      (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (E' := EuclideanSpace ℝ (Fin n)) (H' := EuclideanSpace ℝ (Fin n)) (𝓡 n)
      (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
      (M' := Work.Drive.CappingSpace) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      Work.Drive.cappingSpaceHomeoProj.symm Q Set.univ z
    exact hiff.mp (hQ.contMDiffAt)
  obtain ⟨-, hcls⟩ := (Work.Drive.contMDiffAt_halfLineProjective_iff
    (fun w => Work.Drive.cappingSpaceHomeoProj (Q w)) z).mp hG
  have hF0 := ((Work.Drive.contMDiffAt_projCharted_iff
    (fun y => (Work.Drive.cappingSpaceHomeoProj (Q y)).2) z i hzi).mp hcls).2
  exact (contMDiffAt_iff_contDiffAt.mp hF0).differentiableAt (by norm_num)

/-! ## 2. The charted class regularity from the sweep transversality -/

theorem classReg_of_sweepTransverse_planeClassDeriv
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hval : ∀ k, Work.Drive.clampedSweep (c k) ψ (P k) (x k)
      = Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0))
    (h : TripleTransverse
      (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 0) ψ (P 0)) (x 0))
      (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 1) ψ (P 1)) (x 1))
      (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 2) ψ (P 2)) (x 2))) :
    (∀ k, Function.Injective (Work.Drive.planeClassDeriv c ψ P k x)) ∧
      ((Work.Drive.planeClassDeriv c ψ P 0 x).range ⊓
        (Work.Drive.planeClassDeriv c ψ P 1 x).range ⊓
        (Work.Drive.planeClassDeriv c ψ P 2 x).range = ⊥) :=
  classReg_of_sweepTransverse c ψ P
    (fun k => Work.Drive.projChartIndexOf
      ((Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).2))
    hψ hP x hval
    (fun k => Work.Drive.projCharted_chartAt_eq_projChart _)
    (fun k => differentiableAt_projChartMap_cls (P k) (hP k)
      (Work.Drive.mk2 (x k 0) (x k 1)) _
      (by
        rw [← Work.Drive.cls_clampedSweep (c k) ψ (P k) (x k)]
        exact Work.Drive.projChartIndexOf_spec _))
    h

/-! ## 3. The producer -/

theorem endTripleReg_of_meet3Hyp_sweeps
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (hcpos : ∀ k, 0 < c k) (hc10 : c 1 < c 0) (hc20 : c 2 < c 0)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0) (hcont : ContinuousOn ψ (Set.Icc 0 1))
    (hanti : StrictAntiOn ψ (Set.Icc 0 1))
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < Work.Drive.levelOf (P k y))
    (hmeet : Meet3Hyp Work.Drive.CappingSpace
      (fun k => Work.Drive.clampedSweep (c k) ψ (P k))) :
    ∀ y : Fin 3 → EuclideanSpace ℝ (Fin 2),
      (∀ k, y k ∈ Submission.Drive.unitBox 1) → Work.Drive.CommonClass P y →
      Function.Injective (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P 0)) (y 0)) ∧
      Function.Injective (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P 1)) (y 1)) ∧
      Function.Injective (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P 2)) (y 2)) ∧
      ((mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P 0)) (y 0)).range ⊓
        (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P 1)) (y 1)).range ⊓
        (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P 2)) (y 2)).range = ⊥) := by
  intro y hy hcls
  obtain ⟨x, hxbox, hmk2, hval⟩ :=
    exists_sweepTriple_of_commonClass c ψ P hcpos hc10 hc20 hψ0 hψ1 hcont hanti y hy
      (fun k => hlev k (y k)) hcls
  have hTR := hmeet.trans x hxbox (hval 1).symm (hval 2).symm
  obtain ⟨hInj, hRange⟩ := classReg_of_sweepTransverse_planeClassDeriv c ψ P hψ hP x hval hTR
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hh := (Work.Drive.planeClassDeriv_injective_iff c ψ P hP 0 x).mp (hInj 0)
    rw [hmk2 0] at hh
    exact hh
  · have hh := (Work.Drive.planeClassDeriv_injective_iff c ψ P hP 1 x).mp (hInj 1)
    rw [hmk2 1] at hh
    exact hh
  · have hh := (Work.Drive.planeClassDeriv_injective_iff c ψ P hP 2 x).mp (hInj 2)
    rw [hmk2 2] at hh
    exact hh
  · have hh := (Work.Drive.planeClassDeriv_range_generalPosition_iff c ψ P hP x).mp hRange
    rw [hmk2 0, hmk2 1, hmk2 2] at hh
    exact hh

/-- **The row-1 producer in the shape of `Work.Drive.EndTripleReg`**, with the box hypothesis on the
three plane parameters: every common-class triple of plane parameters **in the closed unit square**
whose plane levels are above the truncation level satisfies the `EndTripleReg` conclusion. -/
theorem endTripleReg_box_of_meet3Hyp_sweeps
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (hcpos : ∀ k, 0 < c k) (hc10 : c 1 < c 0) (hc20 : c 2 < c 0)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0) (hcont : ContinuousOn ψ (Set.Icc 0 1))
    (hanti : StrictAntiOn ψ (Set.Icc 0 1))
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < Work.Drive.levelOf (P k y))
    (hmeet : Meet3Hyp Work.Drive.CappingSpace
      (fun k => Work.Drive.clampedSweep (c k) ψ (P k))) :
    ∀ y₀ y₁ y₂ : EuclideanSpace ℝ (Fin 2),
      (∀ k : Fin 3, (![y₀, y₁, y₂] : Fin 3 → EuclideanSpace ℝ (Fin 2)) k
        ∈ Submission.Drive.unitBox 1) →
      Work.Drive.planeClassMap (P 0) y₀ = Work.Drive.planeClassMap (P 1) y₁ →
      Work.Drive.planeClassMap (P 0) y₀ = Work.Drive.planeClassMap (P 2) y₂ →
      Function.Injective (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P 0)) y₀) ∧
      Function.Injective (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P 1)) y₁) ∧
      Function.Injective (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P 2)) y₂) ∧
      ((mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P 0)) y₀).range ⊓
        (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P 1)) y₁).range ⊓
        (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P 2)) y₂).range = ⊥) := by
  intro y₀ y₁ y₂ hbox h01 h02
  have hcc : Work.Drive.CommonClass P ![y₀, y₁, y₂] := by
    intro k
    fin_cases k
    · rfl
    · simpa using h01.symm
    · simpa using h02.symm
  have h := endTripleReg_of_meet3Hyp_sweeps c ψ P hψ hP hcpos hc10 hc20 hψ0 hψ1 hcont hanti hlev
    hmeet ![y₀, y₁, y₂] hbox hcc
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- **The row-1 producer in the exact shape of `Work.Drive.EndTripleReg`**, at the price of the
*box-residency* hypothesis on the common-class triples: if every triple of plane parameters with a
common class lies in the closed unit square, then `Meet3Hyp` of the three sweeps gives the full
`EndTripleReg` of the three plane class maps.

The box residency is *not* automatic (the class maps are defined on all of `ℝ²`), and the unrestricted
`EndTripleReg` is **not** a consequence of `Meet3Hyp` alone: for three copies of the same *folded*
presentation (`P k = diskPlane Q`), the common-class triples include the fold parameters
(`y k i ∈ {0,1}`), where the class derivative is singular, while `Meet3Hyp` of the three sweeps can
still hold (its triple points are at interior parameters only).  See
`Submission/Work/Drive/ROW1_ENDTRIPLEREG_STATUS.md`. -/
theorem endTripleReg_of_meet3Hyp_sweeps_of_box
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (hcpos : ∀ k, 0 < c k) (hc10 : c 1 < c 0) (hc20 : c 2 < c 0)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0) (hcont : ContinuousOn ψ (Set.Icc 0 1))
    (hanti : StrictAntiOn ψ (Set.Icc 0 1))
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < Work.Drive.levelOf (P k y))
    (hmeet : Meet3Hyp Work.Drive.CappingSpace
      (fun k => Work.Drive.clampedSweep (c k) ψ (P k)))
    (hbox : ∀ y₀ y₁ y₂ : EuclideanSpace ℝ (Fin 2),
      Work.Drive.planeClassMap (P 0) y₀ = Work.Drive.planeClassMap (P 1) y₁ →
      Work.Drive.planeClassMap (P 0) y₀ = Work.Drive.planeClassMap (P 2) y₂ →
      ∀ k : Fin 3, (![y₀, y₁, y₂] : Fin 3 → EuclideanSpace ℝ (Fin 2)) k
        ∈ Submission.Drive.unitBox 1) :
    Work.Drive.EndTripleReg (Work.Drive.planeClassMap (P 0))
      (Work.Drive.planeClassMap (P 1)) (Work.Drive.planeClassMap (P 2)) := by
  intro y₀ y₁ y₂ h01 h02
  exact endTripleReg_box_of_meet3Hyp_sweeps c ψ P hψ hP hcpos hc10 hc20 hψ0 hψ1 hcont hanti
    hlev hmeet y₀ y₁ y₂ (hbox y₀ y₁ y₂ h01 h02) h01 h02

end

end Work.Drive
