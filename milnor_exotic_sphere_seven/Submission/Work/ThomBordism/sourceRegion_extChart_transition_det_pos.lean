import Mathlib
import Submission.Work.PTGeometric.SourceRegionSetupBasic
import Submission.Work.PTGeometric.WeakRegion.Manifold
import Submission.Work.ThomBordism.extChart_transition_det_pos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The region chart structure of the source region is positively oriented

The source region `M = {Φ ≤ 0} ⊂ A` of the null-homotopy construction carries the *weak
region-charting* structure of `Work.PTGeometric.WeakRegion` (`Work.PTGeometric.sourceRegionSetup`).
Here `A = EuclideanHalfSpace (8 + k + 1)` is the half-space *with its identity chart structure*, so
the ambient charts are the identity.

The point of this file is the orientation statement needed for the level-set theory: the transition
maps between the extended charts of the region have **positive** Jacobian determinant on the
interior of the model half-space.

The reason this is true — and it is a rather degenerate reason — is that the region charts at the
*interior* points of the region (i.e. points not in `(𝓡∂ _).boundary M`, which by
`RegionSetupWeak.mem_boundary_iff` means `x.1 ∉ ∂A` and `Φ x.1 < 0`) are the *identity* map:

* by the pinned chart data (`Work.ThomBordism.exists_chartData_pinned`, case `Φ m < 0`) the model
  chart `T m` is `idPH` and the ambient chart `dom m` is a restriction of the ambient chart at
  `m.1`;
* the ambient chart at a point of the half-space *is* `OpenPartialHomeomorph.refl`
  (`chartedSpaceSelf`), so `dom m` is a restriction of the identity;

hence `extChartAt I m p = p.1.1` for every `p` in the chart source, and the transition between two
such extended charts is the identity, of determinant `1 > 0`.

The main theorem `Work.ThomBordism.sourceRegion_extChart_transition_det_pos` is then a direct
application of the general criterion `Work.ThomBordism.extChart_transition_det_pos` (whose
hypothesis is exactly "the two extended charts agree on the common part of their sources").
-/

set_option linter.unusedSectionVars false

namespace Work.ThomBordism

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold

variable {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] [Nonempty ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (mm : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ mm = 1)
    (hphi : Work.PTGeometric.SourceRegionPhiInteriorSign k
      (Work.PTGeometric.sourceZeroSet G mm hpow)
      (Work.PTGeometric.sourceBasepoint (D := D) (Fam := Fam) G mm hpow))
    (hweak : ∀ x : EuclideanHalfSpace ((8 + k) + 1),
      Work.PTGeometric.sourcePhi G mm hpow hphi x = 0 →
      mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ ℝ) (Work.PTGeometric.sourcePhi G mm hpow hphi) x ≠ 0)

noncomputable abbrev sourceRegionMk : Work.PTGeometric.WeakRegion.RegionSetupWeak k :=
  Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G mm hpow hphi hweak

lemma sourceRegionMk_chartAt_eq_refl : ∀ s : (sourceRegionMk G mm hpow hphi hweak).A,
    _root_.chartAt (EuclideanHalfSpace ((8 + k) + 1)) s =
      OpenPartialHomeomorph.refl (EuclideanHalfSpace ((8 + k) + 1)) := fun _ => rfl

lemma sourceRegionMk_extChartAt_apply_of_phi_neg (m : (sourceRegionMk G mm hpow hphi hweak).Region)
    (hm : (sourceRegionMk G mm hpow hphi hweak).Φ m.1 < 0) :
    ∀ p ∈ (extChartAt (𝓡∂ (8 + k + 1)) m).source,
      (extChartAt (𝓡∂ (8 + k + 1)) m) p = p.1.1 := by
  intro p hp
  have hpsrc : p ∈ (sourceRegionMk G mm hpow hphi hweak).chartSource m := by
    rw [extChartAt, OpenPartialHomeomorph.extend_source] at hp
    exact hp
  obtain ⟨U, _hUopen, _hmU, hdom, _hdomsub, hT⟩ :
      ∃ U : Set (sourceRegionMk G mm hpow hphi hweak).A, IsOpen U ∧ m.1 ∈ U ∧
        (sourceRegionMk G mm hpow hphi hweak).dom m =
          (_root_.chartAt (EuclideanHalfSpace (8 + k + 1)) m.1).restr U ∧
        ((sourceRegionMk G mm hpow hphi hweak).dom m).source ⊆ U ∧
        (sourceRegionMk G mm hpow hphi hweak).T m =
          Work.PTGeometric.WeakRegion.RegionSetupWeak.idPH
            (EuclideanSpace ℝ (Fin (8 + k + 1))) :=
    (Classical.choose_spec (Classical.choose_spec
      (Work.ThomBordism.exists_chartData_pinned k (sourceRegionMk G mm hpow hphi hweak) m))).2.2.2.2.2.2.2.2.2 hm
  have hdomapply : (sourceRegionMk G mm hpow hphi hweak).dom m p.1 = p.1 := by
    rw [hdom, OpenPartialHomeomorph.restr_apply, sourceRegionMk_chartAt_eq_refl G mm hpow hphi hweak]
    rfl
  have hdomext : (sourceRegionMk G mm hpow hphi hweak).domExt m p.1 = p.1.1 := by
    show OpenPartialHomeomorph.extend ((sourceRegionMk G mm hpow hphi hweak).dom m)
      (𝓡∂ (8 + k + 1)) p.1 = p.1.1
    rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, hdomapply]
    exact modelWithCornersEuclideanHalfSpace_apply _
  have hcv : (sourceRegionMk G mm hpow hphi hweak).chartVec m p.1 = p.1.1 := by
    show (sourceRegionMk G mm hpow hphi hweak).T m
      ((sourceRegionMk G mm hpow hphi hweak).domExt m p.1) = p.1.1
    rw [hdomext, hT, Work.PTGeometric.WeakRegion.RegionSetupWeak.idPH_apply]
  have hchartval : (sourceRegionMk G mm hpow hphi hweak).chartAt m p = p.1 := by
    rw [show (sourceRegionMk G mm hpow hphi hweak).chartAt m p =
        ⟨(sourceRegionMk G mm hpow hphi hweak).chartVec m p.1,
          (sourceRegionMk G mm hpow hphi hweak).chartVec_nonneg m hpsrc⟩ from dif_pos hpsrc]
    exact Subtype.ext hcv
  rw [extChartAt, OpenPartialHomeomorph.extend_coe, Function.comp_apply]
  rw [show (_root_.chartAt (EuclideanHalfSpace (8 + k + 1)) m) p
      = (sourceRegionMk G mm hpow hphi hweak).chartAt m p from rfl]
  rw [hchartval]
  exact modelWithCornersEuclideanHalfSpace_apply _

/-- **The region chart structure of the source region is positively oriented**: the transition
between the extended charts of the region has positive determinant on the interior of the model
half-space. -/
theorem sourceRegion_extChart_transition_det_pos
    {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] [Nonempty ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (hphi : Work.PTGeometric.SourceRegionPhiInteriorSign k
      (Work.PTGeometric.sourceZeroSet G m hpow)
      {x : EuclideanHalfSpace ((8 + k) + 1) |
        Work.PTGeometric.flatSourceHomotopy8 (k := k)
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ x.1 = D.t₀})
    (hweak : ∀ x : EuclideanHalfSpace ((8 + k) + 1),
      Work.PTGeometric.sourcePhi G m hpow hphi x = 0 →
      mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ ℝ) (Work.PTGeometric.sourcePhi G m hpow hphi) x ≠ 0) :
    let S := Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak
    ∀ (x y : S.Region),
      x ∉ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary S.Region →
      y ∉ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary S.Region →
      ∀ z ∈ (extChartAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) x).target ∩
          (extChartAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) x).symm ⁻¹'
            (extChartAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) y).source,
        z 0 > 0 →
        (0 : ℝ) < LinearMap.det
          ((fderiv ℝ (fun w : EuclideanSpace ℝ (Fin ((8 + k) + 1)) =>
            (extChartAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) y)
              ((extChartAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) x).symm w)) z)
            : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →ₗ[ℝ]
              EuclideanSpace ℝ (Fin ((8 + k) + 1))) := by
  dsimp only
  refine Work.ThomBordism.extChart_transition_det_pos k ?_
  intro x y hx hy p hp
  have hxlt : (sourceRegionMk G m hpow hphi hweak).Φ x.1 < 0 := by
    have hxnot : ¬ (x.1 ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
          (sourceRegionMk G m hpow hphi hweak).A ∨ (sourceRegionMk G m hpow hphi hweak).Φ x.1 = 0) :=
      fun h => hx ((Work.PTGeometric.WeakRegion.RegionSetupWeak.mem_boundary_iff
        (sourceRegionMk G m hpow hphi hweak) x).mpr h)
    exact lt_of_le_of_ne x.2 (fun h0 => hxnot (Or.inr h0))
  have hylt : (sourceRegionMk G m hpow hphi hweak).Φ y.1 < 0 := by
    have hymem : ¬ (y.1 ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
          (sourceRegionMk G m hpow hphi hweak).A ∨ (sourceRegionMk G m hpow hphi hweak).Φ y.1 = 0) :=
      fun h => hy ((Work.PTGeometric.WeakRegion.RegionSetupWeak.mem_boundary_iff
        (sourceRegionMk G m hpow hphi hweak) y).mpr h)
    exact lt_of_le_of_ne y.2 (fun h0 => hymem (Or.inr h0))
  have hx' := sourceRegionMk_extChartAt_apply_of_phi_neg G m hpow hphi hweak x hxlt p hp.1
  have hy' := sourceRegionMk_extChartAt_apply_of_phi_neg G m hpow hphi hweak y hylt p hp.2
  exact hx'.trans hy'.symm

end Work.ThomBordism
