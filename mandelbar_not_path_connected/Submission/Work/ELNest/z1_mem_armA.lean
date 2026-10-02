import Mathlib
import Submission.Work.ELNest.Setup
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.tripodArms_cover
import Submission.Work.ELTop.tripodArms_disjoint
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELTop.landsN_iff_landsAt
import Submission.Work.ELTop.isClosed_pairCurve
import Submission.Work.TopJordan.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

noncomputable section

namespace Work.ELNest

open Work.EL

theorem z1_mem_armA {c : ℂ} (S : Work.ELNest.NestData c) : S.d.z₁ ∈ S.armA := by
  -- the arc `(22/63, 25/63)` of the arm `A` contains the root angle `α₁ = 371/1023`
  have hInArc : InArc Work.EL.alpha1 (22 / 63 : ℝ) (25 / 63) :=
    Work.ELTop.InArc_of_mem_Ioo (by norm_num [Work.EL.alpha1])
      (by norm_num [Work.EL.alpha1]) (by norm_num)
  have hJ : Work.Top.JordanForm := Work.TopJordan.jordanForm
  -- the dynamical ray of angle `α₁` lands at `z₁` (`RootParabolic.rays`)
  have hL : LandsN S.d.hN Work.EL.alpha1 S.d.z₁ :=
    (Work.ELTop.landsN_iff_landsAt S.d.hN S.d.bottcher Work.EL.alpha1 S.d.z₁).mpr S.d.rays.1
  -- hence `z₁` lies in the filled Julia set
  have hK : S.d.z₁ ∈ K c := Work.ELTop.landsN_mem_K S.d.hN hL
  -- the points of the ray `R(α₁)` of level `> 1` lie in the arm `A`
  have hmem : ∀ t : ℝ, 1 < t → rayPt S.d.hN Work.EL.alpha1 t ∈ S.armA := by
    intro t ht
    exact Work.ELTop.paramRay_subset_pairSide S.d.hN hJ (Tripod.pairA S.tripod) hInArc
      (rayPt_mem_paramRay S.d.hN ht)
  -- hence `z₁` lies in the closure of the arm `A`
  have hcl : S.d.z₁ ∈ closure S.armA := by
    refine mem_closure_of_tendsto hL ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hmem t ht
  -- `z₁ ≠ b₂`: `b₂` is fixed by `Tsq c = (T_c)²`, while `z₁` has exact period `5`
  have hne : S.d.z₁ ≠ S.b2 := by
    intro h
    have hfix : Work.Landing.Tsq c S.d.z₁ = S.d.z₁ := by
      rw [h]; exact S.b2_fix
    rw [Tsq_eq_comp] at hfix
    exact S.d.ne_per 2 (by decide) hfix
  -- `z₁` is not on the tripod curve
  have hcurve : S.d.z₁ ∉ Tripod.curve S.tripod := by
    intro h
    rw [Tripod.curve, Set.mem_union, Set.mem_union, Set.mem_union,
      Set.mem_singleton_iff] at h
    rcases h with ((h1 | h2) | h3) | h4
    · exact (paramRay_subset_compl S.d.hN (22 / 63) h1) hK
    · exact hne h2
    · exact (paramRay_subset_compl S.d.hN (25 / 63) h3) hK
    · exact (paramRay_subset_compl S.d.hN (37 / 63) h4) hK
  -- the three arms cover the complement of the tripod curve
  have hcover : S.d.z₁ ∈ Tripod.armA S.tripod ∪ Tripod.armB S.tripod ∪ Tripod.armC S.tripod := by
    rw [Work.ELTop.tripodArms_cover S.d.hN hJ S.tripod]
    exact hcurve
  rcases hcover with (hA | hB) | hC
  · exact hA
  · -- the arm `B` is open and disjoint from the arm `A`, which contains `z₁` in its closure
    exfalso
    have hopen : IsOpen (Tripod.armB S.tripod) :=
      IsOpen.connectedComponentIn
        (Work.ELTop.isClosed_pairCurve S.d.hN (Tripod.pairB S.tripod)).isOpen_compl
    obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hopen S.d.z₁ hB
    obtain ⟨y, hyA, hyd⟩ := Metric.mem_closure_iff.mp hcl ε hεpos
    have hyb : y ∈ Metric.ball S.d.z₁ ε := by
      rw [Metric.mem_ball, dist_comm]; exact hyd
    exact Set.disjoint_left.mp (Work.ELTop.tripodArms_disjoint S.d.hN hJ S.tripod).1 hyA
      (hε hyb)
  · -- the same for the arm `C`
    exfalso
    have hopen : IsOpen (Tripod.armC S.tripod) :=
      IsOpen.connectedComponentIn
        (Work.ELTop.isClosed_pairCurve S.d.hN (Tripod.pairC S.tripod)).isOpen_compl
    obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hopen S.d.z₁ hC
    obtain ⟨y, hyA, hyd⟩ := Metric.mem_closure_iff.mp hcl ε hεpos
    have hyb : y ∈ Metric.ball S.d.z₁ ε := by
      rw [Metric.mem_ball, dist_comm]; exact hyd
    exact Set.disjoint_left.mp (Work.ELTop.tripodArms_disjoint S.d.hN hJ S.tripod).2.2.symm hyA
      (hε hyb)

end Work.ELNest
