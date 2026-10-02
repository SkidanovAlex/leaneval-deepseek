import Mathlib
import Submission.Work.ELNest.Setup
import Submission.Work.ELNest.Qp_shift
import Submission.Work.ELTop.tripodArms_cover
import Submission.Work.ELTop.tripodArms_disjoint
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.TopJordan.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELNest

/-!
# `z0_notMem_clA`: `z₀ = f⁴z₁` lies in the arm `C` of the tripod at `b₂`

The level-`0` pair of the arm-`C` nest of `NestData` has the angles

    armC1 0 = 821/1023  and  armC2 0 + 1 = 326/1023 + 1,

i.e. exactly the two angles of the pair `P₄ = {T⁴α₁, T⁴α₂}` of the root portrait, whose
co-landing point is `f⁴z₁ = (Tantibar c)^[4] z₁`.  Hence the landing point `(Zc 0).y` of the
level-`0` arm-`C` pair *is* `z₀`, and since `cutC_mem` places `(Zc 0).y` in the arm `C`, while the
arms `A` and `C` are disjoint open sets, `z₀` is not in the closure of the arm `A`.
-/

/-! ## The angle arithmetic -/

/-- The fourth iterate of the angle-doubling map `T θ = -2θ mod 1` sends the root angle
`α₁ = 371/1023` to `821/1023` (`= Int.fract (16 · 371/1023)`). -/
theorem T_iterate_four_alpha1 : Work.EL.T^[4] Work.ELNest.alpha1 = 821 / 1023 := by
  rw [Work.ELNest.T_iterate_succ 3, Work.ELNest.alpha1, Int.fract_eq_iff]
  refine ⟨by norm_num, by norm_num, 5, ?_⟩
  push_cast
  norm_num

/-- The `centred` normalisation of `Defs.lean` leaves the small positive number
`821/1023 - 37/63` unchanged: adding `1/2` keeps it below `1`. -/
theorem centred_armC1 : Work.ELNest.centred ((821 : ℝ) / 1023 - 37 / 63)
    = (821 : ℝ) / 1023 - 37 / 63 := by
  have h0 : (0 : ℝ) < 821 / 1023 - 37 / 63 := by norm_num
  have h1 : (821 : ℝ) / 1023 - 37 / 63 < 1 / 2 := by norm_num
  have h : Int.fract ((821 : ℝ) / 1023 - 37 / 63 + 1 / 2) = 821 / 1023 - 37 / 63 + 1 / 2 :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  simp only [Work.ELNest.centred, h]
  ring

/-- The first angle of the level-`0` pair of the arm `C` is the root-portrait angle `821/1023`
(the first angle of `T⁴α₁`). -/
theorem armC1_zero : Work.ELNest.armC1 0 = 821 / 1023 := by
  simp only [Work.ELNest.armC1, Work.ELNest.contract, pow_zero, Nat.cast_one, div_one,
    centred_armC1]
  rw [show (37 : ℝ) / 63 + ((821 : ℝ) / 1023 - 37 / 63) = 821 / 1023 by ring]
  exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

/-! ## The arm statement -/

/-- **`z₀ = f⁴z₁` is not in the closure of the arm `A`.**  It lies in the arm `C`, an open set
disjoint from the arm `A`. -/
theorem z0_notMem_clA {c : ℂ} (S : Work.ELNest.NestData c) :
    (LeanEval.ComplexAnalysis.Tantibar c)^[4] S.d.z₁ ∉ closure S.armA := by
  -- the ray pair `P₀ = (α₁, α₂)` lands at `z₁`
  have hP0 : Work.EL.LandsN S.d.hN Work.ELNest.alpha1 S.d.z₁ := by
    have h := S.P0.lands_a
    rw [S.P0a, S.P0y] at h
    exact h
  -- hence `z₀` is the landing point of the ray of angle `T^[4] α₁ = 821/1023`
  have hL1 : Work.EL.LandsN S.d.hN (821 / 1023)
      ((LeanEval.ComplexAnalysis.Tantibar c)^[4] S.d.z₁) := by
    have h := Work.ELNest.landsN_iterate S.d.hN S.d.bottcher 4 hP0
    rw [T_iterate_four_alpha1] at h
    exact h
  -- the level-`0` arm-`C` pair has the same first angle `821/1023`
  have hL2 : Work.EL.LandsN S.d.hN (821 / 1023) (S.Zc 0).y := by
    have h := (S.Zc 0).lands_a
    rw [S.Zca 0] at h
    rw [armC1_zero] at h
    exact h
  have hzy : (LeanEval.ComplexAnalysis.Tantibar c)^[4] S.d.z₁ = (S.Zc 0).y :=
    Work.ELNest.landsN_unique hL1 hL2
  -- so `z₀` is the cut point of the level-`0` arm-`C` pair, which lies in the arm `C`
  have hzC : (LeanEval.ComplexAnalysis.Tantibar c)^[4] S.d.z₁ ∈ S.armC := by
    rw [hzy]
    exact S.cutC_mem 0
  -- the arm `C` is open and disjoint from the arm `A`
  have hopenC : IsOpen S.armC := by
    show IsOpen (Work.EL.Tripod.armC S.tripod)
    rw [Work.EL.Tripod.armC]
    exact (Work.ELTop.isOpen_pairSide S.d.hN (Work.EL.Tripod.pairC S.tripod)).1
  have hdisj : Disjoint S.armA S.armC :=
    ((Work.ELTop.tripodArms_disjoint S.d.hN Work.TopJordan.jordanForm S.tripod).2.2).symm
  -- an open neighbourhood of `z₀` misses the arm `A`, so `z₀ ∉ closure S.armA`
  intro hcl
  obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hopenC _ hzC
  obtain ⟨y, hyA, hyd⟩ := Metric.mem_closure_iff.mp hcl ε hεpos
  have hyC : y ∈ S.armC := hε (by rw [Metric.mem_ball, dist_comm]; exact hyd)
  exact Set.disjoint_left.mp hdisj hyA hyC

end Work.ELNest
