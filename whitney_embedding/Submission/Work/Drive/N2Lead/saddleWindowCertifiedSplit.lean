import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.packetDefs
import Submission.Work.Drive.N2Lead.saddlePinDefs
import Submission.Work.Drive.N2.GoodDrawingFamily
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2.saddlePack
import Submission.Work.Drive.N2Lead.pinSetup
import Submission.Work.Drive.N2Lead.saddleArcs
import Submission.Work.Drive.N2Lead.saddleAngleFunction
import Submission.Work.Drive.N2Lead.saddleProfileRows
import Submission.Work.Drive.N2Lead.saddleBridgeRow
import Submission.Work.Drive.N2Lead.saddlePacketRows
import Submission.Work.Drive.N2Lead.saddleFlowRowsWide
import Submission.Work.Drive.N2Lead.saddleWindow_of_packet_band_off
import Submission.Work.Drive.N2Lead.saddleLowerCertified
import Submission.Work.Drive.N2Lead.certifiedTransferOnLevel
import Submission.Work.Drive.N2Lead.isCertifiedAt_of_starRegions
import Submission.Work.Drive.N2Lead.upperRegionRate
import Submission.Work.Drive.N2Lead.upperRegionRateNeg
import Submission.Work.Drive.N2Lead.polarBridgeRate
import Submission.Work.Drive.N2Lead.modelArc_cross_about_one
import Submission.Work.Drive.N2Lead.modelArcRayFree
import Submission.Work.Drive.N2.dichotomyOneComp
import Submission.Work.Drive.N2Lead.saddlePin_split_imp_upper
import Submission.Work.Drive.N2Lead.pinUpEqArcs
import Submission.Work.Drive.N2Lead.mobius_park_off
import Submission.Work.Drive.N2Lead.saddlePacketRowsOfArcs

import Submission.Work.Drive.N2Lead.upperRegionMem
import Submission.Work.Drive.N2Lead.polarRayHit
import Submission.Work.Drive.N2Lead.modelArcCross_absLe
import Submission.Work.Drive.N2Lead.polarBridgeRateOdd
import Submission.Work.Drive.N2Lead.arcRangeOrBridgeZone
import Submission.Work.Drive.N2Lead.upperCertSplit
import Submission.Work.N2Lead.absDerivSmoothTransitionLeTwo

namespace Work.Drive.N2Lead

set_option maxHeartbeats 1000000

open scoped Manifold ContDiff Topology
open Set Filter


open scoped Manifold ContDiff Topology in
open Set Filter in
/-- **The profile rows of the saddle packet, with `π`-periodicity added.**  The same statement as
`Work.Drive.N2Lead.saddleProfileRows` (with `r := leadProfileR ηs m R` made explicit), plus the row
`r (φ + π) = r φ` (true because the profile depends on `cos (2φ)` alone); the odd bridge zone of the
upper certificate needs it. -/
theorem saddleProfileRowsPi {ηs m R : ℝ} (hηs : 0 < ηs) (hηs1 : ηs < 1 / 10) (hm : 1 < m)
    (hm2 : m < 2) (hR : 2 ≤ R) :
    ∃ r : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r ∧ (∀ φ : ℝ, 0 < r φ) ∧
      (∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ) ∧ (∀ φ : ℝ, r (φ + Real.pi) = r φ) ∧
      (∀ φ : ℝ, r φ ≤ R) ∧
      (∀ w ∈ Set.Icc (-m) m,
        r (Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs))
          = Real.sqrt (ηs / -Real.cos (2 * (Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs))))) ∧
      (∀ w ∈ Set.Icc (-m) m,
        r (-(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs))
          = Real.sqrt (ηs / -Real.cos (2 * (-(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs))))) ∧
      (∀ (φ : ℝ) (k : ℤ), |φ - k * Real.pi| ≤ Work.Drive.N2Lead.mobiusPhiE ηs m →
        Real.sqrt (ηs ^ 2 + m ^ 2) ≤ r φ ^ 2) ∧
      (∀ φ : ℝ, r (-φ) = r φ) ∧
      (∀ φ ∈ Set.Icc (0 : ℝ) (Work.Drive.N2Lead.mobiusPhiE ηs m), deriv r φ ≤ 0) := by
  have hm0 : 0 < m := by linarith
  have hR0 : 0 < R := by linarith
  obtain ⟨hEcos, hEpos, hElt⟩ := Work.Drive.N2Lead.leadProfile_phiE hηs hm0
  have hA2lt : Real.sqrt (ηs ^ 2 + m ^ 2) < R ^ 2 :=
    Work.Drive.N2Lead.leadProfile_sqrt_lt hηs hηs1 hm hm2.le hR
  have hL : 0 < Work.Drive.N2Lead.leadProfileC2 ηs R - Work.Drive.N2Lead.leadProfileC1 ηs m := by
    have := Work.Drive.N2Lead.leadProfileC1_lt_C2 hηs hA2lt; linarith
  have hper : Function.Periodic (Work.Drive.N2Lead.leadProfileR ηs m R) Real.pi :=
    Work.Drive.N2Lead.leadProfileR_periodic_pi ηs m R
  refine ⟨Work.Drive.N2Lead.leadProfileR ηs m R,
    Work.Drive.N2Lead.leadProfileR_contDiff hηs hR0 hL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ
    exact Work.Drive.N2Lead.leadProfileF_pos hηs hR0 hL
  · intro φ
    calc Work.Drive.N2Lead.leadProfileR ηs m R (φ + 2 * Real.pi)
        = Work.Drive.N2Lead.leadProfileR ηs m R ((φ + Real.pi) + Real.pi) := by
          rw [show φ + 2 * Real.pi = (φ + Real.pi) + Real.pi by ring]
      _ = Work.Drive.N2Lead.leadProfileR ηs m R (φ + Real.pi) := hper (φ + Real.pi)
      _ = Work.Drive.N2Lead.leadProfileR ηs m R φ := hper φ
  · intro φ
    exact hper φ
  · intro φ
    exact Work.Drive.N2Lead.leadProfileF_le_R hηs hR0 hL
  · intro w hw
    have hrange := Work.Drive.N2Lead.phiU_mem_arcRange hηs hm0 hw
    exact Work.Drive.N2Lead.leadProfileR_arc hL hEcos hEpos.le hrange.1 hrange.2
  · intro w hw
    have hrange := Work.Drive.N2Lead.phiU_mem_arcRange hηs hm0 hw
    have hstep : Work.Drive.N2Lead.leadProfileR ηs m R
        (-(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs))
        = Work.Drive.N2Lead.leadProfileR ηs m R
          (Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs)) := by
      have h := hper (-(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs))
      rw [show -(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs) + Real.pi
            = Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs) by ring] at h
      exact h.symm
    rw [hstep, Work.Drive.N2Lead.leadProfileR_arc hL hEcos hEpos.le hrange.1 hrange.2]
    have hcos : Real.cos (2 * (Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs)))
        = Real.cos (2 * (-(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs))) := by
      have h2 : 2 * (Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs))
          = 2 * (-(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs))
            + (1 : ℤ) * (2 * Real.pi) := by
        push_cast; ring
      rw [h2, Real.cos_add_int_mul_two_pi]
    rw [hcos]
  · intro φ k hk
    have h1 : Work.Drive.N2Lead.leadProfileR ηs m R (φ - (k : ℝ) * Real.pi)
        = Work.Drive.N2Lead.leadProfileR ηs m R φ := by
      have hint := (hper.int_mul k) (φ - (k : ℝ) * Real.pi)
      rw [show φ - (k : ℝ) * Real.pi + (k : ℝ) * Real.pi = φ by ring] at hint
      exact hint.symm
    have hb := Work.Drive.N2Lead.leadProfileR_bridge hηs hR0 hL hA2lt.le hEcos hEpos.le hElt.le
      (φ := φ - (k : ℝ) * Real.pi) hk
    rw [h1] at hb
    exact hb
  · intro φ
    exact Work.Drive.N2Lead.leadProfileR_even ηs m R φ
  · intro φ hφ
    have hφ1 : φ ≤ Work.Drive.N2Lead.mobiusPhiE ηs m := hφ.2
    have hsin : 0 ≤ Real.sin (2 * φ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hφ.1]) (by linarith [hElt])
    have hFdiff : DifferentiableAt ℝ (Work.Drive.N2Lead.leadProfileF ηs m R)
        (Real.cos (2 * φ)) :=
      ((Work.Drive.N2Lead.leadProfileF_contDiff hηs hR0 hL).differentiable (by simp)).differentiableAt
    have hderiv : deriv (Work.Drive.N2Lead.leadProfileR ηs m R) φ
        = deriv (Work.Drive.N2Lead.leadProfileF ηs m R) (Real.cos (2 * φ))
          * (-Real.sin (2 * φ) * 2) := by
      have hc : HasDerivAt (fun ψ : ℝ => Real.cos (2 * ψ)) (-Real.sin (2 * φ) * 2) φ := by
        have h1 : HasDerivAt (fun ψ : ℝ => (2 : ℝ) * ψ) 2 φ := by
          simpa using (hasDerivAt_id (x := φ)).const_mul (2 : ℝ)
        exact h1.cos
      exact ((hFdiff.hasDerivAt).comp φ hc).deriv
    rw [hderiv]
    exact mul_nonpos_of_nonneg_of_nonpos
      (Monotone.deriv_nonneg (Work.Drive.N2Lead.leadProfileF_mono hηs hR0 hL))
      (by linarith [hsin])

/-! ## The region family of the upper certificate -/

/-- The right region of the upper certificate: `{Re > 0} ∩ ball 0 5`, centre `1`. -/
def upperRight : Set ℂ := {z : ℂ | 0 < z.re ∧ ‖z‖ < 5}

/-- The left region: the mirror of `upperRight`, centre `-1`. -/
def upperLeft : Set ℂ := {z : ℂ | z.re < 0 ∧ ‖z‖ < 5}

/-- **The regions of the upper certificate**: the left region, the right region (both for the marked
component's polar curve, cut by the sign of the real part) and one disc per parked circle. -/
noncomputable def upperRegions (n : ℕ) (i : Fin n) : Fin (n + 1) → Set ℂ :=
  Fin.cases upperLeft
    (fun j => if j = i then upperRight else Metric.ball (proj2 (farPos n j)) 2)

/-- The centres of the regions: `-1`, `1` and the parking spots' projections. -/
noncomputable def upperCentres (n : ℕ) (i : Fin n) : Fin (n + 1) → ℂ :=
  Fin.cases (-1) (fun j => if j = i then 1 else proj2 (farPos n j))

@[simp] lemma upperRegions_zero (n : ℕ) (i : Fin n) : upperRegions n i 0 = upperLeft := rfl

@[simp] lemma upperRegions_succ (n : ℕ) (i j : Fin n) :
    upperRegions n i j.succ = if j = i then upperRight else Metric.ball (proj2 (farPos n j)) 2 := rfl

@[simp] lemma upperCentres_zero (n : ℕ) (i : Fin n) : upperCentres n i 0 = -1 := rfl

@[simp] lemma upperCentres_succ (n : ℕ) (i j : Fin n) :
    upperCentres n i j.succ = if j = i then 1 else proj2 (farPos n j) := rfl

lemma upperCentres_succ_self (n : ℕ) (i : Fin n) : upperCentres n i i.succ = 1 := by
  rw [upperCentres_succ, if_pos rfl]

lemma upperCentres_succ_of_ne {n : ℕ} {i j : Fin n} (h : j ≠ i) :
    upperCentres n i j.succ = proj2 (farPos n j) := by
  rw [upperCentres_succ, if_neg h]

lemma upperRegions_succ_self (n : ℕ) (i : Fin n) : upperRegions n i i.succ = upperRight := by
  rw [upperRegions_succ, if_pos rfl]

lemma upperRegions_succ_of_ne {n : ℕ} {i j : Fin n} (h : j ≠ i) :
    upperRegions n i j.succ = Metric.ball (proj2 (farPos n j)) 2 := by
  rw [upperRegions_succ, if_neg h]

/-! ## The elementary geometry of the region family -/

lemma mem_upperLeft {z : ℂ} : z ∈ upperLeft ↔ z.re < 0 ∧ ‖z‖ < 5 := Iff.rfl

lemma mem_upperRight {z : ℂ} : z ∈ upperRight ↔ 0 < z.re ∧ ‖z‖ < 5 := Iff.rfl

lemma upperLeft_eq_inter : upperLeft = {z : ℂ | z.re < 0} ∩ {z : ℂ | ‖z‖ < 5} := rfl

lemma upperRight_eq_inter : upperRight = {z : ℂ | 0 < z.re} ∩ {z : ℂ | ‖z‖ < 5} := rfl

lemma mem_upperLeft_ball {z : ℂ} (h1 : z.re < 0) (h2 : ‖z‖ < 5) : z ∈ upperLeft := ⟨h1, h2⟩

lemma mem_upperRight_ball {z : ℂ} (h1 : 0 < z.re) (h2 : ‖z‖ < 5) : z ∈ upperRight := ⟨h1, h2⟩

lemma isOpen_upperLeft : IsOpen upperLeft := by
  have h1 : IsOpen {z : ℂ | z.re < 0} := isOpen_lt Complex.continuous_re continuous_const
  have h2 : IsOpen {z : ℂ | ‖z‖ < 5} := by
    rw [show {z : ℂ | ‖z‖ < 5} = Metric.ball 0 5 by
      ext z; simp [Metric.mem_ball, dist_eq_norm]]
    exact Metric.isOpen_ball
  rw [upperLeft_eq_inter]
  exact h1.inter h2

lemma isOpen_upperRight : IsOpen upperRight := by
  have h1 : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {z : ℂ | ‖z‖ < 5} := by
    rw [show {z : ℂ | ‖z‖ < 5} = Metric.ball 0 5 by
      ext z; simp [Metric.mem_ball, dist_eq_norm]]
    exact Metric.isOpen_ball
  rw [upperRight_eq_inter]
  exact h1.inter h2

lemma convex_re_lt_zero : Convex ℝ {z : ℂ | z.re < 0} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have h1 : (a • x + b • y).re = a * x.re + b * y.re := by simp
  rw [h1]
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · have hb1 : b = 1 := by linarith
    rw [← ha0, zero_mul, zero_add, hb1, one_mul]
    exact hy
  · have h3 : a * x.re < 0 := mul_neg_of_pos_of_neg ha0 hx
    have h4 : b * y.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hy.le
    linarith

lemma convex_re_gt_zero : Convex ℝ {z : ℂ | 0 < z.re} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have h1 : (a • x + b • y).re = a * x.re + b * y.re := by simp
  rw [h1]
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · have hb1 : b = 1 := by linarith
    rw [← ha0, zero_mul, zero_add, hb1, one_mul]
    exact hy
  · have h3 : 0 < a * x.re := mul_pos ha0 hx
    have h4 : 0 ≤ b * y.re := mul_nonneg hb hy.le
    linarith

lemma convex_upperLeft : Convex ℝ upperLeft := by
  rw [upperLeft_eq_inter]
  refine Convex.inter convex_re_lt_zero ?_
  rw [show {z : ℂ | ‖z‖ < 5} = Metric.ball 0 5 by
      ext z; simp [Metric.mem_ball, dist_eq_norm]]
  exact convex_ball 0 5

lemma convex_upperRight : Convex ℝ upperRight := by
  rw [upperRight_eq_inter]
  refine Convex.inter convex_re_gt_zero ?_
  rw [show {z : ℂ | ‖z‖ < 5} = Metric.ball 0 5 by
      ext z; simp [Metric.mem_ball, dist_eq_norm]]
  exact convex_ball 0 5

lemma closedBall_subset_upperLeft : Metric.closedBall (-1 : ℂ) (1 / 2) ⊆ upperLeft := by
  intro z hz
  have h1 : ‖z + 1‖ ≤ 1 / 2 := by
    simpa [Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add] using hz
  show z.re < 0 ∧ ‖z‖ < 5
  constructor
  · have h3 : z.re + 1 ≤ ‖z + 1‖ := by
      have := Complex.abs_re_le_norm (z + 1)
      have h4 := (abs_le.mp this).2
      simpa using h4
    linarith
  · have h2 : ‖z‖ ≤ ‖z + 1‖ + 1 := by
      calc ‖z‖ = ‖(z + 1) - 1‖ := by ring_nf
        _ ≤ ‖z + 1‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖z + 1‖ + 1 := by simp
    linarith

lemma closedBall_subset_upperRight : Metric.closedBall (1 : ℂ) (1 / 2) ⊆ upperRight := by
  intro z hz
  have h1 : ‖z - 1‖ ≤ 1 / 2 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  show 0 < z.re ∧ ‖z‖ < 5
  constructor
  · have h3 : -‖z - 1‖ ≤ z.re - 1 := by
      have := Complex.abs_re_le_norm (z - 1)
      have h4 := (abs_le.mp this).1
      simpa using h4
    linarith
  · have h2 : ‖z‖ ≤ ‖z - 1‖ + 1 := by
      calc ‖z‖ = ‖(z - 1) + 1‖ := by ring_nf
        _ ≤ ‖z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = ‖z - 1‖ + 1 := by simp
    linarith

lemma norm_proj2_farPos_ge_17 (n : ℕ) (j : Fin n) : 17 ≤ ‖proj2 (farPos n j)‖ := by
  have h := norm_proj2_farPos_ge n j
  linarith

lemma isOpen_convex_upperRegions (n : ℕ) (i : Fin n) :
    ∀ k : Fin (n + 1), IsOpen (upperRegions n i k) ∧ Convex ℝ (upperRegions n i k) := by
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · exact ⟨isOpen_upperLeft, convex_upperLeft⟩
  · by_cases hj : j = i
    · rw [upperRegions_succ, if_pos hj]
      exact ⟨isOpen_upperRight, convex_upperRight⟩
    · rw [upperRegions_succ, if_neg hj]
      exact ⟨Metric.isOpen_ball, convex_ball _ _⟩

lemma closedBall_subset_upperRegions (n : ℕ) (i : Fin n) :
    ∀ k : Fin (n + 1), Metric.closedBall (upperCentres n i k) (1 / 2) ⊆ upperRegions n i k := by
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · rw [upperCentres_zero, upperRegions_zero]
    exact closedBall_subset_upperLeft
  · by_cases hj : j = i
    · rw [upperCentres_succ, upperRegions_succ, if_pos hj, if_pos hj]
      exact closedBall_subset_upperRight
    · rw [upperCentres_succ, upperRegions_succ, if_neg hj, if_neg hj]
      intro z hz
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by norm_num)

/-! ### The three pairwise disjointnesses of the pieces -/

lemma disjoint_upperLeft_upperRight : Disjoint upperLeft upperRight := by
  rw [Set.disjoint_left]
  intro z hzL hzR
  rw [mem_upperLeft] at hzL
  rw [mem_upperRight] at hzR
  exact absurd hzL.1 (not_lt.mpr hzR.1.le)

lemma disjoint_upperLeft_far (n : ℕ) (j : Fin n) :
    Disjoint upperLeft (Metric.ball (proj2 (farPos n j)) 2) := by
  rw [Set.disjoint_left]
  intro z hzL hzF
  rw [Metric.mem_ball, dist_eq_norm] at hzF
  have htri : ‖proj2 (farPos n j)‖ - ‖z‖ ≤ ‖proj2 (farPos n j) - z‖ := by
    have h := norm_add_le (proj2 (farPos n j) - z) z
    rw [sub_add_cancel] at h
    linarith
  have h1 : ‖proj2 (farPos n j) - z‖ = ‖z - proj2 (farPos n j)‖ := norm_sub_rev _ _
  rw [h1] at htri
  have h2 := norm_proj2_farPos_ge_17 n j
  rw [mem_upperLeft] at hzL
  linarith [hzL.2]

lemma disjoint_upperRight_far (n : ℕ) (j : Fin n) :
    Disjoint upperRight (Metric.ball (proj2 (farPos n j)) 2) := by
  rw [Set.disjoint_left]
  intro z hzL hzF
  rw [Metric.mem_ball, dist_eq_norm] at hzF
  have htri : ‖proj2 (farPos n j)‖ - ‖z‖ ≤ ‖proj2 (farPos n j) - z‖ := by
    have h := norm_add_le (proj2 (farPos n j) - z) z
    rw [sub_add_cancel] at h
    linarith
  have h1 : ‖proj2 (farPos n j) - z‖ = ‖z - proj2 (farPos n j)‖ := norm_sub_rev _ _
  rw [h1] at htri
  have h2 := norm_proj2_farPos_ge_17 n j
  rw [mem_upperRight] at hzL
  linarith [hzL.2]

lemma disjoint_far_far {n : ℕ} {j k : Fin n} (h : j ≠ k) :
    Disjoint (Metric.ball (proj2 (farPos n j)) 2) (Metric.ball (proj2 (farPos n k)) 2) := by
  rw [Set.disjoint_left]
  intro z hzj hzk
  rw [Metric.mem_ball, dist_eq_norm] at hzj hzk
  have h4 : dist (proj2 (farPos n j)) (proj2 (farPos n k))
      ≤ ‖z - proj2 (farPos n j)‖ + ‖z - proj2 (farPos n k)‖ := by
    rw [dist_eq_norm]
    calc ‖proj2 (farPos n j) - proj2 (farPos n k)‖
        = ‖(proj2 (farPos n j) - z) + (z - proj2 (farPos n k))‖ := by ring_nf
      _ ≤ ‖proj2 (farPos n j) - z‖ + ‖z - proj2 (farPos n k)‖ := norm_add_le _ _
      _ = ‖z - proj2 (farPos n j)‖ + ‖z - proj2 (farPos n k)‖ := by rw [norm_sub_rev]
  have h5 := dist_proj2_farPos_ge (n := n) (j := j) (k := k) h
  linarith

/-- **The classification of the region family.**  A point of `upperRegions n i k` is either in the
left region (and then `k = 0`), or in the right region `upperRight` of the marked component (then
`k = i.succ`), or in the far disc of a component `j ≠ i` (then `k = j.succ`). -/
lemma mem_upperRegions_classify {n : ℕ} {i : Fin n} {k : Fin (n + 1)} {z : ℂ}
    (hz : z ∈ upperRegions n i k) :
    (k = 0 ∧ z ∈ upperLeft) ∨
      ∃ j : Fin n, k = j.succ ∧
        ((j = i ∧ z ∈ upperRight) ∨ (j ≠ i ∧ z ∈ Metric.ball (proj2 (farPos n j)) 2)) := by
  rcases Fin.eq_zero_or_eq_succ k with hk | ⟨j, rfl⟩
  · subst hk
    exact Or.inl ⟨rfl, hz⟩
  · by_cases hj : j = i
    · rw [upperRegions_succ, if_pos hj] at hz
      exact Or.inr ⟨j, rfl, Or.inl ⟨hj, hz⟩⟩
    · rw [upperRegions_succ, if_neg hj] at hz
      exact Or.inr ⟨j, rfl, Or.inr ⟨hj, hz⟩⟩

lemma pairwiseDisjoint_upperRegions (n : ℕ) (i : Fin n) :
    Pairwise fun k l : Fin (n + 1) => Disjoint (upperRegions n i k) (upperRegions n i l) := by
  intro k l hkl
  rw [Set.disjoint_left]
  intro z hzk hzl
  have hLR : ∀ {z : ℂ}, z ∈ upperLeft → z ∈ upperRight → False :=
    fun {z} h1 h2 => Set.disjoint_left.mp disjoint_upperLeft_upperRight h1 h2
  have hLF : ∀ (j : Fin n) {z : ℂ}, z ∈ upperLeft →
      z ∈ Metric.ball (proj2 (farPos n j)) 2 → False :=
    fun j {z} h1 h2 => Set.disjoint_left.mp (disjoint_upperLeft_far n j) h1 h2
  have hRF : ∀ (j : Fin n) {z : ℂ}, z ∈ upperRight →
      z ∈ Metric.ball (proj2 (farPos n j)) 2 → False :=
    fun j {z} h1 h2 => Set.disjoint_left.mp (disjoint_upperRight_far n j) h1 h2
  have hFF : ∀ {j j' : Fin n}, j ≠ j' → ∀ {z : ℂ},
      z ∈ Metric.ball (proj2 (farPos n j)) 2 →
      z ∈ Metric.ball (proj2 (farPos n j')) 2 → False :=
    fun {j j'} hjj {z} h1 h2 => Set.disjoint_left.mp (disjoint_far_far hjj) h1 h2
  rcases mem_upperRegions_classify hzk with ⟨hk0, hzL⟩ | ⟨j, hkj, hzj⟩
  · rcases mem_upperRegions_classify hzl with ⟨hl0, hzlL⟩ | ⟨j', hlj', hzj'⟩
    · exact absurd (hk0.trans hl0.symm) hkl
    · rcases hzj' with ⟨-, hzR⟩ | ⟨-, hzF⟩
      · exact hLR hzL hzR
      · exact hLF j' hzL hzF
  · rcases hzj with ⟨hji, hzR⟩ | ⟨hji, hzF⟩
    · rcases mem_upperRegions_classify hzl with ⟨hl0, hzlL⟩ | ⟨j', hlj', hzj'⟩
      · exact hLR hzlL hzR
      · rcases hzj' with ⟨hj'i, hzR'⟩ | ⟨hj'i, hzF'⟩
        · exact absurd (hkj.trans (by rw [hlj', hji, hj'i])) hkl
        · exact hRF j' hzR hzF'
    · rcases mem_upperRegions_classify hzl with ⟨hl0, hzlL⟩ | ⟨j', hlj', hzj'⟩
      · exact hLF j hzlL hzF
      · rcases hzj' with ⟨hj'i, hzR'⟩ | ⟨hj'i, hzF'⟩
        · exact hRF j hzR' hzF
        · exact hFF (fun hjj => hkl (by rw [hkj, hlj', hjj])) hzF hzF'


open scoped Manifold ContDiff Topology in
open Set Filter in
/-- **The packet rows of the saddle window, in sign-free (abstract-arc) form.**  This is
`Work.Drive.N2Lead.saddlePacketRows` with the two arc families supplied *abstractly* — `αU`, `αD` are
the anchor arcs through the `Z`-coordinate (`Z (αU w) = arcZ ηs w`, `Z (αD w) = -arcZ ηs w`) and the
pin is described by the dictionary `hpinZ` — instead of through the datum chart `D.φ D.j`.

The point is `Submission/Work/Drive/N2/NOTES_dichotomy_hspan_and_packet.md` §3: `saddlePack`'s `Z`
satisfies the *level* law `f = f p + lam0 ^ 2 * Re (Z ·) ^ 2` in both sign cases `s₁ = ±1`, but the
relation to the datum chart is `chartCplx = lam0 * Z` in the `s₁ = 1` case and
`chartCplx = -(I * lam0) * Z` in the `s₁ = -1` case.  The pin condition `|Im (Z ·) ^ 2| ≤ m` and the
level condition are *the same in both cases* (a rotation of `Z` flips both `Re` and `Im` of `Z ^ 2`
simultaneously), so the whole packet argument is sign-free once stated in terms of `Z` and the arc
points, which is what this statement does.

The five rows are the ones consumed by `Work.Drive.N2Lead.saddleWindow_of_packet_band_off` (with
`c := f p`, `lam := lam0 ^ 2`, `η := ηs`, `θ := pinTheta D Z m`); the picture is built from the polar
curve `t ↦ cE3 (r (Θ t) * exp (i Θ t))` on the marked component and the parked circles on the
others.  Compare `Work.Drive.N2Lead.saddlePacketRows` (the `chartCplx = lam0 * Z` form, PROVED), whose
proof is the template: the only changes are that `hpinZ` replaces `hZrel`, that the arc-source rows
`hαsrcU`/`hαsrcD` replace `hpinNorm` (they are what makes `pinTheta (αU w) = 1`), and that
`pin_eq_arc` is re-derived from `hpinZ` and `hlev` (`(Z x) ^ 2 = -ηs + I * Im ((Z x) ^ 2)`), with no
chart involved. -/
theorem saddlePacketRowsSplit {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f) {p : M}
    (D : Work.Drive.N2.WindowDatum f p) {Z : M → ℂ}
    {lam0 ηs δ c₀ m R : ℝ} {n : ℕ}
    (L : Work.Drive.N2C.LevelCurves f (f p - lam0 ^ 2 * ηs) n) (i : Fin n)
    {r Θ τU τL : ℝ → ℝ} {αU αD : ℝ → M}
    (hreg : ∀ x : M, f x = f p - lam0 ^ 2 * ηs → ¬ Work.Drive.Morse.IsCritical f x)
    (hlam0pos : 0 < lam0)
    (hZsm : ∀ x ∈ (D.φ D.j).source,
      ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z x)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re)
    (hpinZ : ∀ x : M, x ∈ Work.Drive.N2Lead.saddlePin D (f p - lam0 ^ 2 * ηs) m ↔
      x ∈ (D.φ D.j).source ∧ ‖Z x‖ < 8 ∧ f x = f p - lam0 ^ 2 * ηs ∧ |((Z x) ^ 2).im| ≤ m)
    (hZinj : ∀ w ∈ Set.Icc (-m) m, ∀ x ∈ (D.φ D.j).source, Z x = Z (αU w) → x = αU w)
    (hZinjD : ∀ w ∈ Set.Icc (-m) m, ∀ x ∈ (D.φ D.j).source, Z x = Z (αD w) → x = αD w)
    (hαsrcU : ∀ w ∈ Set.Icc (-m) m, αU w ∈ (D.φ D.j).source)
    (hαsrcD : ∀ w ∈ Set.Icc (-m) m, αD w ∈ (D.φ D.j).source)
    (hZU : ∀ w ∈ Set.Icc (-m) m, Z (αU w) = Work.Drive.N2Lead.arcZ ηs w)
    (hZD : ∀ w ∈ Set.Icc (-m) m, Z (αD w) = -Work.Drive.N2Lead.arcZ ηs w)
    (hηs : 0 < ηs) (hηs1 : ηs < 1 / 10) (hδ : 0 < δ) (hδ1 : δ < 1 / 10)
    (hm : 1 < m) (hm2 : m < 2) (hR : 2 ≤ R) (hR19 : R < 19)
    (hc19 : c₀ + 2 * ηs < 19 ^ 2)
    (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r) (hrpos : ∀ φ : ℝ, 0 < r φ)
    (hrper : ∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ) (hrR : ∀ φ : ℝ, r φ ≤ R)
    (hrArcU : ∀ w ∈ Set.Icc (-m) m,
      r (Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs))
        = Real.sqrt (ηs / -Real.cos (2 * (Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs)))))
    (hrArcL : ∀ w ∈ Set.Icc (-m) m,
      r (-(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs))
        = Real.sqrt (ηs / -Real.cos (2 * (-(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs)))))
    (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ) (hΘmono : StrictMono Θ)
    (hΘderiv : ∀ t : ℝ, deriv Θ t ≠ 0) (hΘper : ∀ t : ℝ, Θ (t + 1) = Θ t + 2 * Real.pi)
    (hΘU : ∀ w ∈ Set.Icc (-m) m, Θ (τU w) = Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs))
    (hΘL : ∀ w ∈ Set.Icc (-m) m, Θ (τL w) = -(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs))
    (hτU : ∀ w ∈ Set.Icc (-m) m, L.γ i (τU w) = αU w)
    (hτL : ∀ w ∈ Set.Icc (-m) m, L.γ i (τL w) = αD w)
    (hoff : ∀ t : ℝ, (∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-m) m → t ≠ τU w + k) →
      (∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-m) m → t ≠ τL w + k) → c₀ + 2 * ηs < r (Θ t) ^ 2) :
    ∃ A : M → EuclideanSpace ℝ (Fin 3),
      (∀ x : M, ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A x) ∧
      (∀ x y : M, f x = f p - lam0 ^ 2 * ηs → f y = f p - lam0 ^ 2 * ηs → A x = A y → x = y) ∧
      (∀ x : M, f x = f p - lam0 ^ 2 * ηs → ∀ v : TangentSpace (𝓡 2) x,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 →
        mfderiv (𝓡 2) (𝓡 3) A x v = 0 → v = 0) ∧
      (∀ x : M, f x = f p - lam0 ^ 2 * ηs → Work.Drive.N2Lead.pinTheta D Z m x = 1 →
        A x = Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi ηs δ (Z x))) ∧
      (∀ x : M, f x = f p - lam0 ^ 2 * ηs → Work.Drive.N2Lead.pinTheta D Z m x < 1 →
        (A x) 2 ≠ 0 ∨ c₀ + 2 * ηs < ‖A x‖ ^ 2) ∧
      (∀ t : ℝ, A (L.γ i t) =
        Work.Drive.N2.cE3 (r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))) ∧
      (∀ (j : Fin n), j ≠ i → ∀ t : ℝ, A (L.γ j t) = Work.Drive.N2Lead.farCurve n j t) := by
  classical
  -- ## the marked polar curve and the packet family of curves
  let C : ℝ → EuclideanSpace ℝ (Fin 3) :=
    fun t => Work.Drive.N2.cE3 (r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))
  obtain ⟨hCsm, hCper, hCinj, hCder, hCnorm⟩ :=
    saddleMarkedCurve (r := r) (Θ := Θ) (R := R) hr hrpos hrper hrR hΘ hΘmono hΘderiv hΘper
  let c : Fin n → ℝ → EuclideanSpace ℝ (Fin 3) :=
    fun j => if j = i then C else farCurve n j
  have hci : c i = C := by
    show (if i = i then C else farCurve n i) = C
    rw [if_pos rfl]
  have hcj : ∀ j : Fin n, j ≠ i → c j = farCurve n j := by
    intro j hj
    show (if j = i then C else farCurve n j) = farCurve n j
    rw [if_neg hj]
  have hcsm : ∀ j : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c j) := by
    intro j
    by_cases hj : j = i
    · have hji : c j = C := by
        show (if j = i then C else farCurve n j) = C
        rw [if_pos hj]
      rw [hji]; exact hCsm
    · rw [hcj j hj]; exact farCurve_contDiff n j
  have hcper : ∀ (j : Fin n) (t : ℝ), c j (t + 1) = c j t := by
    intro j t
    by_cases hj : j = i
    · have hji : c j = C := by
        show (if j = i then C else farCurve n j) = C
        rw [if_pos hj]
      rw [hji]
      show Work.Drive.N2.cE3 (r (Θ (t + 1))
          * Complex.exp (((Θ (t + 1) : ℝ) : ℂ) * Complex.I))
        = Work.Drive.N2.cE3 (r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))
      rw [hCper t]
    · rw [hcj j hj]; exact farCurve_period n j t
  have hcinj : ∀ (j k : Fin n) (s t : ℝ), c j s = c k t → j = k ∧ ∃ m : ℤ, s = t + m := by
    intro j k s t hst
    change (if j = i then C else farCurve n j) s = (if k = i then C else farCurve n k) t at hst
    by_cases hj : j = i
    · rw [if_pos hj] at hst
      by_cases hk : k = i
      · rw [if_pos hk] at hst
        exact ⟨hj.trans hk.symm, hCinj s t (Work.Drive.N2.cE3_injective hst)⟩
      · rw [if_neg hk] at hst
        exact absurd hst (marked_far_ne hCnorm hR19 s t)
    · rw [if_neg hj] at hst
      by_cases hk : k = i
      · rw [if_pos hk] at hst
        exact absurd hst.symm (marked_far_ne hCnorm hR19 t s)
      · rw [if_neg hk] at hst
        exact farCurve_inj hst
  have hcder : ∀ (j : Fin n) (t : ℝ), deriv (c j) t ≠ 0 := by
    intro j t
    by_cases hj : j = i
    · have hji : c j = C := by
        show (if j = i then C else farCurve n j) = C
        rw [if_pos hj]
      rw [hji]; exact hCder t
    · rw [hcj j hj]; exact deriv_farCurve_ne_zero n j t
  -- ## the anchor picture
  obtain ⟨A, hAsm, hAcurve, hAinj, hAimm⟩ :=
    packetPicture (f := f) (a := f p - lam0 ^ 2 * ηs) (n := n) (c := c) L hf hreg
      hcsm hcper hcinj hcder
  refine ⟨A, fun x => hAsm.contMDiffAt, hAinj, hAimm, ?_, ?_, ?_, ?_⟩
  · -- ## the pin row
    intro x hxf hθ1
    have hxsrc : x ∈ (D.φ D.j).source := by
      by_contra hx
      rw [pinTheta_apply_of_notMem D (Z := Z) (m := m) hx] at hθ1
      norm_num at hθ1
    obtain ⟨himle, _hnorm4⟩ := (pinTheta_eq_one_iff D hm2 hxsrc).mp hθ1
    have hre : ((Z x) ^ 2).re = -ηs := by
      have h := hlev x hxsrc
      rw [hxf] at h
      have h2 : lam0 ^ 2 * ((Z x) ^ 2).re = lam0 ^ 2 * (-ηs) := by linarith
      exact mul_left_cancel₀ (by positivity : (lam0 : ℝ) ^ 2 ≠ 0) h2
    have hPsi : Work.Drive.N2.saddlePsi ηs δ (Z x) = Z x :=
      Work.Drive.N2.saddlePsi_eq_self_of_re_sq_neg_eta hηs hδ (by linarith) hre
    have hwIcc : ((Z x) ^ 2).im ∈ Set.Icc (-m) m := abs_le.mp himle
    have hsq : (Z x) ^ 2 = (arcZ ηs (((Z x) ^ 2).im)) ^ 2 := by
      refine Complex.ext ?_ ?_
      · rw [hre, arcZ_sq_re]
      · rw [arcZ_sq_im]
    rw [hPsi]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with harc | harc
    · -- the upper arc
      have hy : Z (αU (((Z x) ^ 2).im)) = Z x := by
        rw [hZU _ hwIcc]; exact harc.symm
      have hxy : x = αU (((Z x) ^ 2).im) := hZinj _ hwIcc x hxsrc hy.symm
      have hval : r (Θ (τU (((Z x) ^ 2).im)))
            * Complex.exp (((Θ (τU (((Z x) ^ 2).im)) : ℝ) : ℂ) * Complex.I)
          = arcZ ηs (((Z x) ^ 2).im) := by
        rw [hΘU _ hwIcc, hrArcU _ hwIcc, arcZ]
        exact (polarArc_eq_sqrt hηs (((Z x) ^ 2).im)).1
      calc A x = A (αU (((Z x) ^ 2).im)) := congrArg A hxy
        _ = A (L.γ i (τU (((Z x) ^ 2).im))) := by rw [← hτU _ hwIcc]
        _ = c i (τU (((Z x) ^ 2).im)) := hAcurve i _
        _ = C (τU (((Z x) ^ 2).im)) := by rw [hci]
        _ = Work.Drive.N2.cE3 (arcZ ηs (((Z x) ^ 2).im)) := by
              show Work.Drive.N2.cE3 (r (Θ (τU (((Z x) ^ 2).im)))
                * Complex.exp (((Θ (τU (((Z x) ^ 2).im)) : ℝ) : ℂ) * Complex.I)) = _
              rw [hval]
        _ = Work.Drive.N2.cE3 (Z x) := congrArg Work.Drive.N2.cE3 harc.symm
    · -- the lower arc
      have hy : Z (αD (((Z x) ^ 2).im)) = Z x := by
        rw [hZD _ hwIcc]; exact harc.symm
      have hxy : x = αD (((Z x) ^ 2).im) := hZinjD _ hwIcc x hxsrc hy.symm
      have hval : r (Θ (τL (((Z x) ^ 2).im)))
            * Complex.exp (((Θ (τL (((Z x) ^ 2).im)) : ℝ) : ℂ) * Complex.I)
          = -arcZ ηs (((Z x) ^ 2).im) := by
        rw [hΘL _ hwIcc, hrArcL _ hwIcc, arcZ]
        exact (polarArc_eq_sqrt hηs (((Z x) ^ 2).im)).2.1
      calc A x = A (αD (((Z x) ^ 2).im)) := congrArg A hxy
        _ = A (L.γ i (τL (((Z x) ^ 2).im))) := by rw [← hτL _ hwIcc]
        _ = c i (τL (((Z x) ^ 2).im)) := hAcurve i _
        _ = C (τL (((Z x) ^ 2).im)) := by rw [hci]
        _ = Work.Drive.N2.cE3 (-arcZ ηs (((Z x) ^ 2).im)) := by
              show Work.Drive.N2.cE3 (r (Θ (τL (((Z x) ^ 2).im)))
                * Complex.exp (((Θ (τL (((Z x) ^ 2).im)) : ℝ) : ℂ) * Complex.I)) = _
              rw [hval]
        _ = Work.Drive.N2.cE3 (Z x) := congrArg Work.Drive.N2.cE3 harc.symm
  · -- ## the off-pin row
    intro x hxf hθlt
    obtain ⟨j, t, hxt⟩ := L.cover x hxf
    have hAx : A x = c j t := by rw [hxt]; exact hAcurve j t
    by_cases hji : j = i
    · -- the marked component: the parameter avoids the two arcs
      have hjc : c j = C := by rw [hji]; exact hci
      have hnotU : ∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-m) m → t ≠ τU w + k := by
        intro w k hw ht
        have hxarc : x = αU w := by
          rw [hxt, ht, levelCurves_gamma_add_int L j k (τU w), hji]
          exact hτU w hw
        have h1 : pinTheta D Z m x = 1 := by
          rw [hxarc]
          exact pinTheta_arcU D hηs hηs1 hm hm2 (hαsrcU w hw) (hZU w hw) hw
        exact absurd h1 (ne_of_lt hθlt)
      have hnotL : ∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-m) m → t ≠ τL w + k := by
        intro w k hw ht
        have hxarc : x = αD w := by
          rw [hxt, ht, levelCurves_gamma_add_int L j k (τL w), hji]
          exact hτL w hw
        have h1 : pinTheta D Z m x = 1 := by
          rw [hxarc]
          exact pinTheta_arcD D hηs hηs1 hm hm2 (hαsrcD w hw) (hZD w hw) hw
        exact absurd h1 (ne_of_lt hθlt)
      right
      have hbr := hoff t hnotU hnotL
      have hnorm : ‖C t‖ ^ 2 = r (Θ t) ^ 2 := by
        have h1 : ‖C t‖ = r (Θ t) := by
          show ‖Work.Drive.N2.cE3 (r (Θ t)
            * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))‖ = r (Θ t)
          rw [norm_cE3_marked, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
            Complex.norm_of_nonneg (le_of_lt (hrpos (Θ t)))]
        rw [h1]
      rw [hAx, hjc, hnorm]
      exact hbr
    · -- another component: a parked circle, whose third coordinate is `1`
      left
      rw [hAx, hcj j hji, farCurve_apply_two]
      norm_num
  · -- the marked component is drawn by the polar curve
    intro t
    have h := hAcurve i t
    rw [hci] at h
    exact h
  · -- the other components are drawn by the parked circles
    intro j hj t
    have h := hAcurve j t
    rw [hcj j hj] at h
    exact h


theorem saddleWindowCertifiedSplit {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hs1 : D.s₁ D.j = 1) (hs2 : D.s₂ D.j = -1)
    (hjunk : ∀ y : M, y ∉ (D.φ D.j).source → D.φ D.j y = 0)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {η : ℝ} (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (hsep : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η < 2 * D.ηd)
    {n : ℕ} {L : Work.Drive.N2C.LevelCurves f (f p - 3 * η / 2) n} {i : Fin n}
    {τU τL : ℝ → ℝ}
    (hτUsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τU (Set.Ioo (-3) 3))
    (hτUd : ∀ w ∈ Set.Ioo (-3) 3, deriv τU w ≠ 0)
    (hτUanti : StrictAntiOn τU (Set.Ioo (-3) 3))
    (hτUval : ∀ w ∈ Set.Ioo (-3) 3,
      L.γ i (τU w) = Work.Drive.N2Lead.arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
    (hτLsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τL (Set.Ioo (-3) 3))
    (hτLd : ∀ w ∈ Set.Ioo (-3) 3, deriv τL w ≠ 0)
    (hτLanti : StrictAntiOn τL (Set.Ioo (-3) 3))
    (hτLval : ∀ w ∈ Set.Ioo (-3) 3,
      L.γ i (τL w) = Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
    (hord : τL (99 / 50) < τL (-(99 / 50)) ∧ τL (-(99 / 50)) < τU (99 / 50) ∧
      τU (99 / 50) < τU (-(99 / 50)) ∧ τU (-(99 / 50)) < τL (99 / 50) + 1) :
    ∃ W : M → EuclideanSpace ℝ (Fin 3),
      Work.Drive.N2.GoodDrawingOn f (Set.Ioo (f p - 2 * η) (f p + 2 * η)) W ∧
      Work.Drive.N2C.IsCertifiedAt f (f p - 3 * η / 2) W ∧
      Work.Drive.N2C.IsCertifiedAt f (f p + 3 * η / 2) W := by
  classical
  -- ## §1. numeric rows
  have hρpos : 0 < D.ρ D.j := D.hρ D.j
  have hlam0pos : 0 < D.ρ D.j / 8 := div_pos hρpos (by norm_num)
  have hρc : (((D.ρ D.j / 8 : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact ne_of_gt hlam0pos
  have hlamEta : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEta D η = 3 * η / 2 :=
    Work.Drive.N2.packetEta_law D η
  have hlamEtaB : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η = 2 * η :=
    Work.Drive.N2.packetEtaB_law D η
  have hηb43 : Work.Drive.N2.packetEtaB D η = 4 * Work.Drive.N2.packetEta D η / 3 :=
    Work.Drive.N2.packetEtaB_eq D η
  have hηs_pos : 0 < Work.Drive.N2.packetEta D η := Work.Drive.N2.packetEta_pos D hη
  have hηb_pos : 0 < Work.Drive.N2.packetEtaB D η := Work.Drive.N2.packetEtaB_pos D hη
  have hηs_lt10 : Work.Drive.N2.packetEta D η < 1 / 10 := by linarith [hηb43, hsmall]
  have hηs_lt800 : Work.Drive.N2.packetEta D η < 3 / 800 := by linarith [hηb43, hsmall]
  have hηb_lt10 : Work.Drive.N2.packetEtaB D η < 1 / 10 := by linarith [hsmall]
  have hηs_lt_ηb : Work.Drive.N2.packetEta D η < Work.Drive.N2.packetEtaB D η := by
    linarith [hηb43, hηs_pos]
  have hηb_le : Work.Drive.N2.packetEtaB D η ≤ 4 * Work.Drive.N2.packetEta D η / 3 :=
    le_of_eq hηb43
  have h2ηd : 2 * η < 2 * D.ηd := by
    have h := hsep
    rw [hlamEtaB] at h
    exact h
  have hηd : η < D.ηd := by linarith
  have hRt : (2 : ℝ) ≤ 3 := by norm_num
  have hR19 : (3 : ℝ) < 19 := by norm_num
  have hR17 : (3 : ℝ) < 17 := by norm_num
  have hm1 : (1 : ℝ) < 99 / 50 := by norm_num
  have hm2 : (99 / 50 : ℝ) < 2 := by norm_num
  have hm3 : (99 / 50 : ℝ) < 3 := by norm_num
  have hδ0 : (0 : ℝ) < 1 / 11 := by norm_num
  have hδ1 : (1 / 11 : ℝ) < 1 / 10 := by norm_num
  have hδhalf : (1 / 11 : ℝ) < 1 / 2 := by norm_num
  have hc0 : 2 - 2 * (1 / 11 : ℝ) < 39 / 20 := by norm_num
  have hc0' : (39 / 20 : ℝ) < 2 := by norm_num
  have hc0m : (39 / 20 : ℝ) < 99 / 50 := by norm_num
  have hc0le : (39 / 20 : ℝ) ≤ 39 / 20 := le_rfl
  have hc0two : (39 / 20 : ℝ) ≤ 2 := by norm_num
  have hc19 : (39 / 20 : ℝ) + 2 * Work.Drive.N2.packetEta D η < 19 ^ 2 := by
    nlinarith [hηs_lt10]
  have hnum : (39 / 20 : ℝ) + 2 * Work.Drive.N2.packetEta D η
      < Real.sqrt ((Work.Drive.N2.packetEta D η) ^ 2 + (99 / 50 : ℝ) ^ 2) := by
    have h1 : (99 / 50 : ℝ)
        ≤ Real.sqrt ((Work.Drive.N2.packetEta D η) ^ 2 + (99 / 50 : ℝ) ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith)
    nlinarith [hηs_lt800]
  -- ## §2. the chart coordinate
  set Z : M → ℂ := Work.Drive.N2.cl_saddleZ D 1 with hZ
  set Zs : M → ℂ := Work.Drive.N2Lead.chartCplx D with hZs
  have hZs_apply : ∀ y : M, Zs y
      = ((D.φ D.j y 0 : ℝ) : ℂ) + ((D.φ D.j y 1 : ℝ) : ℂ) * Complex.I := by
    intro y; rw [hZs]; exact Work.Drive.N2Lead.chartCplx_apply D y
  have hZrel : ∀ y : M, Zs y = (((D.ρ D.j / 8 : ℝ)) : ℂ) * Z y := by
    intro y
    rw [hZs, hZ, Work.Drive.N2Lead.chartCplx, Work.Drive.N2.cl_saddleZ_apply,
      Work.Drive.N2Lead.cplxE2]
    field_simp
  have hZrel' : ∀ y : M, Work.Drive.N2Lead.chartCplx D y
      = (((D.ρ D.j / 8 : ℝ)) : ℂ) * Z y := by
    intro y; rw [← hZs]; exact hZrel y
  have hZsm : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z (D.φ D.j).source := by
    rw [hZ]
    exact (Work.Drive.N2.cl_scaleCLM (1 / (((D.ρ D.j / 8 : ℝ)) : ℂ))).contMDiff.comp_contMDiffOn
      (Work.Drive.N2.cl_chartZLM.contMDiff.comp_contMDiffOn (D.hφ D.j))
  have hZchart : ∀ y : M, Work.Drive.N2.chartZ (D.φ D.j) y = Zs y := by
    intro y; rw [hZs, Work.Drive.N2Lead.chartCplx_apply, Work.Drive.N2.chartZ_apply]
  have hZinjBall : Set.InjOn Z (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) := by
    rw [hZ]; exact Work.Drive.N2.cl_injOn_saddleZ D one_ne_zero
  have hZimmBall : ∀ x ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j),
      Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z x) := by
    intro x hx; rw [hZ]
    exact Work.Drive.N2.cl_injective_mfderiv_saddleZ D one_ne_zero hx
  have hlev : ∀ y ∈ (D.φ D.j).source,
      f y = f p + (D.ρ D.j / 8) ^ 2 * ((Z y) ^ 2).re := by
    intro y hy
    rw [hZ]
    exact Work.Drive.N2.cl_saddleZ_level D hs1 hs2 (by norm_num) (by norm_num) hy
  have hlevSs : ∀ y ∈ (D.φ D.j).source, f y = f p + ((Zs y) ^ 2).re := by
    intro y hy
    have h := D.hval D.j y hy
    rw [D.hxj, hs1, hs2] at h
    rw [h, hZs, Work.Drive.N2Lead.chartCplx, Work.Drive.N2Lead.cplxE2,
      Work.Drive.N2Lead.sq_re, Work.Drive.N2.chartQ]
    simp only [one_mul, neg_one_mul, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, add_zero, sub_zero]
    ring
  have hODE : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      HasDerivAt (fun σ : ℝ => D.φ D.j (D.Φ (σ, y)) 0)
        (Work.Drive.N2.chartMult (D.ρ D.j / 8) (‖D.φ D.j (D.Φ (t, y))‖ ^ 2)
          * ((1 : ℝ) * D.φ D.j (D.Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => D.φ D.j (D.Φ (σ, y)) 1)
        (Work.Drive.N2.chartMult (D.ρ D.j / 8) (‖D.φ D.j (D.Φ (t, y))‖ ^ 2)
          * ((-1 : ℝ) * D.φ D.j (D.Φ (t, y)) 1)) t := by
    intro y t hconf
    obtain ⟨h0, h1⟩ := D.hODE D.j y t hconf
    rw [hs1] at h0
    rw [hs2] at h1
    exact ⟨h0, h1⟩
  have him : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      ((Zs (D.Φ (t, y))) ^ 2).im = ((Zs y) ^ 2).im := by
    intro y t hconf
    exact Work.Drive.N2.im_sq_eq_of_flow_closedODE (D.φ D.j) Zs
      (fun m => by rw [hZs]; exact Work.Drive.N2Lead.chartCplx_apply D m) (D.ρ D.j / 8)
      hODE D.hΦ0 y t hconf
  have hpinZ : ∀ x : M,
      x ∈ Work.Drive.N2Lead.saddlePin D (f p - (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEta D η) (99 / 50) ↔
      x ∈ (D.φ D.j).source ∧ ‖Z x‖ < 8 ∧
        f x = f p - (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEta D η ∧
        |((Z x) ^ 2).im| ≤ 99 / 50 := by
    intro x
    rw [hZ]
    exact Work.Drive.N2Lead.saddlePin_eq_scaled D hlam0pos rfl hZrel'
  have hcollSrc : ∀ y : M,
      Z y ∈ Work.Drive.N2.saddleCollar (Work.Drive.N2.packetEtaB D η) (1 / 11) →
      y ∈ (D.φ D.j).source := by
    intro y hy
    by_contra hys
    have h0 : Zs y = 0 := by
      rw [hZs, Work.Drive.N2Lead.chartCplx, Work.Drive.N2Lead.cplxE2, hjunk y hys]
      simp
    have h1 : Z y = 0 := by
      have h := hZrel y
      rw [h0] at h
      have : (((D.ρ D.j / 8 : ℝ)) : ℂ) * Z y = 0 := h.symm
      exact (mul_eq_zero.mp this).resolve_left hρc
    rw [h1] at hy
    simp only [Work.Drive.N2.saddleCollar, Set.mem_setOf_eq] at hy
    have : |((0 : ℂ) ^ 2).im| = 0 := by simp
    rw [this] at hy
    linarith [hy.2.1, hδ0]
  -- ## §3. the two anchor arcs
  have harc_ball : ∀ w : ℝ, |w| ≤ 99 / 50 →
      ‖Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w‖ < 8 := by
    intro w hw
    refine Work.Drive.N2Lead.arcZ_norm_lt _ _ ?_ ?_
    · rw [abs_of_pos hηs_pos]; linarith [hηs_lt10]
    · linarith [hw, hm2]
  have hmabs : ∀ w : ℝ, w ∈ Set.Icc (-(99 / 50)) (99 / 50) → |w| ≤ 99 / 50 :=
    fun w hw => abs_le.mpr hw
  have hmIcc : ∀ w : ℝ, w ∈ Set.Icc (-(99 / 50)) (99 / 50) → w ∈ Set.Ioo (-3) 3 := by
    intro w hw; exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hmemT : ∀ w : ℝ, |w| ≤ 99 / 50 →
      Work.Drive.N2Lead.cE2
        (-((((D.ρ D.j / 8 : ℝ)) : ℂ) * Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w))
        ∈ (D.φ D.j).target := by
    intro w hw
    refine Work.Drive.N2.windowBall_subset_target D D.j ?_
    rw [Work.Drive.N2Lead.cE2_norm, norm_neg, norm_mul, Complex.norm_of_nonneg hlam0pos.le]
    nlinarith [harc_ball w hw, hρpos]
  have hZU : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
      Z (Work.Drive.N2Lead.arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
        = Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w := by
    intro w hw
    rw [hZ]
    exact Work.Drive.N2Lead.Z_arcUpPt D (harc_ball w (hmabs w hw)) hlam0pos rfl hZrel'
  have hZD : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
      Z (Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
        = -Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w := by
    intro w hw
    have hphi : D.φ D.j
        (Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
        = Work.Drive.N2Lead.cE2
          (-((((D.ρ D.j / 8 : ℝ)) : ℂ)
            * Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w)) :=
      (D.φ D.j).right_inv (hmemT w (hmabs w hw))
    have hchart : Work.Drive.N2Lead.chartCplx D
        (Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
        = -((((D.ρ D.j / 8 : ℝ)) : ℂ)
            * Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w) := by
      rw [Work.Drive.N2Lead.chartCplx, hphi, Work.Drive.N2Lead.cplxE2_cE2]
    have h := hZrel' (Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
    rw [hchart] at h
    have h2 : (((D.ρ D.j / 8 : ℝ)) : ℂ) * Z
        (Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
        = (((D.ρ D.j / 8 : ℝ)) : ℂ)
          * (-Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w) := by
      rw [← h]; ring
    exact mul_left_cancel₀ hρc h2
  have hαsrcU : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
      Work.Drive.N2Lead.arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w
        ∈ (D.φ D.j).source := by
    intro w hw
    exact Work.Drive.N2Lead.arcUpPt_mem_source D (harc_ball w (hmabs w hw)) rfl
  have hαsrcD : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
      Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w
        ∈ (D.φ D.j).source := by
    intro w hw
    exact (D.φ D.j).map_target (hmemT w (hmabs w hw))
  have hτU' : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
      L.γ i (τU w)
        = Work.Drive.N2Lead.arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w :=
    fun w hw => hτUval w (hmIcc w hw)
  have hτL' : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
      L.γ i (τL w)
        = Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w :=
    fun w hw => hτLval w (hmIcc w hw)
  -- ## §4. the angle function and the profile
  obtain ⟨Θ, hΘsm, hΘmono, hΘderiv, hΘper, hΘU, hΘL⟩ :=
    Work.Drive.N2Lead.saddleAngleFunction hηs_pos (by norm_num) hm3
      hτUsm hτUd hτUanti hτLsm hτLd hτLanti hord
  obtain ⟨r, hr, hrpos, hrper, hrpi, hrR, hrArcU, hrArcL, hrbridge, hrev, hmono⟩ :=
    saddleProfileRowsPi hηs_pos hηs_lt10 hm1 hm2 hRt
  have hoff : ∀ t : ℝ,
      (∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-(99 / 50)) (99 / 50) → t ≠ τU w + k) →
      (∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-(99 / 50)) (99 / 50) → t ≠ τL w + k) →
      (39 / 20 : ℝ) + 2 * Work.Drive.N2.packetEta D η < r (Θ t) ^ 2 :=
    Work.Drive.N2Lead.saddleBridgeRow hηs_pos (by norm_num) hΘmono hΘper hΘU hΘL hrbridge hnum
  have hZsm' : ∀ x ∈ (D.φ D.j).source,
      ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z x :=
    fun x hx => hZsm.contMDiffAt ((D.φ D.j).open_source.mem_nhds hx)
  have hreg : ∀ x : M, f x = f p - (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEta D η →
      ¬ Work.Drive.Morse.IsCritical f x := by
    intro x hx hcrit
    obtain ⟨i, hi⟩ := D.hcover x hcrit
    rcases eq_or_ne i D.j with h | h
    · rw [← hi, h, D.hxj, hlamEta] at hx
      linarith
    · have hsep_i := D.hsep i D.j h
      rw [hi, D.hxj, hx, hlamEta] at hsep_i
      have habs : |f p - 3 * η / 2 - f p| = 3 * η / 2 := by
        rw [show f p - 3 * η / 2 - f p = -(3 * η / 2) by ring, abs_neg,
          abs_of_pos (by linarith [hη] : (0 : ℝ) < 3 * η / 2)]
      rw [habs] at hsep_i
      linarith [h2ηd]
  have hZinj_of : ∀ {x y : M}, x ∈ (D.φ D.j).source → y ∈ (D.φ D.j).source →
      Z x = Z y → x = y := by
    intro x y hx hy hxy
    have h1 : Work.Drive.N2Lead.chartCplx D x = Work.Drive.N2Lead.chartCplx D y := by
      have h := hZrel' x
      rw [hxy] at h
      exact h.trans (hZrel' y).symm
    have h2 : Work.Drive.N2.chartZ (D.φ D.j) x = Work.Drive.N2.chartZ (D.φ D.j) y := by
      rw [hZchart x, hZchart y]; exact h1
    have h3 : D.φ D.j x = D.φ D.j y := by
      have := congrArg Work.Drive.N2Lead.cplxVec h2
      rwa [Work.Drive.N2Lead.cplxVec_chartZ, Work.Drive.N2Lead.cplxVec_chartZ] at this
    exact (D.φ D.j).injOn hx hy h3
  have hZinjU : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50), ∀ x ∈ (D.φ D.j).source,
      Z x = Z (Work.Drive.N2Lead.arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w) →
      x = Work.Drive.N2Lead.arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w :=
    fun w hw x hx hZx => hZinj_of hx (hαsrcU w hw) hZx
  have hZinjD : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50), ∀ x ∈ (D.φ D.j).source,
      Z x = Z (Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w) →
      x = Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w :=
    fun w hw x hx hZx => hZinj_of hx (hαsrcD w hw) hZx
  -- ## §5. the packet picture
  let L' : Work.Drive.N2C.LevelCurves f
      (f p - (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEta D η) n :=
    { L with
      val := fun j x => by rw [hlamEta]; exact L.val j x
      cover := fun x hx => L.cover x (by rw [hlamEta] at hx; exact hx) }
  have hLgamma : ∀ (j : Fin n) (t : ℝ), L'.γ j t = L.γ j t := fun j t => rfl
  obtain ⟨A, hAsm, hAinj, hAimm, hApin, hAoff, hAcurve_i, hAcurve_j⟩ :=
    saddlePacketRowsSplit (lam0 := D.ρ D.j / 8) (ηs := Work.Drive.N2.packetEta D η)
      (δ := 1 / 11) (c₀ := 39 / 20) (m := 99 / 50) (R := 3) (n := n)
      hf D L' i (r := r) (Θ := Θ) (τU := τU) (τL := τL)
      (αU := fun w => Work.Drive.N2Lead.arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
      (αD := fun w => Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
      hreg hlam0pos hZsm' hlev hpinZ
      hZinjU hZinjD
      hαsrcU hαsrcD hZU hZD hηs_pos hηs_lt10 hδ0 hδ1 hm1 hm2 hRt hR19 hc19
      hr hrpos hrper hrR hrArcU hrArcL hΘsm hΘmono hΘderiv hΘper hΘU hΘL hτU' hτL' hoff
  -- ## §6. the pin function with a smooth cutoff
  obtain ⟨χf, hχ0, hχ1, hχ01⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓡 2) (n := (⊤ : ℕ∞))
      (s := (D.φ D.j).sourceᶜ) (t := closure (D.C D.j))
      (D.φ D.j).open_source.isClosed_compl isClosed_closure (by
        rw [Set.disjoint_left]
        intro y hy hyc
        exact hy ((D.hCcl D.j).2 hyc))
  have hχsm : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : M => χf x) :=
    χf.contMDiff
  have hχc : Continuous (fun x : M => χf x) := hχsm.continuous
  have hχ1' : ∀ x ∈ closure (D.C D.j), χf x = 1 := by
    intro x hx
    have h : ∀ᶠ y in 𝓝 x, χf y = 1 := eventually_nhdsSet_iff_forall.mp hχ1 x hx
    exact (isClosed_eq hχc continuous_const).mem_of_tendsto tendsto_id (by simpa using h)
  have hχ0' : ∀ x ∉ (D.φ D.j).source, χf x = 0 := by
    intro x hx
    have h : ∀ᶠ y in 𝓝 x, χf y = 0 := eventually_nhdsSet_iff_forall.mp hχ0 x hx
    exact (isClosed_eq hχc continuous_const).mem_of_tendsto tendsto_id (by simpa using h)
  have hχsrc : ∀ x : M, χf x = 1 → x ∈ (D.φ D.j).source := by
    intro x hx
    by_contra hc
    rw [hχ0' x hc] at hx
    exact one_ne_zero hx.symm
  set θ : M → ℝ := fun y => χf y
      * Real.smoothTransition ((4 - (((Z y) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2))
      * Work.Drive.N2Lead.pinChi ((Z y).re ^ 2 + (Z y).im ^ 2) with hθdef
  have hnormZ : ∀ x : M, (Z x).re ^ 2 + (Z x).im ^ 2 = ‖Z x‖ ^ 2 := by
    intro x
    rw [show (Z x).re ^ 2 + (Z x).im ^ 2 = Complex.normSq (Z x) by
          rw [Complex.normSq_apply]; ring]
    exact (Complex.sq_norm (Z x)).symm
  have hθ01 : ∀ x : M, 0 ≤ θ x ∧ θ x ≤ 1 := by
    intro x
    have h1 : 0 ≤ χf x := (hχ01 x).1
    have h1' : χf x ≤ 1 := (hχ01 x).2
    have h2 : 0 ≤ Real.smoothTransition
        ((4 - (((Z x) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2)) := Real.smoothTransition.nonneg _
    have h2' : Real.smoothTransition
        ((4 - (((Z x) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2)) ≤ 1 :=
      Real.smoothTransition.le_one _
    have h3 : 0 ≤ Work.Drive.N2Lead.pinChi ((Z x).re ^ 2 + (Z x).im ^ 2) :=
      Work.Drive.N2Lead.pinChi_nonneg _
    have h3' : Work.Drive.N2Lead.pinChi ((Z x).re ^ 2 + (Z x).im ^ 2) ≤ 1 :=
      Work.Drive.N2Lead.pinChi_le_one _
    rw [hθdef]
    constructor
    · exact mul_nonneg (mul_nonneg h1 h2) h3
    · calc χf x * Real.smoothTransition ((4 - (((Z x) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2))
            * Work.Drive.N2Lead.pinChi ((Z x).re ^ 2 + (Z x).im ^ 2)
          ≤ 1 * 1 * 1 :=
            mul_le_mul (mul_le_mul h1' h2' h2 (by norm_num)) h3' h3 (by norm_num)
        _ = 1 := by norm_num
  have hpin_of_θ_one : ∀ x : M, θ x = 1 → Work.Drive.N2Lead.pinTheta D Z (99 / 50) x = 1 := by
    intro x hx
    have hA_nn : 0 ≤ χf x := (hχ01 x).1
    have hA_le : χf x ≤ 1 := (hχ01 x).2
    have hB_nn : 0 ≤ Real.smoothTransition
        ((4 - (((Z x) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2)) := Real.smoothTransition.nonneg _
    have hB_le : Real.smoothTransition
        ((4 - (((Z x) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2)) ≤ 1 :=
      Real.smoothTransition.le_one _
    have hC_nn : 0 ≤ Work.Drive.N2Lead.pinChi ((Z x).re ^ 2 + (Z x).im ^ 2) :=
      Work.Drive.N2Lead.pinChi_nonneg _
    have hC_le : Work.Drive.N2Lead.pinChi ((Z x).re ^ 2 + (Z x).im ^ 2) ≤ 1 :=
      Work.Drive.N2Lead.pinChi_le_one _
    have hprod : χf x * Real.smoothTransition ((4 - (((Z x) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2))
        * Work.Drive.N2Lead.pinChi ((Z x).re ^ 2 + (Z x).im ^ 2) = 1 := by
      simpa only [hθdef] using hx
    have hA : χf x = 1 := by
      by_contra hc
      have hlt : χf x < 1 := lt_of_le_of_ne hA_le hc
      have hle : χf x * Real.smoothTransition ((4 - (((Z x) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2))
          * Work.Drive.N2Lead.pinChi ((Z x).re ^ 2 + (Z x).im ^ 2) ≤ χf x := by
        calc χf x * Real.smoothTransition ((4 - (((Z x) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2))
              * Work.Drive.N2Lead.pinChi ((Z x).re ^ 2 + (Z x).im ^ 2)
            ≤ χf x * Real.smoothTransition ((4 - (((Z x) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2))
              * 1 := mul_le_mul_of_nonneg_left hC_le (mul_nonneg hA_nn hB_nn)
          _ = χf x * Real.smoothTransition ((4 - (((Z x) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2)) :=
              mul_one _
          _ ≤ χf x * 1 := mul_le_mul_of_nonneg_left hB_le hA_nn
          _ = χf x := mul_one _
      rw [hprod] at hle
      linarith
    have hB : Real.smoothTransition ((4 - (((Z x) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2)) = 1 := by
      have hprod' : 1 * Real.smoothTransition ((4 - (((Z x) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2))
          * Work.Drive.N2Lead.pinChi ((Z x).re ^ 2 + (Z x).im ^ 2) = 1 := by
        simpa only [hA] using hprod
      by_contra hc
      have hlt : Real.smoothTransition
          ((4 - (((Z x) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2)) < 1 :=
        lt_of_le_of_ne hB_le hc
      have hle : 1 * Real.smoothTransition ((4 - (((Z x) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2))
          * Work.Drive.N2Lead.pinChi ((Z x).re ^ 2 + (Z x).im ^ 2)
          ≤ 1 * Real.smoothTransition ((4 - (((Z x) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2)) * 1 :=
        mul_le_mul_of_nonneg_left hC_le (by rw [one_mul]; exact hB_nn)
      rw [hprod'] at hle
      simp only [one_mul, mul_one] at hle
      linarith
    have hC : Work.Drive.N2Lead.pinChi ((Z x).re ^ 2 + (Z x).im ^ 2) = 1 := by
      have hprod'' : 1 * 1 * Work.Drive.N2Lead.pinChi ((Z x).re ^ 2 + (Z x).im ^ 2) = 1 := by
        simpa only [hA, hB] using hprod
      simpa using hprod''
    have hsrc : x ∈ (D.φ D.j).source := hχsrc x hA
    rw [Work.Drive.N2Lead.pinTheta_eq_one_iff D (by norm_num) hsrc]
    refine ⟨?_, ?_⟩
    · have hle : 1 ≤ (4 - (((Z x) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2) := by
        by_contra hc
        push_neg at hc
        exact absurd hB (ne_of_lt (Real.smoothTransition.lt_one_of_lt_one hc))
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4 - (99 / 50) ^ 2)] at hle
      have hw2 : ((Z x) ^ 2).im ^ 2 ≤ (99 / 50) ^ 2 := by linarith
      have h1 : |((Z x) ^ 2).im| ≤ |(99 / 50 : ℝ)| := sq_le_sq.mp hw2
      rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 99 / 50)] at h1
    · rw [← hnormZ x]
      exact (Work.Drive.N2Lead.pinChi_eq_one_iff _).mp hC
  have hθ_one_of_pin : ∀ x : M, Work.Drive.N2Lead.pinTheta D Z (99 / 50) x = 1 → θ x = 1 := by
    intro x hx
    have hsrc : x ∈ (D.φ D.j).source := by
      by_contra hc
      rw [Work.Drive.N2Lead.pinTheta_apply_of_notMem D (Z := Z) (m := (99 / 50 : ℝ)) hc] at hx
      norm_num at hx
    obtain ⟨himle, hnorm4⟩ := (Work.Drive.N2Lead.pinTheta_eq_one_iff D (by norm_num) hsrc).mp hx
    have hZl : ‖Z x‖ ≤ 2 := by nlinarith [norm_nonneg (Z x)]
    have hnorm_eq : ‖D.φ D.j x‖ = (D.ρ D.j / 8) * ‖Z x‖ := by
      rw [← Work.Drive.N2Lead.norm_chartCplx D x, ← hZs]
      rw [hZrel x, norm_mul, Complex.norm_of_nonneg hlam0pos.le]
    have hmem : x ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) := by
      refine ⟨hsrc, ?_⟩
      rw [hnorm_eq]
      nlinarith [hZl, hlam0pos]
    have hχ1x : χf x = 1 := hχ1' x (subset_closure (D.hCop D.j hmem))
    have hw2 : ((Z x) ^ 2).im ^ 2 ≤ (99 / 50) ^ 2 := by
      have h2 := abs_le.mp himle
      nlinarith [h2.1, h2.2]
    have hst : 1 ≤ (4 - (((Z x) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2) := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4 - (99 / 50) ^ 2)]
      linarith
    have hST1 : Real.smoothTransition ((4 - (((Z x) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2)) = 1 :=
      Real.smoothTransition.one_of_one_le hst
    have hC1 : Work.Drive.N2Lead.pinChi ((Z x).re ^ 2 + (Z x).im ^ 2) = 1 := by
      rw [Work.Drive.N2Lead.pinChi_eq_one_iff, hnormZ]
      exact hnorm4
    simp only [hθdef]
    rw [hχ1x, hST1, hC1]
    norm_num
  have hθsm : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) θ := by
    intro x
    by_cases hx : x ∈ (D.φ D.j).source
    · have hZat : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z x := hZsm' x hx
      have hsq : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : M => (Z y) ^ 2) x :=
        ((ContDiff.pow contDiff_id 2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun z : ℂ => z ^ 2)).contMDiff.contMDiffAt).comp x hZat
      have him : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : M => ((Z y) ^ 2).im) x :=
        Complex.imCLM.contMDiff.contMDiffAt.comp x hsq
      have hre : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : M => (Z y).re) x :=
        Complex.reCLM.contMDiff.contMDiffAt.comp x hZat
      have him' : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : M => (Z y).im) x :=
        Complex.imCLM.contMDiff.contMDiffAt.comp x hZat
      have hnum : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : M => (4 - (((Z y) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2)) x :=
        (contMDiffAt_const.sub (him.pow 2)).div_const _
      have hst : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : M => Real.smoothTransition
            ((4 - (((Z y) ^ 2).im) ^ 2) / (4 - (99 / 50) ^ 2))) x :=
        (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).contMDiff.contMDiffAt.comp x hnum
      have hpoly : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : M => (Z y).re ^ 2 + (Z y).im ^ 2) x := (hre.pow 2).add (him'.pow 2)
      have hchi : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : M => Work.Drive.N2Lead.pinChi ((Z y).re ^ 2 + (Z y).im ^ 2)) x :=
        Work.Drive.N2Lead.pinChi_contDiff.contMDiff.contMDiffAt.comp x hpoly
      have hχat : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : M => χf y) x :=
        hχsm.contMDiffAt
      rw [hθdef]
      exact (hχat.mul hst).mul hchi
    · have h0 : ∀ᶠ y in 𝓝 x, χf y = 0 := eventually_nhdsSet_iff_forall.mp hχ0 x hx
      have hev : θ =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ)) := by
        rw [hθdef]
        filter_upwards [h0] with y hy
        rw [hy]; ring
      exact hev.contMDiffAt_iff.mpr contMDiffAt_const
  -- ## §7. the flow rows of the engine
  set U : Set M := Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) with hUdef
  set a0 : ℝ := f p - (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEta D η with ha0def
  set foot : M → M := Work.Drive.N2.footMap D.Φ f a0 with hfootdef
  set band : Set ℝ := Set.Ioo (f p - (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η)
    (f p + (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η) with hbanddef
  obtain ⟨hflow1, hflow2, hflow3, hflow4, hflow5, hflow6, hflow7⟩ :=
    Work.Drive.N2Lead.saddleFlowRowsWide D (by rw [hs1, hs2]; norm_num)
      (Zs := Zs) (Z := Z) (lam0 := D.ρ D.j / 8) (ηs := Work.Drive.N2.packetEta D η)
      (ηb := Work.Drive.N2.packetEtaB D η) (δ := 1 / 11) (c₀ := 39 / 20)
      hlam0pos rfl hZrel hZs_apply hZsm hlev hlevSs hODE him
      hηs_pos hηs_lt10 hδ0 hδ1 hηs_lt_ηb hηb_lt10 hc0 hc0' hc0m hsep hcollSrc
  -- ## §8. the engine
  have hU : IsOpen U := by
    rw [hUdef, show Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)
        = (D.φ D.j).source ∩ (D.φ D.j) ⁻¹' Metric.ball 0 (D.ρ D.j) from ?_]
    · exact (D.φ D.j).continuousOn.isOpen_inter_preimage (D.φ D.j).open_source Metric.isOpen_ball
    · ext y; simp [Work.Drive.N2.modelBall, Metric.mem_ball, dist_eq_norm]
  have hZsmU : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z U :=
    hZsm.mono (fun y hy => by rw [hUdef] at hy; exact hy.1)
  have hZinjU : Set.InjOn Z U := hZinjBall
  have hZimmU : ∀ x ∈ U, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z x) := hZimmBall
  have hlevU : ∀ x ∈ U, f x = f p + (D.ρ D.j / 8) ^ 2 * ((Z x) ^ 2).re :=
    fun x hx => hlev x (by rw [hUdef] at hx; exact hx.1)
  obtain ⟨hfootsm, hfootinj, hfootimm⟩ :=
    Work.Drive.N2.footMap_rows_noLaw hf D.hΦsm D.hΦ0 D.hΦcomp a0
  have hApin_e : ∀ x : M, f x = a0 → θ x = 1 →
      A x = Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi (Work.Drive.N2.packetEta D η) (1 / 11) (Z x)) :=
    fun x hx hθ => hApin x hx (hpin_of_θ_one x hθ)
  have hAoff_e : ∀ x : M, f x = a0 → θ x < 1 →
      (A x) 2 ≠ 0 ∨ (39 / 20 : ℝ) + 2 * Work.Drive.N2.packetEta D η < ‖A x‖ ^ 2 := by
    intro x hx hθ
    by_cases hp : Work.Drive.N2Lead.pinTheta D Z (99 / 50) x = 1
    · exact absurd (hθ_one_of_pin x hp) (ne_of_lt hθ)
    · exact hAoff x hx (lt_of_le_of_ne
        (Work.Drive.N2Lead.pinTheta_mem_Icc (Z := Z) (m := (99 / 50 : ℝ)) D x).2 hp)
  have hfootFrint_e : ∀ x : M, x ∈ frontier (Work.Drive.N2.saddleRegion U Z (39 / 20)) →
      f x ∈ band → foot x ∈ interior (θ ⁻¹' {1}) := by
    intro x hxfr hxband
    refine interior_mono ?_ (hflow6 x hxfr hxband)
    intro y hy
    exact hθ_one_of_pin y hy
  have hbig_e : ∀ x : M, x ∉ Work.Drive.N2.saddleRegion U Z (39 / 20) → f x ∈ band →
      θ (foot x) = 1 → (39 / 20 : ℝ) ≤ |((Z (foot x)) ^ 2).im| :=
    fun x h1 h2 h3 => hflow5 x h1 h2 (hpin_of_θ_one (foot x) h3)
  have hgd := Work.Drive.N2Lead.saddleWindow_of_packet_band_off
    (c := f p) (η := Work.Drive.N2.packetEta D η) (δ := 1 / 11) (c₀ := 39 / 20)
    (lam := (D.ρ D.j / 8) ^ 2) (ηb := Work.Drive.N2.packetEtaB D η)
    hηs_pos hηs_lt10 hδ0 hδ1 (by positivity) hc0 hc0' (le_of_lt hηs_lt_ηb) hηb_le
    hU hf hZsmU hZinjU hZimmU hlevU (foot := foot)
    (fun x => hfootsm.contMDiffAt) hfootinj hfootimm hflow1 hflow2 hθsm hθ01
    (A := A) hAsm hAinj hAimm hApin_e hAoff_e hflow3 hflow4 hfootFrint_e hflow7 hbig_e
  set W : M → EuclideanSpace ℝ (Fin 3) := fun x =>
    if x ∈ Work.Drive.N2.saddleRegion U Z (39 / 20)
    then Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi (Work.Drive.N2.packetEta D η) (1 / 11) (Z x))
    else A (foot x) with hWdef
  have hgdW : Work.Drive.N2.GoodDrawingOn f (Set.Ioo (f p - 2 * η) (f p + 2 * η)) W := by
    rw [hWdef]
    rw [show Set.Ioo (f p - 2 * η) (f p + 2 * η)
        = Set.Ioo (f p - (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η)
            (f p + (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η) from by rw [hlamEtaB]]
    exact hgd
  -- ## §9. the lower certificate
  have hreg3 : ∀ x : M, f x = f p - 3 * η / 2 → ¬ Work.Drive.Morse.IsCritical f x :=
    fun x hx => hreg x (by rw [ha0def, hlamEta]; exact hx)
  have hAnchInj : ∀ x y : M, f x = f p - 3 * η / 2 → f y = f p - 3 * η / 2 →
      A x = A y → x = y :=
    fun x y hx hy h => hAinj x y (by rw [ha0def, hlamEta]; exact hx)
      (by rw [ha0def, hlamEta]; exact hy) h
  have hAnchImm : ∀ x : M, f x = f p - 3 * η / 2 → ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) A x v = 0 → v = 0 :=
    fun x hx v hv hvA => hAimm x (by rw [ha0def, hlamEta]; exact hx) v hv hvA
  have hAcurveL : ∀ t : ℝ, A (L.γ i t)
      = Work.Drive.N2.cE3 (r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)) :=
    fun t => by rw [← hLgamma i t]; exact hAcurve_i t
  have hAcurveL_j : ∀ (j : Fin n), j ≠ i → ∀ t : ℝ,
      A (L.γ j t) = Work.Drive.N2Lead.farCurve n j t :=
    fun j hj t => by rw [← hLgamma j t]; exact hAcurve_j j hj t
  have hcertLowA : Work.Drive.N2C.IsCertifiedAt f (f p - 3 * η / 2) A :=
    Work.Drive.N2Lead.saddleLowerCertifiedFleet L hf hreg3 hAsm hAnchInj hAnchImm hAcurveL hAcurveL_j
      hr hrpos hrper hrR hR17 hΘsm hΘmono hΘderiv hΘper
  have hAW : ∀ y : M, f y = f p - 3 * η / 2 → A y = W y := by
    intro y hy
    have hyv : f y = a0 := by rw [ha0def, hlamEta]; exact hy
    by_cases hyr : y ∈ Work.Drive.N2.saddleRegion U Z (39 / 20)
    · simp only [hWdef, if_pos hyr]
      exact (hApin y hyv (Work.Drive.N2Lead.pinTheta_anchor_region (c := f p)
        (lam := (D.ρ D.j / 8) ^ 2) (η := Work.Drive.N2.packetEta D η) (c₀ := 39 / 20)
        D hlevU (by positivity) hηs_pos hηs_lt10 hc0le hyr.1 hyr.2 hyv))
    · simp only [hWdef, if_neg hyr]
      rw [show foot y = y from Work.Drive.N2Lead.footMap_eq_self_of_eq D.hΦ0 hyv]
  have hWlower : Work.Drive.N2C.IsCertifiedAt f (f p - 3 * η / 2) W :=
    Work.Drive.N2Lead.isCertifiedAt_of_eqOn_level
      (fun y hy => hAW y hy) hcertLowA
  -- ## §10. the upper certificate
  have hregU : ∀ x : M, f x = f p + 3 * η / 2 → ¬ Work.Drive.Morse.IsCritical f x := by
    intro x hx hcrit
    obtain ⟨i', hi⟩ := D.hcover x hcrit
    rcases eq_or_ne i' D.j with h | h
    · rw [← hi, h, D.hxj] at hx
      linarith
    · have hsep_i := D.hsep i' D.j h
      rw [hi, D.hxj, hx] at hsep_i
      have habs : |f p + 3 * η / 2 - f p| = 3 * η / 2 := by
        rw [show f p + 3 * η / 2 - f p = 3 * η / 2 by ring,
          abs_of_pos (by linarith [hη] : (0 : ℝ) < 3 * η / 2)]
      rw [habs] at hsep_i
      linarith [h2ηd]
  have hu_band : f p + 3 * η / 2 ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) :=
    ⟨by linarith [hη], by linarith [hη]⟩
  have hisoU : Work.Drive.N2C.IsLevelIsotopy f (f p + 3 * η / 2) (fun _ : ℝ => W) := by
    refine ⟨?_, ?_, ?_⟩
    · intro s y hy
      exact ((hgdW.1 y (by rw [hy]; exact hu_band)).comp (s, y)
        (contMDiffAt_snd : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 2)
          ((⊤ : ℕ∞) : WithTop ℕ∞) Prod.snd (s, y)))
    · intro s x y hx hy h
      exact hgdW.2.2 x y (by rw [hx]; exact hu_band) (by rw [hy]; exact hu_band)
        (by rw [hx, hy]) (by simpa using h)
    · intro s y hy v hvf hvW
      exact hgdW.2.1 y (by rw [hy]; exact hu_band) v hvf hvW
  -- the two rows of the rate bricks
  have hC₀two : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ (2 : ℝ) := by
    intro x
    exact Work.N2Lead.absDerivSmoothTransitionLeTwo x
  have hsmallU : 8 * (2 : ℝ) * Work.Drive.N2.packetEta D η ≤ (1 / 11 : ℝ) := by
    linarith [hηs_lt800]
  have hlampos2 : 0 < (D.ρ D.j / 8) ^ 2 := by positivity
  have hcurve : ∀ (j : Fin n) (t : ℝ), A (L.γ j t) =
      (if j = i then Work.Drive.N2.cE3 (r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))
        else Work.Drive.N2Lead.farCurve n j t) := by
    intro j t
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl]
      exact hAcurveL t
    · rw [if_neg hj]
      exact hAcurveL_j j hj t
  have hZu : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
      Z (L.γ i (τU w)) = Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w :=
    fun w hw => by rw [hτU' w hw]; exact hZU w hw
  have hZdU : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
      Z (L.γ i (τL w)) = -Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w :=
    fun w hw => by rw [hτL' w hw]; exact hZD w hw
  have hau : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
      A (L.γ i (τU w))
        = Work.Drive.N2.cE3 (Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w) := by
    intro w hw
    rw [hAcurveL (τU w), hΘU w hw, hrArcU w hw]
    exact congrArg Work.Drive.N2.cE3
      (Work.Drive.N2Lead.polarArc_eq_sqrt (ηs := Work.Drive.N2.packetEta D η) hηs_pos w).1
  have hal : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
      A (L.γ i (τL w))
        = Work.Drive.N2.cE3 (-Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w) := by
    intro w hw
    rw [hAcurveL (τL w), hΘL w hw, hrArcL w hw]
    exact congrArg Work.Drive.N2.cE3
      (Work.Drive.N2Lead.polarArc_eq_sqrt (ηs := Work.Drive.N2.packetEta D η) hηs_pos w).2.1
  have hΘu : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
      Θ (τU w) = Real.pi / 2 - (1 / 2) * Real.arctan (w / Work.Drive.N2.packetEta D η) :=
    fun w hw => hΘU w hw
  have hΘl : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
      Θ (τL w) = -(Real.pi / 2) - (1 / 2) * Real.arctan (w / Work.Drive.N2.packetEta D η) :=
    fun w hw => hΘL w hw
  have hτu : ∀ w ∈ Set.Ioo (-(99 / 50)) (99 / 50),
      DifferentiableAt ℝ τU w ∧ deriv τU w ≠ 0 := by
    intro w hw
    have hw3 : w ∈ Set.Ioo (-3) 3 := ⟨by linarith [hw.1], by linarith [hw.2]⟩
    exact ⟨(hτUsm.contDiffAt (isOpen_Ioo.mem_nhds hw3)).differentiableAt (by simp),
      hτUd w hw3⟩
  have hτl : ∀ w ∈ Set.Ioo (-(99 / 50)) (99 / 50),
      DifferentiableAt ℝ τL w ∧ deriv τL w ≠ 0 := by
    intro w hw
    have hw3 : w ∈ Set.Ioo (-3) 3 := ⟨by linarith [hw.1], by linarith [hw.2]⟩
    exact ⟨(hτLsm.contDiffAt (isOpen_Ioo.mem_nhds hw3)).differentiableAt (by simp),
      hτLd w hw3⟩
  have hloU : ∀ φ ∈ Set.Icc (0 : ℝ)
      (Work.Drive.N2Lead.mobiusPhiE (Work.Drive.N2.packetEta D η) (99 / 50)),
      Real.sqrt ((Work.Drive.N2.packetEta D η) ^ 2 + (99 / 50) ^ 2) ≤ r φ ^ 2 := by
    intro φ hφ
    refine hrbridge φ 0 ?_
    rw [Int.cast_zero, zero_mul, sub_zero, abs_of_nonneg hφ.1]
    exact hφ.2
  have hfront : ∀ x : M, x ∈ frontier (Work.Drive.N2.saddleRegion U Z (39 / 20)) →
      f x ∈ band →
      (fun y : M => Work.Drive.N2.cE3
          (Work.Drive.N2.saddlePsi (Work.Drive.N2.packetEta D η) (1 / 11) (Z y)))
        =ᶠ[𝓝 x] (fun y : M => A (foot y)) := by
    intro x hxfr hxA
    have hfootV : ∀ᶠ y in 𝓝 x, foot y ∈ interior (θ ⁻¹' {1}) :=
      ((hfootsm x).continuousAt).preimage_mem_nhds
        (isOpen_interior.mem_nhds (hfootFrint_e x hxfr hxA))
    have hband' : ∀ᶠ y in 𝓝 x, f y ∈ band :=
      hf.continuous.continuousAt (isOpen_Ioo.mem_nhds hxA)
    filter_upwards [hband', hfootV, hflow7 x hxfr hxA, hflow4 x hxfr hxA]
      with y hyb hθy hlandy hcol
    have hθy1 : θ (foot y) = 1 := by
      have h1 : foot y ∈ θ ⁻¹' {1} := interior_subset hθy
      simpa using h1
    have hcoly : Z y ∈ Work.Drive.N2.saddleCollar (Work.Drive.N2.packetEtaB D η) (1 / 11) :=
      hcol hyb
    have hpt : A (foot y) = Work.Drive.N2.cE3
        (Work.Drive.N2.saddlePsi (Work.Drive.N2.packetEta D η) (1 / 11) (Z (foot y))) :=
      hApin_e (foot y) hlandy hθy1
    have hseamy : Z (foot y)
        = Work.Drive.N2.saddlePsi (Work.Drive.N2.packetEta D η) (1 / 11) (Z y) :=
      hflow3 y hyb hcoly
    have hidem := Work.Drive.N2Lead.saddlePsi_idempotent_of_mem_collarWide hηs_pos hηs_lt10
      (le_of_lt hηs_lt_ηb) hδ0 hδ1 hcoly.1 hcoly.2.1 hcoly.2.2
    show Work.Drive.N2.cE3
        (Work.Drive.N2.saddlePsi (Work.Drive.N2.packetEta D η) (1 / 11) (Z y)) = A (foot y)
    rw [hpt, hseamy, hidem]
  have hregU' : ∀ x : M, f x = f p + (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEta D η →
      ¬ Work.Drive.Morse.IsCritical f x :=
    fun x hx => hregU x (by rw [← hlamEta]; exact hx)
  have hWu : Work.Drive.N2C.IsCertifiedAt f
      (f p + (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEta D η) W :=
    Work.Drive.N2Lead.UpCS.isCertifiedAt_upper_saddleWindow
      (c := f p) (η := Work.Drive.N2.packetEta D η) (δ := 1 / 11) (c₀ := 39 / 20)
      (lam := (D.ρ D.j / 8) ^ 2) (ηb := Work.Drive.N2.packetEtaB D η)
      (m := 99 / 50) (R := 3) (C₀ := 2)
      (U := U) (Z := Z) (foot := foot) (A := A) (θ := θ)
      (n := n)
      (L := ({ L with
        val := fun j x => by rw [hlamEta]; exact L.val j x
        cover := fun x hx => L.cover x (by rw [hlamEta] at hx; exact hx) } :
        Work.Drive.N2C.LevelCurves f
          (f p - (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEta D η) n))
      (i := i) (r := r) (Θ := Θ) (τU := τU) (τL := τL)
      (hη := hηs_pos) (hη' := hηs_lt10) (hδ := hδ0) (hδ' := hδ1) (hlam := hlampos2)
      (hc₀ := hc0) (hc₀' := hc0') (hηb := hηs_lt_ηb)
      (hU := hU) (hZsm := hZsmU) (hZimm := hZimmU) (hlev := hlevU)
      (hf := hf) (hreg := hregU')
      (hfoot := fun x => hfootsm.contMDiffAt) (hfootinj := hfootinj) (hfootimm := hfootimm)
      (hfootval := hflow1) (hlandFr := hflow7) (hfront := hfront)
      (hbig := hbig_e) (hθ01 := hθ01) (hAsm := hAsm) (hAoff := hAoff_e)
      (hAcurve := fun j t => by
        by_cases hj : j = i
        · subst hj
          rw [if_pos rfl]
          exact hAcurveL t
        · rw [if_neg hj]
          exact hAcurveL_j j hj t)
      (hZu := hZu) (hZd := hZdU) (hau := hau) (hal := hal)
      (hΘu := hΘu) (hΘl := hΘl) (hτu := hτu) (hτl := hτl)
      (hr := hr) (hrpos := hrpos) (hrper := hrper) (hrpi := hrpi) (hrev := hrev)
      (hlo := hloU) (hmono := hmono) (hbR := fun φ _ => hrR φ)
      (hR := by norm_num) (hm := hm1) (hm2 := le_of_lt hm2) (hnum := hnum)
      (hΘ := hΘsm) (hΘmono := hΘmono) (hΘderiv := hΘderiv) (hΘper := hΘper)
      (hC₀ := hC₀two) (hsmall := hsmallU) (hW := hgd)
  refine ⟨W, hgdW, hWlower, ?_⟩
  rw [← hlamEta]
  exact hWu


end Work.Drive.N2Lead
