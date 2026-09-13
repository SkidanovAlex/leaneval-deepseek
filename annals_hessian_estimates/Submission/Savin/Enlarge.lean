/-
# Savin's "enlarge opening" lemma (Lemma 2.2)

The growth lemma of the sliding-paraboloid method.  If a paraboloid of small opening `a` touches
the graph of `φ` from below somewhere in `B_r(x₀)`, then the contact set of the (universally)
larger opening `M a` covers a definite fraction of `B_r(x₀)`: see `enlarge_opening` at the end of
this file.

The three steps are:

* `exists_below_touchParab` -- the barrier step: `φ - P` is negative somewhere in `B_{r/2}(x₀)`,
  where `P` is the touching paraboloid of opening `a`.
* `step2_containment` -- the sliding step: every contact point of a paraboloid of opening `M a`
  whose vertex lies in a small ball `V` around `ȳ = (y₁ + (M - 1) x₂)/M` lies in `B_r(x₀)`.
* `enlarge_opening` -- combining with Savin's measure estimate (`contactSet_measure`).
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Barrier
import Submission.Savin.Growth
import Submission.Savin.Measure
import Submission.Commons.Analysis.Growth.cofop_hyp_of_small
import Submission.Commons.Analysis.Real.one_add_half_le_two_rpow
import Submission.Commons.Topology.Metric.dist_add_le_of_closedBall_subset
import Submission.Commons.Analysis.InnerProductSpace.paraboloid_vertex_identity


open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-! ## The touching paraboloid at a contact point -/

/-- The concave paraboloid of opening `a` which touches the graph of `φ` from below at `x`, with
vertex `slideMap a φ x`. -/
noncomputable def touchParab (a : ℝ) (φ : ℝ⁴ → ℝ) (x : ℝ⁴) : ℝ⁴ → ℝ :=
  parab a (slideMap a φ x) (φ x + a / 2 * ‖x - slideMap a φ x‖ ^ 2)

theorem touchParab_apply (a : ℝ) (φ : ℝ⁴ → ℝ) (x z : ℝ⁴) :
    touchParab a φ x z
      = φ x + a / 2 * ‖x - slideMap a φ x‖ ^ 2 - a / 2 * ‖z - slideMap a φ x‖ ^ 2 := by
  simp only [touchParab, parab_apply]; ring

theorem touchParab_self (a : ℝ) (φ : ℝ⁴ → ℝ) (x : ℝ⁴) : touchParab a φ x x = φ x := by
  simp only [touchParab, parab_apply]
  ring

/-- At a contact point the touching paraboloid lies below the graph on the unit ball. -/
theorem touchParab_le_of_mem_contactSet {a : ℝ} {φ : ℝ⁴ → ℝ} {B : Set ℝ⁴} {x : ℝ⁴}
    (hx : x ∈ contactSet a φ B) {z : ℝ⁴} (hz : z ∈ closedBall 0 1) :
    touchParab a φ x z ≤ φ z := by
  have h := hx.2.2 z hz
  simp only [touchParab, parab_apply]
  linarith

theorem touchParab_le_of_mem_contactPt {a : ℝ} {φ : ℝ⁴ → ℝ} {x : ℝ⁴}
    (hx : x ∈ contactPt a φ) {z : ℝ⁴} (hz : z ∈ closedBall 0 1) :
    touchParab a φ x z ≤ φ z := by
  have h := (mem_contactPt.mp hx).2.2 z hz
  simp only [touchParab, parab_apply]
  linarith

/-! ## Step 1: the barrier -/

/-- **Step 1 of the growth lemma.**  If a paraboloid of opening `a` touches `φ` from below at
`x₁ ∈ B_r(x₀)`, then there is a point `x₂ ∈ B_{r/2}(x₀)` where the *value* of `φ` is at most
`a r² C₀` above the touching paraboloid, `C₀ = (1/p)(2^p - 1)`. -/
theorem exists_below_touchParab {φ : ℝ⁴ → ℝ} (hφ : ContDiffOn ℝ 2 φ (ball 0 (3 / 2)))
    {C : ℝ⁴ →L[ℝ] ℝ⁴} (hC : C.IsSymmetric) {c c' : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪C v, v⟫) (hcq' : ∀ v : ℝ⁴, ⟪C v, v⟫ ≤ c' * ‖v‖ ^ 2)
    {ε : ℝ} (hε : 0 < ε) (heq : ∀ x ∈ ball 0 (3 / 2), Fop C ε (hessOp φ x) = 0)
    {a p r : ℝ} (ha : 0 < a) (hp : 0 < p) (hr : 0 < r)
    (hpbig : 16 * c' / c + 2 ≤ p) (hεa : 48 * ε * a * 2 ^ (2 * p + 4) ≤ c)
    {x₀ x₁ : ℝ⁴} (hx₁ : x₁ ∈ contactPt a φ) (hx₁ball : x₁ ∈ ball x₀ r)
    (hsub : closedBall x₀ r ⊆ ball 0 (3 / 2)) (hsub1 : closedBall x₀ r ⊆ closedBall 0 1) :
    ∃ x₂ ∈ closedBall x₀ (r / 2),
      φ x₂ - touchParab a φ x₁ x₂ ≤ a * r ^ 2 * ((1 / p) * (2 ^ p - 1)) := by
  have hc' : 0 < c' := by
    have h1 := hcq (stdB4 0); have h2 := hcq' (stdB4 0)
    have h3 : ‖stdB4 0‖ = 1 := stdB4.orthonormal.1 0
    rw [h3] at h1 h2; nlinarith
  have hcc' : c ≤ c' := by
    have h1 := hcq (stdB4 0); have h2 := hcq' (stdB4 0)
    have h3 : ‖stdB4 0‖ = 1 := stdB4.orthonormal.1 0
    rw [h3] at h1 h2; nlinarith
  have hp4 : 4 ≤ p := by
    have h2 : (1 : ℝ) ≤ c' / c := (one_le_div hc).mpr hcc'
    have h3 : (16 : ℝ) * 1 ≤ 16 * (c' / c) := by linarith
    have h4 : 16 * c' / c = 16 * (c' / c) := by ring
    linarith
  have hεa' : 12 * ε * a * 2 ^ (p + 2) ≤ c :=
    Commons.Analysis.Growth.cofop_hyp_of_small hε ha hp.le hεa
  have hcontp : Continuous (touchParab a φ x₁) := by
    simp only [touchParab]
    exact (continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2)).add
      continuous_const
  have hψcont : Continuous (fun z => touchParab a φ x₁ z + growthBarrier p a r x₀ z) :=
    hcontp.add (continuous_growthBarrier p a r x₀)
  have hψC2 : ∀ x, r / 2 < ‖x - x₀‖ → ‖x - x₀‖ < r →
      ContDiffAt ℝ 2 (fun z => touchParab a φ x₁ z + growthBarrier p a r x₀ z) x := by
    intro x hx1 hx2
    show ContDiffAt ℝ 2 (fun z =>
      parab a (slideMap a φ x₁) (φ x₁ + a / 2 * ‖x₁ - slideMap a φ x₁‖ ^ 2) z
        + growthBarrier p a r x₀ z) x
    exact contDiffAt_parab_add_growthBarrier hr hx1 hx2
  have hhess : ∀ x, r / 2 < ‖x - x₀‖ → ‖x - x₀‖ < r →
      hessOp (fun z => touchParab a φ x₁ z + growthBarrier p a r x₀ z) x
        = growthOp p a r x₀ x := by
    intro x hx1 hx2
    show hessOp (fun z =>
      parab a (slideMap a φ x₁) (φ x₁ + a / 2 * ‖x₁ - slideMap a φ x₁‖ ^ 2) z
        + growthBarrier p a r x₀ z) x = growthOp p a r x₀ x
    exact hessOp_growthFunction hp hr hx1 hx2
  have hψF : ∀ x, r / 2 < ‖x - x₀‖ → ‖x - x₀‖ < r →
      0 < Fop C ε (hessOp (fun z => touchParab a φ x₁ z + growthBarrier p a r x₀ z) x) := by
    intro x hx1 hx2
    rw [hhess x hx1 hx2]
    exact Fop_growthOp_pos hC hc hcq hcq' hε ha hp hr hx1 hx2 hpbig hεa
  have hψcof : ∀ x, r / 2 < ‖x - x₀‖ → ‖x - x₀‖ < r →
      ∀ v : ℝ⁴, 0 ≤ ⟪(C + ε • cofOp (hessOp
        (fun z => touchParab a φ x₁ z + growthBarrier p a r x₀ z) x)) v, v⟫ := by
    intro x hx1 hx2 v
    rw [hhess x hx1 hx2]
    exact cofOp_growthOp_nonneg hc hcq hε ha hp4 hr hx1 hx2 hεa' v
  have hsphere : ∀ z ∈ sphere x₀ r,
      0 ≤ φ z - (fun z => touchParab a φ x₁ z + growthBarrier p a r x₀ z) z := by
    intro z hz
    have hzr : ‖z - x₀‖ = r := by rw [mem_sphere, dist_eq_norm] at hz; exact hz
    have hzcl : z ∈ closedBall x₀ r := by rw [mem_closedBall, dist_eq_norm, hzr]
    have hle := touchParab_le_of_mem_contactPt hx₁ (hsub1 hzcl)
    have hzero : growthBarrier p a r x₀ z = 0 :=
      growthBarrier_eq_zero hr (le_of_eq hzr.symm)
    simp only [hzero, add_zero]
    linarith
  have hx₁neg : φ x₁ - (fun z => touchParab a φ x₁ z + growthBarrier p a r x₀ z) x₁ < 0 := by
    have hlt : ‖x₁ - x₀‖ < r := by rw [mem_ball, dist_eq_norm] at hx₁ball; exact hx₁ball
    have hpos : 0 < growthBarrier p a r x₀ x₁ := growthBarrier_pos hp ha hr hlt
    simp only [touchParab_self]
    linarith
  obtain ⟨x₂, hx₂mem, hx₂le⟩ := exists_below_of_supersolution hφ hC hε heq hr hsub
    hψcont hψC2 hψF hψcof hsphere hx₁ball hx₁neg
  refine ⟨x₂, hx₂mem, ?_⟩
  have hbdd : growthBarrier p a r x₀ x₂ ≤ a * r ^ 2 * ((1 / p) * (2 ^ p - 1)) :=
    growthBarrier_le hp ha.le x₀ x₂
  have hexp : φ x₂ - touchParab a φ x₁ x₂
      = (φ x₂ - (fun z => touchParab a φ x₁ z + growthBarrier p a r x₀ z) x₂)
        + growthBarrier p a r x₀ x₂ := by
    simp only []
    ring
  rw [hexp]
  linarith

/-! ## Step 2: the sliding step -/

/-- **Step 2 of the growth lemma.**  Every contact point of a paraboloid of opening `M a` whose
vertex lies in the small ball of radius `r(M-1)/(8M)` around `ȳ = M⁻¹(y₁ + (M-1)x₂)` lies in
`B_r(x₀)`. -/
theorem step2_containment {φ : ℝ⁴ → ℝ}
    {a p r M : ℝ} (ha : 0 < a) (hr : 0 < r) (hp : 0 < p) (hM1 : 1 < M)
    (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1)))
    {x₀ x₁ x₂ : ℝ⁴} (hsub1 : closedBall x₀ r ⊆ closedBall 0 1)
    (hx₂ : x₂ ∈ closedBall x₀ (r / 2))
    (hd : φ x₂ - touchParab a φ x₁ x₂ ≤ a * r ^ 2 * ((1 / p) * (2 ^ p - 1)))
    (hP : ∀ z ∈ closedBall 0 1, touchParab a φ x₁ z ≤ φ z)
    {yt : ℝ⁴} (hyt : yt ∈ closedBall (M⁻¹ • (slideMap a φ x₁ + (M - 1) • x₂))
      (r * (M - 1) / (8 * M)))
    {x : ℝ⁴} (hx1 : x ∈ closedBall 0 1)
    (hmin : ∀ z ∈ closedBall 0 1,
      φ x + (M * a) / 2 * ‖x - yt‖ ^ 2 ≤ φ z + (M * a) / 2 * ‖z - yt‖ ^ 2) :
    ‖x - x₀‖ < r := by
  set y₁ : ℝ⁴ := slideMap a φ x₁ with hy₁def
  set yb : ℝ⁴ := M⁻¹ • (y₁ + (M - 1) • x₂) with hybdef
  set w : ℝ⁴ := x₂ + ((M - 1)⁻¹ * M) • (yt - yb) with hwdef
  have hMne : M ≠ 1 := ne_of_gt hM1
  have hMm1 : 0 < M - 1 := by linarith
  have hMpos : 0 < M := by linarith
  have hyt' : yt ∈ closedBall yb (r * (M - 1) / (8 * M)) := by
    simp only [hybdef, hy₁def] at hyt ⊢
    exact hyt
  have hrel : M • yb = y₁ + (M - 1) • x₂ := by
    rw [hybdef, smul_smul]
    have h1 : M * M⁻¹ = 1 := by field_simp
    rw [h1, one_smul]
  have hid : ∀ z : ℝ⁴, ‖z - y₁‖ ^ 2 - M * ‖z - yt‖ ^ 2
      = (1 - M) * ‖z - w‖ ^ 2 + (‖w - y₁‖ ^ 2 - M * ‖w - yt‖ ^ 2) := by
    intro z
    exact Commons.Analysis.InnerProductSpace.paraboloid_vertex_identity (M := M) (y₁ := y₁) (yb := yb) (x₂ := x₂)
      (yt := yt) hMne hrel z
  have hx₂1 : x₂ ∈ closedBall 0 1 :=
    hsub1 (closedBall_subset_closedBall (by linarith : r / 2 ≤ r) hx₂)
  set Q : ℝ⁴ → ℝ := parab (M * a) yt (φ x + (M * a) / 2 * ‖x - yt‖ ^ 2) with hQdef
  have hQx : Q x = φ x := by simp only [hQdef, parab_apply]; ring
  have hQx₂ : Q x₂ ≤ φ x₂ := by
    have h := hmin x₂ hx₂1
    simp only [hQdef, parab_apply]
    linarith
  have hsum : (Q x - Q x₂) + (touchParab a φ x₁ x₂ - touchParab a φ x₁ x)
      = (a / 2) * (1 - M) * (‖x - w‖ ^ 2 - ‖x₂ - w‖ ^ 2) := by
    have h1 := hid x
    have h2 := hid x₂
    simp only [hy₁def] at h1 h2
    simp only [hQdef, touchParab, parab_apply]
    linear_combination (a / 2) * h1 - (a / 2) * h2
  have hkey : 0 ≤ (a / 2) * (1 - M) * (‖x - w‖ ^ 2 - ‖x₂ - w‖ ^ 2)
      + a * r ^ 2 * ((1 / p) * (2 ^ p - 1)) := by
    have h0 : 0 ≤ Q x - touchParab a φ x₁ x := by
      rw [hQx]; exact sub_nonneg.mpr (hP x hx1)
    have hb : Q x₂ - touchParab a φ x₁ x₂ ≤ a * r ^ 2 * ((1 / p) * (2 ^ p - 1)) := by
      linarith [hQx₂, hd]
    have hsplit : Q x - touchParab a φ x₁ x
        = (Q x - Q x₂) + (Q x₂ - touchParab a φ x₁ x₂)
          + (touchParab a φ x₁ x₂ - touchParab a φ x₁ x) := by ring
    rw [hsplit] at h0
    linarith [hsum]
  have hC₀pos : 0 < (1 / p) * (2 ^ p - 1) := by
    have h2p : 1 < (2 : ℝ) ^ p := Real.one_lt_rpow (by norm_num) hp
    have h1 : 0 < (2 : ℝ) ^ p - 1 := by linarith
    exact mul_pos (one_div_pos.mpr hp) h1
  have hMm1' : M - 1 = 128 * ((1 / p) * (2 ^ p - 1)) := by rw [hM]; ring
  have h2C₀ : 2 * ((1 / p) * (2 ^ p - 1)) / (M - 1) = 1 / 64 := by
    rw [hMm1',
      div_eq_iff (ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 128) hC₀pos))]
    ring
  have hD : ‖x - w‖ ^ 2 ≤ ‖x₂ - w‖ ^ 2 + 2 * r ^ 2 * ((1 / p) * (2 ^ p - 1)) / (M - 1) := by
    have ha2 : 0 < a / 2 := by linarith
    have hcoef : 0 < (a / 2) * (M - 1) := mul_pos ha2 hMm1
    have h1 : (a / 2) * (M - 1) * (‖x - w‖ ^ 2 - ‖x₂ - w‖ ^ 2)
        ≤ a * r ^ 2 * ((1 / p) * (2 ^ p - 1)) := by nlinarith [hkey]
    have h2 : ‖x - w‖ ^ 2 - ‖x₂ - w‖ ^ 2
        ≤ a * r ^ 2 * ((1 / p) * (2 ^ p - 1)) / ((a / 2) * (M - 1)) :=
      (le_div_iff₀ hcoef).mpr (by rw [mul_comm]; exact h1)
    have h3 : a * r ^ 2 * ((1 / p) * (2 ^ p - 1)) / ((a / 2) * (M - 1))
        = 2 * r ^ 2 * ((1 / p) * (2 ^ p - 1)) / (M - 1) := by
      field_simp
    linarith [h2, h3]
  have hwx₂ : w - x₂ = ((M - 1)⁻¹ * M) • (yt - yb) := by
    rw [hwdef, add_sub_cancel_left]
  have hcoefnn : (0 : ℝ) < (M - 1)⁻¹ * M := mul_pos (inv_pos.mpr hMm1) hMpos
  have hnorm : ‖w - x₂‖ ≤ r / 8 := by
    rw [hwx₂, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoefnn.le]
    have hyn : ‖yt - yb‖ ≤ r * (M - 1) / (8 * M) := by
      have := mem_closedBall.mp hyt'
      rwa [dist_eq_norm] at this
    calc (M - 1)⁻¹ * M * ‖yt - yb‖ ≤ (M - 1)⁻¹ * M * (r * (M - 1) / (8 * M)) :=
          mul_le_mul_of_nonneg_left hyn hcoefnn.le
      _ = r / 8 := by field_simp
  have hx₂w : ‖x₂ - w‖ ^ 2 ≤ r ^ 2 / 64 := by
    rw [norm_sub_rev]
    have h1 : 0 ≤ ‖w - x₂‖ := norm_nonneg _
    nlinarith [hnorm, hr, h1]
  have h2C₀' : 2 * r ^ 2 * ((1 / p) * (2 ^ p - 1)) / (M - 1) = r ^ 2 / 64 := by
    rw [show 2 * r ^ 2 * ((1 / p) * (2 ^ p - 1)) / (M - 1)
        = r ^ 2 * (2 * ((1 / p) * (2 ^ p - 1)) / (M - 1)) by ring, h2C₀]
    ring
  have hxw : ‖x - w‖ ^ 2 ≤ r ^ 2 / 32 := by linarith [hD, hx₂w, h2C₀']
  have hxw' : ‖x - w‖ ≤ r / 4 := by
    have h1 : 0 ≤ ‖x - w‖ := norm_nonneg _
    nlinarith [hxw, hr, h1]
  have hx₂x₀ : ‖x₂ - x₀‖ ≤ r / 2 := by
    have := mem_closedBall.mp hx₂
    rwa [dist_eq_norm] at this
  have htri1 : ‖x - x₀‖ ≤ ‖x - w‖ + ‖w - x₀‖ := by
    have h : x - x₀ = (x - w) + (w - x₀) := by abel
    rw [h]; exact norm_add_le _ _
  have htri2 : ‖w - x₀‖ ≤ ‖w - x₂‖ + ‖x₂ - x₀‖ := by
    have h : w - x₀ = (w - x₂) + (x₂ - x₀) := by abel
    rw [h]; exact norm_add_le _ _
  calc ‖x - x₀‖ ≤ ‖x - w‖ + ‖w - x₀‖ := htri1
    _ ≤ ‖x - w‖ + (‖w - x₂‖ + ‖x₂ - x₀‖) := by linarith
    _ ≤ r / 4 + (r / 8 + r / 2) := by linarith
    _ < r := by linarith

/-! ## Step 3: the measure estimate -/

/-- **Savin's "enlarge opening" lemma (Lemma 2.2).**  If a paraboloid of opening `a` touches `φ`
from below at a point of `B_r(x₀)` and `φ` solves `Fop C ε = 0`, then the contact set of the
universally larger opening `M a = (1 + 128 C₀) a` covers a definite fraction of `B_r(x₀)`. -/
theorem enlarge_opening {φ : ℝ⁴ → ℝ} (hφ : ContDiffOn ℝ 2 φ (ball 0 (3 / 2)))
    {C : ℝ⁴ →L[ℝ] ℝ⁴} (hC : C.IsSymmetric) {c c' : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪C v, v⟫) (hcq' : ∀ v : ℝ⁴, ⟪C v, v⟫ ≤ c' * ‖v‖ ^ 2)
    {ε : ℝ} (hε : 0 < ε) (heq : ∀ x ∈ ball 0 (3 / 2), Fop C ε (hessOp φ x) = 0)
    {a p r M : ℝ} (ha : 0 < a) (hp : 0 < p) (hr : 0 < r)
    (hM1 : 1 < M) (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1)))
    (hpbig : 16 * c' / c + 2 ≤ p) (hεa : 48 * ε * a * 2 ^ (2 * p + 4) ≤ c)
    (hεa' : 3 * ε * (M * a) ≤ c / 2)
    {x₀ x₁ : ℝ⁴} (hx₁ : x₁ ∈ contactPt a φ) (hx₁ball : x₁ ∈ ball x₀ r)
    (hsub : closedBall x₀ r ⊆ ball 0 (3 / 2)) (hsub2 : closedBall x₀ r ⊆ closedBall 0 (1 / 2)) :
    ENNReal.ofReal (((M - 1) / (8 * M)) ^ 4 / (1 + (2 * trOp C / c + 3)) ^ 4)
        * volume (closedBall x₀ r)
      ≤ volume (contactPt (M * a) φ ∩ closedBall x₀ r) := by
  have hC₀pos : 0 < (1 / p) * (2 ^ p - 1) := by
    have h2p : 1 < (2 : ℝ) ^ p := Real.one_lt_rpow (by norm_num) hp
    have h1 : 0 < (2 : ℝ) ^ p - 1 := by linarith
    exact mul_pos (one_div_pos.mpr hp) h1
  have hMm1pos : 0 < M - 1 := by
    rw [hM]
    have : (0 : ℝ) < 128 * ((1 / p) * (2 ^ p - 1)) := by positivity
    linarith
  have hMpos : 0 < M := by linarith
  have htrC : 0 ≤ trOp C := by
    rw [trOp_eq_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    have h2 := hcq (stdB4 i)
    have h3 : ‖stdB4 i‖ = 1 := stdB4.orthonormal.1 i
    rw [h3] at h2
    nlinarith [h2]
  have hKpos : 0 < 1 + (2 * trOp C / c + 3) := by positivity
  set K' : ℝ := (1 + (2 * trOp C / c + 3)) ^ 4 with hK'def
  have hK'pos : 0 < K' := by rw [hK'def]; positivity
  set k : ℝ := (M - 1) / (8 * M) with hkdef
  have hkpos : 0 < k := by
    rw [hkdef]
    exact div_pos hMm1pos (by positivity)
  -- Step 1
  have hsub1 : closedBall x₀ r ⊆ closedBall 0 1 := fun z hz =>
    closedBall_subset_closedBall (by norm_num : (1 : ℝ) / 2 ≤ 1) (hsub2 hz)
  obtain ⟨x₂, hx₂, hd⟩ := exists_below_touchParab hφ hC hc hcq hcq' hε heq ha hp hr hpbig
    hεa hx₁ hx₁ball hsub hsub1
  have hP : ∀ z ∈ closedBall 0 1, touchParab a φ x₁ z ≤ φ z := fun z hz =>
    touchParab_le_of_mem_contactPt hx₁ hz
  set yb : ℝ⁴ := M⁻¹ • (slideMap a φ x₁ + (M - 1) • x₂) with hybdef
  set ρ : ℝ := r * k with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact mul_pos hr hkpos
  have hρeq : ρ = r * (M - 1) / (8 * M) := by rw [hρdef, hkdef]; ring
  -- Step 2: the contact points of the enlarged opening with vertex in `closedBall yb ρ`
  have hcontact : ∀ y ∈ closedBall yb ρ, ∃ x ∈ closedBall 0 (1 / 2),
      ∀ z ∈ closedBall 0 1,
        φ x + (M * a) / 2 * ‖x - y‖ ^ 2 ≤ φ z + (M * a) / 2 * ‖z - y‖ ^ 2 := by
    intro y hy
    have hcontφ : ContinuousOn φ (closedBall 0 1) :=
      hφ.continuousOn.mono (closedBall_subset_ball (by norm_num : (1 : ℝ) < 3 / 2))
    have hcont : ContinuousOn (fun z : ℝ⁴ => φ z + (M * a) / 2 * ‖z - y‖ ^ 2)
        (closedBall 0 1) :=
      hcontφ.add ((continuous_const.mul
        ((continuous_id.sub continuous_const).norm.pow 2)).continuousOn)
    obtain ⟨x, hxmem, hxmin⟩ := (isCompact_closedBall (0 : ℝ⁴) 1).exists_isMinOn
      ⟨0, by simp⟩ hcont
    have hy' : y ∈ closedBall (M⁻¹ • (slideMap a φ x₁ + (M - 1) • x₂))
        (r * (M - 1) / (8 * M)) := by
      rw [hybdef, hρeq] at hy
      exact hy
    have hstep := step2_containment ha hr hp hM1 hM hsub1 hx₂ hd hP (yt := y) hy'
      hxmem (fun z hz => hxmin hz)
    exact ⟨x, hsub2 (mem_closedBall.mpr (by rw [dist_eq_norm]; exact hstep.le)),
      fun z hz => hxmin hz⟩
  -- the measure estimate
  have hmeas : volume (closedBall yb ρ)
      ≤ ENNReal.ofReal K' * volume (contactSet (M * a) φ (closedBall yb ρ)) := by
    have h := contactSet_measure hφ hC hc hcq hε (mul_pos hMpos ha) hεa' heq
      isClosed_closedBall hcontact
    rwa [← hK'def] at h
  -- the vertex of a contact point of the enlarged opening stays in the unit ball
  have hy₁1 : ‖slideMap a φ x₁‖ ≤ 1 := by
    have h := mem_closedBall.mp (mem_contactPt.mp hx₁).2.1
    rwa [dist_zero_right] at h
  have hx₂1 : ‖x₂‖ ≤ 1 / 2 := by
    have h := hsub2 (closedBall_subset_closedBall (by linarith : r / 2 ≤ r) hx₂)
    rwa [mem_closedBall, dist_zero_right] at h
  have hr1 : r ≤ 1 / 2 := by
    have h := Commons.Topology.Metric.dist_add_le_of_closedBall_subset hr.le hsub2
    rw [dist_zero_right] at h
    linarith [norm_nonneg x₀]
  have hρ1 : ρ ≤ 1 / 16 := by
    rw [hρeq]
    have h2 : r * (M - 1) / (8 * M) = (r / 8) * ((M - 1) / M) := by ring
    rw [h2]
    have h3 : (M - 1) / M ≤ 1 := by
      rw [div_le_one hMpos]; linarith
    nlinarith [hr1, hMpos, h3,
      mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ r / 8)]
  have hC₀half : (1 / 2 : ℝ) ≤ (1 / p) * (2 ^ p - 1) := by
    have h2p : 1 + p / 2 ≤ (2 : ℝ) ^ p :=
      Commons.Analysis.Real.one_add_half_le_two_rpow hp.le
    have hpe : (1 / p) * (2 ^ p - 1) = (2 ^ p - 1) / p := by rw [one_div, inv_mul_eq_div]
    rw [hpe, le_div_iff₀ hp]
    linarith
  have hMlarge : 16 / 7 ≤ M := by rw [hM]; nlinarith [hC₀half]
  have hinvM : 1 / M ≤ 7 / 16 := by
    rw [div_le_iff₀ hMpos]; nlinarith [hMlarge]
  have hyb1 : ‖yb‖ + ρ ≤ 1 := by
    have h1 : ‖yb‖ ≤ 1 / 2 + 1 / (2 * M) := by
      rw [hybdef]
      calc ‖M⁻¹ • (slideMap a φ x₁ + (M - 1) • x₂)‖
          = M⁻¹ * ‖slideMap a φ x₁ + (M - 1) • x₂‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hMpos)]
        _ ≤ M⁻¹ * (‖slideMap a φ x₁‖ + ‖(M - 1) • x₂‖) :=
              mul_le_mul_of_nonneg_left (norm_add_le _ _) (inv_nonneg.mpr hMpos.le)
        _ ≤ M⁻¹ * (1 + (M - 1) * (1 / 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hMpos.le)
              have h₂ : ‖(M - 1) • x₂‖ ≤ (M - 1) * (1 / 2) := by
                rw [norm_smul, Real.norm_eq_abs,
                  abs_of_nonneg (by linarith : (0 : ℝ) ≤ M - 1)]
                nlinarith [hx₂1, hMpos]
              linarith [hy₁1, h₂]
        _ = 1 / 2 + 1 / (2 * M) := by field_simp; ring
    have h2M : 1 / (2 * M) ≤ 7 / 32 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * M)]
      nlinarith [hMlarge]
    linarith [h1, hρ1, h2M]
  have hV : closedBall yb ρ ⊆ closedBall (0 : ℝ⁴) 1 := by
    intro z hz
    have hz1 : ‖z - yb‖ ≤ ρ := by
      have h := mem_closedBall.mp hz; rwa [dist_eq_norm] at h
    rw [mem_closedBall, dist_zero_right]
    calc ‖z‖ ≤ ‖z - yb‖ + ‖yb‖ := by
          have h := norm_add_le (z - yb) yb
          rwa [sub_add_cancel] at h
      _ ≤ ρ + ‖yb‖ := by linarith
      _ ≤ 1 := by linarith [hyb1]
  -- the contact set of the enlarged opening is contained in `B_r(x₀)`
  have hsub3 : contactSet (M * a) φ (closedBall yb ρ)
      ⊆ contactPt (M * a) φ ∩ closedBall x₀ r := by
    intro x hx
    have hx' := mem_contactSet.mp hx
    have hy' : slideMap (M * a) φ x ∈ closedBall
        (M⁻¹ • (slideMap a φ x₁ + (M - 1) • x₂)) (r * (M - 1) / (8 * M)) := by
      rw [hybdef, hρeq] at hx'
      exact hx'.2.1
    have hstep := step2_containment ha hr hp hM1 hM hsub1 hx₂ hd hP
      (yt := slideMap (M * a) φ x) hy' (closedBall_subset_closedBall (by norm_num) hx'.1)
      hx'.2.2
    exact ⟨contactSet_subset_contactPt hV hx,
      mem_closedBall.mpr (by rw [dist_eq_norm]; exact hstep.le)⟩
  -- volume computations
  have hvolV : volume (closedBall yb ρ)
      = ENNReal.ofReal (ρ ^ 4) * volume (ball (0 : ℝ⁴) 1) := by
    have h := Measure.addHaar_closedBall (volume : Measure ℝ⁴) yb hρpos.le
    simpa using h
  have hvol0 : volume (closedBall x₀ r)
      = ENNReal.ofReal (r ^ 4) * volume (ball (0 : ℝ⁴) 1) := by
    have h := Measure.addHaar_closedBall (volume : Measure ℝ⁴) x₀ hr.le
    simpa using h
  have hρk : ρ = k * r := by rw [hρdef]; ring
  have hvolrel : volume (closedBall yb ρ)
      = ENNReal.ofReal (k ^ 4) * volume (closedBall x₀ r) := by
    rw [hvolV, hvol0, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow, ← hρk]
  have hofK : ENNReal.ofReal (K'⁻¹) = (ENNReal.ofReal K')⁻¹ := ENNReal.ofReal_inv_of_pos hK'pos
  calc ENNReal.ofReal (k ^ 4 / K') * volume (closedBall x₀ r)
      = (ENNReal.ofReal (k ^ 4) * ENNReal.ofReal (K'⁻¹)) * volume (closedBall x₀ r) := by
        rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (K'⁻¹) * (ENNReal.ofReal (k ^ 4) * volume (closedBall x₀ r)) := by
        rw [mul_comm (ENNReal.ofReal (k ^ 4)) (ENNReal.ofReal (K'⁻¹)), mul_assoc]
    _ = ENNReal.ofReal (K'⁻¹) * volume (closedBall yb ρ) := by rw [← hvolrel]
    _ ≤ ENNReal.ofReal (K'⁻¹)
          * (ENNReal.ofReal K' * volume (contactSet (M * a) φ (closedBall yb ρ))) :=
        mul_le_mul_of_nonneg_left hmeas (by simp)
    _ = volume (contactSet (M * a) φ (closedBall yb ρ)) := by
        rw [← mul_assoc, hofK,
          ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hK'pos))
            ENNReal.ofReal_ne_top, one_mul]
    _ ≤ volume (contactPt (M * a) φ ∩ closedBall x₀ r) := measure_mono hsub3

end

end Submission
