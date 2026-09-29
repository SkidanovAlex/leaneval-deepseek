import Mathlib
import Submission.Work.A14D.exists_sol_LZ_convex
import Submission.Work.A14D.eqOn_of_sol_LZ
import Submission.Work.A14D.glue_three_LZ_Om1
import Submission.Work.A14D.om1_geometry
import Submission.Work.A14D.slitPieces
import Submission.Work.A14D.Dzc_helpers

/-!
# `Work.A14D.exists_sol_LZ_Om1_of_ball_one`

Every solution `f` of `LZ f = 0` on the disc `ball (1 : ℂ) δ` (`δ > 0`) extends to a solution
`F` of `LZ F = 0` on the whole slit plane `Om1 = ℂ ∖ (−∞, 1]`, in such a way that `F = f` on
`ball (1 : ℂ) δ ∩ Om1`.

The operator `LZ y = PZ·y'' + PZ'·y' + RZ·y` has its only singularities at the three real points
`0, 1/9, 1`, all of which lie on the slit; on `Om1` the coefficient `PZ` does not vanish.  The
slit plane is covered by the three convex open sets

* `upSet = {0 < Im}`, `dnSet = {Im < 0}`, `rtSet = {1 < Re}`,

with `upSet ∩ dnSet = ∅` and `upSet ∩ rtSet`, `dnSet ∩ rtSet` nonempty.  On each of them a
solution of `LZ = 0` exists for any prescribed initial data at any point
(`exists_sol_LZ_convex`, using convexity and `PZ ≠ 0`), and two solutions agreeing on a nonempty
open subset of a convex set coincide there (`eqOn_of_sol_LZ`).  Seeding each of the three pieces
from `f` at a point of the ball, and comparing pairwise on the (convex) overlaps — where both
functions equal `f` on `ball ∩ overlap` — we may glue the three pieces along `Om1`
(`glue_three_LZ_Om1`).
-/

namespace Work.A14D

open Work.A14D Complex Metric Filter
open scoped Topology

noncomputable section

/-! ## The three convex pieces covering the slit plane -/

private def upSet : Set ℂ := {z : ℂ | 0 < z.im}

private def dnSet : Set ℂ := {z : ℂ | z.im < 0}

private def rtSet : Set ℂ := {z : ℂ | 1 < z.re}

private lemma isOpen_upSet : IsOpen upSet :=
  isOpen_lt continuous_const Complex.continuous_im

private lemma isOpen_dnSet : IsOpen dnSet :=
  isOpen_lt Complex.continuous_im continuous_const

private lemma isOpen_rtSet : IsOpen rtSet :=
  isOpen_lt continuous_const Complex.continuous_re

private lemma convex_upSet : Convex ℝ upSet := convex_halfSpace_im_gt 0

private lemma convex_dnSet : Convex ℝ dnSet := convex_halfSpace_im_lt 0

private lemma convex_rtSet : Convex ℝ rtSet := convex_halfSpace_re_gt 1

private lemma upSet_subset_Om1 : upSet ⊆ Om1 := fun _ hz => Or.inl (ne_of_gt hz)

private lemma dnSet_subset_Om1 : dnSet ⊆ Om1 := fun _ hz => Or.inl (ne_of_lt hz)

private lemma rtSet_subset_Om1 : rtSet ⊆ Om1 := fun _ hz => Or.inr hz

private lemma upSet_inter_dnSet : upSet ∩ dnSet = ∅ := by
  ext z
  simp only [upSet, dnSet, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
  exact ⟨fun h => absurd h.2 (not_lt.mpr h.1.le), fun h => h.elim⟩

private lemma Om1_subset_cover : ∀ z : ℂ, z ∈ Om1 → z ∈ upSet ∨ z ∈ dnSet ∨ z ∈ rtSet := by
  intro z hz
  rcases hz with h | h
  · rcases lt_or_gt_of_ne h with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inl h'
  · exact Or.inr (Or.inr h)

/-- The zeros of `PZ` are `0`, `1`, `1/9`, all of real part at most `1`. -/
private lemma PZ_re_le_one_of_eq_zero {z : ℂ} (h : PZ z = 0) : z.re ≤ 1 := by
  rw [PZ] at h
  rcases mul_eq_zero.mp h with h2 | h2
  · rcases mul_eq_zero.mp h2 with h2 | h2
    · rw [h2]; simp
    · have hz : z = 1 := by linear_combination -h2
      rw [hz]; norm_num
  · have h3 : 9 * z = 1 := by linear_combination -h2
    have hz : z = 1 / 9 := by
      rw [eq_div_iff (by norm_num : (9 : ℂ) ≠ 0)]
      linear_combination h3
    rw [hz]; norm_num

private lemma PZ_ne_zero_of_re_gt_one {z : ℂ} (hz : 1 < z.re) : PZ z ≠ 0 := by
  intro h
  have := PZ_re_le_one_of_eq_zero h
  linarith

/-! ## Four explicit points of `ball (1 : ℂ) δ` -/

/-- A point of `ball 1 δ ∩ upSet ∩ rtSet`: `1 + δ/4 + i δ/4`. -/
private def PU (δ : ℝ) : ℂ := ((1 + δ / 4 : ℝ) : ℂ) + ((δ / 4 : ℝ) : ℂ) * Complex.I

/-- A point of `ball 1 δ ∩ dnSet ∩ rtSet`: `1 + δ/4 − i δ/4`. -/
private def PL (δ : ℝ) : ℂ := ((1 + δ / 4 : ℝ) : ℂ) - ((δ / 4 : ℝ) : ℂ) * Complex.I

/-- A point of `ball 1 δ ∩ upSet`: `1 + i δ/2`. -/
private def PA (δ : ℝ) : ℂ := (1 : ℂ) + ((δ / 2 : ℝ) : ℂ) * Complex.I

/-- A point of `ball 1 δ ∩ dnSet`: `1 − i δ/2`. -/
private def PB (δ : ℝ) : ℂ := (1 : ℂ) - ((δ / 2 : ℝ) : ℂ) * Complex.I

private lemma mem_ball_one_of_re_im {δ : ℝ} {z : ℂ} (h : |z.re - 1| + |z.im| < δ) :
    z ∈ Metric.ball (1 : ℂ) δ := by
  rw [Metric.mem_ball, Complex.dist_eq]
  calc ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| := Complex.norm_le_abs_re_add_abs_im (z - 1)
    _ = |z.re - 1| + |z.im| := by simp
    _ < δ := h

private lemma PU_re (δ : ℝ) : (PU δ).re = 1 + δ / 4 := by
  simp [PU, Complex.add_re, Complex.mul_re]

private lemma PU_im (δ : ℝ) : (PU δ).im = δ / 4 := by
  simp [PU, Complex.add_im, Complex.mul_im]

private lemma PL_re (δ : ℝ) : (PL δ).re = 1 + δ / 4 := by
  simp [PL, Complex.sub_re, Complex.mul_re]

private lemma PL_im (δ : ℝ) : (PL δ).im = -(δ / 4) := by
  simp [PL, Complex.sub_im, Complex.mul_im]

private lemma PA_re (δ : ℝ) : (PA δ).re = 1 := by
  simp [PA, Complex.add_re, Complex.mul_re]

private lemma PA_im (δ : ℝ) : (PA δ).im = δ / 2 := by
  simp [PA, Complex.add_im, Complex.mul_im]

private lemma PB_re (δ : ℝ) : (PB δ).re = 1 := by
  simp [PB, Complex.sub_re, Complex.mul_re]

private lemma PB_im (δ : ℝ) : (PB δ).im = -(δ / 2) := by
  simp [PB, Complex.sub_im, Complex.mul_im]

private lemma PU_mem_ball {δ : ℝ} (hδ : 0 < δ) : PU δ ∈ Metric.ball (1 : ℂ) δ := by
  have h4 : (0 : ℝ) < δ / 4 := by linarith
  refine mem_ball_one_of_re_im ?_
  rw [PU_re, PU_im,
    show |1 + δ / 4 - 1| = δ / 4 by
      rw [show 1 + δ / 4 - 1 = δ / 4 by ring, abs_of_pos h4],
    abs_of_pos h4]
  linarith

private lemma PL_mem_ball {δ : ℝ} (hδ : 0 < δ) : PL δ ∈ Metric.ball (1 : ℂ) δ := by
  have h4 : (0 : ℝ) < δ / 4 := by linarith
  refine mem_ball_one_of_re_im ?_
  rw [PL_re, PL_im,
    show |1 + δ / 4 - 1| = δ / 4 by
      rw [show 1 + δ / 4 - 1 = δ / 4 by ring, abs_of_pos h4],
    abs_neg, abs_of_pos h4]
  linarith

private lemma PA_mem_ball {δ : ℝ} (hδ : 0 < δ) : PA δ ∈ Metric.ball (1 : ℂ) δ := by
  have h2 : (0 : ℝ) < δ / 2 := by linarith
  refine mem_ball_one_of_re_im ?_
  have h0 : |(1 : ℝ) - 1| = 0 := by norm_num
  rw [PA_re, PA_im, h0, zero_add, abs_of_pos h2]
  linarith

private lemma PB_mem_ball {δ : ℝ} (hδ : 0 < δ) : PB δ ∈ Metric.ball (1 : ℂ) δ := by
  have h2 : (0 : ℝ) < δ / 2 := by linarith
  refine mem_ball_one_of_re_im ?_
  have h0 : |(1 : ℝ) - 1| = 0 := by norm_num
  rw [PB_re, PB_im, h0, zero_add, abs_neg, abs_of_pos h2]
  linarith

private lemma PU_mem_up {δ : ℝ} (hδ : 0 < δ) : PU δ ∈ upSet := by
  show 0 < (PU δ).im
  rw [PU_im]; linarith

private lemma PL_mem_dn {δ : ℝ} (hδ : 0 < δ) : PL δ ∈ dnSet := by
  show (PL δ).im < 0
  rw [PL_im]; linarith

private lemma PA_mem_up {δ : ℝ} (hδ : 0 < δ) : PA δ ∈ upSet := by
  show 0 < (PA δ).im
  rw [PA_im]; linarith

private lemma PB_mem_dn {δ : ℝ} (hδ : 0 < δ) : PB δ ∈ dnSet := by
  show (PB δ).im < 0
  rw [PB_im]; linarith

private lemma PU_mem_rt {δ : ℝ} (hδ : 0 < δ) : PU δ ∈ rtSet := by
  show 1 < (PU δ).re
  rw [PU_re]; linarith

private lemma PL_mem_rt {δ : ℝ} (hδ : 0 < δ) : PL δ ∈ rtSet := by
  show 1 < (PL δ).re
  rw [PL_re]; linarith

/-! ## The extension theorem -/

set_option linter.unusedVariables false in
/-- **Extension of `LZ`-solutions from the disc `ball 1 δ` to the slit plane `Om1`.**  Note that
the hypothesis `δ < 8/9` is not needed for the argument. -/
theorem exists_sol_LZ_Om1_of_ball_one {δ : ℝ} (hδ : 0 < δ) (hδ89 : δ < 8 / 9) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball (1 : ℂ) δ))
    (hode : ∀ z ∈ Metric.ball (1 : ℂ) δ, LZ f z = 0) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Om1 ∧ (∀ z ∈ Om1, LZ F z = 0) ∧
      ∀ z ∈ Metric.ball (1 : ℂ) δ ∩ Om1, F z = f z := by
  -- ## a solution on each of the three convex pieces, seeded from `f` inside the ball
  obtain ⟨gA, hAd, hApA, hApA', -, hAL⟩ :=
    exists_sol_LZ_convex (Ω := upSet) isOpen_upSet convex_upSet
      (fun z hz => PZ_ne_zero_of_im_pos hz) (z₀ := PA δ) (PA_mem_up hδ) (f (PA δ))
      (deriv f (PA δ))
  obtain ⟨gB, hBd, hBpB, hBpB', -, hBL⟩ :=
    exists_sol_LZ_convex (Ω := dnSet) isOpen_dnSet convex_dnSet
      (fun z hz => PZ_ne_zero_of_im_neg hz) (z₀ := PB δ) (PB_mem_dn hδ) (f (PB δ))
      (deriv f (PB δ))
  obtain ⟨gC, hCd, hCpC, hCpC', -, hCL⟩ :=
    exists_sol_LZ_convex (Ω := rtSet) isOpen_rtSet convex_rtSet
      (fun z hz => PZ_ne_zero_of_re_gt_one hz) (z₀ := PU δ) (PU_mem_rt hδ) (f (PU δ))
      (deriv f (PU δ))
  -- ## each piece agrees with `f` on the part of the piece lying in the ball
  have hAf : Set.EqOn gA f (Metric.ball (1 : ℂ) δ ∩ upSet) :=
    eqOn_of_sol_LZ (U := Metric.ball (1 : ℂ) δ ∩ upSet)
      (Metric.isOpen_ball.inter isOpen_upSet)
      ((convex_ball (1 : ℂ) δ).inter convex_upSet).isPreconnected
      (fun z hz => PZ_ne_zero_of_im_pos hz.2)
      (hAd.mono Set.inter_subset_right) (hf.mono Set.inter_subset_left)
      (fun z hz => hAL z hz.2) (fun z hz => hode z hz.1)
      ⟨PA_mem_ball hδ, PA_mem_up hδ⟩ hApA hApA'
  have hBf : Set.EqOn gB f (Metric.ball (1 : ℂ) δ ∩ dnSet) :=
    eqOn_of_sol_LZ (U := Metric.ball (1 : ℂ) δ ∩ dnSet)
      (Metric.isOpen_ball.inter isOpen_dnSet)
      ((convex_ball (1 : ℂ) δ).inter convex_dnSet).isPreconnected
      (fun z hz => PZ_ne_zero_of_im_neg hz.2)
      (hBd.mono Set.inter_subset_right) (hf.mono Set.inter_subset_left)
      (fun z hz => hBL z hz.2) (fun z hz => hode z hz.1)
      ⟨PB_mem_ball hδ, PB_mem_dn hδ⟩ hBpB hBpB'
  have hCf : Set.EqOn gC f (Metric.ball (1 : ℂ) δ ∩ rtSet) :=
    eqOn_of_sol_LZ (U := Metric.ball (1 : ℂ) δ ∩ rtSet)
      (Metric.isOpen_ball.inter isOpen_rtSet)
      ((convex_ball (1 : ℂ) δ).inter convex_rtSet).isPreconnected
      (fun z hz => PZ_ne_zero_of_re_gt_one hz.2)
      (hCd.mono Set.inter_subset_right) (hf.mono Set.inter_subset_left)
      (fun z hz => hCL z hz.2) (fun z hz => hode z hz.1)
      ⟨PU_mem_ball hδ, PU_mem_rt hδ⟩ hCpC hCpC'
  -- ## the pieces are mutually consistent on the (convex) overlaps
  have hAC : Set.EqOn gA gC (upSet ∩ rtSet) :=
    Dzc_eqOn_of_agree_open (U := upSet ∩ rtSet)
      (V := Metric.ball (1 : ℂ) δ ∩ (upSet ∩ rtSet))
      (isOpen_upSet.inter isOpen_rtSet)
      (convex_upSet.inter convex_rtSet).isPreconnected
      (fun z hz => PZ_ne_zero_of_im_pos hz.1)
      (hAd.mono Set.inter_subset_left) (hCd.mono Set.inter_subset_right)
      (fun z hz => hAL z hz.1) (fun z hz => hCL z hz.2)
      (fun _ hz => hz.2)
      (Metric.isOpen_ball.inter (isOpen_upSet.inter isOpen_rtSet))
      ⟨PU δ, PU_mem_ball hδ, PU_mem_up hδ, PU_mem_rt hδ⟩
      (fun z hz => (hAf ⟨hz.1, hz.2.1⟩).trans (hCf ⟨hz.1, hz.2.2⟩).symm)
  have hBC : Set.EqOn gB gC (dnSet ∩ rtSet) :=
    Dzc_eqOn_of_agree_open (U := dnSet ∩ rtSet)
      (V := Metric.ball (1 : ℂ) δ ∩ (dnSet ∩ rtSet))
      (isOpen_dnSet.inter isOpen_rtSet)
      (convex_dnSet.inter convex_rtSet).isPreconnected
      (fun z hz => PZ_ne_zero_of_im_neg hz.1)
      (hBd.mono Set.inter_subset_left) (hCd.mono Set.inter_subset_right)
      (fun z hz => hBL z hz.1) (fun z hz => hCL z hz.2)
      (fun _ hz => hz.2)
      (Metric.isOpen_ball.inter (isOpen_dnSet.inter isOpen_rtSet))
      ⟨PL δ, PL_mem_ball hδ, PL_mem_dn hδ, PL_mem_rt hδ⟩
      (fun z hz => (hBf ⟨hz.1, hz.2.1⟩).trans (hCf ⟨hz.1, hz.2.2⟩).symm)
  -- ## glue the three pieces into a solution on the whole slit plane
  obtain ⟨F, hFd, hFL, hFA, hFB, hFC⟩ :=
    glue_three_LZ_Om1 (A := upSet) (B := dnSet) (C := rtSet)
      isOpen_upSet isOpen_dnSet isOpen_rtSet upSet_inter_dnSet Om1_subset_cover
      hAd hBd hCd hAL hBL hCL hAC hBC
  refine ⟨F, hFd, hFL, ?_⟩
  rintro z ⟨hzb, hzO⟩
  rcases Om1_subset_cover z hzO with h | h | h
  · exact (hFA h).trans (hAf ⟨hzb, h⟩)
  · exact (hFB h).trans (hBf ⟨hzb, h⟩)
  · exact (hFC h).trans (hCf ⟨hzb, h⟩)

end

end Work.A14D
