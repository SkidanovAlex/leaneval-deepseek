import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Gates
import Submission.Work.Pert.Qm_slice
import Submission.Work.Pert.pert2v2.waist_window_cover
import Submission.Work.Interfaces.Fatou

/-!
# `pert2v2.waist_window_cover_margin`

This is the **margin** refinement of `Work.Pert.pert2v2.waist_window_cover`.  That theorem
produces, for every window point `w` (`|Re w| < 1`, `|Im w|` large), a point
`ς ∈ Qm Ξ α ∩ Qp Ξ α` with `Φ ς = w`.  Here we additionally demand that `ς` lies **strictly
inside** the waist, with a fixed margin `2`:

  `|ς.re| + 2 < |ς.im| - Ξ`.

Since `Qm Ξ α ∩ Qp Ξ α = {|Re z| < |Im z| - Ξ}`, a point on the boundary of that window would
not qualify; but the covering argument actually places `ς` in the *small* disc
`closedBall w (t/8)` (`t = |Im w|`), and every point of that disc enjoys the margin as soon as
`t` exceeds a second, purely geometric threshold.  We are free to enlarge `Hthr`, so we take

  `Hthr = max H (4 (Ξ + 3) / 3 + 1)`,

where `H` is the threshold of `waist_threshold`.  -/

namespace Work.Pert.pert2v2

open MandelDim

/-- The lower gate `Qm ξ α` is open (reproduced locally; the copy in `waist_window_cover` is
`private`). -/
private lemma isOpen_Qm_margin (ξ : ℝ) (α : ℂ) : IsOpen (Work.Pert.Qm ξ α) := by
  have h1 : IsOpen {z : ℂ | -|(z - ((ξ : ℂ) - 1 / α)).im| < (z - ((ξ : ℂ) - 1 / α)).re} :=
    isOpen_lt (continuous_abs.comp
        (Complex.continuous_im.comp (continuous_id.sub continuous_const))).neg
      (Complex.continuous_re.comp (continuous_id.sub continuous_const))
  have h2 : IsOpen {z : ℂ | (z - (-(ξ : ℂ))).re < |(z - (-(ξ : ℂ))).im|} :=
    isOpen_lt (Complex.continuous_re.comp (continuous_id.sub continuous_const))
      (continuous_abs.comp
        (Complex.continuous_im.comp (continuous_id.sub continuous_const)))
  have h3 : Work.Pert.Qm ξ α =
      {z : ℂ | -|(z - ((ξ : ℂ) - 1 / α)).im| < (z - ((ξ : ℂ) - 1 / α)).re} ∩
        {z : ℂ | (z - (-(ξ : ℂ))).re < |(z - (-(ξ : ℂ))).im|} := by
    ext z
    simp [Work.Pert.Qm, MandelDim.Qreg]
  rw [h3]
  exact h1.inter h2

theorem waist_window_cover_margin {Ξ A C R₂ : ℝ} (hΞ : 0 < Ξ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hR₂ : 0 < R₂) :
    ∃ Hthr : ℝ, 0 < Hthr ∧ ∀ (α : ℂ) (Φ : ℂ → ℂ), MandelDim.InF1 α →
      MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) →
      MandelDim.QAdm (some (Ξ : ℂ)) (some (-(Ξ : ℂ) + 1 / α)) →
      DifferentiableOn ℂ Φ (Work.Pert.Qm Ξ α) →
      (∀ (z : ℂ) (R : ℝ), R₂ ≤ R → Metric.ball z R ⊆ Work.Pert.Qm Ξ α →
        ‖deriv Φ z - 1‖ ≤ 1 / 2) →
      (∀ z : ℂ, Metric.ball z R₂ ⊆ Work.Pert.Qm Ξ α →
        ‖Φ z - z‖ ≤ A * Real.log (‖z‖ + 2) + C + ‖z‖ / 64) →
      ∀ w : ℂ, |w.re| < 1 → Hthr ≤ |w.im| →
        ∃ ς ∈ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α, Φ ς = w ∧ |ς.re| + 2 < |ς.im| - Ξ := by
  -- the α- and Φ-independent height threshold of `waist_window_cover`, enlarged so that
  -- `t ≥ Hthr` also forces `3 + Ξ < 3 t / 4` (which is what the margin condition needs)
  obtain ⟨H, _hHpos, hthr⟩ := waist_threshold (Ξ := Ξ) hA hC hR₂
  refine ⟨max H (4 * (Ξ + 3) / 3 + 1), ?_, ?_⟩
  · have hpos : 0 < 4 * (Ξ + 3) / 3 + 1 := by linarith
    exact lt_max_iff.mpr (Or.inr hpos)
  intro α Φ hInF1 _hQAdm₁ _hQAdm₂ hdiffOn hderΦ hdevΦ w hwre hwim
  -- the height `t = |Im w|` and the radius `r = t/8`
  set t : ℝ := |w.im| with ht
  have htH : H ≤ t := le_trans (le_max_left _ _) hwim
  have htbig : 4 * (Ξ + 3) / 3 + 1 ≤ t := le_trans (le_max_right _ _) hwim
  obtain ⟨hgeom, hR₂le, hdev_thr⟩ := hthr t htH
  have htpos : 0 < t := by linarith
  -- the geometric margin: `3 + Ξ < 3 t / 4`
  have hmargin : 3 + Ξ < 3 * t / 4 := by linarith
  set r : ℝ := t / 8 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  have hR₂r : R₂ ≤ r := by rw [hr]; exact hR₂le
  -- ## the waist disc around the centre `w`
  have hball4 : Metric.ball w (t / 4) ⊆ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α :=
    ball_subset_waist_center (Ξ := Ξ) (T := t) (α := α) (w := w)
      hInF1 hwre ht.symm hgeom
  have hsub : Metric.closedBall w r ⊆ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α := by
    intro z hz
    refine hball4 ?_
    rw [Metric.mem_ball]
    have h1 : dist z w ≤ r := by rwa [Metric.mem_closedBall] at hz
    linarith
  -- ## `‖deriv Φ - 1‖ ≤ 1/2` on `closedBall w r`
  have hder : ∀ ζ ∈ Metric.closedBall w r, ‖deriv Φ ζ - 1‖ ≤ 1 / 2 := by
    intro ζ hζ
    refine hderΦ ζ r hR₂r ?_
    intro z hz
    rw [Metric.mem_ball] at hz
    have h1 : dist ζ w ≤ r := by rwa [Metric.mem_closedBall] at hζ
    refine (hball4 ?_).1
    rw [Metric.mem_ball]
    calc dist z w ≤ dist z ζ + dist ζ w := dist_triangle _ _ _
      _ < r + r := by linarith
      _ = t / 4 := by rw [hr]; ring
  have hdiff : ∀ ζ ∈ Metric.closedBall w r, DifferentiableAt ℂ Φ ζ := by
    intro ζ hζ
    exact hdiffOn.differentiableAt ((isOpen_Qm_margin Ξ α).mem_nhds (hsub hζ).1)
  -- ## the quarter-ball covering
  have hcov : Metric.ball (Φ w) (r / 4) ⊆ Φ '' Metric.closedBall w r :=
    Work.Pert.image_cover_centered hrpos hdiff hder
  -- ## the deviation at the centre: `‖Φ w - w‖ < t/32 = r/4`
  have hdevw : ‖Φ w - w‖ < t / 32 := by
    refine dev_at_center_lt (A := A) (C := C) (T := t) (Φ := Φ) (w := w)
      hA hwre ht.symm hdev_thr ?_
    refine hdevΦ w ?_
    intro z hz
    rw [Metric.mem_ball] at hz
    refine (hball4 ?_).1
    rw [Metric.mem_ball]
    calc dist z w < R₂ := hz
      _ ≤ t / 8 := hR₂le
      _ < t / 4 := by linarith
  have hwmem : w ∈ Metric.ball (Φ w) (r / 4) := by
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
    have h32 : r / 4 = t / 32 := by rw [hr]; ring
    rw [h32]
    exact hdevw
  -- ## the preimage lies in the small disc
  obtain ⟨ς, hςball, hςeq⟩ := hcov hwmem
  refine ⟨ς, hsub hςball, hςeq, ?_⟩
  -- ## the margin
  have hςdist : ‖ς - w‖ ≤ r := by
    have h := hςball
    rw [Metric.mem_closedBall, dist_eq_norm] at h
    exact h
  have hre : |ς.re| < 1 + t / 8 := by
    have h2 : |ς.re| ≤ |w.re| + |ς.re - w.re| := by
      have h := abs_sub_abs_le_abs_sub ς.re w.re
      linarith
    have h3 : |ς.re - w.re| ≤ ‖ς - w‖ := by simpa using Complex.abs_re_le_norm (ς - w)
    rw [hr] at hςdist
    linarith
  have him : 7 * t / 8 ≤ |ς.im| := by
    have h4 : |w.im| - |ς.im - w.im| ≤ |ς.im| := by
      have h := abs_sub_abs_le_abs_sub w.im ς.im
      rw [abs_sub_comm w.im ς.im] at h
      linarith
    have h5 : |ς.im - w.im| ≤ ‖ς - w‖ := by simpa using Complex.abs_im_le_norm (ς - w)
    rw [← ht] at h4
    rw [hr] at hςdist
    linarith
  linarith

end Work.Pert.pert2v2
