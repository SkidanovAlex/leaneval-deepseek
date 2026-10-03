import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Gates
import Submission.Work.Pert.Qm_slice
import Submission.Work.Pert.image_cover_centered
import Submission.Work.Interfaces.Fatou
import Submission.Work.Pert.pert2v2.waist_window_cover_margin

namespace Work.Pert.pert2v2

open MandelDim

/-- The lower gate `Qm ξ α` is open (reproduced locally; the copies in the sibling files are
`private`). -/
private lemma isOpen_Qm_dev (ξ : ℝ) (α : ℂ) : IsOpen (Work.Pert.Qm ξ α) := by
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

/-- **Window covering with a pointwise deviation hypothesis.**

For every `Ξ` and every `R₂ > 0` there is a height threshold `Hthr > 0` such that, for every
`α ∈ 𝓕₁`, every `Φ` differentiable on the gate `Qm Ξ α` whose derivative is within `1/2` of `1`
on every disc of radius `≥ R₂` inside the gate (`injectivity scale`), and every window point `w`
(`|Re w| < 1`) at height `|Im w| ≥ Hthr` whose *value* deviation is small
(`‖Φ w - w‖ < |Im w| / 32`), the point `w` is the image under `Φ` of some `ς` inside the **waist**
`Qm Ξ α ∩ Qp Ξ α`, with the margin `|ς.re| + 2 < |ς.im| - Ξ`.

The argument is the one of `waist_window_cover_margin`, with the growth bound at the centre
replaced by the pointwise hypothesis (which is all that the centre estimate uses):

* `t := |Im w|`, `r := t/8`; the threshold guarantees `1 + Ξ ≤ t/2` (gate opening) and `R₂ ≤ r`.
* `ball w (t/4) ⊆ Qm Ξ α ∩ Qp Ξ α` (`ball_subset_waist_center`), hence
  `closedBall w r ⊆` the waist and `ball ζ r ⊆ Qm Ξ α` for `ζ ∈ closedBall w r`.
* So `‖deriv Φ - 1‖ ≤ 1/2` on `closedBall w r` and, by the quarter-ball covering
  (`image_cover_centered`), `ball (Φ w) (r/4) ⊆ Φ '' closedBall w r`.
* The pointwise deviation places `w` in `ball (Φ w) (r/4)` (since `r/4 = t/32`), so `w = Φ ς` for
  some `ς ∈ closedBall w r ⊆` waist.
* The margin is the remaining purely geometric part: enlarging `Hthr` makes
  `3 + Ξ < 3t/4`, which together with `|ς.re| < 1 + t/8` and `|ς.im| ≥ 7t/8` gives
  `|ς.re| + 2 < |ς.im| - Ξ`. -/
theorem window_cover_dev {Ξ R₂ : ℝ} (hR₂ : 0 < R₂) :
    ∃ Hthr : ℝ, 0 < Hthr ∧ ∀ (α : ℂ) (Φ : ℂ → ℂ), MandelDim.InF1 α →
      DifferentiableOn ℂ Φ (Work.Pert.Qm Ξ α) →
      (∀ (z : ℂ) (R : ℝ), R₂ ≤ R → Metric.ball z R ⊆ Work.Pert.Qm Ξ α →
        ‖deriv Φ z - 1‖ ≤ 1 / 2) →
      ∀ w : ℂ, |w.re| < 1 → Hthr ≤ |w.im| → ‖Φ w - w‖ < |w.im| / 32 →
        ∃ ς ∈ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α, Φ ς = w ∧ |ς.re| + 2 < |ς.im| - Ξ := by
  -- the α- and Φ-independent height threshold of `waist_threshold` (with `A = C = 0`, since we
  -- only need the geometric part `1 + Ξ ≤ t/2`, `R₂ ≤ t/8`)
  obtain ⟨H, hHpos, hthr⟩ :=
    waist_threshold (Ξ := Ξ) (A := 0) (C := 0) (R₂ := R₂) le_rfl le_rfl hR₂
  -- enlarge it (also by `1`, since `Ξ` may be negative) so that `t ≥ Hthr` forces both the
  -- gate opening `1 + Ξ ≤ t/2` and the strict margin condition `3 + Ξ < 3t/4`
  refine ⟨max H (max 1 (4 * (Ξ + 3) / 3 + 1)), ?_, ?_⟩
  · refine lt_of_lt_of_le zero_lt_one (le_trans (le_max_left 1 _) (le_max_right H _))
  intro α Φ hInF1 hdiffOn hderΦ w hwre hwim hdevw
  -- the height `t = |Im w|` and the radius `r = t/8`
  set t : ℝ := |w.im| with ht
  have htH : H ≤ t := le_trans (le_max_left H _) hwim
  have htbig : 4 * (Ξ + 3) / 3 + 1 ≤ t :=
    le_trans (le_trans (le_max_right 1 _) (le_max_right H _)) hwim
  obtain ⟨hgeom, hR₂le, _hdev_thr⟩ := hthr t htH
  have htpos : 0 < t := lt_of_lt_of_le hHpos htH
  -- the margin condition `3 + Ξ < 3 t / 4`
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
    exact hdiffOn.differentiableAt ((isOpen_Qm_dev Ξ α).mem_nhds (hsub hζ).1)
  -- ## the quarter-ball covering
  have hcov : Metric.ball (Φ w) (r / 4) ⊆ Φ '' Metric.closedBall w r :=
    Work.Pert.image_cover_centered hrpos hdiff hder
  -- ## the pointwise deviation at the centre: `‖Φ w - w‖ < t/32 = r/4`
  have hdevw' : ‖Φ w - w‖ < t / 32 := by
    rw [ht]; exact hdevw
  have hwmem : w ∈ Metric.ball (Φ w) (r / 4) := by
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
    have h32 : r / 4 = t / 32 := by rw [hr]; ring
    rw [h32]
    exact hdevw'
  -- ## the preimage lies in the small disc inside the waist
  obtain ⟨ς, hςball, hςeq⟩ := hcov hwmem
  refine ⟨ς, hsub hςball, hςeq, ?_⟩
  have hςdist : ‖ς - w‖ ≤ r := by
    have h := hςball
    rw [Metric.mem_closedBall, dist_eq_norm] at h
    exact h
  -- ## the margin
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
