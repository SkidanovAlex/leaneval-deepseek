import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.AsmDefs
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Gates
import Submission.Work.Pert.Qm_slice
import Submission.Work.Pert.image_cover_centered
import Submission.Work.Pert.pert2v2.waist_threshold
import Submission.Work.Pert.pert2v2.ball_subset_waist_center
import Submission.Work.Pert.pert2v2.dev_at_center_lt

/-! Guidance from the project lead (the requester):

LEAD (pert2_v2 skeleton item S11). Every window point at large height lies in the waist image of a Fatou coordinate with the pinned deviation bound. Hthr is chosen BEFORE α and Φ (it depends only on Ξ, A, C, R₂).
Route:
  - Fix w with |Re w| < 1 and t := |Im w| ≥ Hthr. Put r := t/8.
  - By Work.Pert.Qm_inter_Qp (InF1 ⇒ waist = {|Re z| < |Im z| − Ξ}), ball w r ⊆ Qm ∩ Qp, and every z ∈ ball w r has ball z (t/8) ⊆ Qm. This needs 1 + t/4 < 3t/4 − Ξ and t/8 ≥ R₂, both true for Hthr large.
  - So ‖deriv Φ − 1‖ ≤ 1/2 on ball w r.
  - The quarter-ball covering (Work.Pert.image_cover_centered) gives Φ '' ball w r ⊇ ball (Φ w) (r/4).
  - The dev bound at w gives ‖Φ w − w‖ ≤ A log(t + 3) + C + (t+1)/64 < t/32 = r/4 for Hthr large (log is sublinear). So w ∈ ball (Φ w) (r/4) ⊆ Φ '' ball w r ⊆ Φ '' (Qm ∩ Qp).
Reuse: Pert/CoverHigh/cover_anchor.lean, waist_cover_window.lean, PinFromCoord/gate_aux.lean (ball_subset_Qm_of_bounds) for the geometry.
-/

/-! ## The proof, in one page

Fix `Ξ, A, C, R₂` with `A, C ≥ 0`, `R₂ > 0`, and let `Hthr` be the (α- and Φ-independent)
threshold supplied by `Work.Pert.pert2v2.waist_threshold`: for `t ≥ Hthr`

  `1 + Ξ ≤ t/2`,  `R₂ ≤ t/8`,  `A log (t+3) + C + (t+1)/64 < t/32`.

Given `α ∈ 𝓕₁`, `Φ` differentiable on the gate `Qm Ξ α` with `‖Φ' - 1‖ ≤ 1/2` on every disc of
radius `≥ R₂` inside the gate, and `‖Φ z - z‖ ≤ A log(‖z‖+2) + C + ‖z‖/64` on such discs, take
`w` with `|Re w| < 1` and `t := |Im w| ≥ Hthr`.

* **Geometry.**  `Work.Pert.pert2v2.ball_subset_waist_center` (which is the waist description
  `Qm ∩ Qp = {|Re| < |Im| - Ξ}` plus the two elementary estimates
  `|z.re| < 1 + t/4`, `|z.im| > 3t/4` on `ball w (t/4)`) shows
  `ball w (t/4) ⊆ Qm Ξ α ∩ Qp Ξ α`; this is exactly where `1 + Ξ ≤ t/2` is used.
* **The derivative bound.**  With `r := t/8`, `R₂ ≤ r`, and for `ζ ∈ closedBall w r` the disc
  `ball ζ r` lies in `ball w (t/4) ⊆ Qm Ξ α`, so the hypothesis gives `‖deriv Φ ζ - 1‖ ≤ 1/2`
  there.  Differentiability at `ζ` follows from `DifferentiableOn Φ (Qm Ξ α)` and openness.
* **Covering.**  `Work.Pert.image_cover_centered` then yields
  `ball (Φ w) (r/4) ⊆ Φ '' closedBall w r ⊆ Φ '' (Qm Ξ α ∩ Qp Ξ α)`.
* **The centre is reached.**  `Work.Pert.pert2v2.dev_at_center_lt` turns the deviation bound at
  `w` (legal since `ball w R₂ ⊆ ball w (t/4) ⊆ Qm Ξ α`) into `‖Φ w - w‖ < t/32 = r/4`, i.e.
  `w ∈ ball (Φ w) (r/4)`.

Chaining the last two lines gives `w ∈ Φ '' (Qm Ξ α ∩ Qp Ξ α)`. -/

namespace Work.Pert.pert2v2

open MandelDim

/-- The lower gate `Qm ξ α` is open: it is the intersection of the two open half-planes
`-|(z - b₁).im| < (z - b₁).re` and `(z - b₂).re < |(z - b₂).im|`. -/
private lemma isOpen_Qm (ξ : ℝ) (α : ℂ) : IsOpen (Work.Pert.Qm ξ α) := by
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

theorem waist_window_cover {Ξ A C R₂ : ℝ} (hΞ : 0 < Ξ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hR₂ : 0 < R₂) :
    ∃ Hthr : ℝ, ∀ (α : ℂ) (Φ : ℂ → ℂ), MandelDim.InF1 α →
      MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) →
      MandelDim.QAdm (some (Ξ : ℂ)) (some (-(Ξ : ℂ) + 1 / α)) →
      DifferentiableOn ℂ Φ (Work.Pert.Qm Ξ α) →
      (∀ (z : ℂ) (R : ℝ), R₂ ≤ R → Metric.ball z R ⊆ Work.Pert.Qm Ξ α →
        ‖deriv Φ z - 1‖ ≤ 1 / 2) →
      (∀ z : ℂ, Metric.ball z R₂ ⊆ Work.Pert.Qm Ξ α →
        ‖Φ z - z‖ ≤ A * Real.log (‖z‖ + 2) + C + ‖z‖ / 64) →
      ∀ w : ℂ, |w.re| < 1 → Hthr ≤ |w.im| →
        w ∈ Φ '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) := by
  -- the α- and Φ-independent height threshold
  obtain ⟨Hthr, hHthrpos, hthr⟩ := waist_threshold (Ξ := Ξ) hA hC hR₂
  refine ⟨Hthr, ?_⟩
  intro α Φ hInF1 _hQAdm₁ _hQAdm₂ hdiffOn hderΦ hdevΦ w hwre hwim
  -- the height `t = |Im w|` and the radius `r = t/8`
  set t : ℝ := |w.im| with ht
  have htH : Hthr ≤ t := by rw [ht]; exact hwim
  obtain ⟨hgeom, hR₂le, hdev_thr⟩ := hthr t htH
  have htpos : 0 < t := lt_of_lt_of_le hHthrpos htH
  set r : ℝ := t / 8 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  have hrt4 : r < t / 4 := by rw [hr]; linarith
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
    exact hdiffOn.differentiableAt (isOpen_Qm Ξ α |>.mem_nhds (hsub hζ).1)
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
  exact Set.image_mono hsub (hcov hwmem)

end Work.Pert.pert2v2
