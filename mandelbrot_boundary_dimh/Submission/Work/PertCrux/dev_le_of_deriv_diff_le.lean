import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Pert.Ksub2.deriv_diff_le
import Submission.Work.Pert.Ksub2.Geom

/-!
# `Work.PertCrux.dev_le_of_deriv_diff_le`

The deviation bound for two Fatou coordinates of two near-translations `F`, `F₀` on a common ball
`Metric.ball c (2R)`, obtained by integrating the *derivative* comparison
`Work.Pert.Ksub2.deriv_diff_le`.

Both `Φ` and `Φ₀` are univalent Fatou coordinates of `F` resp. `F₀` on the ball of radius `2R`, and
`‖F w - (w+1)‖ < 1/4`, `‖F₀ w - (w+1)‖ < 1/4` there, with `‖F w - F₀ w‖ ≤ E`.  Shishikura's Lemma
A.2.4(i) (`MandelDim.FatouDerivEstimate`) gives

`‖deriv Φ z - deriv Φ₀ z‖ ≤ C'/R + 4E` for `z` in the smaller ball,

by comparing `deriv Φ z ≈ 1/(F z - z)` and `deriv Φ₀ z ≈ 1/(F₀ z - z)`.  Since `Φ - Φ₀` is
holomorphic on the (convex) ball `ball c R` and vanishes at `c`, the mean value inequality
`Work.Pert.Ksub2.dev_le_of_deriv_bound` upgrades this to

`‖Φ z - Φ₀ z‖ ≤ (C/R + 4E) ‖z - c‖`.

The constant is `C = max C' 1`, so that `C ≤ R` implies the hypothesis `C' ≤ R` of
`Ksub2.deriv_diff_le` (applied at each centre `w ∈ ball c R` with radius `R`, which is legitimate
because `ball w R ⊆ ball c (2R)`).
-/

namespace Work.PertCrux

open Metric

theorem dev_le_of_deriv_diff_le (hDE : MandelDim.FatouDerivEstimate) :
    ∃ C : ℝ, 0 < C ∧ ∀ {F F₀ Φ Φ₀ : ℂ → ℂ} {c : ℂ} {R E : ℝ},
      C ≤ R → 0 ≤ E →
      DifferentiableOn ℂ F (Metric.ball c (2 * R)) → DifferentiableOn ℂ F₀ (Metric.ball c (2 * R)) →
      MandelDim.IsFatouCoordOn F Φ (Metric.ball c (2 * R)) →
      MandelDim.IsFatouCoordOn F₀ Φ₀ (Metric.ball c (2 * R)) →
      (∀ w ∈ Metric.ball c (2 * R), ‖F w - (w + 1)‖ < 1 / 4) →
      (∀ w ∈ Metric.ball c (2 * R), ‖F₀ w - (w + 1)‖ < 1 / 4) →
      (∀ w ∈ Metric.ball c (2 * R), ‖F w - F₀ w‖ ≤ E) →
      Φ c = Φ₀ c →
      ∀ z ∈ Metric.ball c R, ‖Φ z - Φ₀ z‖ ≤ (C / R + 4 * E) * ‖z - c‖ := by
  obtain ⟨C', hC'pos, hC'⟩ := Work.Pert.Ksub2.deriv_diff_le hDE
  refine ⟨max C' 1, lt_of_lt_of_le zero_lt_one (le_max_right C' 1), ?_⟩
  intro F F₀ Φ Φ₀ c R E hCR hE hdF hdF₀ hΦ hΦ₀ hF1 hF01 hdist hagree z hz
  have hC'le : C' ≤ R := le_trans (le_max_left C' 1) hCR
  have hRpos : 0 < R := lt_of_lt_of_le hC'pos hC'le
  -- every radius-`R` ball centred in `ball c R` sits inside `ball c (2R)`
  have hsub_of : ∀ w ∈ Metric.ball c R, Metric.ball w R ⊆ Metric.ball c (2 * R) := by
    intro w hw u hu
    rw [Metric.mem_ball] at hu hw ⊢
    calc dist u c ≤ dist u w + dist w c := dist_triangle _ _ _
      _ < R + R := add_lt_add hu hw
      _ = 2 * R := by ring
  -- the derivative comparison, at every centre of the small ball
  have key : ∀ w ∈ Metric.ball c R, ‖deriv Φ w - deriv Φ₀ w‖ ≤ C' / R + 4 * E := by
    intro w hw
    have hsub := hsub_of w hw
    have hww : w ∈ Metric.ball w R := Metric.mem_ball_self hRpos
    have hnhds : Metric.ball w R ∈ nhds w := Metric.isOpen_ball.mem_nhds hww
    exact hC' (F := F) (F₀ := F₀) (Φ := Φ) (Φ₀ := Φ₀) (R := R) (E := E) (z := w)
      hC'le hE (hdF.mono hsub) (hdF₀.mono hsub)
      ⟨hΦ.1.mono hsub, hΦ.2.1.mono hsub,
        fun u hu hu' => hΦ.2.2 u (hsub hu) (hsub hu')⟩
      ⟨hΦ₀.1.mono hsub, hΦ₀.2.1.mono hsub,
        fun u hu hu' => hΦ₀.2.2 u (hsub hu) (hsub hu')⟩
      ((hΦ.1.mono hsub).differentiableAt hnhds) ((hΦ₀.1.mono hsub).differentiableAt hnhds)
      (fun u hu => hF1 u (hsub hu)) (fun u hu => hF01 u (hsub hu))
      (fun u hu => hdist u (hsub hu))
  have hKnn : 0 ≤ max C' 1 / R + 4 * E := by
    have h1 : 0 ≤ max C' 1 / R :=
      div_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_right C' 1))) (le_of_lt hRpos)
    linarith
  refine Work.Pert.Ksub2.dev_le_of_deriv_bound (Φ := Φ) (Φ₀ := Φ₀) (c := c) (r := R)
    (K := max C' 1 / R + 4 * E) hRpos hKnn ?_ ?_ hagree z hz
  · intro w hw
    have hw2 : w ∈ Metric.ball c (2 * R) := by
      rw [Metric.mem_ball] at hw ⊢
      linarith
    exact (hΦ.1.differentiableAt (Metric.isOpen_ball.mem_nhds hw2)).sub
      (hΦ₀.1.differentiableAt (Metric.isOpen_ball.mem_nhds hw2))
  · intro w hw
    have hw2 : w ∈ Metric.ball c (2 * R) := by
      rw [Metric.mem_ball] at hw ⊢
      linarith
    have hnhds : Metric.ball c (2 * R) ∈ nhds w := Metric.isOpen_ball.mem_nhds hw2
    have hderiv : deriv (fun u : ℂ => Φ u - Φ₀ u) w = deriv Φ w - deriv Φ₀ w := by
      change deriv (Φ - Φ₀) w = deriv Φ w - deriv Φ₀ w
      exact deriv_sub (hΦ.1.differentiableAt hnhds) (hΦ₀.1.differentiableAt hnhds)
    rw [hderiv]
    have h2 : C' / R ≤ max C' 1 / R :=
      div_le_div_of_nonneg_right (le_max_left C' 1) (le_of_lt hRpos)
    linarith [key w hw]

end Work.PertCrux
