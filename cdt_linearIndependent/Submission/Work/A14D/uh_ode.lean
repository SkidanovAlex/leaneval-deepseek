import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.uh_defs
import Submission.Work.A14D.uh_series_basic
import Submission.Work.A14D.uh_ode_w

/-!
# A14D — the holomorphic solution `u_h` of the Zagier operator at `x = 1`

The power series `uh = Σ aₙ (1−z)ⁿ` (`a = uhCoeff`) is the holomorphic solution of
`LZ y = 0` at `x = 1`, normalised by `uh 1 = 1`; it is holomorphic exactly on
`ball 1 (8/9)`.

The proof reduces to the same statement for the coefficient series `G0 w = Σ aₙ wⁿ`
(`Work.A14D.uh_ode_w`): after `z = 1 − w` the operator `LZ` becomes
`A(w)·y'' + B(w)·y' + C(w)·y` with `A = -8w+17w²-9w³`, `B = -8+34w-27w²`, `C = 6-9w`,
and `G0` is related to `uh` by the chain rules of `uh_deriv_transfer`.
-/

open Complex Metric

namespace Work.A14D

/-- Chain rules for the change of variable `z ↦ w = 1 - z` on the disc of convergence. -/
lemma uh_deriv_transfer (hG : DifferentiableOn ℂ G0 (Metric.ball 0 (8 / 9)))
    (hGd : DifferentiableOn ℂ (deriv G0) (Metric.ball 0 (8 / 9))) :
    ∀ z ∈ Metric.ball (1 : ℂ) (8 / 9),
      deriv uh z = -deriv G0 (1 - z) ∧ deriv (deriv uh) z = deriv (deriv G0) (1 - z) := by
  have hmem : ∀ z ∈ Metric.ball (1 : ℂ) (8 / 9), (1 : ℂ) - z ∈ Metric.ball 0 (8 / 9) := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    rw [sub_zero, norm_sub_rev]
    exact hz
  have h1 : ∀ z ∈ Metric.ball (1 : ℂ) (8 / 9), deriv uh z = -deriv G0 (1 - z) := by
    intro z hz
    have hd0 : HasDerivAt G0 (deriv G0 (1 - z)) (1 - z) :=
      (hG.differentiableAt (Metric.isOpen_ball.mem_nhds (hmem z hz))).hasDerivAt
    have hcomp : HasDerivAt (fun z' : ℂ => G0 (1 - z')) (deriv G0 (1 - z) * (-1)) z :=
      hd0.comp z ((hasDerivAt_id z).const_sub (1 : ℂ))
    rw [uh_eq_G0]
    simpa using hcomp.deriv
  intro z hz
  refine ⟨h1 z hz, ?_⟩
  have hev : deriv uh =ᶠ[nhds z] fun z' => -deriv G0 (1 - z') := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with z' hz'
    rw [h1 z' hz']
  rw [hev.deriv_eq]
  have hd0 : HasDerivAt (deriv G0) (deriv (deriv G0) (1 - z)) (1 - z) :=
    (hGd.differentiableAt (Metric.isOpen_ball.mem_nhds (hmem z hz))).hasDerivAt
  have hcomp : HasDerivAt (fun z' : ℂ => deriv G0 (1 - z')) (deriv (deriv G0) (1 - z) * (-1)) z :=
    hd0.comp z ((hasDerivAt_id z).const_sub (1 : ℂ))
  simpa using hcomp.neg.deriv

/-- Assembly: the `w`-variable ODE for the coefficient series `G0` gives the theorem. -/
private lemma uh_ode_of_w (hG : DifferentiableOn ℂ G0 (Metric.ball 0 (8 / 9)))
    (hGd : DifferentiableOn ℂ (deriv G0) (Metric.ball 0 (8 / 9)))
    (hodew : ∀ w : ℂ, ‖w‖ < 8 / 9 →
      ((-8 : ℂ) * w + 17 * w ^ 2 - 9 * w ^ 3) * deriv (deriv G0) w
        + ((-8 : ℂ) + 34 * w - 27 * w ^ 2) * deriv G0 w + (6 - 9 * w) * G0 w = 0) :
    DifferentiableOn ℂ uh (ball 1 (8 / 9)) ∧ uh 1 = 1 ∧
      ∀ z ∈ ball (1 : ℂ) (8 / 9), LZ uh z = 0 := by
  have hmem : ∀ z ∈ Metric.ball (1 : ℂ) (8 / 9), (1 : ℂ) - z ∈ Metric.ball 0 (8 / 9) := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    rw [sub_zero, norm_sub_rev]
    exact hz
  have hnorm : ∀ z ∈ Metric.ball (1 : ℂ) (8 / 9), ‖(1 : ℂ) - z‖ < 8 / 9 := by
    intro z hz
    have h := hmem z hz
    rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at h
  have h1 : ∀ z ∈ Metric.ball (1 : ℂ) (8 / 9), deriv uh z = -deriv G0 (1 - z) :=
    fun z hz => (uh_deriv_transfer hG hGd z hz).1
  have h2 : ∀ z ∈ Metric.ball (1 : ℂ) (8 / 9), deriv (deriv uh) z = deriv (deriv G0) (1 - z) :=
    fun z hz => (uh_deriv_transfer hG hGd z hz).2
  refine ⟨?_, ?_, ?_⟩
  · rw [uh_eq_G0]
    exact hG.comp ((differentiableOn_const (c := (1 : ℂ))).sub differentiableOn_id)
      (fun z hz => hmem z hz)
  · rw [uh]
    rw [tsum_eq_single 0]
    · norm_num [uhCoeff]
    · intro n hn
      rw [show (1 : ℂ) - 1 = 0 by norm_num, zero_pow hn, mul_zero]
  · intro z hz
    have hode := hodew (1 - z) (hnorm z hz)
    have hkey : PZ z * deriv (deriv G0) (1 - z) + PZ' z * (-deriv G0 (1 - z))
          + RZ z * G0 (1 - z)
        = ((-8 : ℂ) * (1 - z) + 17 * (1 - z) ^ 2 - 9 * (1 - z) ^ 3)
            * deriv (deriv G0) (1 - z)
          + ((-8 : ℂ) + 34 * (1 - z) - 27 * (1 - z) ^ 2) * deriv G0 (1 - z)
          + (6 - 9 * (1 - z)) * G0 (1 - z) := by
      simp only [PZ, PZ', RZ]; ring
    simp only [LZ, h1 z hz, h2 z hz, congrFun uh_eq_G0 z, hkey]
    exact hode

theorem uh_ode : DifferentiableOn ℂ uh (ball 1 (8 / 9)) ∧ uh 1 = 1 ∧ ∀ z ∈ ball (1 : ℂ) (8 / 9), LZ uh z = 0 := by
  obtain ⟨_, hG, hGd, _, _, _, _, _⟩ := uh_series_basic
  exact uh_ode_of_w hG hGd uh_ode_w

end Work.A14D
