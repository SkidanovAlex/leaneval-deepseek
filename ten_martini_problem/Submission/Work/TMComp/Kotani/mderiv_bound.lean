import Mathlib
import Submission.Work.TMComp.Kotani.EllDerivDefs

/-!
# C8 (Kotani theory): a uniform bound for the energy-derivative of `m`

By Cauchy's estimate on a disc of radius `ε/4` around `E₀ + iu`, together with the uniform
bound `mfun_norm_le` for the `m`-function, `∂_E m(E,y)` is bounded uniformly in the phase `y`
and in the energy `E = E₀ + iu` with `ε/2 < u < 2ε`.
-/

open MeasureTheory Filter Topology Set
open Work.TMComp.Kotani
open Work.TMComp.Kotani.MfunProbs

noncomputable section

namespace Work.TMComp.Kotani

theorem mderiv_bound (α lam : ℝ) (E₀ ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ u : ℝ, ε / 2 < u → u < 2 * ε → ∀ y : ℝ,
      ‖mderiv α lam ((E₀ : ℂ) + (u : ℂ) * Complex.I) y‖ ≤ C := by
  refine ⟨max 1 (‖E₀‖ + 2*ε + ε/4 + 2*|lam| + 1/min (ε/4) 1) / (ε/4), ?_⟩
  have hρ : 0 < ε/4 := by linarith
  have hh : 0 < min (ε/4) 1 := lt_min hρ one_pos
  have h1 : min (ε/4) 1 ≤ 1 := min_le_right _ _
  have hminle : min (ε/4) 1 ≤ ε/4 := min_le_left _ _
  intro u hu1 hu2 y
  have hu : 0 < u := by linarith
  have hEim : ((E₀:ℂ) + (u:ℂ)*Complex.I).im = u := by simp
  have hsub : Metric.closedBall ((E₀:ℂ) + (u:ℂ)*Complex.I) (ε/4) ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have h1' := Complex.abs_im_le_norm (z - ((E₀:ℂ) + (u:ℂ)*Complex.I))
    have ha := (abs_le.mp (le_trans h1' hz)).1
    rw [Complex.sub_im, hEim] at ha
    change 0 < z.im
    linarith
  have hdc : DiffContOnCl ℂ (fun z : ℂ => mfun α lam z y)
      (Metric.ball ((E₀:ℂ) + (u:ℂ)*Complex.I) (ε/4)) :=
    (mfun_differentiableOn α lam y).diffContOnCl_ball hsub
  have hC : ∀ z ∈ Metric.sphere ((E₀:ℂ) + (u:ℂ)*Complex.I) (ε/4),
      ‖mfun α lam z y‖ ≤ max 1 (‖E₀‖ + 2*ε + ε/4 + 2*|lam| + 1/min (ε/4) 1) := by
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    have hzim : min (ε/4) 1 ≤ z.im := by
      have h1' := Complex.abs_im_le_norm (z - ((E₀:ℂ) + (u:ℂ)*Complex.I))
      have ha := (abs_le.mp (le_trans h1' (le_of_eq hz))).1
      rw [Complex.sub_im, hEim] at ha
      linarith
    have hznorm : ‖z‖ ≤ ‖E₀‖ + 2 * ε + ε/4 := by
      have h3 : ‖z‖ ≤ ‖(E₀:ℂ) + (u:ℂ)*Complex.I‖ + ε/4 := by
        calc ‖z‖ = ‖((E₀:ℂ) + (u:ℂ)*Complex.I) + (z - ((E₀:ℂ) + (u:ℂ)*Complex.I))‖ := by ring_nf
          _ ≤ _ + ‖z - ((E₀:ℂ) + (u:ℂ)*Complex.I)‖ := norm_add_le _ _
          _ = _ + ε/4 := by rw [hz]
      have h4 : ‖(E₀:ℂ) + (u:ℂ)*Complex.I‖ ≤ ‖E₀‖ + 2 * ε := by
        calc ‖(E₀:ℂ) + (u:ℂ)*Complex.I‖ ≤ ‖(E₀:ℂ)‖ + ‖(u:ℂ)*Complex.I‖ := norm_add_le _ _
          _ = ‖E₀‖ + |u| := by simp
          _ ≤ ‖E₀‖ + 2 * ε := by
              have : |u| ≤ 2 * ε := by rw [abs_of_pos hu]; linarith
              linarith
      linarith
    calc ‖mfun α lam z y‖ ≤ max 1 (‖z‖ + 2 * |lam| + 1 / min (ε/4) 1) :=
          mfun_norm_le α lam hh h1 hzim y
      _ ≤ max 1 (‖E₀‖ + 2*ε + ε/4 + 2*|lam| + 1/min (ε/4) 1) := by
          apply max_le_max_left
          have hp : 0 < min (ε/4) 1 := hh
          have : 1 / min (ε/4) 1 ≤ 1 / min (ε/4) 1 := le_rfl
          linarith
  have hbd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := fun z : ℂ => mfun α lam z y)
    (c := (E₀:ℂ) + (u:ℂ)*Complex.I) (R := ε/4) (C := max 1 (‖E₀‖ + 2*ε + ε/4 + 2*|lam| + 1/min (ε/4) 1))
    hρ hdc hC
  calc ‖mderiv α lam ((E₀:ℂ) + (u:ℂ)*Complex.I) y‖
      = ‖deriv (fun z : ℂ => mfun α lam z y) ((E₀:ℂ) + (u:ℂ)*Complex.I)‖ := rfl
    _ ≤ max 1 (‖E₀‖ + 2*ε + ε/4 + 2*|lam| + 1/min (ε/4) 1) / (ε/4) := hbd

end Work.TMComp.Kotani
