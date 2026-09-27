import Mathlib
import Submission.Work.Drive.no_small_squares
import Submission.Work.Drive.curve_deriv_ne_zero
import Submission.Work.Drive.exists_uniform_local_monotone

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold
open Submission.Geometry (eucDot eucNorm)

/-- **The secant length grows at least like the tangent length.**

For a smooth embedded closed plane curve `curve γ t = γ (Circle.exp t)` and every parameter `t`
there is `δ > 0` such that for all `0 < s < δ` the (Euclidean) length of the secant joining
`curve γ (t - s)` to `curve γ (t + s)` is at least `s` times the (Euclidean) length of the
tangent `curve γ' t`.

Indeed, with `e = curve γ' t` and `c = ‖e‖ > 0` (the tangent never vanishes for an immersion),
the derivative bounds of `nss_exists_local_deriv_bounds` give
`(15/16) c² ≤ ⟪curve γ' u, e⟫` on a neighbourhood of `t`; the mean value inequality
`nss_mul_sub_le_sub_of_le_deriv` applied to `u ↦ ⟪curve γ u, e⟫` on the two intervals `[t, t+s]`
and `[t-s, t]` then yields
`(15/8) c² s ≤ ⟪curve γ (t+s) - curve γ (t-s), e⟫`, and Cauchy–Schwarz
(`nss_eucDot_cauchy`) bounds the right hand side by `‖curve γ (t+s) - curve γ (t-s)‖ · c`. -/
theorem secant_len_lower (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (t : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      Submission.Geometry.eucNorm (deriv (Work.Drive.curve γ) t) * s
        ≤ Submission.Geometry.eucNorm (Work.Drive.curve γ (t + s) - Work.Drive.curve γ (t - s)) := by
  have hC1 : ContDiff ℝ 1 (curve γ) := nss_contDiff_one_curve hγ
  obtain ⟨δ, hδpos, hδ⟩ := nss_exists_local_deriv_bounds (γ := γ) hγ t
  refine ⟨δ, hδpos, ?_⟩
  intro s hs0 hsδ
  set e : ℝ × ℝ := deriv (curve γ) t with he
  set c : ℝ := eucNorm e with hc
  have hcpos : 0 < c := by
    rw [hc, he]
    exact Submission.Geometry.eucNorm_pos (curve_deriv_ne_zero γ hγ t)
  -- the derivative of `u ↦ ⟪curve γ u, e⟫`
  have hderiv : ∀ u : ℝ,
      deriv (fun x => eucDot (curve γ x) e) u = eucDot (deriv (curve γ) u) e :=
    fun u => deriv_eucDot_curve_const hC1 e u
  -- the derivative bound `(15/16) c² ≤ φ'` on a neighbourhood of `t`
  have hbnd : ∀ u : ℝ, |u - t| < δ → (15 / 16) * c ^ 2 ≤ eucDot (deriv (curve γ) u) e := by
    intro u hu
    have h := (hδ u hu).1
    rw [hc, he]
    exact h
  -- mean value inequality on `[t, t+s]`
  have hA := nss_mul_sub_le_sub_of_le_deriv (φ := fun x => eucDot (curve γ x) e)
    (s := t) (t := t + s) (c := (15 / 16) * c ^ 2) (by linarith)
    (nss_continuousOn_eucDot_curve hC1 e t (t + s))
    (fun u _ => nss_differentiableAt_eucDot_curve hC1 e u)
    (fun u hu => by
      rw [hderiv u]
      exact hbnd u (by
        rw [abs_lt]
        exact ⟨by linarith [hu.1, hδpos], by linarith [hu.2, hsδ]⟩))
  -- mean value inequality on `[t-s, t]`
  have hB := nss_mul_sub_le_sub_of_le_deriv (φ := fun x => eucDot (curve γ x) e)
    (s := t - s) (t := t) (c := (15 / 16) * c ^ 2) (by linarith)
    (nss_continuousOn_eucDot_curve hC1 e (t - s) t)
    (fun u _ => nss_differentiableAt_eucDot_curve hC1 e u)
    (fun u hu => by
      rw [hderiv u]
      exact hbnd u (by
        rw [abs_lt]
        exact ⟨by linarith [hu.1, hsδ], by linarith [hu.2, hδpos]⟩))
  have hA' : (15 / 16) * c ^ 2 * s ≤ eucDot (curve γ (t + s)) e - eucDot (curve γ t) e := by
    simpa using hA
  have hB' : (15 / 16) * c ^ 2 * s ≤ eucDot (curve γ t) e - eucDot (curve γ (t - s)) e := by
    simpa using hB
  -- the secant has a large component along the tangent
  have hval : (15 / 8) * c ^ 2 * s ≤ eucDot (curve γ (t + s) - curve γ (t - s)) e := by
    rw [nss_eucDot_sub_left]
    linarith [hA', hB']
  -- Cauchy–Schwarz turns this into a lower bound for the Euclidean length
  have hcs := nss_eucDot_cauchy (curve γ (t + s) - curve γ (t - s)) e
  have hle : eucDot (curve γ (t + s) - curve γ (t - s)) e
      ≤ eucNorm (curve γ (t + s) - curve γ (t - s)) * c := by
    have h1 : eucDot (curve γ (t + s) - curve γ (t - s)) e
        ≤ |eucDot (curve γ (t + s) - curve γ (t - s)) e| := le_abs_self _
    have h2 : |eucDot (curve γ (t + s) - curve γ (t - s)) e|
        ≤ eucNorm (curve γ (t + s) - curve γ (t - s)) * eucNorm e := hcs
    rw [← hc] at h2
    linarith
  have hmul : c * s * c ≤ eucNorm (curve γ (t + s) - curve γ (t - s)) * c := by
    have h1 : c * s * c ≤ (15 / 8) * c ^ 2 * s := by nlinarith [hcpos, hs0]
    linarith [h1, hval, hle]
  have hfin : c * s ≤ eucNorm (curve γ (t + s) - curve γ (t - s)) :=
    (mul_le_mul_iff_of_pos_right hcpos).mp hmul
  simpa only [hc, he] using hfin

end Work.Drive
