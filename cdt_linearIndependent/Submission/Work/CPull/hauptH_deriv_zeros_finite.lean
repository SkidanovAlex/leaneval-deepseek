import Mathlib
import Submission.Work.CPull.cdt_interfaces

namespace Work.CPull

open scoped Topology

/-!
# Finiteness of the zeros of `deriv hauptH` in the disc of radius `3/4`

This file proves `Work.CPull.hauptH_deriv_zeros_finite`: the derivative of the hauptmodul
`Submission.CDTPlan.hauptH` has only finitely many zeros in the closed disc of radius `3/4`.

The proof is the standard "zeros of a non-zero analytic function are isolated" argument, packaged
as the reusable helper `Work.CPull.finite_zeros_deriv_of_differentiableOn`:

* a non-zero analytic function has isolated zeros, so an infinite zero set in a compact disc would
  accumulate at some point `z` of the disc;
* at an interior accumulation point of the zero set, analyticity forces the function to vanish
  identically near `z` (identity theorem), so the function is identically `0` on the whole disc;
* for the derivative this contradicts `deriv hauptH 0 = -256 ≠ 0`.
-/

/-- **Zeros of the derivative of an analytic function on a disc are finite on smaller closed
discs.**  If `f` is holomorphic on the open disc of radius `R` and `deriv f 0 ≠ 0` (so that
`deriv f` is not identically zero there), then `deriv f` vanishes at only finitely many points of
the closed disc of radius `r`, for every `0 ≤ r < R`. -/
theorem finite_zeros_deriv_of_differentiableOn {f : ℂ → ℂ} {r R : ℝ} (hr0 : 0 ≤ r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) (h0 : deriv f 0 ≠ 0) :
    {z : ℂ | z ∈ Metric.closedBall (0 : ℂ) r ∧ deriv f z = 0}.Finite := by
  set Z : Set ℂ := {z : ℂ | z ∈ Metric.closedBall (0 : ℂ) r ∧ deriv f z = 0} with hZ
  by_contra hfin
  rw [Set.not_finite] at hfin
  have hK : IsCompact (Metric.closedBall (0 : ℂ) r) := isCompact_closedBall 0 r
  have hZK : Z ⊆ Metric.closedBall (0 : ℂ) r := fun z hz => hz.1
  -- the closed disc of radius `r` sits inside the open disc of radius `R`
  have hcb : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) R := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    linarith
  -- an infinite subset of the compact disc accumulates at a point of it
  obtain ⟨z, hzK, hzacc⟩ := hfin.exists_accPt_of_subset_isCompact hK hZK
  have hzR : z ∈ Metric.ball (0 : ℂ) R := hcb hzK
  -- hence `deriv f` vanishes frequently in every punctured neighbourhood of `z`
  have hfreq : ∃ᶠ w in 𝓝[≠] z, deriv f w = 0 := by
    refine (accPt_iff_frequently_nhdsNE.mp hzacc).mono (fun w hw => ?_)
    rw [hZ] at hw
    exact hw.2
  -- `deriv f` is analytic on the disc, so it vanishes identically there (identity theorem)
  have hAn : AnalyticOnNhd ℂ (deriv f) (Metric.ball 0 R) :=
    (hf.analyticOnNhd Metric.isOpen_ball).deriv
  have hzero : Set.EqOn (deriv f) 0 (Metric.ball (0 : ℂ) R) :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero hAn Metric.isPreconnected_ball
      hzR hfreq
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_self]
    linarith
  exact h0 (hzero h0mem)

/-- The derivative of the hauptmodul has only finitely many zeros in the closed disc of radius
`3/4`. -/
theorem hauptH_deriv_zeros_finite (hM : Submission.CDTPlan.HauptFacts) :
    {w : ℂ | w ∈ Metric.closedBall (0 : ℂ) (3 / 4) ∧ deriv Submission.CDTPlan.hauptH w = 0}.Finite := by
  have hd : DifferentiableOn ℂ Submission.CDTPlan.hauptH (Metric.ball 0 1) := hM.1
  have h0 : deriv Submission.CDTPlan.hauptH 0 ≠ 0 := by
    rw [hM.2.1]
    norm_num
  exact finite_zeros_deriv_of_differentiableOn (by norm_num) (by norm_num) hd h0

end Work.CPull
