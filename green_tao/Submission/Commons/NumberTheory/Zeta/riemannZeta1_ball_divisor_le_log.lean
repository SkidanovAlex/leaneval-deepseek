import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_ball3_divisor_le_log

open Complex Filter Metric Set
open scoped Real Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- For `|t| ≥ 5`, the point `2 + i t` is at distance at least `5` from `1`. -/
private lemma norm_one_sub_center_ge {t : ℝ} (ht : 5 ≤ |t|) :
    5 ≤ ‖(1 : ℂ) - ((2 : ℂ) + Complex.I * (t : ℂ))‖ := by
  have h := Complex.abs_im_le_norm ((1 : ℂ) - ((2 : ℂ) + Complex.I * (t : ℂ)))
  have hval : ((1 : ℂ) - ((2 : ℂ) + Complex.I * (t : ℂ))).im = -t := by simp
  rw [hval, abs_neg] at h
  linarith

/-- Every point of the open ball of radius `4` about `2 + i t` (`|t| ≥ 5`) differs from `1`. -/
private lemma ne_one_of_ball_four {t : ℝ} (ht : 5 ≤ |t|) {z : ℂ}
    (hz : z ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ)) : z ≠ 1 := by
  intro hz1
  have hzd : ‖z - ((2 : ℂ) + Complex.I * (t : ℂ))‖ < (4 : ℝ) := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  rw [hz1] at hzd
  have hge := norm_one_sub_center_ge (t := t) ht
  linarith

/-- On the open ball of radius `4` about `2 + i t` (`|t| ≥ 5`), the entire function
`riemannZeta₁ = (s-1)·ζ(s) + O((s-1)²)` agrees with `(s-1)·ζ(s)`. -/
private lemma riemannZeta₁_eq_mul_sub_ball_four {t : ℝ} (ht : 5 ≤ |t|) {z : ℂ}
    (hz : z ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ)) :
    riemannZeta₁ z = (z - 1) * riemannZeta z := by
  have hz1 : z ≠ 1 := ne_one_of_ball_four ht hz
  rw [riemannZeta_eq_inv_sub_mul hz1, mul_inv_cancel_left₀ (sub_ne_zero.mpr hz1)]

/-- On the open ball of radius `4` about `2 + i t` (`|t| ≥ 5`) the meromorphic order of
`riemannZeta₁` coincides with that of `ζ` (multiplication by the analytic, non-vanishing
factor `s - 1` does not change the order). -/
private lemma meromorphicOrderAt_riemannZeta₁_eq_riemannZeta_ball_four {t : ℝ} (ht : 5 ≤ |t|)
    {u : ℂ} (hu : u ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ)) :
    meromorphicOrderAt riemannZeta₁ u = meromorphicOrderAt riemannZeta u := by
  have hball : Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ) ∈ 𝓝 u :=
    Metric.isOpen_ball.mem_nhds hu
  have hev : riemannZeta₁ =ᶠ[𝓝[≠] u] ((fun z : ℂ => z - 1) * riemannZeta) := by
    filter_upwards [nhdsWithin_le_nhds hball] with z hz
    exact riemannZeta₁_eq_mul_sub_ball_four ht hz
  have hg : AnalyticAt ℂ (fun z : ℂ => z - 1) u := by fun_prop
  have hg0 : u - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_ball_four ht hu)
  calc meromorphicOrderAt riemannZeta₁ u
      = meromorphicOrderAt ((fun z : ℂ => z - 1) * riemannZeta) u :=
        meromorphicOrderAt_congr hev
    _ = meromorphicOrderAt riemannZeta u := meromorphicOrderAt_mul_of_ne_zero hg hg0

/-- `ζ` is analytic on the closed ball of radius `3` about `2 + i t` (`|t| ≥ 5`), which avoids
the pole at `1`. -/
private lemma analyticOn_riemannZeta_closedBall_three {t : ℝ} (ht : 5 ≤ |t|) :
    AnalyticOnNhd ℂ riemannZeta
      (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ)) := by
  refine analyticOn_riemannZeta.mono ?_
  intro z hz hz1
  rw [Set.mem_singleton_iff] at hz1
  rw [hz1] at hz
  have hd : ‖(1 : ℂ) - ((2 : ℂ) + Complex.I * (t : ℂ))‖ ≤ (3 : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hge := norm_one_sub_center_ge (t := t) ht
  linarith

/-- **Lagarias–Jensen bound for the divisor of `riemannZeta₁` on a disk centred on `re s = 2`.**

For every real ordinate `t` with `|t| ≥ 5` and every radius `R` with `0 < R ≤ 4`, the
(multiplicity-weighted) divisor sum of the entire function `riemannZeta₁` on the closed disk of
radius `R/2` about `2 + i t` is `O(log |t|)`.  The disk of radius `R/2 ≤ 2` is contained in the
disk of radius `3`, where `riemannZeta₁` has the same divisor as `ζ`; monotonicity of the
divisor sum together with the Lagarias–Jensen bound `zeta_ball3_divisor_le_log` for `ζ` gives
the claim. -/
theorem riemannZeta1_ball_divisor_le_log :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 5 ≤ |t| → ∀ R : ℝ, 0 < R → R ≤ 4 →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta₁
          (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2))) u : ℤ) : ℝ)) ≤
        K * (Real.log (|t| + 6) + 1) := by
  classical
  rcases zeta_ball3_divisor_le_log with ⟨K, hKpos, hK⟩
  refine ⟨K, hKpos, ?_⟩
  intro t ht R hR hR4
  -- analyticity of ζ and ζ₁ on the relevant disks
  have hζan : AnalyticOnNhd ℂ riemannZeta
      (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ)) :=
    analyticOn_riemannZeta_closedBall_three ht
  have hζ1an : AnalyticOnNhd ℂ riemannZeta₁
      (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2)) :=
    fun z _ => differentiable_riemannZeta₁.analyticAt z
  -- pointwise comparison of the two divisors
  have hpoint : ∀ u : ℂ,
      (MeromorphicOn.divisor riemannZeta₁
          (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2))) u ≤
        (MeromorphicOn.divisor riemannZeta
          (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u := by
    intro u
    by_cases hu : u ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2)
    · have hu4 : u ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ) := by
        simp only [Metric.mem_closedBall] at hu
        simp only [Metric.mem_ball]
        linarith
      have hu3 : u ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ) := by
        simp only [Metric.mem_closedBall] at hu ⊢
        linarith
      have hord : meromorphicOrderAt riemannZeta₁ u = meromorphicOrderAt riemannZeta u :=
        meromorphicOrderAt_riemannZeta₁_eq_riemannZeta_ball_four ht hu4
      rw [MeromorphicOn.divisor_apply hζ1an.meromorphicOn hu,
        MeromorphicOn.divisor_apply hζan.meromorphicOn hu3, hord]
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
      exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hζan u
  -- finiteness of both divisors
  have hfin1 : Function.HasFiniteSupport
      (fun u : ℂ => (MeromorphicOn.divisor riemannZeta₁
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2))) u) := by
    simpa [Function.HasFiniteSupport] using
      ((MeromorphicOn.divisor riemannZeta₁
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2))).finiteSupport
        (isCompact_closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2)))
  have hfin3 : Function.HasFiniteSupport
      (fun u : ℂ => (MeromorphicOn.divisor riemannZeta
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u) := by
    simpa [Function.HasFiniteSupport] using
      ((MeromorphicOn.divisor riemannZeta
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))).finiteSupport
        (isCompact_closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ)))
  -- integer-level monotonicity and its cast to ℝ
  have hZle : (∑ᶠ u : ℂ, (MeromorphicOn.divisor riemannZeta₁
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2))) u) ≤
      (∑ᶠ u : ℂ, (MeromorphicOn.divisor riemannZeta
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u) :=
    finsum_le_finsum' hfin1 hfin3 hpoint
  have hmap1 : (↑(∑ᶠ u : ℂ, (MeromorphicOn.divisor riemannZeta₁
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2))) u) : ℝ) =
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta₁
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2))) u : ℤ) : ℝ)) :=
    map_finsum (Int.castRingHom ℝ) hfin1
  have hmap3 : (↑(∑ᶠ u : ℂ, (MeromorphicOn.divisor riemannZeta
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u) : ℝ) =
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u : ℤ) : ℝ)) :=
    map_finsum (Int.castRingHom ℝ) hfin3
  have hcast : (↑(∑ᶠ u : ℂ, (MeromorphicOn.divisor riemannZeta₁
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2))) u) : ℝ) ≤
      (↑(∑ᶠ u : ℂ, (MeromorphicOn.divisor riemannZeta
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u) : ℝ) :=
    Int.cast_le.mpr hZle
  calc
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta₁
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2))) u : ℤ) : ℝ))
        = (↑(∑ᶠ u : ℂ, (MeromorphicOn.divisor riemannZeta₁
            (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2))) u) : ℝ) := hmap1.symm
    _ ≤ (↑(∑ᶠ u : ℂ, (MeromorphicOn.divisor riemannZeta
            (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u) : ℝ) := hcast
    _ = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta
            (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u : ℤ) : ℝ)) := hmap3
    _ ≤ K * (Real.log (|t| + 6) + 1) := hK t ht

end Commons.NumberTheory.Zeta
