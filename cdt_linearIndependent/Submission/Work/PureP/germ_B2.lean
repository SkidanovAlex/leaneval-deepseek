import Mathlib
import Submission.Work.PureP.basic
import Submission.Work.PureP.hasSum_coeff_B2_yps
import Submission.Work.CPull.defs
import Submission.Work.CPull.germs

/-!
# Area PureP — the pullback germ of `B₂` along an arbitrary lifted map

Generic (i.e. `LiftData`-only) form of `Submission.Work.CPull.germ_B2`.

With the odd logarithm `ℓ` of `1 - Φ` (`Work.PureP.exists_odd_log_phi`), the closed form of the
pullback of `B₂` along the symmetrisation `y = Φ z ^ 2/(Φ z - 1)` is

`E z = 2 · φ (z^2) - (Φ z) (Φ z - 2)/(Φ z - 1) · ℓ z`,

which is holomorphic on the disc (`Φ ≠ 1`).  Near `0` it is the germ of `Σₙ [yⁿ]B₂ · φ (z^2)ⁿ`
by `Work.PureP.hasSum_coeff_B2_yps` at `x = Φ z` (`ℓ = log (1 - Φ ·)` and `φ (z^2) = Φ z^2/(Φ z-1)`),
so `E` is even (the germ is a function of `z ^ 2`, and analytic continuation applies), and
`Work.CPull.germ_of_even` descends to a germ for the pullback along `φ`.
-/

namespace Work.PureP

open Complex Metric Filter
open scoped Topology
open Submission.CDTPlan

/-- The pullback germ of `B₂` along any `φ` admitting a lift `Φ`, with denominator `1`. -/
theorem germ_B2 (φ Φ : ℂ → ℂ) (hφ : DifferentiableOn ℂ φ (Metric.ball 0 1)) (hφ0 : φ 0 = 0)
    (hL : LiftData φ Φ) :
    ∃ N : ℂ → ℂ, DifferentiableOn ℂ N (Metric.ball 0 1) ∧
      ∀ᶠ w in 𝓝 (0 : ℂ), HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n B2 : ℚ) : ℂ) * φ w ^ n) (N w) := by
  obtain ⟨ℓ, r, hrpos, hrle1, hℓdiff, hℓ0, hℓexp, hℓodd, hℓlog⟩ :=
    exists_odd_log_phi hL.1 (lift_zero hφ0 hL) (lift_ne_one hL) (one_sub_neg hL)
  -- the radius at which `Φ` is small
  have hΦcont : ContinuousAt Φ 0 :=
    hL.1.continuousOn.continuousAt (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  have hsmall : ∀ᶠ z in 𝓝 (0 : ℂ), ‖Φ z‖ < 1 / 2 := by
    have h := hΦcont.eventually (Metric.ball_mem_nhds (Φ 0) (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [h] with z hz
    rw [lift_zero hφ0 hL] at hz
    simpa [Metric.mem_ball, dist_zero_right] using hz
  -- the candidate
  set E : ℂ → ℂ := fun z => 2 * φ (z ^ 2) - Φ z * (Φ z - 2) / (Φ z - 1) * ℓ z with hEdef
  -- the germ identity
  have hgerm : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n B2 : ℚ) : ℂ) * φ (z ^ 2) ^ n) (E z) := by
    filter_upwards [hsmall, Metric.ball_mem_nhds (0 : ℂ) hrpos] with z hzsmall hzr
    have hz1 : ‖z‖ < 1 := by
      rw [Metric.mem_ball, dist_zero_right] at hzr
      exact lt_of_lt_of_le hzr hrle1
    have hzball : z ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]; exact hz1
    have hlog : ℓ z = Complex.log (1 - Φ z) := hℓlog z hzr
    have hmain := hasSum_coeff_B2_yps (Φ z) hzsmall
    have hval : E z = 2 * ((Φ z) ^ 2 / (Φ z - 1))
        - Φ z * (Φ z - 2) * Complex.log (1 - Φ z) / (Φ z - 1) := by
      rw [hEdef]
      simp only
      rw [phi_sq_eq hL z hzball, hlog]
      ring
    rw [hval]
    refine hmain.congr_fun fun n => ?_
    rw [phi_sq_eq hL z hzball]
  -- `E` is holomorphic on the disc
  have hEd : DifferentiableOn ℂ E (Metric.ball 0 1) := by
    rw [hEdef]
    have h1 : DifferentiableOn ℂ (fun z : ℂ => φ (z ^ 2)) (Metric.ball 0 1) := by
      refine hφ.comp (differentiableOn_id.pow 2) ?_
      intro z hz
      rw [Metric.mem_ball, dist_zero_right] at hz ⊢
      rw [norm_pow]
      nlinarith [norm_nonneg z]
    have h2 : DifferentiableOn ℂ (fun z : ℂ => Φ z * (Φ z - 2) / (Φ z - 1))
        (Metric.ball 0 1) :=
      (hL.1.mul (hL.1.sub_const 2)).div (hL.1.sub_const 1)
        (fun z hz => sub_ne_zero.mpr (lift_ne_one hL z hz))
    exact (h1.const_mul 2).sub (h2.mul hℓdiff)
  -- hence `E` is even: `E z = E (-z)` near `0`, since both sides are the (even) germ
  have hevenEv : ∀ᶠ z in 𝓝 (0 : ℂ), E z = E (-z) := by
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hgerm
    refine Filter.Eventually.mono (Metric.ball_mem_nhds (0 : ℂ) hδpos) fun z hz => ?_
    have hzδ : dist z 0 < δ := Metric.mem_ball.mp hz
    have hnδ : dist (-z) 0 < δ := by
      rw [dist_zero_right, norm_neg]; rwa [dist_zero_right] at hzδ
    rw [← (hδ hzδ).tsum_eq, ← (hδ hnδ).tsum_eq]
    exact tsum_congr fun n => by rw [show (-z) ^ 2 = z ^ 2 from by ring]
  have heven : ∀ z ∈ Metric.ball (0 : ℂ) 1, E (-z) = E z := by
    have hnegmap : Set.MapsTo (fun z : ℂ => -z) (Metric.ball 0 1) (Metric.ball 0 1) := by
      intro z hz
      rw [Metric.mem_ball, dist_zero_right] at hz ⊢
      simpa using hz
    have h2 : DifferentiableOn ℂ (fun z => E (-z)) (Metric.ball (0 : ℂ) 1) :=
      hEd.comp differentiable_neg.differentiableOn hnegmap
    have heq : Set.EqOn E (fun z => E (-z)) (Metric.ball (0 : ℂ) 1) :=
      AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
        (hEd.analyticOnNhd Metric.isOpen_ball) (h2.analyticOnNhd Metric.isOpen_ball)
        (convex_ball (0 : ℂ) 1).isPreconnected (by simp [Metric.mem_ball]) hevenEv
    intro z hz
    exact (heq hz).symm
  exact Work.CPull.germ_of_even (Ψ := φ) (f := B2) (E := E) hEd heven hgerm

end Work.PureP
