import Mathlib
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.anchor_scale_geom
import Submission.Work.Pert.Ksub2.anchor_scale_close
import Submission.Work.Pert.Ksub2.anchor_scale_deriv
import Submission.Work.Pert.Ksub2.Xcurve_bounds
import Submission.Work.Pert.exists_fatouCoord_inv_tau0_phi
import Submission.Work.Parab.inversion.exists_mul_log_lt

/-!
# `Work.Pert.Ksub2.exists_anchor_sharp`

Sharp form of the datum anchor of `Work.Pert.Ksub2.exists_anchor`: instead of a free deep point
`u₀` together with `‖u₀ - (-M)‖ ≤ M/10`, the anchor is placed *exactly* at the point `-M`, and the
local Fatou coordinate `Φ₀` of `F₀ = τ₀ ∘ f₀ ∘ τ₀` is required to move its domain by at most
`M/40`, i.e. `‖Φ₀ ζ - ζ‖ ≤ M/40` for every `ζ` in the ball
`ball (Xc d (-M)) (M/40)`.

The extra content over `exists_anchor` is exactly the "sharpness" of the choice of the anchor
point: when the anchor sits at `w₀ = -M` (rather than at a point `u₀` merely `M/10`-close to `-M`),
both `Xc d (-M)` and every value `Φ₀ ζ` stay within the *closed* ball of radius `M/10` around
`-M`, where `Xcurve_bounds` bounds the quadratic-logarithmic deviation of the curve by
`C * (1 + log ‖u‖) ≤ C * (1 + log (2M)) ≤ M/40` as soon as `M` is large.  Thus:

* `‖Xc d (-M) - (-M)‖ ≤ M/40` is `anchor_scale_close`;
* `‖Φ₀ ζ - ζ‖ = ‖u - Xc d u‖ ≤ M/40` for `u = Φ₀ ζ ∈ closedBall (-M) (M/10)` is the new
  estimate `Xc_sub_id_le_aux` below.

The remaining structure (the covering lemma `exists_fatouCoord_inv_tau0_phi` applied at `w₀ = -M`,
and the pinning `Φ₀ (Xc d (-M)) = -M` from the reverse-expansion estimate) is verbatim that of
`exists_anchor`.
-/

namespace Work.Pert.Ksub2

open Metric Set Complex
open scoped Topology

noncomputable section

/-- `deriv` is the junk value `0` where the function is not complex differentiable, so the bound
`‖deriv Φ u - 1‖ ≤ 1/2` forces differentiability at `u`. -/
private lemma differentiableAt_of_norm_deriv_sub_one_le {Φ : ℂ → ℂ} {u : ℂ}
    (h : ‖deriv Φ u - 1‖ ≤ 1 / 2) : DifferentiableAt ℂ Φ u := by
  by_contra hd
  have h0 : deriv Φ u = 0 := deriv_zero_of_not_differentiableAt hd
  rw [h0] at h
  norm_num at h

/-- **Sharp deviation bound on the deep disc.**  For every §4.1 datum `d` there is a scale `R`
such that for all `M ≥ R` the curve `u ↦ Xc d u = τ₀ (φ₀ u)` moves points of the closed disc of
centre `-M` and radius `M/10` by at most `M/40`:

`‖Xc d u - u‖ ≤ M/40`.

Indeed, for such `u` one has `9M/10 ≤ ‖u‖ ≤ 11M/10` and `Re u ≤ -9M/10`, so `u` and the whole
disc `ball u (‖u‖/10)` used by the Cauchy estimate of `Xcurve_bounds` lie in the half plane
`{Re w < -ξ₀} ⊆ QLeft ξ₀`; `Xcurve_bounds` then gives `‖Xc d u - u‖ ≤ C (1 + log ‖u‖) ≤
C (1 + log (2M))`, and `log = o(id)` (`exists_mul_log_lt_aux`) makes this shorter than `M/40`. -/
private lemma Xc_sub_id_le_aux {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ R : ℝ, 0 < R ∧ ∀ M : ℝ, R ≤ M →
      ∀ u ∈ Metric.closedBall (((-M : ℝ) : ℂ)) (M / 10),
        ‖Work.Pert.Xc d u - u‖ ≤ M / 40 := by
  obtain ⟨C, hCpos, hC⟩ := Xcurve_bounds d
  obtain ⟨R₀, _hR₀pos, hR₀⟩ :=
    Work.Parab.inversion.exists_mul_log_lt_aux (a := C) (b := C) (c := 1 / 40) (by norm_num)
  refine ⟨max (max (20 * d.ξ₀ + 20) (10 * C / 9 + 1)) (max R₀ 1), ?_, ?_⟩
  · exact lt_max_iff.mpr (Or.inl (lt_max_iff.mpr (Or.inl (by linarith [d.ξ₀_pos]))))
  · intro M hM u hu
    have hM_A : 20 * d.ξ₀ + 20 ≤ M :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
    have hM_B : 10 * C / 9 + 1 ≤ M :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
    have hM_R0 : R₀ ≤ M :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
    have hM_1 : (1 : ℝ) ≤ M :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
    have hMpos : 0 < M := lt_of_lt_of_le one_pos hM_1
    have hξpos : 0 < d.ξ₀ := d.ξ₀_pos
    -- ## position and norm of `u`
    have hdist : ‖u - (((-M : ℝ) : ℂ))‖ ≤ M / 10 := by
      have := Metric.mem_closedBall.mp hu
      rwa [dist_eq_norm] at this
    have hadd : u - (((-M : ℝ) : ℂ)) = u + (M : ℂ) := by push_cast; ring
    have hdist' : ‖u + (M : ℂ)‖ ≤ M / 10 := by rw [← hadd]; exact hdist
    have hnormM : ‖(M : ℂ)‖ = M := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hMpos.le]
    have hre : u.re ≤ -(9 * M / 10) := by
      have h1 : |(u + (M : ℂ)).re| ≤ ‖u + (M : ℂ)‖ := Complex.abs_re_le_norm _
      have h2 : (u + (M : ℂ)).re = u.re + M := by simp
      rw [h2] at h1
      have h3 := le_trans (le_abs_self (u.re + M)) h1
      linarith
    have hnorm_lo : 9 * M / 10 ≤ ‖u‖ := by
      have h1 : (M : ℝ) ≤ ‖u + (M : ℂ)‖ + ‖u‖ := by
        have h := norm_sub_le (u + (M : ℂ)) u
        have h2 : u + (M : ℂ) - u = (M : ℂ) := by ring
        rw [h2, hnormM] at h
        exact h
      linarith
    have hnorm_hi : ‖u‖ ≤ 11 * M / 10 := by
      have h1 : ‖u‖ ≤ ‖u + (M : ℂ)‖ + M := by
        have h := norm_add_le (u + (M : ℂ)) (-(M : ℂ))
        have h2 : u + (M : ℂ) + -(M : ℂ) = u := by ring
        rw [h2, norm_neg, hnormM] at h
        exact h
      linarith
    -- ## sector membership of `u` and of the disc `ball u (‖u‖/10)`
    have hgoal_u : u.re < -d.ξ₀ := by linarith
    have huQ : u ∈ MandelDim.QLeft d.ξ₀ := Work.Parab.halfplane_subset_QLeft d.ξ₀ hgoal_u
    have hball : Metric.ball u (‖u‖ / 10) ⊆ MandelDim.QLeft d.ξ₀ := by
      intro v hv
      have hgoal_v : v.re < -d.ξ₀ := by
        have hv1 : ‖v - u‖ < ‖u‖ / 10 := by
          have := Metric.mem_ball.mp hv
          rwa [dist_eq_norm] at this
        have hv2 : ‖v - u‖ < 11 * M / 100 := by linarith
        have hvre : v.re ≤ u.re + ‖v - u‖ := by
          have h1 : (v - u).re = v.re - u.re := Complex.sub_re v u
          have h2 : (v - u).re ≤ ‖v - u‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
          linarith
        linarith
      exact Work.Parab.halfplane_subset_QLeft d.ξ₀ hgoal_v
    have hCu : C ≤ ‖u‖ := by linarith
    -- ## the value estimate
    have hb := (hC u huQ hCu hball).1
    have hlogu : Real.log ‖u‖ ≤ Real.log (2 * M) := by
      have h1 : (0 : ℝ) < ‖u‖ := by linarith
      have h2 : ‖u‖ ≤ 2 * M := by linarith
      exact Real.log_le_log h1 h2
    have hlog_le : C * (1 + Real.log ‖u‖) ≤ C * (1 + Real.log (2 * M)) := by
      have h := mul_le_mul_of_nonneg_left hlogu hCpos.le
      linarith
    have hR0M := hR₀ M hM_R0
    have hkey : C * (1 + Real.log (2 * M)) < M / 40 := by
      have he : C * (1 + Real.log (2 * M)) = C + C * Real.log (2 * M) := by ring
      rw [he]; linarith
    exact le_trans hb (le_trans hlog_le hkey.le)

/-- **Sharp anchor.**  For every §4.1 datum `d` and every lower bound `M₀` there is a scale `M ≥ M₀`
and a local Fatou coordinate `Φ₀` of `F₀ = τ₀ ∘ f₀ ∘ τ₀` on the ball of centre the anchored curve
point `Xc d (-M)` and radius `M/40`, which inverts the curve there, moves points by at most `M/40`,
and is normalised at the anchor: `Φ₀ (Xc d (-M)) = -M`. -/
theorem exists_anchor_sharp {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) (M₀ : ℝ) :
    ∃ M : ℝ, M₀ ≤ M ∧ 0 < M ∧ ∃ Φ₀ : ℂ → ℂ,
      MandelDim.IsFatouCoordOn (Work.Pert.F0f f₀) Φ₀
        (Metric.ball (Work.Pert.Xc d (((-M : ℝ) : ℂ))) (M / 40)) ∧
      (∀ ζ ∈ Metric.ball (Work.Pert.Xc d (((-M : ℝ) : ℂ))) (M / 40),
        Work.Pert.Xc d (Φ₀ ζ) = ζ ∧ ‖Φ₀ ζ - ζ‖ ≤ M / 40) ∧
      Φ₀ (Work.Pert.Xc d (((-M : ℝ) : ℂ))) = (((-M : ℝ) : ℂ)) ∧
      ‖Work.Pert.Xc d (((-M : ℝ) : ℂ)) - (((-M : ℝ) : ℂ))‖ ≤ M / 40 := by
  obtain ⟨R₁, _hR₁pos, hR₁⟩ := anchor_scale_geom d
  obtain ⟨R₂, _hR₂pos, hR₂⟩ := anchor_scale_close d
  obtain ⟨R₃, _hR₃pos, hR₃⟩ := anchor_scale_deriv d
  obtain ⟨R₄, _hR₄pos, hR₄⟩ := Xc_sub_id_le_aux d
  set M : ℝ := max (max M₀ 1) (max R₁ (max R₂ (max R₃ R₄))) with hMdef
  have hM₀ : M₀ ≤ M := by
    rw [hMdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hMdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  have hMR₁ : R₁ ≤ M := by
    rw [hMdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hMR₂ : R₂ ≤ M := by
    rw [hMdef]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hMR₃ : R₃ ≤ M := by
    rw [hMdef]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hMR₄ : R₄ ≤ M := by
    rw [hMdef]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  obtain ⟨h8, hballQ⟩ := hR₁ M hMR₁
  have hclose := hR₂ M hMR₂
  have hder := hR₃ M hMR₃
  have hsharp := hR₄ M hMR₄
  have hnormw : ‖(((-M : ℝ)) : ℂ)‖ = M := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hMpos.le]
  have hbw : 0 < ‖(((-M : ℝ)) : ℂ)‖ / 4 := by rw [hnormw]; linarith
  have hder' : ∀ u ∈ Metric.ball (((-M : ℝ)) : ℂ) (‖(((-M : ℝ)) : ℂ)‖ / 4),
      ‖deriv (fun v : ℂ => MandelDim.tau0 (d.φ v)) u - 1‖ ≤ 1 / 2 := by
    intro u hu
    exact hder u (by simpa only [hnormw] using hu)
  obtain ⟨Φ₀, hinv, hfat⟩ :=
    Work.Pert.exists_fatouCoord_inv_tau0_phi (w₀ := (((-M : ℝ)) : ℂ)) d
      (by simpa only [hnormw] using hballQ)
      (by simpa only [hnormw] using h8)
      (by simpa only [hnormw] using hclose)
      hder'
  refine ⟨M, hM₀, hMpos, Φ₀, ?_, ?_, ?_, ?_⟩
  · unfold Work.Pert.F0f Work.Pert.Xc
    simpa only [hnormw] using hfat
  · intro ζ hζ
    obtain ⟨hmem, hval⟩ := hinv ζ (by simpa only [Work.Pert.Xc, hnormw] using hζ)
    refine ⟨hval, ?_⟩
    have hmem' : Φ₀ ζ ∈ Metric.closedBall (((-M : ℝ)) : ℂ) (M / 10) := by
      simpa only [hnormw] using hmem
    have hb := hsharp (Φ₀ ζ) hmem'
    have hX : Work.Pert.Xc d (Φ₀ ζ) = ζ := hval
    rw [hX] at hb
    simpa [norm_sub_rev] using hb
  · have hU : Work.Pert.Xc d (((-M : ℝ)) : ℂ) ∈
        Metric.ball (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) (M / 40) := by
      rw [Metric.mem_ball, dist_self]; linarith
    have hU' : Work.Pert.Xc d (((-M : ℝ)) : ℂ) ∈
        Metric.ball (MandelDim.tau0 (d.φ (((-M : ℝ)) : ℂ))) (‖(((-M : ℝ)) : ℂ)‖ / 40) := by
      simpa only [Work.Pert.Xc, hnormw] using hU
    have hmem : Φ₀ (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) ∈
        Metric.closedBall (((-M : ℝ)) : ℂ) (‖(((-M : ℝ)) : ℂ)‖ / 10) :=
      (hinv (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) hU').1
    have hΨ' : MandelDim.tau0 (d.φ (Φ₀ (Work.Pert.Xc d (((-M : ℝ)) : ℂ)))) =
        MandelDim.tau0 (d.φ (((-M : ℝ)) : ℂ)) := (hinv _ hU').2
    have hdiffΨ : DifferentiableOn ℂ (fun v : ℂ => MandelDim.tau0 (d.φ v))
        (Metric.ball (((-M : ℝ)) : ℂ) (‖(((-M : ℝ)) : ℂ)‖ / 4)) := fun u hu =>
      (differentiableAt_of_norm_deriv_sub_one_le (hder' u hu)).differentiableWithinAt
    have hexp := Work.Pert.inv_close_of_deriv_close Metric.isOpen_ball
      (convex_ball (((-M : ℝ)) : ℂ) (‖(((-M : ℝ)) : ℂ)‖ / 4)) hdiffΨ hder'
      (Φ₀ (Work.Pert.Xc d (((-M : ℝ)) : ℂ)))
      (Metric.closedBall_subset_ball (by rw [hnormw]; linarith) hmem)
      (((-M : ℝ)) : ℂ) (Metric.mem_ball_self hbw)
    have h0 : ‖Φ₀ (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) - (((-M : ℝ)) : ℂ)‖ ≤ 0 := by
      rw [hΨ'] at hexp
      simpa using hexp
    have hz : Φ₀ (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) - (((-M : ℝ)) : ℂ) = 0 :=
      norm_eq_zero.mp (le_antisymm h0 (norm_nonneg _))
    exact sub_eq_zero.mp hz
  · simpa only [Work.Pert.Xc] using hclose

end

end Work.Pert.Ksub2
