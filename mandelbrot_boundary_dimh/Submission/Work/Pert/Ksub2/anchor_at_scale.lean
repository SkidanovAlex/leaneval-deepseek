import Mathlib
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.exists_anchor_sharp
import Submission.Work.Pert.Ksub2.anchor_scale_geom
import Submission.Work.Pert.Ksub2.anchor_scale_close
import Submission.Work.Pert.Ksub2.anchor_scale_deriv
import Submission.Work.Pert.Ksub2.Xc_small_bound
import Submission.Work.Pert.Ksub2.Xc_sub_id_le
import Submission.Work.Pert.Ksub2.Xcurve_bounds

/-!
# `Work.Pert.Ksub2.anchor_at_scale`

The datum-side anchor of `Ksub2.exists_anchor_sharp`, in the *eventually-in-`M`* form needed by
the level-`K` perturbation argument: there is a scale `Mthr > 0` such that **every** `M ≥ Mthr`
carries a local Fatou coordinate `Φ₀` of the limit dynamics `F₀ = τ₀ ∘ f₀ ∘ τ₀` on the ball
`ball (Xc d (-M)) (M/40)` which right-inverts the datum's curve `Xc d = τ₀ ∘ φ₀` there, moves its
domain points by at most `M/40` (`‖Φ₀ ζ - ζ‖ ≤ M/40`) and is pinned at the anchor,
`Φ₀ (Xc d (-M)) = -M`.

The construction is that of `exists_anchor_sharp` (which delivers the same conclusion for *one*
scale above any prescribed `M₀`); here the three datum inputs — `anchor_scale_geom` (the quarter
disc `ball (-M) (M/4)` lies in the repelling sector `QLeft ξ₀`, together with `8 ≤ M`),
`anchor_scale_close` (the anchor is placed within `M/40` of `-M`) and `anchor_scale_deriv`
(Shishikura's A.4 estimate `‖(τ₀ ∘ φ₀)' - 1‖ ≤ 1/2` on that quarter disc) — are each of the form
`∀ M ≥ R, …`, so with `Mthr = max 1 (max R₁ (max R₂ (max R₃ R₄)))` the *same* construction runs at
every `M ≥ Mthr`.

The extra input over `exists_anchor_sharp`'s ingredients is the sharp deviation bound
`Work.Pert.Ksub2.Xc_sub_id_le` (`‖Xc d u - u‖ ≤ M/40` for every `u` in `closedBall (-M) (M/10)`),
which converts the range information `Φ₀ ζ ∈ closedBall (-M) (M/10)` of the local inverse into
`‖Φ₀ ζ - ζ‖ = ‖u - Xc d u‖ ≤ M/40`.
-/

namespace Work.Pert.Ksub2

open Metric Set Complex
open scoped Topology

noncomputable section

/-- `deriv` is the junk value `0` where the function is not complex differentiable, so the bound
`‖deriv Φ u - 1‖ ≤ 1/2` forces differentiability at `u`. -/
private lemma differentiableAt_of_norm_deriv_sub_one_le' {Φ : ℂ → ℂ} {u : ℂ}
    (h : ‖deriv Φ u - 1‖ ≤ 1 / 2) : DifferentiableAt ℂ Φ u := by
  by_contra hd
  have h0 : deriv Φ u = 0 := deriv_zero_of_not_differentiableAt hd
  rw [h0] at h
  norm_num at h

/-- **The datum anchor at every sufficiently large scale.**  There is `Mthr > 0` such that for
every `M ≥ Mthr` the curve `Xc d` has a local inverse `Φ₀` on `ball (Xc d (-M)) (M/40)` which is a
Fatou coordinate of `F₀ = τ₀ ∘ f₀ ∘ τ₀`, moves points by at most `M/40`, and is pinned at the
anchor `Xc d (-M) ↦ -M`; moreover `Xc d (-M)` itself is within `M/40` of `-M`. -/
theorem anchor_at_scale {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ Mthr : ℝ, 0 < Mthr ∧ ∀ M : ℝ, Mthr ≤ M → ∃ Φ₀ : ℂ → ℂ,
      MandelDim.IsFatouCoordOn (Work.Pert.F0f f₀) Φ₀
        (Metric.ball (Work.Pert.Xc d (((-M : ℝ) : ℂ))) (M / 40)) ∧
      (∀ ζ ∈ Metric.ball (Work.Pert.Xc d (((-M : ℝ) : ℂ))) (M / 40),
        Work.Pert.Xc d (Φ₀ ζ) = ζ ∧ ‖Φ₀ ζ - ζ‖ ≤ M / 40) ∧
      Φ₀ (Work.Pert.Xc d (((-M : ℝ) : ℂ))) = (((-M : ℝ)) : ℂ) ∧
      ‖Work.Pert.Xc d (((-M : ℝ) : ℂ)) - (((-M : ℝ)) : ℂ)‖ ≤ M / 40 := by
  obtain ⟨R₁, -, hR₁⟩ := anchor_scale_geom d
  obtain ⟨R₂, -, hR₂⟩ := anchor_scale_close d
  obtain ⟨R₃, -, hR₃⟩ := anchor_scale_deriv d
  obtain ⟨R₄, -, hR₄⟩ := Xc_sub_id_le d
  refine ⟨max 1 (max R₁ (max R₂ (max R₃ R₄))), ?_, ?_⟩
  · have h := le_max_left (1 : ℝ) (max R₁ (max R₂ (max R₃ R₄)))
    linarith
  · intro M hM
    have hM1 : (1 : ℝ) ≤ M := le_trans (le_max_left _ _) hM
    have hMR₁ : R₁ ≤ M :=
      le_trans (le_trans (le_max_left R₁ _) (le_max_right 1 _)) hM
    have hMR₂ : R₂ ≤ M :=
      le_trans (le_trans (le_trans (le_max_left R₂ _) (le_max_right R₁ _)) (le_max_right 1 _)) hM
    have hMR₃ : R₃ ≤ M :=
      le_trans (le_trans (le_trans (le_trans (le_max_left R₃ R₄) (le_max_right R₂ _))
        (le_max_right R₁ _)) (le_max_right 1 _)) hM
    have hMR₄ : R₄ ≤ M :=
      le_trans (le_trans (le_trans (le_trans (le_max_right R₃ R₄) (le_max_right R₂ _))
        (le_max_right R₁ _)) (le_max_right 1 _)) hM
    obtain ⟨h8, hballQ⟩ := hR₁ M hMR₁
    have hclose := hR₂ M hMR₂
    have hder := hR₃ M hMR₃
    have hsharp := hR₄ M hMR₄
    have hMpos : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM1
    have hnormw : ‖(((-M : ℝ)) : ℂ)‖ = M := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hMpos.le]
    have hbw : 0 < ‖(((-M : ℝ)) : ℂ)‖ / 4 := by rw [hnormw]; linarith
    have hder' : ∀ u ∈ Metric.ball (((-M : ℝ)) : ℂ) (‖(((-M : ℝ)) : ℂ)‖ / 4),
        ‖deriv (fun v : ℂ => MandelDim.tau0 (d.φ v)) u - 1‖ ≤ 1 / 2 :=
      fun u hu => hder u (by simpa only [hnormw] using hu)
    obtain ⟨Φ₀, hinv, hfat⟩ :=
      Work.Pert.exists_fatouCoord_inv_tau0_phi (w₀ := (((-M : ℝ)) : ℂ)) d
        (by simpa only [hnormw] using hballQ)
        (by simpa only [hnormw] using h8)
        (by simpa only [hnormw] using hclose)
        hder'
    refine ⟨Φ₀, ?_, ?_, ?_, ?_⟩
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
        (differentiableAt_of_norm_deriv_sub_one_le' (hder' u hu)).differentiableWithinAt
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
