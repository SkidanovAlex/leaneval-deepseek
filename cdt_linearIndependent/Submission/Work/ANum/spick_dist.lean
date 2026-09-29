import Mathlib
import Submission.Work.ANum.spick_shim

open Complex Metric Set Filter
open scoped ComplexConjugate Topology

namespace Work.ANum

/-- The disc automorphism `w ↦ (c - w)/(1 - star c * w)` is an involution on the unit disc
(extended to the closed disc): if `‖c‖ < 1` and `‖x‖ ≤ 1` then `discAut c (discAut c x) = x`. -/
lemma discAut_invol {c x : ℂ} (hc : ‖c‖ < 1) (hx : ‖x‖ ≤ 1) :
    Commons.Analysis.Complex.spick.discAut c (Commons.Analysis.Complex.spick.discAut c x) = x := by
  have h1 : 1 - (starRingEnd ℂ) c * x ≠ 0 := by
    simpa only [Complex.star_def] using Commons.Analysis.Complex.spick.den_ne_zero hc hx
  have h2 : 1 - (starRingEnd ℂ) c * c ≠ 0 := by
    rw [Commons.Analysis.Complex.spick.one_sub_conj_mul c]
    simp only [ne_eq, Complex.ofReal_eq_zero]
    have hlt := (Commons.Analysis.Complex.spick.normSq_lt_one_iff_norm).mpr hc
    linarith
  unfold Commons.Analysis.Complex.spick.discAut
  have h1' : 1 - x * (starRingEnd ℂ) c ≠ 0 := by rw [mul_comm]; exact h1
  have h3 : 1 - (starRingEnd ℂ) c * ((c - x) / (1 - (starRingEnd ℂ) c * x)) ≠ 0 := by
    have he : 1 - (starRingEnd ℂ) c * ((c - x) / (1 - (starRingEnd ℂ) c * x)) =
        (1 - (starRingEnd ℂ) c * c) / (1 - (starRingEnd ℂ) c * x) := by
      field_simp
      ring
    rw [he]
    exact div_ne_zero h2 h1
  rw [div_eq_iff h3]
  field_simp [h1']
  ring

/-- **Schwarz–Pick lemma, distance (pseudohyperbolic) form.** A holomorphic self-map of the unit
disc is a contraction for the pseudohyperbolic distance: for `z, w` in the disc with `‖g z‖ < 1`,
`‖g w - g z‖ / ‖1 - star (g z) * g w‖ ≤ ‖w - z‖ / ‖1 - star z * w‖`.

Proof route (all machinery is in `Submission/Work/ANum/spick_shim.lean`, namespace
`Commons.Analysis.Complex.spick`): set `M := spick.discAut z`, `N := spick.discAut (g z)`,
`F := N ∘ g ∘ M`. Then `F 0 = 0`, `F` is differentiable on `ball 0 1` and maps it to
`closedBall 0 1` (`spick.differentiableOn_ball`, `spick.mapsTo_ball`,
`spick.differentiableOn_closedBall`, `spick.mapsTo_closedBall`), so Schwarz's lemma
`Complex.norm_le_norm_of_mapsTo_ball` gives `‖F (M w)‖ ≤ ‖M w‖`. Since `discAut` is an involution
(`spick.discAut c (spick.discAut c x) = x`, a direct `field_simp; ring` computation using
`spick.den_ne_zero` for the two denominators), `F (M w) = N (g w)`, and unfolding the two
`discAut`s turns the conclusion into exactly the stated inequality. -/
theorem spick_dist {g : ℂ → ℂ} {z w : ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1))
    (hmaps : Set.MapsTo g (Metric.ball (0 : ℂ) 1) (Metric.closedBall (0 : ℂ) 1))
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) (hgz : ‖g z‖ < 1) :
    ‖g w - g z‖ / ‖1 - star (g z) * g w‖ ≤ ‖w - z‖ / ‖1 - star z * w‖ := by
  have hw' : w ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hw
  let M : ℂ → ℂ := Commons.Analysis.Complex.spick.discAut z
  let N : ℂ → ℂ := Commons.Analysis.Complex.spick.discAut (g z)
  let F : ℂ → ℂ := N ∘ g ∘ M
  have hM_ball : MapsTo M (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    simpa [M] using Commons.Analysis.Complex.spick.mapsTo_ball hz
  have hM_diff : DifferentiableOn ℂ M (ball (0 : ℂ) 1) := by
    simpa [M] using Commons.Analysis.Complex.spick.differentiableOn_ball hz
  have hgM_diff : DifferentiableOn ℂ (g ∘ M) (ball (0 : ℂ) 1) := hg.comp hM_diff hM_ball
  have hgM_closed : MapsTo (g ∘ M) (ball (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := hmaps.comp hM_ball
  have hN_diff : DifferentiableOn ℂ N (closedBall (0 : ℂ) 1) := by
    simpa [N] using Commons.Analysis.Complex.spick.differentiableOn_closedBall hgz
  have hN_closed : MapsTo N (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
    simpa [N] using Commons.Analysis.Complex.spick.mapsTo_closedBall hgz
  have hF_diff : DifferentiableOn ℂ F (ball (0 : ℂ) 1) := by
    simpa [F, Function.comp_assoc] using hN_diff.comp hgM_diff hgM_closed
  have hF_maps : MapsTo F (ball (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
    simpa [F, Function.comp_assoc] using hN_closed.comp hgM_closed
  have hF0 : F 0 = 0 := by simp [F, M, N, Commons.Analysis.Complex.spick.discAut]
  have hMw : M w ∈ ball (0 : ℂ) 1 := hM_ball hw'
  have hS : ‖F (M w)‖ ≤ ‖M w‖ :=
    Complex.norm_le_norm_of_mapsTo_ball hF_diff hF_maps hF0 (mem_ball_zero_iff.mp hMw)
  have hinv : M (M w) = w := discAut_invol hz (le_of_lt hw)
  have hFMw : F (M w) = N (g w) := by simp only [F, Function.comp_apply, hinv]
  rw [hFMw] at hS
  have hmain : ‖(g z - g w) / (1 - (starRingEnd ℂ) (g z) * g w)‖ ≤
      ‖(z - w) / (1 - (starRingEnd ℂ) z * w)‖ := by
    simpa [N, M, Commons.Analysis.Complex.spick.discAut] using hS
  simp only [norm_div] at hmain
  rwa [norm_sub_rev (g z) (g w), norm_sub_rev z w] at hmain

end Work.ANum
