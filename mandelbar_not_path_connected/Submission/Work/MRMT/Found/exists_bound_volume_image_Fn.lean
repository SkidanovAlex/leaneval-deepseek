import Mathlib
import Submission.Work.MRMT.Found.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Filter Topology Complex Function
open scoped Topology ENNReal

/-- The images of a fixed compact set under the diffeomorphism approximants `F n` have
uniformly bounded (Lebesgue) area, eventually in `n`.

This uses only the *locally uniform* convergence `F n → φ` of the principal data: on the
compact set `L` the convergence is uniform, so eventually `F n` maps `L` into a fixed ball
containing `φ '' L`, whence the measure of `F n '' L` is bounded by the (finite) measure of
that ball.  No derivative or Beltrami information is needed. -/
theorem exists_bound_volume_image_Fn {μ : ℂ → ℂ} (d : PrincipalData μ) {L : Set ℂ}
    (hL : IsCompact L) :
    ∃ Cb : ℝ, ∀ᶠ n in Filter.atTop,
      ((MeasureTheory.volume : MeasureTheory.Measure ℂ) (((d.Fn n) : ℂ → ℂ) '' L)).toReal ≤ Cb := by
  -- `F n` converges locally uniformly to `φ`, hence uniformly on the compact set `L`.
  have hunif : TendstoUniformlyOn (fun n => ((d.Fn n) : ℂ → ℂ)) (d.φ : ℂ → ℂ) Filter.atTop L :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp d.tendsto_Fn) L hL
  -- the image `φ '' L` is compact, hence contained in a closed ball.
  have hφL : IsCompact ((d.φ : ℂ → ℂ) '' L) := hL.image d.φ.continuous
  obtain ⟨R, hR⟩ := hφL.isBounded.exists_norm_le
  -- eventually `F n` maps `L` into the ball of radius `R + 1`.
  have hev : ∀ᶠ n in Filter.atTop,
      ((d.Fn n : ℂ → ℂ) '' L) ⊆ Metric.closedBall (0 : ℂ) (R + 1) := by
    have hδ : ∀ᶠ n in Filter.atTop,
        ∀ x ∈ L, dist ((d.φ : ℂ → ℂ) x) ((d.Fn n : ℂ → ℂ) x) < 1 :=
      (Metric.tendstoUniformlyOn_iff.mp hunif) 1 one_pos
    filter_upwards [hδ] with n hn y hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [Metric.mem_closedBall, dist_zero_right]
    have hz' : dist ((d.φ : ℂ → ℂ) z) 0 ≤ R := by
      rw [dist_zero_right]; exact hR _ ⟨z, hz, rfl⟩
    refine le_of_lt ?_
    calc ‖(d.Fn n : ℂ → ℂ) z‖
        = dist ((d.Fn n : ℂ → ℂ) z) 0 := (dist_zero_right _).symm
      _ ≤ dist ((d.Fn n : ℂ → ℂ) z) ((d.φ : ℂ → ℂ) z) + dist ((d.φ : ℂ → ℂ) z) 0 :=
          dist_triangle _ _ _
      _ = dist ((d.φ : ℂ → ℂ) z) ((d.Fn n : ℂ → ℂ) z) + dist ((d.φ : ℂ → ℂ) z) 0 := by
          rw [dist_comm ((d.Fn n : ℂ → ℂ) z)]
      _ < 1 + R := add_lt_add_of_lt_of_le (hn z hz) hz'
      _ = R + 1 := by ring
  refine ⟨(MeasureTheory.volume (Metric.closedBall (0 : ℂ) (R + 1))).toReal, ?_⟩
  exact hev.mono fun n hn =>
    ENNReal.toReal_mono (isCompact_closedBall (0 : ℂ) (R + 1)).measure_lt_top.ne
      (MeasureTheory.measure_mono hn)

end Work.MRMT.Found
