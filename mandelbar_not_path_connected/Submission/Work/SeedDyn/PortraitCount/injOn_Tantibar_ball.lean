import Mathlib
import Submission.Work.SeedDyn.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedDyn.PortraitCount

/-! ## Local injectivity of `Tantibar c` off the critical point

`Tantibar c z = conj z ^ 2 + c` is the composition of the conjugation (a homeomorphism of the
plane) with the polynomial `w ↦ w ^ 2 + conj c`, which is a local bijection exactly where
`w ≠ 0`.  On the ball of radius `‖y'‖ / 2` about a point `y' ≠ 0` this gives global injectivity,
with an elementary proof: two distinct points with the same image satisfy `z₁ = -z₂`, and then the
triangle inequality around `y'` gives `‖y'‖ < ‖y'‖`. -/

theorem injOn_Tantibar_ball {c y' : ℂ} (hy' : y' ≠ 0) :
    Set.InjOn (LeanEval.ComplexAnalysis.Tantibar c) (Metric.ball y' (‖y'‖ / 2)) := by
  have hpos : 0 < ‖y'‖ / 2 := by
    have := norm_pos_iff.mpr hy'
    linarith
  intro z₁ hz₁ z₂ hz₂ h
  rw [Metric.mem_ball, dist_eq_norm] at hz₁ hz₂
  have hsq : (starRingEnd ℂ z₁) ^ 2 = (starRingEnd ℂ z₂) ^ 2 := by
    have h' : (starRingEnd ℂ z₁) ^ 2 + c = (starRingEnd ℂ z₂) ^ 2 + c := h
    exact add_right_cancel h'
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
  · exact star_inj.mp h1
  · exfalso
    have hz₂ : z₂ = -z₁ := by
      have : (starRingEnd ℂ) z₁ = (starRingEnd ℂ) (-z₂) := by
        rw [map_neg]; exact h1
      have h2 : z₁ = -z₂ := star_inj.mp this
      rw [h2, neg_neg]
    have hnorm : 2 * ‖z₁‖ < ‖y'‖ := by
      have h3 : ‖z₁ - z₂‖ ≤ ‖z₁ - y'‖ + ‖z₂ - y'‖ := by
        calc ‖z₁ - z₂‖ = ‖(z₁ - y') - (z₂ - y')‖ := by ring_nf
          _ ≤ ‖z₁ - y'‖ + ‖z₂ - y'‖ := norm_sub_le _ _
      have h4 : ‖z₁ - z₂‖ = 2 * ‖z₁‖ := by
        rw [hz₂, sub_neg_eq_add, ← two_mul, norm_mul]
        norm_num
      linarith
    have hfinal : ‖y'‖ < ‖y'‖ := by
      have h5 : ‖y'‖ ≤ ‖y' - z₁‖ + ‖z₁‖ := by
        calc ‖y'‖ = ‖(y' - z₁) + z₁‖ := by ring_nf
          _ ≤ ‖y' - z₁‖ + ‖z₁‖ := norm_add_le _ _
      rw [norm_sub_rev y' z₁] at h5
      linarith
    exact lt_irrefl _ hfinal

end Work.SeedDyn.PortraitCount
