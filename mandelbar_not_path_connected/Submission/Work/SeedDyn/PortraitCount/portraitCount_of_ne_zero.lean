import Mathlib
import Submission.Work.SeedDyn.Defs
import Submission.Work.ELPull.landsN_image
import Submission.Work.Top.rayPt_injOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedDyn.PortraitCount

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The local injectivity of `Tantibar c` off the critical point

`Tantibar c z = conj z ^ 2 + c` is the composition of the conjugation (a homeomorphism of the
plane) with the polynomial `w ↦ w ^ 2 + conj c`, which is a local bijection exactly where
`w ≠ 0`.  On the ball of radius `‖y'‖ / 2` about a point `y' ≠ 0` this gives global injectivity,
with an elementary proof: two distinct points with the same image satisfy `z₁ = -z₂`, and then the
triangle inequality around `y'` gives `‖y'‖ < ‖y'‖`. -/

theorem injOn_Tantibar_ball {c y' : ℂ} (hy' : y' ≠ 0) :
    Set.InjOn (Tantibar c) (Metric.ball y' (‖y'‖ / 2)) := by
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

/-! ## The orbit-portrait count at a point off the critical point -/

/-- **P4 (the portrait count off the critical point).**  If two rays of angles `θ'`, `θ''` in
`[0,1)` land at the same point `y' ≠ 0` and have the same image angle `T θ' = T θ''`, then
`θ' = θ''`.

The two rays of angles `θ'` and `θ''` are mapped by `Tantibar c` onto the *same* ray (the ray of
angle `T θ' = T θ''`): at level `t` both ray points have the same image, the ray point of angle
`T θ'` at level `t ^ 2`.  Since `y'` is not the critical point, `Tantibar c` is injective near
`y'`, so for `t` close to `1` the two ray points coincide; then the Böttcher coordinate of that
common point reads off the angle, whence `θ' = θ''`. -/
theorem portraitCount_of_ne_zero {c : ℂ} (hN : Work.ELPull.DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c))
    {y' : ℂ} (hy' : y' ≠ 0) {θ' θ'' : ℝ}
    (h' : θ' ∈ Set.Ico (0 : ℝ) 1) (h'' : θ'' ∈ Set.Ico (0 : ℝ) 1)
    (l' : Work.ELPull.LandsN hN θ' y') (l'' : Work.ELPull.LandsN hN θ'' y')
    (hT : Work.ELPull.T θ' = Work.ELPull.T θ'') : θ' = θ'' := by
  have hrad : 0 < ‖y'‖ / 2 := by
    have hpos : 0 < ‖y'‖ := norm_pos_iff.mpr hy'
    linarith
  have hball : ∀ᶠ t in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      hN.rayPt θ' t ∈ Metric.ball y' (‖y'‖ / 2) ∧
        hN.rayPt θ'' t ∈ Metric.ball y' (‖y'‖ / 2) :=
    (l'.eventually (Metric.ball_mem_nhds y' hrad)).and
      (l''.eventually (Metric.ball_mem_nhds y' hrad))
  have hgt : ∀ᶠ t in nhdsWithin (1 : ℝ) (Set.Ioi 1), (1 : ℝ) < t :=
    self_mem_nhdsWithin
  obtain ⟨t, ht1, hA, hB⟩ := (hgt.and hball).exists
  have himg : Tantibar c (hN.rayPt θ' t) = Tantibar c (hN.rayPt θ'' t) := by
    have h1 := Work.ELPull.rayPt_Tantibar hN hφ (θ := θ') ht1
    have h2 := Work.ELPull.rayPt_Tantibar hN hφ (θ := θ'') ht1
    rw [← h1, ← h2, hT]
  have heq : hN.rayPt θ' t = hN.rayPt θ'' t := injOn_Tantibar_ball hy' hA hB himg
  exact (Work.Top.rayPt_injOn hN h'.1 h'.2 h''.1 h''.2 ht1 ht1 heq).1

end Work.SeedDyn.PortraitCount
