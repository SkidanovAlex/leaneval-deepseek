import Mathlib
import Submission.Work.MRMT.Found.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-!
# The inverse of a homeomorphism of `ℂ` close to the identity near infinity

Let `F : ℂ ≃ₜ ℂ` be a homeomorphism of the plane whose displacement decays like
`‖F z - z‖ ≤ C / ‖z‖` outside the ball of radius `R`.  Then `F.symm` satisfies the same
kind of decay, with constant `2 C` and starting at radius `8 (R + C + 1)`; this is
`norm_symm_sub_le`, the statement of the assignment.

The mathematical content is that `F` maps the closed ball of radius `R` into the closed
ball of radius `R + C`, so that a point of large norm has a preimage of norm `> R`, where
the decay hypothesis applies.  The boundedness of `F '' ball R` is obtained from the
compactness of `F '' closedBall R`, and the containment `F '' closedBall R ⊆ closedBall (R+C)`
is proved by a "ray" argument: if `‖F y‖ > R + C` with `‖y‖ ≤ R`, the points
`t ↦ F.symm ((1+t) • F y)`, `t ≥ 0`, never cross the sphere of radius `R` (at a crossing the
decay hypothesis would force `‖F y‖ ≤ R + C`), and hence would lie in the bounded set
`F '' ball R` while having unbounded norm.  The "never cross" step is the intermediate
value theorem for the continuous function `t ↦ ‖F.symm ((1+t) • F y)‖ - R` on `[0, T]`.
-/

open Metric

/-- **Quantitative bound on the image of a ball.**  If `‖F z - z‖ ≤ C / ‖z‖` for
`‖z‖ ≥ R` then `F` maps the closed ball of radius `R` into the closed ball of
radius `R + C`. -/
theorem image_closedBall_subset_closedBall_of_decay {F : ℂ ≃ₜ ℂ} {C R : ℝ}
    (hR : 1 ≤ R) (hC : 0 ≤ C)
    (hdec : ∀ z : ℂ, R ≤ ‖z‖ → ‖F z - z‖ ≤ C / ‖z‖) :
    ∀ p ∈ (F : ℂ → ℂ) '' Metric.closedBall 0 R, ‖p‖ ≤ R + C := by
  rintro p ⟨y, hy, rfl⟩
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy
  by_contra hcon
  rw [not_le] at hcon
  have hRpos : (0 : ℝ) < R := by linarith
  have hCR : C / R ≤ C := by
    rw [div_le_iff₀ hRpos]
    nlinarith
  have hy1 : (1 : ℝ) ≤ ‖F y‖ := by linarith
  have hyR : ‖y‖ < R := by
    rcases lt_or_eq_of_le hy with h | h
    · exact h
    · exfalso
      have h1 : ‖F y - y‖ ≤ C / R := by
        have := hdec y (le_of_eq h.symm)
        rwa [h] at this
      have h2 : ‖F y‖ ≤ ‖F y - y‖ + ‖y‖ := by
        have := norm_add_le (F y - y) y
        rwa [sub_add_cancel] at this
      have h3 : ‖F y‖ ≤ C + R := by
        calc ‖F y‖ ≤ ‖F y - y‖ + ‖y‖ := h2
          _ ≤ C / R + R := add_le_add h1 (le_of_eq h)
          _ ≤ C + R := by linarith
      linarith
  have hfyball : F y ∈ (F : ℂ → ℂ) '' Metric.ball 0 R :=
    ⟨y, by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hyR, rfl⟩
  -- `F '' ball 0 R` is contained in the compact set `F '' closedBall 0 R`, hence bounded.
  have hcmp : IsCompact ((F : ℂ → ℂ) '' Metric.closedBall 0 R) :=
    (isCompact_closedBall (0 : ℂ) R).image F.continuous
  have hbddU : Bornology.IsBounded ((F : ℂ → ℂ) '' Metric.ball 0 R) :=
    hcmp.isBounded.subset (Set.image_mono Metric.ball_subset_closedBall)
  obtain ⟨B, hB⟩ := hbddU.exists_norm_le
  have hB1 : (1 : ℝ) ≤ B := le_trans hy1 (hB (F y) hfyball)
  have hBpos : B < (1 + (B + 1)) * ‖F y‖ := by
    have h : (1 + (B + 1)) * 1 ≤ (1 + (B + 1)) * ‖F y‖ :=
      mul_le_mul_of_nonneg_left hy1 (by linarith)
    linarith
  -- The ray through `F y`, pulled back by `F`.
  let Z : ℝ → ℂ := fun t => (F.symm : ℂ → ℂ) ((1 + t) • (F y))
  have hZcont : Continuous Z := by
    unfold Z
    exact F.symm.continuous.comp ((continuous_const.add continuous_id).smul continuous_const)
  have hFZ : ∀ t : ℝ, F (Z t) = (1 + t) • (F y) := by
    intro t; simp only [Z]; rw [F.apply_symm_apply]
  have hnormFZ : ∀ t : ℝ, 0 ≤ t → ‖(1 + t) • (F y)‖ = (1 + t) * ‖F y‖ := by
    intro t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + t)]
  -- The ray never meets the sphere of radius `R`.
  have hZne : ∀ t : ℝ, 0 ≤ t → ‖Z t‖ ≠ R := by
    intro t ht hRZ
    have h1 : ‖F (Z t) - Z t‖ ≤ C / R := by
      have := hdec (Z t) (le_of_eq hRZ.symm)
      rwa [hRZ] at this
    have h2 : ‖F (Z t)‖ ≤ ‖F (Z t) - Z t‖ + ‖Z t‖ := by
      have := norm_add_le (F (Z t) - Z t) (Z t)
      rwa [sub_add_cancel] at this
    have h3 : ‖F (Z t)‖ = (1 + t) * ‖F y‖ := by rw [hFZ t, hnormFZ t ht]
    have h4 : ‖F y‖ ≤ (1 + t) * ‖F y‖ := by nlinarith [norm_nonneg (F y)]
    linarith [hcon]
  have hZT : ‖Z (B + 1)‖ < R := by
    by_contra hgt
    rw [not_lt] at hgt
    have hlt : R < ‖Z (B + 1)‖ := lt_of_le_of_ne hgt (Ne.symm (hZne (B + 1) (by linarith)))
    have hcont : ContinuousOn (fun t : ℝ => ‖Z t‖ - R) (Set.Icc (0 : ℝ) (B + 1)) :=
      (hZcont.norm.sub continuous_const).continuousOn
    have hIcc := intermediate_value_Icc (show (0 : ℝ) ≤ B + 1 by linarith) hcont
    have hZ0 : Z 0 = y := by simp [Z, F.symm_apply_apply]
    have hmem0 : (0 : ℝ) ∈
        Set.Icc ((fun t : ℝ => ‖Z t‖ - R) 0) ((fun t : ℝ => ‖Z t‖ - R) (B + 1)) := by
      constructor
      · show ‖Z 0‖ - R ≤ 0
        rw [hZ0]; linarith
      · show 0 ≤ ‖Z (B + 1)‖ - R
        linarith
    obtain ⟨t, ht, hft⟩ := hIcc hmem0
    have : ‖Z t‖ = R := by linarith [hft]
    exact hZne t ht.1 this
  have hmemT : F (Z (B + 1)) ∈ (F : ℂ → ℂ) '' Metric.ball 0 R :=
    ⟨Z (B + 1), by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hZT, rfl⟩
  have hBT := hB _ hmemT
  rw [hFZ (B + 1), hnormFZ (B + 1) (by linarith)] at hBT
  linarith [hBT, hBpos]

theorem norm_symm_sub_le {F : ℂ ≃ₜ ℂ} {C R : ℝ} (hR : 1 ≤ R) (hC : 0 ≤ C)
    (hdec : ∀ z : ℂ, R ≤ ‖z‖ → ‖F z - z‖ ≤ C / ‖z‖) :
    ∀ w : ℂ, 8 * (R + C + 1) ≤ ‖w‖ → ‖(F.symm : ℂ → ℂ) w - w‖ ≤ 2 * C / ‖w‖ := by
  intro w hw
  have hkey := image_closedBall_subset_closedBall_of_decay hR hC hdec
  set z : ℂ := (F.symm : ℂ → ℂ) w with hz
  have hFz : F z = w := by rw [hz]; exact F.apply_symm_apply w
  -- `z` lies outside the ball of radius `R`.
  have hzR : R ≤ ‖z‖ := by
    by_contra hlt
    rw [not_le] at hlt
    have hmem : w ∈ (F : ℂ → ℂ) '' Metric.closedBall 0 R :=
      ⟨z, by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact le_of_lt hlt, hFz⟩
    have hbound := hkey w hmem
    nlinarith [hw, hR, hC]
  have hwpos : (0 : ℝ) < ‖w‖ := by nlinarith [hw, hR, hC]
  have h1 : ‖w - z‖ ≤ C / ‖z‖ := by
    have := hdec z hzR
    rwa [hFz] at this
  have hCz : C / ‖z‖ ≤ C := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖z‖)]
    nlinarith
  -- `‖z‖` is at least `‖w‖ - C`, hence at least `‖w‖ / 2`.
  have hzw : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
    have := norm_add_le z (w - z)
    rwa [add_sub_cancel] at this
  have hC2 : 2 * C ≤ ‖w‖ := by nlinarith [hw, hR, hC]
  have hzge2 : ‖w‖ / 2 ≤ ‖z‖ := by linarith
  calc ‖(F.symm : ℂ → ℂ) w - w‖ = ‖z - w‖ := by rw [← hz]
    _ = ‖w - z‖ := norm_sub_rev z w
    _ ≤ C / ‖z‖ := h1
    _ ≤ C / (‖w‖ / 2) := div_le_div_of_nonneg_left hC (by linarith) hzge2
    _ = 2 * C / ‖w‖ := by rw [div_div_eq_mul_div]; ring

end Work.MRMT.Found
