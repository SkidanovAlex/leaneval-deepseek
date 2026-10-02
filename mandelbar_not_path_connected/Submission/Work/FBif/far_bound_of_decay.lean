import Mathlib
import Submission.Work.MRMT.Found.norm_symm_sub_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

/-- **The far-field bound.**  If a homeomorphism `Φ` of `ℂ` is `C/‖·‖`-close to the
identity outside the ball of radius `R` (`C ≤ 1`, `R ≥ 1`) and `F` agrees with the
antiholomorphic map `z ↦ z̄² + c` there, then the conjugate `Φ ∘ F ∘ Φ⁻¹` agrees with
`z ↦ z̄² + c` up to `4C` outside a radius `T` depending only on `R` and `c` (not on
`Φ`, `F` or `C`).

The uniform choice of `T` is the point: outside radius `R` the map `Φ` is within
`1/R` of the identity, so it squeezes the ball of radius `S` into the ball of radius
`S + 1` (`Work.MRMT.Found.image_closedBall_subset_closedBall_of_decay`), hence any `z`
of norm `> S + 1` has preimage `w = Φ⁻¹ z` of norm `> S`.  For such `w` all three
pieces — `Φ` at `F w`, the displacement `z - w`, and the algebraic identity
`(w̄)² - (z̄)² = (w̄ - z̄)(w̄ + z̄)` — are small. -/
theorem far_bound_of_decay {R : ℝ} (hR : 1 ≤ R) (c : ℂ) :
    ∃ T : ℝ, 0 ≤ T ∧
      ∀ (C : ℝ) (Φ : ℂ ≃ₜ ℂ) (F : ℂ → ℂ), 0 ≤ C → C ≤ 1 →
        (∀ z : ℂ, R ≤ ‖z‖ → ‖Φ z - z‖ ≤ C / ‖z‖) →
        (∀ z : ℂ, R ≤ ‖z‖ → F z = (star z) ^ 2 + c) →
        ∀ z : ℂ, T ≤ ‖z‖ →
          ‖Φ (F ((Φ.symm : ℂ → ℂ) z)) - (star z) ^ 2 - c‖ ≤ 4 * C := by
  -- The radius outside which every quantity behaves: `≥ R`, `≥ 1` and `S² ≥ R + ‖c‖`.
  set S : ℝ := max R (max 1 (Real.sqrt (R + ‖c‖))) with hSdef
  refine ⟨S + 2, ?_, ?_⟩
  · have hS1 : (1 : ℝ) ≤ S := by
      rw [hSdef]; exact le_trans (le_max_left 1 _) (le_max_right R _)
    linarith
  · intro C Φ F hC0 hC1 hdec hasymp z hz
    have hS_R : R ≤ S := by rw [hSdef]; exact le_max_left R _
    have hS_1 : (1 : ℝ) ≤ S := by
      rw [hSdef]; exact le_trans (le_max_left 1 _) (le_max_right R _)
    have hS_sqrt : Real.sqrt (R + ‖c‖) ≤ S := by
      rw [hSdef]; exact le_trans (le_max_right 1 _) (le_max_right R _)
    have hS_nonneg : (0 : ℝ) ≤ S := le_trans (by norm_num) hS_1
    have hS_sq : R + ‖c‖ ≤ S ^ 2 := by
      have h2 : Real.sqrt (R + ‖c‖) * Real.sqrt (R + ‖c‖) ≤ S * S :=
        mul_le_mul hS_sqrt hS_sqrt (Real.sqrt_nonneg _) hS_nonneg
      have h3 : Real.sqrt (R + ‖c‖) * Real.sqrt (R + ‖c‖) = R + ‖c‖ := by
        rw [← pow_two]; exact Real.sq_sqrt (add_nonneg (le_trans zero_le_one hR) (norm_nonneg c))
      have h4 : S * S = S ^ 2 := by rw [pow_two]
      linarith
    -- the preimage `w = Φ⁻¹ z`
    set w : ℂ := (Φ.symm : ℂ → ℂ) z with hwdef
    have hΦw : Φ w = z := by rw [hwdef]; exact Φ.apply_symm_apply z
    have hdecS : ∀ u : ℂ, S ≤ ‖u‖ → ‖Φ u - u‖ ≤ C / ‖u‖ :=
      fun u hu => hdec u (le_trans hS_R hu)
    have himg := Work.MRMT.Found.image_closedBall_subset_closedBall_of_decay
        (F := Φ) (C := C) (R := S) hS_1 hC0 hdecS
    -- `z` far out forces `w` far out
    have hwS : S ≤ ‖w‖ := by
      by_contra hlt
      rw [not_le] at hlt
      have hmem : w ∈ Metric.closedBall (0 : ℂ) S := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact le_of_lt hlt
      have hb : ‖Φ w‖ ≤ S + C := himg (Φ w) ⟨w, hmem, rfl⟩
      rw [hΦw] at hb
      have hlt2 : S + C < ‖z‖ := by linarith
      linarith
    have hwR : R ≤ ‖w‖ := le_trans hS_R hwS
    have hw1 : (1 : ℝ) ≤ ‖w‖ := le_trans hS_1 hwS
    have hFw : F w = (star w) ^ 2 + c := hasymp w hwR
    -- `F w` is far out, so `Φ` is close to the identity there too
    have hFwR : R ≤ ‖F w‖ := by
      rw [hFw]
      have hn : ‖(star w) ^ 2‖ = ‖w‖ ^ 2 := by rw [norm_pow, norm_star]
      have htri : ‖(star w) ^ 2‖ ≤ ‖(star w) ^ 2 + c‖ + ‖c‖ := by
        have h := norm_sub_le ((star w) ^ 2 + c) c
        rwa [add_sub_cancel_right] at h
      have hSsq : S ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ hS_nonneg hwS 2
      rw [hn] at htri
      nlinarith [hS_sq, htri, hSsq]
    have hdecFw : ‖Φ (F w) - F w‖ ≤ C / ‖F w‖ := hdec (F w) hFwR
    have hFw1 : (1 : ℝ) ≤ ‖F w‖ := le_trans hR hFwR
    -- the algebraic difference `(w̄)² - (z̄)²`
    have hdiff : ‖(star w) ^ 2 - (star z) ^ 2‖ ≤ ‖w - z‖ * (‖w‖ + ‖z‖) := by
      have hfac : (star w) ^ 2 - (star z) ^ 2 = (star w - star z) * (star w + star z) := by
        ring
      rw [hfac, norm_mul]
      have hstar : ‖star w - star z‖ = ‖w - z‖ := by rw [← star_sub, norm_star]
      rw [hstar]
      have hplus : ‖star w + star z‖ ≤ ‖w‖ + ‖z‖ := by
        calc ‖star w + star z‖ ≤ ‖star w‖ + ‖star z‖ := norm_add_le _ _
          _ = ‖w‖ + ‖z‖ := by rw [norm_star, norm_star]
      exact mul_le_mul_of_nonneg_left hplus (norm_nonneg _)
    have he : ‖w - z‖ ≤ C / ‖w‖ := by
      have h1 : ‖Φ w - w‖ ≤ C / ‖w‖ := hdec w hwR
      rw [hΦw] at h1
      rw [norm_sub_rev]; exact h1
    have hzle : ‖z‖ ≤ ‖w‖ + ‖w - z‖ := by
      have h := norm_add_le w (z - w)
      rw [add_sub_cancel] at h
      rwa [norm_sub_rev] at h
    -- numerical bookkeeping
    have hnum_F : C / ‖F w‖ ≤ C := by
      rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hFw1)]
      nlinarith [mul_le_mul_of_nonneg_left hFw1 hC0]
    have hnum_zw : ‖w - z‖ * (‖w‖ + ‖z‖) ≤ 3 * C := by
      have hwpos : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) hw1
      have hd0 : 0 ≤ ‖w - z‖ := norm_nonneg _
      have hdw : ‖w - z‖ * ‖w‖ ≤ C := by
        rw [le_div_iff₀ hwpos] at he; exact he
      have hd2 : ‖w - z‖ ^ 2 ≤ C := by
        have hcw : 0 ≤ C / ‖w‖ := div_nonneg hC0 hwpos.le
        have hsq : ‖w - z‖ ^ 2 ≤ (C / ‖w‖) ^ 2 := by
          rw [sq_le_sq, abs_of_nonneg hd0, abs_of_nonneg hcw]; exact he
        have hc1 : C / ‖w‖ ≤ C := by
          rw [div_le_iff₀ hwpos]; nlinarith [mul_le_mul_of_nonneg_left hw1 hC0]
        have hsq2 : (C / ‖w‖) ^ 2 ≤ C ^ 2 := by
          rw [sq_le_sq, abs_of_nonneg hcw, abs_of_nonneg hC0]; exact hc1
        have hC2 : C ^ 2 ≤ C := by nlinarith [hC0, hC1]
        linarith
      have hzw : ‖w‖ + ‖z‖ ≤ 2 * ‖w‖ + ‖w - z‖ := by linarith
      have hprod := mul_le_mul_of_nonneg_left hzw hd0
      nlinarith [hprod, hdw, hd2]
    have hstep1 : ‖Φ (F w) - (star z) ^ 2 - c‖
        ≤ ‖Φ (F w) - F w‖ + ‖(star w) ^ 2 - (star z) ^ 2‖ := by
      have heq : Φ (F w) - (star z) ^ 2 - c
          = (Φ (F w) - F w) + ((star w) ^ 2 - (star z) ^ 2) := by
        rw [hFw]; ring
      rw [heq]; exact norm_add_le _ _
    calc ‖Φ (F w) - (star z) ^ 2 - c‖
        ≤ ‖Φ (F w) - F w‖ + ‖(star w) ^ 2 - (star z) ^ 2‖ := hstep1
      _ ≤ C / ‖F w‖ + ‖w - z‖ * (‖w‖ + ‖z‖) := add_le_add hdecFw hdiff
      _ ≤ C + 3 * C := add_le_add hnum_F hnum_zw
      _ = 4 * C := by ring

end Work.FBif
