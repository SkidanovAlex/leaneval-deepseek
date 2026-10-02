import Mathlib
import Submission.Work.MRMT.Found.norm_symm_sub_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

/-- Boundedness of the conjugacy error.

If `Φ : ℂ ≃ₜ ℂ` is a homeomorphism of the plane which is close to the identity
outside the ball of radius `R` (`‖Φ z - z‖ ≤ C / ‖z‖`), and `F` agrees outside the
ball of radius `R` with the antiholomorphic quadratic map `z ↦ (star z) ^ 2 + c`,
then `Φ` conjugates `F` to a map which differs from `z ↦ (star z) ^ 2` by a
bounded amount.

The bound comes from two regions.  Far out (`‖w‖ ≥ S`), writing `w` for
`Φ.symm z`, one has `F w = (star w) ^ 2 + c`, so
`Φ (F w) - (star (Φ w)) ^ 2
   = (Φ (F w) - F w) + ((star w) ^ 2 - (star (Φ w)) ^ 2) + c`,
where the first term is `≤ C` (decay of `Φ` at `F w`, whose norm is `≳ ‖w‖ ^ 2 ≫ R`),
and the second term is controlled by the decay of `Φ` at `w`:
`(star w) ^ 2 - (star (Φ w)) ^ 2 = star (w - Φ w) * star (w + Φ w)` has norm
`≤ (C / ‖w‖) * (3 ‖w‖) = 3 C`.  On the compact disc `‖w‖ ≤ S` the same expression
is continuous, hence bounded. -/
theorem bounded_conj_of_decay {c : ℂ} {Φ : ℂ ≃ₜ ℂ} {F : ℂ → ℂ} {R C : ℝ}
    (hR : 1 ≤ R) (hC : 0 ≤ C) (hcont : Continuous F)
    (hdec : ∀ z : ℂ, R ≤ ‖z‖ → ‖Φ z - z‖ ≤ C / ‖z‖)
    (hasymp : ∀ z : ℂ, R ≤ ‖z‖ → F z = (star z) ^ 2 + c) :
    ∃ K : ℝ, ∀ z : ℂ, ‖Φ (F ((Φ.symm : ℂ → ℂ) z)) - (star z) ^ 2‖ ≤ K := by
  classical
  set S : ℝ := max 1 (max R (max (R + ‖c‖) C + 1)) with hSdef
  have hS1 : 1 ≤ S := by rw [hSdef]; exact le_max_left _ _
  have hS0 : 0 ≤ S := le_trans zero_le_one hS1
  have hSR : R ≤ S := by
    rw [hSdef]
    exact le_trans (le_max_left R _) (le_max_right 1 _)
  have hSRc : R + ‖c‖ ≤ S := by
    rw [hSdef]
    have h1 : R + ‖c‖ ≤ max (R + ‖c‖) C := le_max_left _ _
    have h2 : max (R + ‖c‖) C ≤ max (R + ‖c‖) C + 1 := le_add_of_nonneg_right zero_le_one
    have h3 : max (R + ‖c‖) C + 1 ≤ max R (max (R + ‖c‖) C + 1) := le_max_right _ _
    exact le_trans h1 (le_trans h2 (le_trans h3 (le_max_right 1 _)))
  have hSC : C ≤ S := by
    rw [hSdef]
    have h1 : C ≤ max (R + ‖c‖) C := le_max_right _ _
    have h2 : max (R + ‖c‖) C ≤ max (R + ‖c‖) C + 1 := le_add_of_nonneg_right zero_le_one
    have h3 : max (R + ‖c‖) C + 1 ≤ max R (max (R + ‖c‖) C + 1) := le_max_right _ _
    exact le_trans h1 (le_trans h2 (le_trans h3 (le_max_right 1 _)))
  have hS2 : S ≤ S ^ 2 := by nlinarith [hS1]
  -- ------------------------------------------------------------------ --
  -- The far-region bound.
  -- ------------------------------------------------------------------ --
  have hfar : ∀ w : ℂ, S ≤ ‖w‖ → ‖Φ (F w) - (star (Φ w)) ^ 2‖ ≤ 4 * C + ‖c‖ := by
    intro w hw
    have hRw : R ≤ ‖w‖ := le_trans hSR hw
    have hw1 : 1 ≤ ‖w‖ := le_trans hS1 hw
    have hasympw : F w = (star w) ^ 2 + c := hasymp w hRw
    -- `F w` lies far enough out that the decay hypothesis applies to it.
    have hnorm_sq : ‖(star w) ^ 2‖ = ‖w‖ ^ 2 := by rw [norm_pow, norm_star]
    have h1 : ‖(star w) ^ 2‖ - ‖c‖ ≤ ‖(star w) ^ 2 + c‖ := by
      have := norm_sub_norm_le ((star w) ^ 2) (-c)
      simpa using this
    have h2 : S ^ 2 ≤ ‖w‖ ^ 2 := by
      have := mul_self_le_mul_self hS0 hw
      nlinarith [this]
    have h3 : R + ‖c‖ ≤ ‖w‖ ^ 2 := le_trans hSRc (le_trans hS2 h2)
    have hFw_lower : R ≤ ‖F w‖ := by
      rw [hasympw]
      linarith [h1, h3, hnorm_sq]
    have hdecF : ‖Φ (F w) - F w‖ ≤ C := by
      have hh := hdec (F w) hFw_lower
      have hCdivF : C / ‖F w‖ ≤ C := div_le_self hC (le_trans hR hFw_lower)
      linarith
    -- The square-difference term is bounded by `3 C`.
    have hsq : ‖(star w) ^ 2 - (star (Φ w)) ^ 2‖ ≤ 3 * C := by
      have key : (star w) ^ 2 - (star (Φ w)) ^ 2 = star (w - Φ w) * star (w + Φ w) := by
        simp only [star_sub, star_add]; ring
      rw [key, norm_mul, norm_star, norm_star]
      have hdw : ‖w - Φ w‖ ≤ C / ‖w‖ := by
        rw [norm_sub_rev]; exact hdec w hRw
      have hsum : ‖w + Φ w‖ ≤ 3 * ‖w‖ := by
        have h4 : ‖w + Φ w‖ ≤ ‖w‖ + ‖Φ w‖ := norm_add_le w (Φ w)
        have h5 : ‖Φ w‖ ≤ ‖w‖ + ‖Φ w - w‖ := by
          have := norm_add_le w (Φ w - w)
          rwa [add_sub_cancel] at this
        have h6 : ‖Φ w - w‖ ≤ C / ‖w‖ := hdec w hRw
        have h7 : C / ‖w‖ ≤ C := div_le_self hC hw1
        have h8 : C ≤ ‖w‖ := le_trans hSC hw
        linarith
      have hCdiv_nn : 0 ≤ C / ‖w‖ := div_nonneg hC (norm_nonneg w)
      calc ‖w - Φ w‖ * ‖w + Φ w‖
          ≤ (C / ‖w‖) * (3 * ‖w‖) := mul_le_mul hdw hsum (norm_nonneg _) hCdiv_nn
        _ = 3 * C := by field_simp
    -- Assemble the three pieces.
    have key2 : F w - (star (Φ w)) ^ 2 = ((star w) ^ 2 - (star (Φ w)) ^ 2) + c := by
      rw [hasympw]; ring
    have hg_eq : Φ (F w) - (star (Φ w)) ^ 2
        = (Φ (F w) - F w) + (F w - (star (Φ w)) ^ 2) := by ring
    rw [hg_eq, key2]
    calc ‖(Φ (F w) - F w) + ((star w) ^ 2 - (star (Φ w)) ^ 2 + c)‖
        ≤ ‖Φ (F w) - F w‖ + ‖(star w) ^ 2 - (star (Φ w)) ^ 2 + c‖ := norm_add_le _ _
      _ ≤ ‖Φ (F w) - F w‖ + (‖(star w) ^ 2 - (star (Φ w)) ^ 2‖ + ‖c‖) :=
          add_le_add_right (norm_add_le _ _) _
      _ ≤ 4 * C + ‖c‖ := by linarith [hdecF, hsq]
  -- ------------------------------------------------------------------ --
  -- The compact-region bound.
  -- ------------------------------------------------------------------ --
  have hgcont : Continuous (fun w : ℂ => Φ (F w) - (star (Φ w)) ^ 2) := by
    refine Continuous.sub ?_ ?_
    · exact Φ.continuous.comp hcont
    · exact (continuous_star.comp Φ.continuous).pow 2
  obtain ⟨K2, hK2⟩ := (isCompact_closedBall (0 : ℂ) S).exists_bound_of_continuousOn
      hgcont.continuousOn
  refine ⟨max K2 (4 * C + ‖c‖), fun z => ?_⟩
  have hbound : ∀ w : ℂ, ‖Φ (F w) - (star (Φ w)) ^ 2‖ ≤ max K2 (4 * C + ‖c‖) := by
    intro w
    rcases le_or_gt ‖w‖ S with hle | hlt
    · refine le_trans (hK2 w ?_) (le_max_left _ _)
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hle
    · exact le_trans (hfar w (le_of_lt hlt)) (le_max_right _ _)
  have := hbound ((Φ.symm : ℂ → ℂ) z)
  simpa [Homeomorph.apply_symm_apply] using this

end Work.FBif
