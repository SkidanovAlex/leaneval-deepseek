import Mathlib
import Submission.Work.MRMT.Found.norm_symm_sub_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- If `F : ℂ ≃ₜ ℂ` is a homeomorphism of the plane whose displacement decays like
`‖F z - z‖ ≤ C / ‖z‖` outside the ball of radius `R`, then `F` is globally bounded by
`max R ‖z‖ + C` on the point `z`.

Outside the ball of radius `R` this is immediate from the decay hypothesis.  Inside the
ball it follows from the fact (proved in `norm_symm_sub_le`) that `F` maps the closed ball
of radius `R` into the closed ball of radius `R + C`, via the topological "ray" argument
relying on `F` being a homeomorphism. -/
theorem norm_image_le_of_decay {F : ℂ ≃ₜ ℂ} {C R : ℝ} (hR : 1 ≤ R) (hC : 0 ≤ C)
    (hdec : ∀ z : ℂ, R ≤ ‖z‖ → ‖F z - z‖ ≤ C / ‖z‖) :
    ∀ z : ℂ, ‖(F : ℂ → ℂ) z‖ ≤ max R ‖z‖ + C := by
  intro z
  by_cases hz : ‖z‖ ≤ R
  · -- Inside the closed ball of radius `R`: use the topological inner bound.
    have hmem : F z ∈ (F : ℂ → ℂ) '' Metric.closedBall 0 R :=
      ⟨z, by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hz, rfl⟩
    have hbound := image_closedBall_subset_closedBall_of_decay hR hC hdec (F z) hmem
    rw [max_eq_left hz]
    exact hbound
  · -- Outside the ball: the decay hypothesis applies directly.
    have hlt : R < ‖z‖ := not_le.mp hz
    have hRnle : R ≤ ‖z‖ := le_of_lt hlt
    have hznorm : (1 : ℝ) ≤ ‖z‖ := le_trans hR hRnle
    have hzpos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le (by linarith) hznorm
    have h1 : ‖F z‖ ≤ ‖z‖ + C / ‖z‖ := by
      have htri : ‖F z‖ ≤ ‖F z - z‖ + ‖z‖ := by
        have := norm_add_le (F z - z) z
        rwa [sub_add_cancel] at this
      have hd := hdec z hRnle
      calc ‖F z‖ ≤ ‖F z - z‖ + ‖z‖ := htri
        _ ≤ C / ‖z‖ + ‖z‖ := add_le_add hd le_rfl
        _ = ‖z‖ + C / ‖z‖ := by ring
    have h2 : C / ‖z‖ ≤ C := by
      rw [div_le_iff₀ hzpos]
      nlinarith
    rw [max_eq_right hRnle]
    linarith

end Work.MRMT.Found
