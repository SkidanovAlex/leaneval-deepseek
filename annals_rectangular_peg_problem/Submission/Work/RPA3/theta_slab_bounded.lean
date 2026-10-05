import Mathlib
import Submission.Work.RPA3.TubularHDefs

/-!
# Boundedness of the tubular map on the compact slab

`theta_slab_bounded`: for the parameter region `τ ∈ [-1,2]`, `|x| ≤ max X₀ 0`, `t ∈ [0,2π]` and
transverse variable `‖ξ‖ ≤ ε/2`, the coordinates `|q₁| + |p₁| + |p₂|` of

`θ(τ,x,t,ξ) = ℓ τ (x,t) + J (ξ₁ ∂_xℓ(τ)(x,t) + ξ₂ ∂_tℓ(τ)(x,t))`

are bounded by a constant `R` depending only on `L` and `T`.

The parameter region is a product of compacta, `θ` is continuous there (`continuous_thetaZ`), so
the norm `‖θ‖` is bounded; each of the three coordinates is dominated by `‖θ‖` (in the sup norm on
`PS = (ℝ×ℝ) × (ℝ×ℝ)`), which gives the claim.
-/

set_option autoImplicit false
noncomputable section

namespace Work.RPA3

/-- The first coordinate `q₁` of a point of the phase space is bounded by its (sup) norm. -/
lemma theta_slab_abs_q1 (w : PS) : |w.1.1| ≤ ‖w‖ := by
  rw [Prod.norm_def, Prod.norm_def]
  exact le_trans (le_max_left _ _) (le_max_left _ _)

/-- The third coordinate `p₁` of a point of the phase space is bounded by its (sup) norm. -/
lemma theta_slab_abs_p1 (w : PS) : |w.2.1| ≤ ‖w‖ := by
  rw [Prod.norm_def, Prod.norm_def]
  exact le_trans (le_max_left _ _) (le_max_right _ _)

/-- The fourth coordinate `p₂` of a point of the phase space is bounded by its (sup) norm. -/
lemma theta_slab_abs_p2 (w : PS) : |w.2.2| ≤ ‖w‖ := by
  rw [Prod.norm_def, Prod.norm_def]
  exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem theta_slab_bounded (L : Work.RPA3.LagFamilyAll) (T : Work.RPA3.TubularData L) :
    ∃ R : ℝ, ∀ τ ∈ Set.Icc (-1 : ℝ) 2, ∀ x t : ℝ, |x| ≤ max L.X0 0 →
      t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) → ∀ ξ : ℝ × ℝ, ‖ξ‖ ≤ T.ε / 2 →
      |(Work.RPA3.theta L τ x t ξ).1.1| + |(Work.RPA3.theta L τ x t ξ).2.1| +
        |(Work.RPA3.theta L τ x t ξ).2.2| ≤ R := by
  -- The compact slab `K = [-1,2] × ([-max X₀ 0, max X₀ 0] × [0,2π]) × B(0,ε/2)`.
  have hK : IsCompact (Set.Icc (-1 : ℝ) 2 ×ˢ
      ((Set.Icc (-(max L.X0 0)) (max L.X0 0) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) ×ˢ
        Metric.closedBall (0 : ℝ × ℝ) (T.ε / 2))) :=
    isCompact_Icc.prod ((isCompact_Icc.prod isCompact_Icc).prod
      (ProperSpace.isCompact_closedBall (0 : ℝ × ℝ) (T.ε / 2)))
  -- `θ` is continuous in `w = (τ, ((x,t), ξ))`, so its norm is bounded on `K`.
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (continuous_thetaZ L).continuousOn
  refine ⟨M + M + M, ?_⟩
  rintro τ hτ x t hx ht ξ hξ
  have hw : (τ, ((x, t), ξ)) ∈
      Set.Icc (-1 : ℝ) 2 ×ˢ
      ((Set.Icc (-(max L.X0 0)) (max L.X0 0) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) ×ˢ
        Metric.closedBall (0 : ℝ × ℝ) (T.ε / 2)) := by
    refine ⟨hτ, ⟨abs_le.mp hx, ht⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hξ
  have hM' : ‖theta L τ x t ξ‖ ≤ M := by
    simpa using hM (τ, ((x, t), ξ)) hw
  have h1 : |(theta L τ x t ξ).1.1| ≤ M := le_trans (theta_slab_abs_q1 _) hM'
  have h2 : |(theta L τ x t ξ).2.1| ≤ M := le_trans (theta_slab_abs_p1 _) hM'
  have h3 : |(theta L τ x t ξ).2.2| ≤ M := le_trans (theta_slab_abs_p2 _) hM'
  linarith

end Work.RPA3
