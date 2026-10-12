import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB3.Scaling.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3/Scaling/chiU_sq_indicator` — the window profile identity

`χ_Λ(x)² = φ(ℓ⁻¹•x)` on the box `Λ = acube ℓ` (and `0` outside), i.e.

`(1_{Λ(ℓ)} · (χ_U(ℓ,0))²)(z) = φ(ℓ⁻¹ • z)`,   `φ = χ²`.

Two ingredients:

* `chiU ℓ 0 z = χ(ℓ⁻¹ • z − 0) = χ(ℓ⁻¹ • z)`, so off the indicator the two sides
  already agree up to `phi = χ²`;
* the support condition: `supp χ ⊆ ball 0 (1/2)`, hence `χ(ℓ⁻¹ • z) = 0` whenever
  `ℓ⁻¹‖z‖ > 1/2`, i.e. `‖z‖ > ℓ/2`.  A point outside the centred cube `acube ℓ`
  has some coordinate of modulus `> ℓ/2`, and `|z m| ≤ ‖z‖`, so indeed
  `‖z‖ > ℓ/2` and the extra indicator factor is redundant.

This is the identity FS use to rewrite the localisation window `χ_Λ²` appearing in
`q3convWord`/`multOn` by the profile `φ` (FS `sec:3Q`, `eq:3Q-splitting`); it feeds
`Work.BoseFixB3.Scaling.chiSq_mult_bound` and `...Scaling.kinFT_scaled_phi`.
-/

namespace Work.BoseFixB3.Scaling

open Submission.BoseGases

theorem chiU_sq_indicator (ℓ : ℝ) (hℓ : 0 < ℓ) (z : EuclideanSpace ℝ (Fin 3)) :
    ((Submission.BoseGases.acube ℓ).indicator
        (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiU ℓ 0 z ^ 2) z : ℝ)
      = Work.BoseFixB3.Scaling.phi (ℓ⁻¹ • z) := by
  classical
  rw [Set.indicator_apply]
  by_cases hz : z ∈ Submission.BoseGases.acube ℓ
  · -- On the box: `chiU ℓ 0 z = χ (ℓ⁻¹ • z)` and `phi = χ²`.
    simp only [hz, if_true]
    simp [Submission.BoseGases.chiU, Work.BoseFixB3.Scaling.phi]
  · -- Outside the box: the profile already vanishes, because `supp χ ⊆ ball 0 1/2`
    -- and `‖z‖ > ℓ/2`.
    simp only [hz, if_false]
    have hznorm : ℓ / 2 < ‖z‖ := by
      by_contra hc
      push Not at hc
      exact hz (Submission.BoseGases.mem_acube_of_norm_le hℓ.le hc)
    rw [Work.BoseFixB3.Scaling.phi,
      Submission.BoseGases.chi_eq_zero_of_norm_gt _ (by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
        have h2 : ℓ⁻¹ * (ℓ / 2) = 1 / 2 := by field_simp
        nlinarith [inv_pos.mpr hℓ])]
    norm_num

end Work.BoseFixB3.Scaling
