import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Compact support of the physical vorticity of a profile

The physical vorticity of the localised data is the `e_θ`-field

  `omegaProfile p F x = F (ρ(x)^p) (θ(x)) • e_θ(x)`

(`Work.FTS.LocData.omegaProfile`).  Its support is controlled by the single property of the
profile that the localisation provides, namely that `F` vanishes for self-similar variables
beyond a scale `Z` (`Work.FTS.LocData.ProfileZeroFar`).

This module records the two consequences:

* a pointwise vanishing criterion: `Z ≤ ρ(x)^p` forces `omegaProfile p F x = 0`;
* `HasCompactSupport (omegaProfile p F)`: the support is contained in the closed ball of radius
  `Z^(1/p)`, because `ρ(x)^p < Z` with `p > 0` forces `ρ(x) < Z^(1/p)` and `ρ = ‖·‖`.

Note that no regularity of `F` is needed: only the vanishing.
-/

noncomputable section

open scoped Real Topology

namespace Work.FTS.LocData

/-- `Rc p x = ρ(x)^p` — the defining equation of `Work.Cyl.Rc`, recorded for rewriting. -/
private theorem Rc_eq_rho_rpow (p : ℝ) (x : R3) : Work.Cyl.Rc p x = Work.Cyl.rho x ^ p := rfl

/-- **Pointwise vanishing.** If the self-similar variable `ρ(x)^p` is beyond the scale `Z` where
the profile dies, the physical vorticity at `x` is zero. -/
private theorem omegaProfile_eq_zero_of_le {p Z : ℝ} {F : ℝ → ℝ → ℝ} (hF : ProfileZeroFar Z F)
    {x : R3} (hx : Z ≤ Work.Cyl.rho x ^ p) : omegaProfile p F x = 0 := by
  rw [omegaProfile_apply, Rc_eq_rho_rpow p x,
    hF (Work.Cyl.rho x ^ p) (Work.Cyl.theta x) hx, zero_smul]

/-- **The support is contained in a ball.** If `ρ(x)^p < Z` with `p > 0` and `Z > 0`, then
`‖x‖ = ρ(x) < Z^(1/p)`. -/
private theorem norm_lt_rpow_of_rpow_lt {p Z : ℝ} (hp : 0 < p) (hZ : 0 < Z) {x : R3}
    (h : Work.Cyl.rho x ^ p < Z) : ‖x‖ < Z ^ (1 / p) := by
  have hZpow : (Z ^ (1 / p)) ^ p = Z := by
    rw [← Real.rpow_mul hZ.le, div_mul_cancel₀ 1 (ne_of_gt hp), Real.rpow_one]
  have hb : Work.Cyl.rho x ^ p < (Z ^ (1 / p)) ^ p := by rw [hZpow]; exact h
  rw [← Work.Cyl.rho_eq_norm]
  exact (Real.rpow_lt_rpow_iff (Work.Cyl.rho_nonneg x) (Real.rpow_nonneg hZ.le _) hp).mp hb

/-- **THE COMPACT SUPPORT OF THE LOCALISED VORTICITY.**  If the profile vanishes beyond the
self-similar scale `Z` (`ProfileZeroFar Z F`) then

* the physical vorticity of the profile vanishes wherever `ρ(x)^p ≥ Z`, and
* it is compactly supported — indeed its support is contained in the ball of radius
  `Z^(1/p)`.

The vanishing hypothesis `hp : 0 < p` is what turns the condition `ρ(x)^p < Z` on the
self-similar variable into the radial bound `ρ(x) < Z^(1/p)`; without it (e.g. `p < 0`) the
support would be the complement of a ball and there would be no compactness. -/
theorem omegaProfile_compact {p : ℝ} (hp : 0 < p) {Z : ℝ} (hZ : 0 < Z) {F : ℝ → ℝ → ℝ}
    (hF : ProfileZeroFar Z F) :
    (∀ x : R3, Z ≤ Work.Cyl.rho x ^ p → omegaProfile p F x = 0) ∧
      HasCompactSupport (omegaProfile p F) := by
  have hvan : ∀ x : R3, Z ≤ Work.Cyl.rho x ^ p → omegaProfile p F x = 0 :=
    fun _ hx => omegaProfile_eq_zero_of_le hF hx
  refine ⟨hvan, ?_⟩
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Metric.closedBall (0 : R3) (Z ^ (1 / p))) (isCompact_closedBall 0 _) ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  refine le_of_lt (norm_lt_rpow_of_rpow_lt hp hZ ?_)
  by_contra h
  exact (Function.mem_support.mp hx) (hvan x (le_of_not_gt h))

end Work.FTS.LocData
