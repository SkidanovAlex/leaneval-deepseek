import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

/-- **An angular derivative divisible by `sin 2θ` costs nothing against the radial weight.**
PLACEMENT: file `Submission/Work/FTS/EllipticEst/Blocks/angular_sq_mul_Wt_sq_le_radial.lean`,
namespace `Work.FTS.EllipticEst.Blocks`, so the fully qualified name is
`Work.FTS.EllipticEst.Blocks.angular_sq_mul_Wt_sq_le_radial`.
If `d² ≤ K · sin(2θ)²` at `θ ∈ (0,π/2)`, `K ≥ 0` and `α ≤ 1`, then for arbitrary `u, z`
`(d·u)² · Wt(α,z,θ)² ≤ K · (u · w(z)/sin(2θ)^{η/2})²`,
where `Wt α z θ = w z · sin(2θ)^{-γ/2}`, `γ = 1 + α/10`, `η = 99/100` and
`w z = (1+z)²/z²` (`Submission/Work/Spaces/Defs.lean`).
Route: `Wt² = w²·sin(2θ)^{-γ}`, so after cancelling `w²u²` it suffices to show
`sin(2θ)^{2-γ} ≤ sin(2θ)^{-η}`, i.e. `sin(2θ)^{2-γ+η} ≤ 1`, which holds because
`2 - γ + η ≥ 2 - 11/10 + 99/100 > 0` and `0 < sin(2θ) ≤ 1`. -/
theorem angular_sq_mul_Wt_sq_le_radial {K d u α z θ : ℝ} (hα1 : α ≤ 1) (hK : 0 ≤ K)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hd : d ^ 2 ≤ K * (Real.sin (2 * θ)) ^ 2) :
    (d * u) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
      ≤ K * (u * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  set S := Real.sin (2 * θ) with hS
  -- `S = sin(2θ)` lies in `(0,1]` on the open quadrant.
  have hspos : 0 < S := by
    rw [hS]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hsle1 : S ≤ 1 := by rw [hS]; exact Real.sin_le_one _
  have hsnn : 0 ≤ S := le_of_lt hspos
  -- `(S^a)^2 = S^(2a)`: the key `rpow` identity, valid since `S > 0`.
  have hsq : ∀ a : ℝ, (S ^ a) ^ 2 = S ^ (a * 2) := by
    intro a
    rw [pow_two, ← Real.rpow_add hspos]
    congr 1
    ring
  have hgam : (S ^ (-(Work.Spaces.gam α / 2))) ^ 2 = S ^ (-(Work.Spaces.gam α)) := by
    rw [hsq]; congr 1; ring
  have heta : (S ^ (-(Work.Spaces.eta / 2))) ^ 2 = S ^ (-(Work.Spaces.eta)) := by
    rw [hsq]; congr 1; ring
  -- The two sides in explicit form.
  have hWt2 : (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.gam α)) := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, ← hS, mul_pow, hgam]
  have hR2 : (u * (Work.Spaces.w z / S ^ (Work.Spaces.eta / 2))) ^ 2
      = u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.eta))) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hsnn, mul_pow, mul_pow, heta]
  have hL : (d * u) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
      = d ^ 2 * u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.gam α))) := by
    rw [mul_pow, hWt2]
  -- The core estimate.
  have hmain : d ^ 2 * u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.gam α)))
      ≤ K * (u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.eta)))) := by
    have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
    have hA : 0 ≤ (Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.gam α)) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsnn _)
    have hc : 0 ≤ u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.gam α))) :=
      mul_nonneg hu2 hA
    -- combine the two `rpow`s
    have hcomb : S ^ 2 * S ^ (-(Work.Spaces.gam α)) = S ^ (2 - Work.Spaces.gam α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hspos]
      congr 1
    -- the numerical exponent comparison `-η ≤ 2 - γ`
    have hexp : -(Work.Spaces.eta) ≤ 2 - Work.Spaces.gam α := by
      rw [Work.Spaces.eta, Work.Spaces.gam]; linarith
    have hSS : S ^ (2 - Work.Spaces.gam α) ≤ S ^ (-(Work.Spaces.eta)) :=
      Real.rpow_le_rpow_of_exponent_ge hspos hsle1 hexp
    have hcoef : 0 ≤ K * u ^ 2 * (Work.Spaces.w z) ^ 2 :=
      mul_nonneg (mul_nonneg hK hu2) (sq_nonneg _)
    calc d ^ 2 * u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.gam α)))
        = d ^ 2 * (u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.gam α)))) := by
          ring
      _ ≤ (K * S ^ 2) * (u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.gam α)))) :=
          mul_le_mul_of_nonneg_right hd hc
      _ = K * u ^ 2 * (Work.Spaces.w z) ^ 2 * (S ^ 2 * S ^ (-(Work.Spaces.gam α))) := by
          ring
      _ = K * u ^ 2 * (Work.Spaces.w z) ^ 2 * S ^ (2 - Work.Spaces.gam α) := by rw [hcomb]
      _ ≤ K * u ^ 2 * (Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_left hSS hcoef
      _ = K * (u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.eta)))) := by ring
  calc (d * u) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
      = d ^ 2 * u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.gam α))) := hL
    _ ≤ K * (u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.eta)))) := hmain
    _ = K * (u * (Work.Spaces.w z / S ^ (Work.Spaces.eta / 2))) ^ 2 := by rw [hR2]

end Work.FTS.EllipticEst.Blocks
