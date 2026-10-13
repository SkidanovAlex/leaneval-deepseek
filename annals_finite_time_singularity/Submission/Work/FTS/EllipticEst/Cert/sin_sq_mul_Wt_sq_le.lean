import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

/-- **The angular weight comparison behind the level-six slots.**

For `α ≤ 1`, `θ ∈ Iθ` and `sin(2θ) > 0` one has

  `sin(2θ)² · Wt(α,z,θ)² ≤ (w z / sin(2θ)^{η/2})²`,

i.e. the `γ`-weighted square slot `sin²·Wt² = w²·sin^{2-γ}` of the `ℋ⁶`-integrand is dominated by
the `η`-weighted one `w²·sin^{-η}`: after cancelling `w²` the claim is
`sin(2θ)^{2-γ} ≤ sin(2θ)^{-η}`, which holds because `2 - γ + η ≥ 0` (`γ = 1 + α/10 ≤ 11/10`,
`η = 99/100`) and `sin(2θ) ≤ 1`. -/
theorem sin_sq_mul_Wt_sq_le (α : ℝ) (hα1 : α ≤ 1) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hs : 0 < Real.sin (2 * θ)) :
    (Real.sin (2 * θ)) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
      ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
  set s := Real.sin (2 * θ) with hsdef
  have hs0 : 0 < s := by rw [hsdef]; exact hs
  have hsle : s ≤ 1 := by rw [hsdef]; exact Real.sin_le_one (2 * θ)
  have hexp : 0 ≤ 2 - Work.Spaces.gam α + Work.Spaces.eta := by
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
  -- the exponent comparison `s ^ (2 - γ) ≤ s ^ (-η)`
  have hkey : s ^ (2 - Work.Spaces.gam α) ≤ s ^ (-(Work.Spaces.eta)) := by
    have h1 : s ^ (2 - Work.Spaces.gam α + Work.Spaces.eta) ≤ 1 :=
      Real.rpow_le_one hs0.le hsle hexp
    calc s ^ (2 - Work.Spaces.gam α)
        = s ^ ((2 - Work.Spaces.gam α + Work.Spaces.eta) + (-(Work.Spaces.eta))) := by
          congr 1; ring
      _ = s ^ (2 - Work.Spaces.gam α + Work.Spaces.eta) * s ^ (-(Work.Spaces.eta)) :=
          Real.rpow_add hs0 _ _
      _ ≤ 1 * s ^ (-(Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hs0.le _)
      _ = s ^ (-(Work.Spaces.eta)) := one_mul _
  -- the two algebraic normalisations of the two sides
  have hγsq : (s ^ (-(Work.Spaces.gam α / 2))) ^ 2 = s ^ (-(Work.Spaces.gam α)) := by
    calc (s ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = s ^ (-(Work.Spaces.gam α / 2)) * s ^ (-(Work.Spaces.gam α / 2)) := by rw [pow_two]
      _ = s ^ (-(Work.Spaces.gam α / 2) + -(Work.Spaces.gam α / 2)) :=
          (Real.rpow_add hs0 _ _).symm
      _ = s ^ (-(Work.Spaces.gam α)) := by congr 1; ring
  have hηsq : ((s ^ (Work.Spaces.eta / 2))⁻¹) ^ 2 = s ^ (-(Work.Spaces.eta)) := by
    have h1 : (s ^ (Work.Spaces.eta / 2))⁻¹ = s ^ (-(Work.Spaces.eta / 2)) :=
      (Real.rpow_neg hs0.le _).symm
    calc ((s ^ (Work.Spaces.eta / 2))⁻¹) ^ 2
        = (s ^ (Work.Spaces.eta / 2))⁻¹ * (s ^ (Work.Spaces.eta / 2))⁻¹ := by rw [pow_two]
      _ = s ^ (-(Work.Spaces.eta / 2)) * s ^ (-(Work.Spaces.eta / 2)) := by rw [h1]
      _ = s ^ (-(Work.Spaces.eta / 2) + -(Work.Spaces.eta / 2)) :=
          (Real.rpow_add hs0 _ _).symm
      _ = s ^ (-(Work.Spaces.eta)) := by congr 1; ring
  have hWt : (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * s ^ (-(Work.Spaces.gam α)) := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, ← hsdef, mul_pow, hγsq]
  have hR : (Work.Spaces.w z / s ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * s ^ (-(Work.Spaces.eta)) := by
    rw [div_eq_mul_inv, mul_pow, hηsq]
  rw [hWt, hR]
  have hs2 : s ^ (2 : ℕ) * s ^ (-(Work.Spaces.gam α)) = s ^ (2 - Work.Spaces.gam α) := by
    rw [← Real.rpow_natCast s 2, ← Real.rpow_add hs0]
    congr 1
  calc s ^ 2 * ((Work.Spaces.w z) ^ 2 * s ^ (-(Work.Spaces.gam α)))
      = (Work.Spaces.w z) ^ 2 * (s ^ 2 * s ^ (-(Work.Spaces.gam α))) := by ring
    _ = (Work.Spaces.w z) ^ 2 * s ^ (2 - Work.Spaces.gam α) := by rw [hs2]
    _ ≤ (Work.Spaces.w z) ^ 2 * s ^ (-(Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_left hkey (sq_nonneg _)

end Work.FTS.EllipticEst.Cert
