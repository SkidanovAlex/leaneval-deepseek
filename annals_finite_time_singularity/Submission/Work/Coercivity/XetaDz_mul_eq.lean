import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Coercivity.H1IPAddDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

/-- Scalar `rpow` identity: for `s ≥ 0` and reals `w`, `a`,
`(w / s ^ a) * (w / s ^ a) = w ^ 2 * s ^ (-(2 * a))`.

This is the algebraic core of the identities `D_z a · D_z b · ρη = XetaDz a · XetaDz b`
(and similarly for the `η`-block `Xeta`): the block carries the weight `w / √(sin 2θ^η)`,
whose square is `w² · sin(2θ)^{-η}`. -/
theorem div_rpow_mul_self_eq (s w a : ℝ) (hs : 0 ≤ s) :
    (w / s ^ a) * (w / s ^ a) = w ^ 2 * s ^ (-(2 * a)) := by
  have h2 : (s ^ (-a)) ^ 2 = s ^ (-(2 * a)) := by
    rw [← Real.rpow_natCast (s ^ (-a)) 2]
    rw [show -(2 * a) = -a * 2 by ring, Real.rpow_mul hs]
    norm_num
  have h1 : w / s ^ a = w * s ^ (-a) := by
    rw [div_eq_mul_inv, Real.rpow_neg hs a]
  calc (w / s ^ a) * (w / s ^ a) = (w * s ^ (-a)) * (w * s ^ (-a)) := by rw [h1]
    _ = w ^ 2 * (s ^ (-a)) ^ 2 := by ring
    _ = w ^ 2 * s ^ (-(2 * a)) := by rw [h2]

/-- `D_z a · D_z b · ρη = XetaDz a · XetaDz b`: the product of the two `D_z¹`-blocks of the
`ℋ¹` integrand reproduces the weighted pairing integrand `D_z a · D_z b · ρη`. -/
theorem XetaDz_mul_eq (a b : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    XetaDz a z θ * XetaDz b z θ = Spaces.Dz a z θ * Spaces.Dz b z θ * lamEta z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_mem_Icc
    have h1 : 0 ≤ θ := hθ.1
    have h2 : θ ≤ Real.pi / 2 := hθ.2
    constructor <;> linarith [Real.pi_pos]
  have hkey : (Spaces.w z / Real.sin (2 * θ) ^ (Spaces.eta / 2)) *
        (Spaces.w z / Real.sin (2 * θ) ^ (Spaces.eta / 2))
      = Spaces.w z ^ 2 * Real.sin (2 * θ) ^ (-Spaces.eta) := by
    have h := div_rpow_mul_self_eq (Real.sin (2 * θ)) (Spaces.w z) (Spaces.eta / 2) hs
    simpa [show -(2 * (Spaces.eta / 2)) = -Spaces.eta by ring] using h
  simp only [XetaDz, lamEta]
  rw [show (Spaces.Dz a z θ * (Spaces.w z / Real.sin (2 * θ) ^ (Spaces.eta / 2))) *
          (Spaces.Dz b z θ * (Spaces.w z / Real.sin (2 * θ) ^ (Spaces.eta / 2)))
        = Spaces.Dz a z θ * Spaces.Dz b z θ *
          ((Spaces.w z / Real.sin (2 * θ) ^ (Spaces.eta / 2)) *
           (Spaces.w z / Real.sin (2 * θ) ^ (Spaces.eta / 2))) by ring]
  rw [hkey]

end Work.Coercivity
