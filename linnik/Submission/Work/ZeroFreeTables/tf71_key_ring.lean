import Mathlib

namespace Work.ZeroFreeTables

/-- A purely algebraic (ring) identity in the four quantities
`sin θ, cos θ, sin (c θ), cos (c θ)`, used in the reduction of the `tf71`
zero-free region table. -/
theorem tf71_key_ring (θ c : ℝ) (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hc2 : c ≠ -1) :
   (1-c^2)*(2*Real.cos θ^2*(Real.sin (c*θ))^2/c^2
        - (Real.cos θ*Real.sin (c*θ) - Real.sin θ*Real.cos (c*θ))^2/(c-1)
        + (Real.cos θ*Real.sin (c*θ) + Real.sin θ*Real.cos (c*θ))^2/(c+1)
        - 4*Real.sin θ*Real.cos θ*Real.sin (c*θ)*Real.cos (c*θ)/c)
   = 2*(Real.sin θ*Real.cos (c*θ) - Real.cos θ*Real.sin (c*θ)/c)^2 := by
  have h1 : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
  have h2 : c + 1 ≠ 0 := by intro h; apply hc2; linarith
  field_simp
  ring

end Work.ZeroFreeTables
