import Mathlib
import Submission.Work.MotV5.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

/-- `℘` is `𝔽₅`-linear, and the Artin–Schreier bridge is invariant under rescaling the class: for
`c ∈ 𝕜` with `c ^ 5 = c` and `c ≠ 0` (a nonzero element of the prime field `𝔽₅`), the bridge
condition for the parameter `algebraMap 𝕜 F c * g` implies the bridge condition for `g`.

Proof: for `v` trivial on `𝕜` one has `v c = 1`, and `c⁵ = c`, `c ≠ 0` give `c⁴ = 1`, hence
`c * ℘(c⁻¹ u) = c⁵ c⁻⁵ u⁵ - u = ℘ u`; so a witness `u` for the rescaled parameter can be replaced by
`c⁻¹ u` for the original one.

This is what decouples the field from the parameter in `Nodes/bridge_AS`: since
`fAS 𝕜 = 3 * (2 • fAS 𝕜)` and `2 • fAS 𝕜 = 2 * fAS 𝕜` with `2, 3 ∈ 𝔽₅^×`, the instances with the
parameter differing from the bundle's class (in particular the `hB₂` of
`Nodes/v1_AS_of_bridge`) follow from the diagonal instances. -/
theorem ASUnramified_smul_of_pow_eq (𝕜 F : Type) [Field 𝕜] [CharP 𝕜 5] [Field F] [Algebra 𝕜 F]
    (t g : F) (c : 𝕜) (hc5 : c ^ 5 = c) (hc0 : c ≠ 0)
    (h : Work.MotV5.ASUnramified 𝕜 F t (algebraMap 𝕜 F c * g)) :
    Work.MotV5.ASUnramified 𝕜 F t g := by
  intro v hv hvt
  obtain ⟨u, hu⟩ := h v hv hvt
  refine ⟨(algebraMap 𝕜 F c)⁻¹ * u, ?_⟩
  have hc : algebraMap 𝕜 F c ≠ 0 := by
    intro hzero
    exact hc0 (RingHom.injective (algebraMap 𝕜 F) (by rw [hzero, map_zero]))
  have hcw : ∀ y : F, algebraMap 𝕜 F c * ((algebraMap 𝕜 F c)⁻¹ * y) = y :=
    fun y => by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have hmain : algebraMap 𝕜 F c *
      (g - (((algebraMap 𝕜 F c)⁻¹ * u)^5 - (algebraMap 𝕜 F c)⁻¹ * u))
      = algebraMap 𝕜 F c * g - (u^5 - u) := by
    have h5 : (algebraMap 𝕜 F c)^5 = algebraMap 𝕜 F c := by
      rw [← map_pow, hc5]
    have hp : ((algebraMap 𝕜 F c)⁻¹ * u)^5 = (algebraMap 𝕜 F c)⁻¹ * u^5 := by
      rw [mul_pow, inv_pow, h5]
    rw [hp, mul_sub, mul_sub, hcw, hcw]
  rw [← hmain] at hu
  rw [Valuation.map_mul, hv c hc0, one_mul] at hu
  exact hu

end Work.MotV5
