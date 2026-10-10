import Mathlib
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

theorem fifthPowerValued_map_algHom {𝕜 F N : Type*} [Field 𝕜] [Field F] [Algebra 𝕜 F]
    [Field N] [Algebra 𝕜 N] (φ : F →ₐ[𝕜] RatFunc N) (g : F)
    (h : Work.MotV.FifthPowerValued 𝕜 g) : Work.MotV.FifthPowerValued N (φ g) := by
  intro v hv
  obtain ⟨u, hu⟩ := h (v.comap (φ : F →+* RatFunc N)) (fun c hc => by
    -- `v` is trivial on `N`, and the `𝕜`-algebra structure on `RatFunc N` is the composite
    -- `𝕜 → N → RatFunc N`, so `v` is trivial on the image of `𝕜` as well.
    rw [Valuation.comap_apply]
    rw [show (φ : F →+* RatFunc N) (algebraMap 𝕜 F c) = algebraMap 𝕜 (RatFunc N) c from
      AlgHom.commutes φ c]
    rw [IsScalarTower.algebraMap_apply 𝕜 N (RatFunc N)]
    exact hv (algebraMap 𝕜 N c) (by simpa using hc))
  exact ⟨φ u, by simpa using hu⟩

end Work.MotV
