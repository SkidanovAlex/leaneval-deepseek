import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotT

/-- **T12a.** A field with a transcendental element over `𝔽` is infinite.  Route: the `𝔽`-algebra
map `𝔽[X] → K`, `X ↦ t` is injective (`Polynomial.aeval` of a transcendental element), and `𝔽[X]` is
infinite (the powers of `X` are pairwise distinct), so `Infinite.of_injective` applies.
Declare it in namespace `Work.MotT` so that its full name is `Work.MotT.infinite_of_transcendental`. -/
theorem infinite_of_transcendental {𝔽 K : Type} [Field 𝔽] [Field K] [Algebra 𝔽 K]
    (h : ∃ t : K, Transcendental 𝔽 t) : Infinite K := by
  obtain ⟨t, ht⟩ := h
  -- The `𝔽`-algebra map `𝔽[X] →ₐ[𝔽] K`, `X ↦ t`, is injective since `t` is transcendental,
  -- and `𝔽[X]` is infinite because `𝔽` is nontrivial.
  exact Infinite.of_injective (Polynomial.aeval t : Polynomial 𝔽 → K)
    (transcendental_iff_injective.mp ht)

end Work.MotT
