import Mathlib
import Submission.Work.FatouParabolic2.Defs
import Submission.Work.SeedLimit.Postcritical

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic2

/-- **NC6 of the tricorn project, simple parabolic case.**  If the holomorphic return map
`(Tsq c)^[5] = (T_c)^[10]` of the period-`5` cycle of the tricorn has a fixed point `z` of
multiplier `1` which is *simple* (`iteratedDeriv 2 ((Tsq c)^[5]) z ≠ 0`), then
`c ∈ Mandelbar` — from the simple case `FatouParabolicInput_simple` of Fatou's classical input on
parabolic cycles.

This is the direct analogue of `Work.SeedLimit.mem_Mandelbar_of_parabolic` (file
`Submission/Work/SeedLimit/Postcritical.lean`) with the classical input consumed in its simple
form (the extra hypothesis `h2`).  The proof is that delivered proof verbatim: the input, applied
to the degree-`1024` polynomial `(Tsq c)^[5]` (`Work.SeedLimit.isPolynomial_returnMap`), produces
a critical point whose return-map orbit converges to `z`; that orbit is bounded
(`Work.SeedLimit.exists_bound_of_tendsto`), and
`Work.SeedLimit.mem_Mandelbar_of_critical_bounded` finishes. -/
theorem mem_Mandelbar_of_parabolic_returnMap_simple (hFatou : FatouParabolicInput_simple) {c z : ℂ}
    (hfix : ((Work.Landing.Tsq c)^[5]) z = z)
    (hder : deriv (((Work.Landing.Tsq c)^[5])) z = 1)
    (h2 : iteratedDeriv 2 (((Work.Landing.Tsq c)^[5])) z ≠ 0) :
    c ∈ LeanEval.ComplexAnalysis.Mandelbar := by
  have hpol := Work.SeedLimit.isPolynomial_returnMap c
  obtain ⟨w, hcrit, hbasin⟩ := hFatou ((Work.Landing.Tsq c)^[5]) z hpol hfix hder h2
  refine Work.SeedLimit.mem_Mandelbar_of_critical_bounded hcrit ?_
  rw [Work.FatouParabolic.mem_basin] at hbasin
  exact Work.SeedLimit.exists_bound_of_tendsto _ z hbasin

end Work.FatouParabolic2
