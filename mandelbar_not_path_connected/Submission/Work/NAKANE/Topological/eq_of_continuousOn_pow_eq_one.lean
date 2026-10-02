import Mathlib
import Submission.Work.NAKANE.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE.Topological

/-- The set of `m`-th roots of unity in `ℂ` (for `m > 0`) is finite: it is the finset
`Polynomial.nthRootsFinset m 1`. -/
private lemma finite_rootsOfUnity_eq_one {m : ℕ} (hm : 0 < m) :
    ({z : ℂ | z ^ m = 1} : Set ℂ).Finite := by
  have h : ({z : ℂ | z ^ m = 1} : Set ℂ) = ↑(Polynomial.nthRootsFinset m (1 : ℂ)) := by
    ext z; simp [Polynomial.mem_nthRootsFinset hm]
  rw [h]; exact Finset.finite_toSet _

/-- **A continuous function on a preconnected set whose values are `m`-th roots of unity is
constant.**  (Used to show that the `4^N`-th-root classes below are locally constant.)

Proof: each fibre `{x ∈ U | f x = ζ}`, `ζ ^ m = 1`, is open in `U` (the `m` roots of unity are
pairwise at distance `≥` some `δ > 0`, and continuity gives a neighbourhood on which
`|f x - ζ| < δ/2`, which by `(f x) ^ m = 1` forces `f x = ζ`) and closed in `U` (continuity), and
these `m` fibres partition `U`; a nonempty clopen subset of a preconnected set is everything
(`IsClopen.eq_empty_or_univ` on the subtype `↥U`, noting `U` is nonempty by `hx`).
Cf. `Submission/Work/ParamRays/isPreconnected_subsingleton_of_pow_two_pow_eq_one.lean`, which
proves the analogue with the hypothesis `∃ n, ζ ^ (2 ^ n) = 1` instead of `ζ ^ m = 1`. -/
theorem eq_of_continuousOn_pow_eq_one {X : Type*} [TopologicalSpace X] {U : Set X}
    (hU : IsPreconnected U) {f : X → ℂ} (hf : ContinuousOn f U) {m : ℕ} (hm : 0 < m)
    (hvals : ∀ x ∈ U, (f x) ^ m = 1) {x y : X} (hx : x ∈ U) (hy : y ∈ U) : f x = f y := by
  -- `f` maps `U` into the finite (hence discrete) set of `m`-th roots of unity, so
  -- `IsPreconnected.constant_of_mapsTo` applies.
  exact hU.constant_of_mapsTo (finite_rootsOfUnity_eq_one hm).isDiscrete hf
    (fun z hz => hvals z hz) hx hy

end Work.NAKANE.Topological
