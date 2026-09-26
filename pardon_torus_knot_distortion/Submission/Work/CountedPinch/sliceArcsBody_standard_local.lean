import Mathlib
import Submission.Work.CountedPinch.Defs
import Submission.Work.CoreTopology.Winding
import Submission.Work.CoreTopology.Basic
import Submission.Work.CountedPinch.StdLocalDefs

namespace Work.CountedPinch

/-- **A non-degenerate instance of the honest arcs datum**: the standard torus, the small box
`PBox (1/4) (3,0,0) (refl (Fin 3))` (half-lengths `1/4, 2^(1/3)/4, 2^(2/3)/4`, centred at the point
`(3,0,0)` of the outer equator of the torus), and the cutting plane `{z = 0}` (`σ = refl`, `u = 0`).

The trace of the plane with the torus is the union of the outer equator `{v = 0}` (radius `3`) and
the inner equator `{v = π}` (radius `1`), and the plane coordinate is the second parameter of the
torus.  The box meets only the outer equator, in a single open arc: the binding faces are the two
`y`-faces, `3 |sin u| = 2^(1/3)/4`, so the slice is the arc with parameters
`u ∈ (-α, α)`, `α = arcsin (2^(1/3)/12)` (the `x`-face condition `3 - 3 cos u < 1/4` is never
reached, since `3 sin u` has already left the box).  Its closure is a single compact arc of the
surface with endpoints on the box sphere; the inner equator is at distance `2` from the box centre.
Hence the closure of the slice is one embedded arc of the surface, and `SliceArcsBody` holds with
`n = 1` (the parametrisation of that arc, e.g. by the parameter `u` ranging over `[-α, α]`).

This certifies that `CountedSliceArcs` is not vacuous at a *non-degenerate* configuration (a trace
which genuinely leaves the open box), unlike the empty-slice certificates of `Instances.lean`. -/
theorem sliceArcsBody_standard_local :
    Work.CountedPinch.SliceArcsBody Work.CoreTopology.standard
      (Work.CoreTopology.standardCurve 1 1) (1 / 4)
      (WithLp.toLp 2 (![3, 0, 0] : Fin 3 → ℝ)) (Equiv.refl (Fin 3)) 0 := by
  show Work.CountedPinch.SliceArcsBody Work.CoreTopology.standard
      (Work.CoreTopology.standardCurve 1 1) (1 / 4)
      StdLocal.c (Equiv.refl (Fin 3)) 0
  refine ⟨1, fun _ => StdLocal.arcMap, ?_, ?_, ?_, ?_⟩
  · intro j
    exact StdLocal.arcMap_injective
  · intro j x
    rw [StdLocal.closure_slice_eq]
    exact ⟨StdLocal.arcArg (x : ℝ), StdLocal.arcArg_mem_Icc x.2, rfl⟩
  · intro j j' hjj
    exact absurd (Subsingleton.elim j j') hjj
  · rw [StdLocal.closure_slice_eq]
    rintro y ⟨θ, hθ, rfl⟩
    refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    rw [StdLocal.range_arcMap]
    exact ⟨θ, hθ, rfl⟩

end Work.CountedPinch
