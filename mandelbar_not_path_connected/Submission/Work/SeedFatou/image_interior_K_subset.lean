/-
# `T_c` maps the interior of the filled Julia set into itself

The filled Julia set `Work.EL.K c = Work.ParamRays.filledJulia c` of `T_c(z) = z̄² + c` is
*completely invariant*: `z ∈ K c` iff `T_c z ∈ K c`.  Consequently the (open, by
`Work.ELPull.isOpenMap_Tantibar`) image `T_c '' interior (K c)` is an open set contained in
`K c`, hence in `interior (K c)`:

  `Work.SeedFatou.image_interior_K_subset_one`.

Iterating this single-step statement with `Set.image_mono` gives the claimed
`Work.SeedFatou.image_interior_K_subset`: every iterate `(T_c)^[k]` maps `interior (K c)`
into itself.
-/
import Mathlib
import Submission.Work.SeedFatou.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function Set
open scoped Topology

namespace Work.SeedFatou

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The single step.**  `T_c` maps `interior (K c)` into `interior (K c)`: the image is open
(the antiholomorphic quadratic map is an open map) and is contained in the closed invariant set
`K c`. -/
theorem image_interior_K_subset_one (c : ℂ) :
    Tantibar c '' interior (Work.EL.K c) ⊆ interior (Work.EL.K c) := by
  refine interior_maximal ?_ (Work.ELPull.isOpenMap_Tantibar c _ isOpen_interior)
  rintro w ⟨z, hz, rfl⟩
  show Work.ParamRays.BoundedOrbit c (Tantibar c z)
  -- `z ∈ K c` has a bounded `T_c`-orbit, hence so does `T_c z` (the orbit shifted by one).
  have hzK : z ∈ Work.ParamRays.filledJulia c := interior_subset hz
  have hb : Work.ParamRays.BoundedOrbit c z := hzK
  simpa [Work.ParamRays.orbit] using hb.shift 1

/-- **Every iterate preserves `interior (K c)`.**  Immediate by induction from
`image_interior_K_subset_one`. -/
theorem image_interior_K_subset (c : ℂ) (k : ℕ) :
    (LeanEval.ComplexAnalysis.Tantibar c)^[k] '' interior (Work.EL.K c) ⊆ interior (Work.EL.K c) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Set.image_comp]
    exact (Set.image_mono ih).trans (image_interior_K_subset_one c)

end Work.SeedFatou
