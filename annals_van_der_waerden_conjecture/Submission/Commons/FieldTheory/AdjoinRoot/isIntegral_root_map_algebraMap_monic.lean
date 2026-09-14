import Mathlib.RingTheory.AdjoinRoot

namespace Commons.FieldTheory.AdjoinRoot

open Polynomial in
/-- If `g : ℤ[X]` is monic then the adjoined root of the image of `g` in `ℚ[X]` is an algebraic
integer.

Proof sketch: `AdjoinRoot.isIntegral_root' hg` gives `IsIntegral ℤ (AdjoinRoot.root g)` in
`AdjoinRoot g`; push it forward along the ring hom
`AdjoinRoot.map (algebraMap ℤ ℚ) g (g.map (algebraMap ℤ ℚ)) rfl`, using
`AdjoinRoot.map_root` to identify the image of the root with `AdjoinRoot.root (g.map _)`,
and `IsIntegral.map`.  (Alternatively use `isIntegral_iff` with `p = g`.) -/
theorem isIntegral_root_map_algebraMap_monic
    (g : ℤ[X]) (hg : g.Monic) :
    IsIntegral ℤ (AdjoinRoot.root (g.map (algebraMap ℤ ℚ))) := by
  refine ⟨g, hg, ?_⟩
  rw [show algebraMap ℤ (AdjoinRoot (g.map (algebraMap ℤ ℚ))) =
      (AdjoinRoot.of (g.map (algebraMap ℤ ℚ))).comp (algebraMap ℤ ℚ) from rfl]
  rw [← eval₂_map]
  exact AdjoinRoot.eval₂_root _

end Commons.FieldTheory.AdjoinRoot