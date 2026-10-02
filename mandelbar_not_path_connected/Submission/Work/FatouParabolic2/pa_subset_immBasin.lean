import Mathlib
import Submission.Work.FatouParabolic2.Defs
import Submission.Work.FatouParabolic.Core.ImmBasin.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic2

/-- **The petal lies in the immediate basin.**  The immediate basin
`Work.FatouParabolic.Core.immBasin F z₀ p₀ = connectedComponentIn (interior (basin F z₀)) p₀`
contains the whole petal of petal data: the petal is open (`pd.isOpen_Pa`) and contained in the
basin (orbits in it converge to `z₀`, `pd.tendsto_Pa`), hence in `interior (basin F z₀)`, and it is
preconnected and contains `p₀`, so it lies in the connected component of `p₀`.

This is the direct analogue of `Work.FatouParabolic.Core.exists_pa_subset_immBasin` with the
flower replaced by `PetalData`; that delivered proof replays verbatim with `pd.tendsto_Pa`,
`pd.isOpen_Pa`, `pd.isPreconnected_Pa` in place of the flower fields. -/
theorem pa_subset_immBasin {F : ℂ → ℂ} {z₀ : ℂ} (pd : PetalData F z₀) {p₀ : ℂ}
    (hp₀ : p₀ ∈ pd.Pa) : pd.Pa ⊆ Work.FatouParabolic.Core.immBasin F z₀ p₀ := by
  have hPa_basin : pd.Pa ⊆ Work.FatouParabolic.basin F z₀ :=
    fun z hz => Work.FatouParabolic.mem_basin.mpr (pd.tendsto_Pa z hz)
  have hPa_int : pd.Pa ⊆ interior (Work.FatouParabolic.basin F z₀) :=
    interior_maximal hPa_basin pd.isOpen_Pa
  exact pd.isPreconnected_Pa.subset_connectedComponentIn hp₀ hPa_int

end Work.FatouParabolic2
