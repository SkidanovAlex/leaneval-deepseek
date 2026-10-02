import Mathlib
import Submission.Work.FatouParabolic2.Defs
import Submission.Work.FatouParabolic.Core.ImmBasin.Defs
import Submission.Work.FatouParabolic.Poly.isPolynomialMap_differentiable

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter Set

namespace Work.FatouParabolic2

noncomputable section

/-- A polynomial map of degree `≥ 2` is an open map: it is the evaluation map of a polynomial of
positive degree, hence an open quotient map of `ℂ`. -/
private theorem isOpenMap_of_isPolynomialMapOfDegreeAtLeastTwo {F : ℂ → ℂ}
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) : IsOpenMap F := by
  obtain ⟨P, hPdeg, hPF⟩ := hF
  have hne : P.natDegree ≠ 0 := by omega
  rw [show F = fun z : ℂ => P.eval z from funext hPF]
  exact (Polynomial.isOpenQuotientMap_eval P hne).isOpenMap

/-- The petal of petal data lies in the immediate basin: it is open and contained in the basin
(orbits in it converge to `z₀`), hence in `interior (basin F z₀)`, and it is preconnected and
contains `p₀`. -/
private theorem pa_subset_immBasin {F : ℂ → ℂ} {z₀ : ℂ} (pd : PetalData F z₀) {p₀ : ℂ}
    (hp₀ : p₀ ∈ pd.Pa) : pd.Pa ⊆ Work.FatouParabolic.Core.immBasin F z₀ p₀ := by
  have hPa_basin : pd.Pa ⊆ Work.FatouParabolic.basin F z₀ :=
    fun z hz => Work.FatouParabolic.mem_basin.mpr (pd.tendsto_Pa z hz)
  have hPa_int : pd.Pa ⊆ interior (Work.FatouParabolic.basin F z₀) :=
    interior_maximal hPa_basin pd.isOpen_Pa
  exact pd.isPreconnected_Pa.subset_connectedComponentIn hp₀ hPa_int

/-- **The immediate basin of petal data is invariant under `F`.**  Under the polynomial-map
hypothesis (used only to know that `F` is continuous and open), the image of the immediate basin
`Work.FatouParabolic.Core.immBasin F z₀ p₀` under `F` is open (the open mapping principle for
non-constant holomorphic maps), contained in the basin, hence in `interior (basin F z₀)`, and
preconnected, so it lies in the connected component of `F p₀` — which is the component of `p₀`
because `F p₀` lies in the petal and hence in that component.

This is the direct analogue of `Work.FatouParabolic.Core.exists_mapsTo_immBasin` with the flower
replaced by `PetalData`; the proof of that delivered result replays with `pd.tendsto_Pa`,
`pd.isOpen_Pa`, `pd.isPreconnected_Pa`, `pd.mapsTo_Pa` in place of the flower fields, the
sub-inclusion `pd.Pa ⊆ immBasin F z₀ p₀` being the four lines
`mem_basin.mpr (pd.tendsto_Pa · ·)`, `interior_maximal`, `pd.isPreconnected_Pa.subset_connectedComponentIn`
(for which `Submission.Work.FatouParabolic2.pa_subset_immBasin` may be used when it is built). -/
theorem mapsTo_immBasin {F : ℂ → ℂ} {z₀ : ℂ}
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) (pd : PetalData F z₀) {p₀ : ℂ}
    (hp₀ : p₀ ∈ pd.Pa) :
    Set.MapsTo F (Work.FatouParabolic.Core.immBasin F z₀ p₀)
      (Work.FatouParabolic.Core.immBasin F z₀ p₀) := by
  have hopenmap : IsOpenMap F := isOpenMap_of_isPolynomialMapOfDegreeAtLeastTwo hF
  have hcont : Continuous F :=
    (Work.FatouParabolic.Poly.isPolynomialMap_differentiable hF).continuous
  have hPaimm : pd.Pa ⊆ Work.FatouParabolic.Core.immBasin F z₀ p₀ := pa_subset_immBasin pd hp₀
  have hFp₀ : F p₀ ∈ Work.FatouParabolic.Core.immBasin F z₀ p₀ := hPaimm (pd.mapsTo_Pa hp₀)
  -- `F '' Ω` is open and contained in the basin, hence in `interior (basin F z₀)`
  have hFΩ_int : F '' (Work.FatouParabolic.Core.immBasin F z₀ p₀) ⊆
      interior (Work.FatouParabolic.basin F z₀) := by
    refine interior_maximal ?_ (hopenmap _ isOpen_interior.connectedComponentIn)
    rintro _ ⟨z, hz, rfl⟩
    have hzbasin : z ∈ Work.FatouParabolic.basin F z₀ :=
      Work.FatouParabolic.Core.immBasin_subset_basin hz
    rw [Work.FatouParabolic.mem_basin] at hzbasin ⊢
    rw [show (fun k : ℕ => (F^[k]) (F z)) = (fun k : ℕ => (F^[k + 1]) z) from
      funext fun k => (Function.iterate_succ_apply F k z).symm]
    exact (Filter.tendsto_add_atTop_iff_nat (f := fun k : ℕ => (F^[k]) z) 1).mpr hzbasin
  -- the image is preconnected and meets the component of `p₀` at `F p₀`
  have himg : F '' (Work.FatouParabolic.Core.immBasin F z₀ p₀) ⊆
      connectedComponentIn (interior (Work.FatouParabolic.basin F z₀)) (F p₀) :=
    (isPreconnected_connectedComponentIn.image F hcont.continuousOn).subset_connectedComponentIn
      ⟨p₀, hPaimm hp₀, rfl⟩ hFΩ_int
  rw [← connectedComponentIn_eq hFp₀] at himg
  intro z hz
  exact himg ⟨z, hz, rfl⟩

end

end Work.FatouParabolic2
