import Mathlib
import Submission.NK.HeckeL.Dictionary
import Submission.NK.HeckeL.heckeEulerProduct_eq_artinLSeries
import Submission.NK.HeckeL.Series.heckeLSeries_eq_heckeEulerProduct

open Filter
open scoped Topology

namespace NK.HeckeL

/-- **Hecke's regularity at `s = 1`, transferred from the Artin side.**

The Hecke `L`-series of a ray class character `χ` agrees with the Artin `L`-series of the
corresponding Galois character `rayCharEquivGalois h e χ` on the half-plane `s > 1`
(`heckeEulerProduct_eq_artinLSeries` identifies the Euler factors at every prime outside `S`,
and `heckeLSeries_eq_heckeEulerProduct` identifies the Euler product with the Dirichlet series
there).  Hence, if the Artin `L`-series converges to `H.value` as `s → 1⁺`, so does the Hecke
`L`-series.  This is the converse of `artinLSeries_tendsto_of_hecke`. -/
theorem heckeLSeries_tendsto_of_artin {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] {U : Subgroup (NK.GlobalCFT.Idele K)}
    [Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U)]
    (h : NK.GlobalCFT.ArtinReciprocity K L)
    (e : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U ≃*
      (NK.GlobalCFT.IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K L))
    (S : Finset (NK.HeckeL.PrimeIdeal K))
    (hFrob : NK.HeckeL.FrobeniusCompatibility K L U h e S)
    (χ : NK.HeckeL.RayChar K U)
    (H : NK.HeckeL.ArtinLRegularAtOne K L S (NK.HeckeL.rayCharEquivGalois h e χ)) :
    Filter.Tendsto (fun s : ℝ => NK.HeckeL.heckeLSeries K U S χ s)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds H.value) := by
  -- the two functions agree on `s > 1`, a neighbourhood within `Ioi 1`
  refine Filter.Tendsto.congr' ?_ H.tendsto
  refine Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun s hs => ?_
  show NK.HeckeL.artinLSeries K L S (NK.HeckeL.rayCharEquivGalois h e χ) s
    = NK.HeckeL.heckeLSeries K U S χ s
  rw [NK.HeckeL.Series.heckeLSeries_eq_heckeEulerProduct U S χ hs]
  exact (NK.HeckeL.heckeEulerProduct_eq_artinLSeries h e S hFrob χ s).symm

end NK.HeckeL
