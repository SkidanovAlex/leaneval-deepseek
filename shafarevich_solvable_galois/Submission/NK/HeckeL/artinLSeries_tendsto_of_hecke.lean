import Mathlib
import Submission.NK.HeckeL.Dictionary
import Submission.NK.HeckeL.Series.heckeLSeries_eq_heckeEulerProduct
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped BigOperators Classical Topology
open Filter

namespace NK.HeckeL

/-- On the region `s > 1` of absolute convergence, the Artin `L`-series of the Galois character
attached to `χ` by Artin reciprocity agrees with the Hecke `L`-series of `χ`: the Euler factor
comparison `artinEulerFactor_toGalois` identifies the two Euler products, and the Euler product
is the Dirichlet series there (`heckeLSeries_eq_heckeEulerProduct`). -/
theorem artinLSeries_eq_heckeLSeries {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] {U : Subgroup (NK.GlobalCFT.Idele K)}
    [Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U)]
    (h : NK.GlobalCFT.ArtinReciprocity K L)
    (e : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U ≃*
      (NK.GlobalCFT.IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K L))
    (S : Finset (NK.HeckeL.PrimeIdeal K))
    (hFrob : NK.HeckeL.FrobeniusCompatibility K L U h e S)
    (χ : NK.HeckeL.RayChar K U) {s : ℝ} (hs : 1 < s) :
    NK.HeckeL.artinLSeries K L S (NK.HeckeL.rayCharEquivGalois h e χ) s
      = NK.HeckeL.heckeLSeries K U S χ s := by
  have hEuler : ∀ t : ℝ, heckeEulerProduct K U S χ t =
      artinLSeries K L S (rayCharEquivGalois h e χ) t := by
    intro t
    unfold heckeEulerProduct artinLSeries
    refine tprod_congr fun 𝔭 => ?_
    exact (artinEulerFactor_toGalois h e S hFrob χ 𝔭.1 𝔭.2 t).symm
  rw [Series.heckeLSeries_eq_heckeEulerProduct U S χ hs, hEuler s]

theorem artinLSeries_tendsto_of_hecke {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] {U : Subgroup (NK.GlobalCFT.Idele K)}
    [Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U)]
    (h : NK.GlobalCFT.ArtinReciprocity K L)
    (e : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U ≃*
      (NK.GlobalCFT.IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K L))
    (S : Finset (NK.HeckeL.PrimeIdeal K))
    (hFrob : NK.HeckeL.FrobeniusCompatibility K L U h e S)
    (χ : NK.HeckeL.RayChar K U) (H : NK.HeckeL.HeckeLRegularAtOne K U S χ) :
    Filter.Tendsto (fun s : ℝ => NK.HeckeL.artinLSeries K L S
      (NK.HeckeL.rayCharEquivGalois h e χ) s) (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhds H.value) := by
  -- the two functions agree on the region `s > 1`, which is a neighbourhood within `Ioi 1`
  refine Filter.Tendsto.congr' ?_ H.tendsto
  refine Filter.eventuallyEq_of_mem self_mem_nhdsWithin ?_
  intro s hs
  show heckeLSeries K U S χ s = artinLSeries K L S (rayCharEquivGalois h e χ) s
  exact (artinLSeries_eq_heckeLSeries h e S hFrob χ hs).symm

end NK.HeckeL
