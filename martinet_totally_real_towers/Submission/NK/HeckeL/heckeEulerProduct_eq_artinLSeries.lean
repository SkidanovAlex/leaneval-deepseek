import Mathlib
import Submission.NK.HeckeL.Dictionary

namespace NK.HeckeL

/-- **The Hecke Euler product of a ray class character equals the Artin `L`-series of the
corresponding Galois character.**  Both are infinite products over the primes `𝔭 ∉ S`, and the
factors agree at each such prime by `NK.HeckeL.artinEulerFactor_toGalois`, which is exactly the
Frobenius compatibility `hFrob` fed through Artin reciprocity. -/
theorem heckeEulerProduct_eq_artinLSeries {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] {U : Subgroup (NK.GlobalCFT.Idele K)}
    (h : NK.GlobalCFT.ArtinReciprocity K L)
    (e : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U ≃*
      (NK.GlobalCFT.IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K L))
    (S : Finset (NK.HeckeL.PrimeIdeal K))
    (hFrob : NK.HeckeL.FrobeniusCompatibility K L U h e S)
    (χ : NK.HeckeL.RayChar K U) (s : ℝ) :
    NK.HeckeL.heckeEulerProduct K U S χ s =
      NK.HeckeL.artinLSeries K L S (NK.HeckeL.rayCharEquivGalois h e χ) s := by
  unfold NK.HeckeL.heckeEulerProduct NK.HeckeL.artinLSeries
  exact tprod_congr fun 𝔭 =>
    (NK.HeckeL.artinEulerFactor_toGalois h e S hFrob χ 𝔭.1 𝔭.2 s).symm

end NK.HeckeL
