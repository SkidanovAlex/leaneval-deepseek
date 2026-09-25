import Mathlib
import Submission.NK.HeckeL.Zeta

namespace NK.HeckeL.Product

/-- The Artin `L`-series of the trivial character `1 : Gal(L/K) →* ℂˣ` is the unramified Dedekind
zeta product of `K`: both are the Euler product
`∏_{𝔭 ∉ S} (1 - N𝔭^{-s})⁻¹`, since the trivial character takes the value `1` at every Frobenius
element. -/
theorem artinLSeries_one {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (S : Finset (NK.HeckeL.PrimeIdeal K))
    (s : ℝ) :
    NK.HeckeL.artinLSeries K L S (1 : Gal(L/K) →* ℂˣ) s =
      NK.HeckeL.zetaUnramifiedK K S s := by
  simp [NK.HeckeL.artinLSeries, NK.HeckeL.zetaUnramifiedK, NK.HeckeL.artinEulerFactor]

end NK.HeckeL.Product
