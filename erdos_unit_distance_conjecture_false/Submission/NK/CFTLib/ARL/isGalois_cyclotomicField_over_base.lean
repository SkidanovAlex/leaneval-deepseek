import Mathlib
import Submission.NK.CFTLib.ARL.Cyclic

namespace NK.CFTLib.ARL

set_option linter.style.haveILetI false

open Polynomial

/-- If `L/K` is a Galois extension of number fields, then adjoining the `M`-th roots of
unity (i.e. `CyclotomicField M L = L(ζ_M)`) stays Galois over `K`.

This is the compositum of the two Galois extensions `L/K` and `K(ζ_M)/K` inside
`L(ζ_M)`: `L(ζ_M)` is the splitting field over `K` of `p * (X^M - 1)`, where `p` is any
polynomial over `K` whose splitting field is `L`. -/
theorem isGalois_cyclotomicField_over_base {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (M : ℕ) [NeZero M] :
    IsGalois K (CyclotomicField M L) := by
  obtain ⟨p, hp_sep, hp_split⟩ := IsGalois.is_separable_splitting_field K L
  haveI : IsSplittingField K L p := hp_split
  have hp_ne : p ≠ 0 := hp_sep.ne_zero
  have hg_ne : (X ^ M - 1 : K[X]) ≠ 0 := by
    simpa using Polynomial.X_pow_sub_C_ne_zero (NeZero.pos M) (1 : K)
  have hmap : (X ^ M - 1 : K[X]).map (algebraMap K L) = (X ^ M - 1 : L[X]) := by
    simp [Polynomial.map_sub, Polynomial.map_pow]
  haveI hL : IsSplittingField L (CyclotomicField M L)
      ((X ^ M - 1 : K[X]).map (algebraMap K L)) := by
    rw [hmap]
    exact IsCyclotomicExtension.isSplittingField_X_pow_sub_one M L _
  haveI hprod : IsSplittingField K (CyclotomicField M L) (p * (X ^ M - 1 : K[X])) :=
    IsSplittingField.mul (F := K) (K := L) (CyclotomicField M L) p (X ^ M - 1) hp_ne hg_ne
  refine isGalois_iff.mpr ⟨inferInstance, ?_⟩
  exact Normal.of_isSplittingField (p * (X ^ M - 1 : K[X]))

end NK.CFTLib.ARL
