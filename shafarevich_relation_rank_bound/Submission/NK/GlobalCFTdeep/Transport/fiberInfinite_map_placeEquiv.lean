import Mathlib
import Submission.NK.GlobalCFTdeep.Transport.PlaceDefs
import Submission.NK.GlobalCFTdeep.Transport.liesOver_placeEquiv

/-!
# The archimedean fibre above a place is transported by `placeEquiv`

Given a compatible pair of ring equivalences `eK : K ≃+* K'`, `eL : L ≃+* L'` of number fields
(`hcomp`: `eL ∘ algebraMap K L = algebraMap K' L' ∘ eK`), the bijection
`infinitePlaceEquiv eL : InfinitePlace L ≃ InfinitePlace L'` sends the set of archimedean
places of `L` lying over `w` onto the set of archimedean places of `L'` lying over
`infinitePlaceEquiv eK w`:

  `(fiberInfinite w).map (infinitePlaceEquiv eL) = fiberInfinite (infinitePlaceEquiv eK w)`.

This is the index-level statement needed to transport the restricted product decompositions of
the idèles (and hence the norm subgroup `N_{L/K} C_L`) across a ring equivalence.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace NK.GlobalCFTdeep.Transport

open NK.GlobalCFT

/-- The "lies over" relation on archimedean places, in the form of the underlying finsets: the
fibre `fiberInfinite w` of `w` in the extension `L/K` is carried by `infinitePlaceEquiv eL`
onto the fibre of `infinitePlaceEquiv eK w` in the extension `L'/K'`. -/
theorem fiberInfinite_map_placeEquiv
    {K L K' L' : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Field K'] [NumberField K'] [Field L'] [NumberField L'] [Algebra K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (w : NumberField.InfinitePlace K) :
    (NK.GlobalCFT.Place.fiberInfinite (K := K) (L := L) w).map
        (NK.GlobalCFTdeep.Transport.infinitePlaceEquiv eL).toEmbedding =
      NK.GlobalCFT.Place.fiberInfinite (K := K') (L := L')
        (NK.GlobalCFTdeep.Transport.infinitePlaceEquiv eK w) := by
  ext w'
  rw [Finset.mem_map_equiv]
  simp only [NK.GlobalCFT.Place.fiberInfinite, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [NK.GlobalCFTdeep.Transport.infinitePlaceEquiv_liesOver_iff eK eL hcomp]
  simp

end NK.GlobalCFTdeep.Transport
