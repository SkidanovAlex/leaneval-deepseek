import Mathlib
import Submission.Work.Tower.Defs
import Submission.Work.Tower.Unramified.Basic

/-!
# Total realness is preserved by unramified odd-degree Galois extensions

If `F` is totally real and `L/F` is a finite **Galois** extension of odd degree, then `L` is
totally real.  Indeed, a real place of `F` that became complex in `L` would have a ramified
infinite place; Mathlib's `InfinitePlace.even_finrank_of_not_isUnramifiedIn` then forces
`[L : F]` to be even.  This is the paper's argument ("a real place becoming complex would give a
decomposition group at an infinite place of order `2`, impossible in a `3`-group").

Note that the finite-prime unramifiedness hypothesis of the paper's statement is *not* needed
for this conclusion; we record the sharp statement, and the corollary
`isTotallyReal_of_isPGroup_three_unramified` in the form used in the tower construction.

## Main results

* `Work.Tower.isTotallyReal_of_odd_finrank`;
* `Work.Tower.isTotallyReal_of_isPGroup_three`.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace Tower

/-- **Total realness is preserved by odd-degree Galois extensions.** -/
theorem isTotallyReal_of_odd_finrank {F L : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L] (hF : IsTotallyReal F)
    (hodd : Odd (Module.finrank F L)) : IsTotallyReal L := by
  by_contra h
  rw [isTotallyReal_iff] at h
  push Not at h
  obtain ⟨v, hv⟩ := h
  have hvC : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
  have hwR : (v.comap (algebraMap F L)).IsReal := IsTotallyReal.isReal _
  have hram : v.IsRamified F := InfinitePlace.isRamified_iff.mpr ⟨hvC, hwR⟩
  have hnot : ¬ (v.comap (algebraMap F L)).IsUnramifiedIn L := by
    intro hI
    exact hram (hI v rfl)
  exact (Nat.not_even_iff_odd.mpr hodd) (InfinitePlace.even_finrank_of_not_isUnramifiedIn hnot)

/-- **Total realness is preserved by unramified (indeed any) Galois `3`-group extensions.** -/
theorem isTotallyReal_of_isPGroup_three {F L : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L] (hF : IsTotallyReal F)
    (h : IsPGroup 3 (Gal(L/F))) : IsTotallyReal L := by
  refine isTotallyReal_of_odd_finrank hF ?_
  rw [← IsGalois.card_aut_eq_finrank]
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3) (G := Gal(L/F))).mp h
  rw [hn]
  exact Odd.pow (by decide : Odd 3)

/-- The form used in the tower construction: the finite-prime unramifiedness hypothesis of the
paper is carried along (it is not needed for the conclusion). -/
theorem isTotallyReal_of_isPGroup_three_unramified {F L : Type*} [Field F] [Field L] [Algebra F L]
    [NumberField F] [NumberField L] [FiniteDimensional F L] [IsGalois F L]
    (hF : IsTotallyReal F) (hunr : IsUnramifiedExtension F L)
    (h : IsPGroup 3 (Gal(L/F))) : IsTotallyReal L :=
  isTotallyReal_of_isPGroup_three hF h

end Tower
end Work
