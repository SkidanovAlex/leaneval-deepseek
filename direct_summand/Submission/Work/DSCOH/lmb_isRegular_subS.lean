import Mathlib
import Submission.Work.DSCOH.LocBasisDefs

open MvPolynomial

namespace Work.DSCOH

/-- Every element of the submonoid `subS S` (i.e. every monomial in the variables indexed by `S`)
is a regular element of `A[X₀,…,X_{n-1}]`: multiplication by such a monomial is injective. -/
theorem lmb_isRegular_subS {A : Type*} [CommRing A] {n : ℕ} (S : Finset (Fin n))
    (u : subS (A := A) S) : IsRegular (u : Poly A n) := by
  refine Submonoid.closure_induction (motive := fun x (_ : x ∈ _) => IsRegular x) ?_ ?_ ?_ u.2
  · rintro x ⟨i, -, rfl⟩
    exact MvPolynomial.isRegular_X
  · exact isRegular_one
  · intro x y _ _ hx hy
    exact hx.mul hy

end Work.DSCOH
