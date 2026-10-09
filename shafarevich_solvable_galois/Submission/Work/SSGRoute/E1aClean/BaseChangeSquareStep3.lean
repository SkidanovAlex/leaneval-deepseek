import Submission.Work.SSGRoute.E1aClean.BaseChangeSquareStep2
import Submission.Work.SSGRoute.PT.delta_restrictSES
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # Step 3 of the wiring: δ-naturality under restriction

The δ-form of the dictionary (step 2) is `(e1aSESgen N).delta` applied to `PsiEMap`.  The left-hand
side of the square restricts that `H¹`-class to the fixing subgroup of `LOmega L`, and
`PT.delta_restrictSES` is exactly the statement that the connecting map commutes with that
restriction.  Two corrections found by the first attempt (§2m): the `H⁰`-source of `e1aSESgen N`
sits at `homCoind k Ω K (E1cR1 N)` (the third term of the dualised resolution is
`homCoind (kernel (freeCover N))`), not at `homCoind k Ω K N`; and the `AbsoluteKummer` closure of
`delta_restrictSES` needs `[CharZero k]`. -/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]

/-- **Step 3**: the δ-naturality clause at the square's data, with `x` in the correct `H⁰`-slot. -/
theorem resH1_delta_e1aSESgen (L : IntermediateField k K)
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    (x : ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.homCoind k Ω K
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) N)))) :
    Work.SSGRoute.PT.H2Fin.resH1 (LOmega L).fixingSubgroup
        (Work.SSGRoute.homCoind k Ω K N)
        ((Work.SSGRoute.PT.e1aSESgen (k := k) (Ω := Ω) (K := K) N).delta x)
      = (Work.SSGRoute.ExtChain.restrictSES
          (Work.SSGRoute.PT.e1aSESgen (k := k) (Ω := Ω) (K := K) N)
          (LOmega L).fixingSubgroup).delta
        ⟨x.1, fun u => x.2 (u : Ω ≃ₐ[k] Ω)⟩ :=
  Work.SSGRoute.PT.delta_restrictSES
    (Work.SSGRoute.PT.e1aSESgen (k := k) (Ω := Ω) (K := K) N) (LOmega L).fixingSubgroup x

end

end Work.SSGRoute.E1aClean
