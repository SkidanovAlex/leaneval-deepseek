import Mathlib
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

set_option linter.style.haveILetI false in
/-- The fraction ring of the polynomial ring in no variables over `M` is just `M`:
since `MvPolynomial (Fin 0) M ≃ₐ[M] M` is a field of fractions of `M`, the same holds for
`FractionRing (MvPolynomial (Fin 0) M)` by `IsFractionRing.trans`, so the `M`-algebra map
into the fraction ring is surjective. -/
theorem exists_eq_algebraMap_fin_zero (𝕜 M : Type) [Field 𝕜] [Field M] [Algebra 𝕜 M]
    (z : FractionRing (MvPolynomial (Fin 0) M)) :
    ∃ c : M, z = algebraMap M (FractionRing (MvPolynomial (Fin 0) M)) c := by
  -- `MvPolynomial (Fin 0) M` is `M` itself, hence a field of fractions of `M`;
  haveI h1 : IsFractionRing M (MvPolynomial (Fin 0) M) :=
    IsFractionRing.of_algEquiv (MvPolynomial.isEmptyAlgEquiv M (Fin 0)).symm
  -- hence its fraction ring is again a field of fractions of `M`,
  haveI h2 : IsFractionRing M (FractionRing (MvPolynomial (Fin 0) M)) :=
    IsFractionRing.trans M (MvPolynomial (Fin 0) M) (FractionRing (MvPolynomial (Fin 0) M))
  -- and so it is isomorphic to `FractionRing M ≃ₐ[M] M` as an `M`-algebra.
  let e : FractionRing (MvPolynomial (Fin 0) M) ≃ₐ[M] M :=
    (IsLocalization.algEquiv (nonZeroDivisors M) (FractionRing M)
      (FractionRing (MvPolynomial (Fin 0) M))).symm.trans (FractionRing.algEquiv M M)
  exact ⟨e z, by rw [← e.injective.eq_iff]; simp⟩

end Work.MotV
