import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Submission.Work.SSGRoute.RamifiedPlacesAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The rational prime below a finite place of `ℚ̄` is a conjugacy invariant

If two finite places `A`, `B` of `ℚ̄` lie over the same prime of `ℚ` — equivalently, are conjugate
under `G_ℚ = Ω ≃ₐ[ℚ] Ω` — then the rational primes `placePrime A hA` and `placePrime B hB` below
them coincide.

The proof is the level-`ℚ` case of "the prime below a place depends only on the trace of the place":
`placePrime` is `Rat.HeightOneSpectrum.primesEquiv` applied to `primeOf`, and `primeOf` depends only
on the restriction `A.comap (algebraMap ℚ ℚ̄)` of `A` to `ℚ`.  A Galois translate `σ • A` has the
same restriction to `ℚ`, since `σ` fixes `ℚ` pointwise.
-/

namespace Work.SSGRoute

theorem placePrime_eq_of_isConjPlace {A B : ValuationSubring SSGRoute.QBar}
    (hA : SSGRoute.IsFinPlace ℚ A) (hB : SSGRoute.IsFinPlace ℚ B)
    (h : SSGRoute.IsConjPlace ℚ A B) :
    Work.SSGRoute.placePrime A hA = Work.SSGRoute.placePrime B hB := by
  obtain ⟨σ, hσ⟩ := h
  -- a Galois translate has the same trace on the base field `ℚ`
  have hcomap : A.comap (algebraMap ℚ SSGRoute.QBar) = B.comap (algebraMap ℚ SSGRoute.QBar) := by
    rw [← hσ]
    exact (Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap
      (K := ℚ) (K' := SSGRoute.QBar) A σ).symm
  -- `placePrime` is `primesEquiv ∘ primeOf`, and `primeOf` only sees the trace
  unfold Work.SSGRoute.placePrime
  exact congrArg Rat.HeightOneSpectrum.primesEquiv
    (Submission.NeukirchUchida.primeOf_eq_of_comap_eq hA hB hcomap)

end Work.SSGRoute
