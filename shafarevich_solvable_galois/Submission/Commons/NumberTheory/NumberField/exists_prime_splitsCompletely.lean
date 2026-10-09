import Mathlib
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField

open IsDedekindDomain

theorem exists_prime_splitsCompletely {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    ∃ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard = Module.finrank K L := by
  by_contra h
  rw [not_exists] at h
  set S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
    {p | (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard = Module.finrank K L}
    with hSdef
  have hSfin : S.Finite := by
    rw [show S = ∅ by ext p; simp [hSdef, h p]]
    exact Set.finite_empty
  have h0 : NumberField.Set.HasDirichletDensity S 0 :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite hSfin
  have h1 : NumberField.Set.HasDirichletDensity S (1 / (Module.finrank K L : ℝ)) :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
  have heq : (0 : ℝ) = 1 / (Module.finrank K L : ℝ) :=
    tendsto_nhds_unique h0 h1
  have hpos : (0 : ℝ) < (Module.finrank K L : ℝ) := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := L))
  have : (0 : ℝ) < 1 / (Module.finrank K L : ℝ) := by positivity
  linarith

end Commons.NumberTheory.NumberField
