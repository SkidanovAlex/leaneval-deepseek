import Mathlib.NumberTheory.NumberField.DirichletDensity
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_of_density_zero
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Set

open Filter IsDedekindDomain Topology Set

/-- **Dirichlet density is insensitive to finite modifications.**

If `S` has Dirichlet density `δ` and `T` is a finite set of primes, then `S ∪ T` again has
Dirichlet density `δ`.  This is the form in which density statements are used in practice: the
finitely many ramified primes, or the finitely many primes dividing a fixed modulus, never change
a density.  It follows from
`Commons.NumberField.Set.hasDirichletDensity_zero_of_finite` (a finite set has density `0`) and
`Commons.NumberField.Set.hasDirichletDensity_union_of_density_zero`. -/
theorem hasDirichletDensity_union_finite {K : Type*} [Field K] [NumberField K]
    {S T : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {δ : ℝ}
    (hS : NumberField.Set.HasDirichletDensity S δ) (hT : T.Finite) :
    NumberField.Set.HasDirichletDensity (S ∪ T) δ := by
  exact hasDirichletDensity_union_of_density_zero hS (hasDirichletDensity_zero_of_finite hT)

end Commons.NumberTheory.NumberField.Set
