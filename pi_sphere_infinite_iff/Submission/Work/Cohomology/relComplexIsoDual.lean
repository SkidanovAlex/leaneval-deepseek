import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.relCochainDual

/-!
# The relative cochain complex is the dual of the relative chain complex

For a topological space `X` and a subset `A ⊆ X`, the relative singular cochains `C^*(X,A)` are
the kernel of the restriction `C^*(X) ⟶ C^*(A)`, while the relative singular chains `C_*(X,A)` are
the cokernel of the inclusion `C_*(A) ⟶ C_*(X)`.  Since `Hom_ℤ(-, ℤ)` carries cokernels of
`ℤ`-modules to kernels, the two complexes agree:

`C^*(X,A) ≅ Hom_ℤ(C_*(X,A), ℤ) = dualComplex ℤ (relChains X A)`.

This is proved in `Submission.Work.Cohomology.relCochainDual` (degreewise, using the left
exactness of `Hom_ℤ(-, ℤ)`), and recorded here under the requested name.
-/

namespace Work.Cohomology

theorem relComplexIsoDual (X : TopCat) (A : Set X) :
    Nonempty (relComplex ℤ X A ≅ dualComplex ℤ (relChains X A)) :=
  relCochainDual X A

end Work.Cohomology
