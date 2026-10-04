import Mathlib
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.dualDifferential_comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Singular cohomology (first definitions)

Packaging `Submission.Work.Cohomology.Chains` with the lemma
`Work.Cohomology.dualDifferential_comp` (the transposed differentials compose to zero):

* `singularCochainComplex R X` — the `R`-dual cochain complex of the singular chains of `X`;
* `singularCohomology R n X` — the `n`-th singular cohomology `Hⁿ(X; R)`.

This is the first step of the cohomology chapter which `Submission/NOTES.md` describes; the
remaining steps (cup products, Mayer–Vietoris, Poincaré duality, characteristic classes) are what
the dimension-8 signature theorem — and hence the exoticness of `Mk (-2)` — needs.
-/

open CategoryTheory AlgebraicTopology

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-- The **singular cochain complex** of a topological space with coefficients in `R`: the `R`-dual
of the singular chain complex, with differential `f ↦ f ∘ d`. -/
def singularCochainComplex (X : TopCat) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (dualChains R X) (dualDifferential R X)
    (fun n => dualDifferential_comp R X n)

/-- **Singular cohomology** of a topological space with coefficients in `R`. -/
def singularCohomology (n : ℕ) (X : TopCat) : ModuleCat R :=
  (singularCochainComplex R X).homology n

end

end Work.Cohomology
