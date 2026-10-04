import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Singular chains and the dual differential

Mathlib has the singular chain complex of a topological space
(`AlgebraicTopology.singularChainComplexFunctor`) but no cohomology.  This file starts the missing
chapter with the two definitions on which everything else rests:

* `singularChains R X` — the singular chain complex of `X` with coefficients in the ring `R`;
* `dualDifferential R X n` — the transpose `f ↦ f ∘ d` of the `n`-th differential, as a morphism
  between the `R`-duals of the modules of `n`- and `(n+1)`-chains.

The fact that these differentials compose to zero (so that they define a *cochain* complex) is the
separate lemma `Work.Cohomology.dualDifferential_comp`.
-/

open CategoryTheory AlgebraicTopology

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-- The singular chain complex of a topological space, with coefficients in `R`. -/
abbrev singularChains (X : TopCat) : ChainComplex (ModuleCat R) ℕ :=
  ((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).obj X

/-- The `R`-dual of the module of `n`-chains of `X`. -/
abbrev dualChains (X : TopCat) (n : ℕ) : ModuleCat R :=
  ModuleCat.of R ((singularChains R X).X n →ₗ[R] R)

/-- The transpose `f ↦ f ∘ d` of the `n`-th singular differential, as a morphism of `R`-modules
from the dual of the `n`-chains to the dual of the `(n+1)`-chains. -/
def dualDifferential (X : TopCat) (n : ℕ) : dualChains R X n ⟶ dualChains R X (n + 1) :=
  ModuleCat.ofHom
    { toFun := fun f => f.comp (((singularChains R X).d (n + 1) n).hom)
      map_add' := fun f g => by ext x; simp [LinearMap.add_comp]
      map_smul' := fun a f => by ext x; simp [LinearMap.smul_comp] }

end

end Work.Cohomology
