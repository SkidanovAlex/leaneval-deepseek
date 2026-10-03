import Mathlib
import Submission.Work.ORLyndon.Lyndon
import Submission.Work.ORLyndon.Augmentation
import Submission.Work.ORLyndon.lyndon_exact_relationModuleMap
import Submission.Work.ORLyndon.relationModuleMap_injective
import Submission.Work.ORLyndon.lyndonDelta_range_eq_augIdeal

/-!
# The Lyndon sequence `0 → K[G] ⊗_{K⟨u⟩} K → K[G]^X → K[G] → K → 0`

This file collects the exactness of the Lyndon resolution of a one-relator presentation
`G = ⟨X | r = u ^ l⟩` into a single statement: the four-term exact sequence

`0 → K[G] ⊗_{K⟨u⟩} K → K[G]^X → K[G] → K → 0`,

where

* the first term is the relation module `relationModule K r u = K[G]/K[G](u-1)`
  (`Work.ORLyndon.relationModule_eq_quot_augIdealIn` identifies it with `K[G] ⧸ I^G_{K[⟨u⟩]}`, and
  `Submission/Work/ORLyndon/relationModule_balTensor.lean` with the balanced tensor product
  `K[G] ⊗_{K⟨u⟩} K`),
* the second is the free module `K[G]^X` (`X →₀ K[G]`),
* the third is `K[G]`, and the last is `K`.

The content is the conjunction of the results proved in the sibling files:
`Work.ORLyndon.relationModuleMap_injective`,
`Work.ORLyndon.lyndon_exact_relationModuleMap` and
`Work.ORLyndon.lyndonDelta_range_eq_augIdeal`, together with the definitional fact that the
augmentation `ε : K[G] →ₐ[K] K` has kernel `I_{K[G]} = augIdeal K G` and is surjective.  It is
packaged here because this is the form in which the sequence is quoted in the paper (JL Section 5,
before transposing to the two-term form of Claim 5.10).
-/

set_option autoImplicit false

open MonoidAlgebra

universe u v

namespace Work.ORLyndon

/-- **The Lyndon sequence of a one-relator presentation is exact.**  For `G = ⟨X | r = u^l⟩` with
`LyndonIdentity K X r u l` (`range θ = ker δ`, `ker θ = K[G](u - 1)`), the sequence

`0 → relationModule K r u → K[G]^X → K[G] → K → 0`

is exact: the first map is injective with image `ker δ`, `δ` has image `I_{K[G]}`, and the
augmentation has kernel `I_{K[G]}` and is surjective. -/
theorem lyndon_fourTerm_exact {X : Type u} [DecidableEq X] {K : Type v} [Field K]
    {r u : FreeGroup X} {l : ℕ} (h : LyndonIdentity K X r u l) :
    Function.Injective (relationModuleMap K r u l h) ∧
      LinearMap.range (relationModuleMap K r u l h) = LinearMap.ker (lyndonDelta (K := K) r) ∧
      LinearMap.range (lyndonDelta (K := K) r) = augIdeal K (OneRelatorGroup r) ∧
      RingHom.ker (augmentation K (OneRelatorGroup r) :
        MonoidAlgebra K (OneRelatorGroup r) →+* K) = augIdeal K (OneRelatorGroup r) ∧
      Function.Surjective (augmentation K (OneRelatorGroup r)) :=
  ⟨relationModuleMap_injective h, lyndon_exact_relationModuleMap h,
    lyndonDelta_range_eq_augIdeal (K := K) r, (augIdeal_def).symm,
    fun c => ⟨MonoidAlgebra.single (1 : OneRelatorGroup r) c, augmentation_single _ _⟩⟩

end Work.ORLyndon
