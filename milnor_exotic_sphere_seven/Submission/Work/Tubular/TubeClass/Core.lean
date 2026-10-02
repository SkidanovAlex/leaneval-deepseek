import Submission.Work.Tubular.Gauss
import Submission.Work.Tubular.OnePointLocalDegree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The degree-one property of the Pontryagin–Thom collapse: core vocabulary

This file fixes the vocabulary of the proof of
`Work.Tubular.tubeCollapseClass_span_top`: the point `x₀` at which the collapse is a local
homeomorphism (a point of the zero section of the normal bundle), the localisation
`H_{8+k}(ν⁺) ⟶ H_{8+k}(ν⁺, ν⁺∖{x₀})`, and the two statements into which the theorem decomposes:

* `Work.Tubular.isZero_homology_onePoint_compl_zeroSectionPoint` — the vanishing
  `H_{8+k}(ν⁺∖{x₀}) = 0` for connected `V`, which makes the localisation injective
  (long exact sequence of the pair `(ν⁺, ν⁺∖{x₀})`);
* `Work.Tubular.localisation_collapseClass_span_top` — the local degree: the localisation of the
  Hurewicz class of the collapse generates the (infinite cyclic) local group `H_{8+k}(ν⁺,ν⁺∖{x₀})`.

Given the two, the theorem is a short argument: an injective map that sends `h` to a generator has
`h` generating, and the map `H_{8+k}(ν⁺) → H_{8+k}(ν⁺,A)` is onto because `A` is contractible.
-/

open CategoryTheory Limits
open scoped Topology

namespace Work.Tubular

noncomputable section

open Work.Cohomology

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The point of the zero section** at which the collapse is a local homeomorphism. -/
def zeroSectionPunctPt (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (v₀ : V.pt) : OnePoint (NormalTotal E) :=
  zeroSectionOnePoint E v₀

/-- The complement of the point `x₀` in `ν⁺`, as a subspace. -/
abbrev PunctCompl (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    Type _ :=
  {p : OnePoint (NormalTotal E) // p ≠ zeroSectionPunctPt E v₀}

/-- **The localisation at `x₀`**: the map `H_n(ν⁺) ⟶ H_n(ν⁺, ν⁺∖{x₀})` on homology, i.e. the map
of the pair `(ν⁺, ∅) → (ν⁺, ν⁺∖{x₀})`.  It is the degree-`n` part of the cokernel projection
defining the relative chain complex of the pair with sub-object `{x₀}ᶜ`. -/
noncomputable def localisationPunct (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (v₀ : V.pt) (n : ℕ) :
    (singularChains ℤ (TopCat.of (OnePoint (NormalTotal E)))).homology n →ₗ[ℤ]
      (relChains (TopCat.of (OnePoint (NormalTotal E)))
        ({zeroSectionPunctPt E v₀}ᶜ : Set (OnePoint (NormalTotal E)))).homology n :=
  (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
    (CategoryTheory.Limits.cokernel.π (inclChains (TopCat.of (OnePoint (NormalTotal E)))
      ({zeroSectionPunctPt E v₀}ᶜ : Set (OnePoint (NormalTotal E))))) n))

end

end Work.Tubular
