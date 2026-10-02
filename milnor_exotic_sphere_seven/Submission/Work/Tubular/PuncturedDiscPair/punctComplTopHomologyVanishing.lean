import Mathlib
import Submission.Work.Tubular.PuncturedDiscPair.puncturedNormalPair_vanishing
import Submission.Work.Tubular.PuncturedDiscPair.punctCompl_of_pairVanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

/-!
# Vanishing of the top homology of `ν⁺ ∖ {x₀}`

For a connected closed oriented `8`-manifold `V` embedded in `ℝ^{8+k}`
(`E : EmbeddingData V (8+k)`) and a point `v₀ : V`, the complement of the corresponding point `x₀`
of the zero section in the Thom space `ν⁺` of the normal bundle has vanishing `H_{8+k}`:

`H_{8+k}(ν⁺ ∖ {x₀}) = 0`.

## Proof

This is the geometric input `hA` of the tubular chapter (item (B2) of
`Submission/Work/Tubular/TubeClass`).  It is obtained in two steps.

* The **local degree input** is the vanishing of the top homology of the *punctured normal pair*
  `(ν ∖ {x₀}, ν ∖ 0)` — the statement that the fundamental class of the disc-bundle pair localises
  non-trivially at a point of the zero section.  It is proved as
  `Work.Tubular.PuncturedDiscPair.puncturedNormalPair_vanishing` (via the sphere bundle over the
  punctured base).
* The **comparison** `H_{8+k}(ν⁺∖{x₀}) ≅ H_{8+k}(ν∖{x₀}, ν∖0)` is excision of the point at
  infinity together with the contractibility of the complement of the zero section; it is
  `Work.Tubular.PuncturedDiscPair.punctCompl_of_pairVanishing`.

-/

open CategoryTheory Limits
open scoped Topology

namespace Work.Tubular.PuncturedDiscPair

noncomputable section

/-- **The vanishing of `H_{8+k}(ν⁺ ∖ {x₀})`.** -/
theorem punctComplTopHomologyVanishing {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of (Work.Tubular.PunctCompl E v₀))).homology (8 + k)) :=
  punctCompl_of_pairVanishing E v₀ (puncturedNormalPair_vanishing E v₀)

end

end Work.Tubular.PuncturedDiscPair
