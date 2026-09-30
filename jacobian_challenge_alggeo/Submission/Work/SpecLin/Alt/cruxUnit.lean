import Mathlib
import Submission.Work.SpecLin.Alt.conservationNumber
import Submission.Work.SpecLin.Alt.refinedHartogs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

namespace Work.SpecLin.Alt

universe u

/-- **The unit step (crux) of the affine-chart core of specialisation of linear equivalence.**

`A` is the coordinate ring of an affine chart of a smooth curve over `K`: finitely generated,
smooth, one-dimensional (`Ring.KrullDimLE 1`, and *not* zero-dimensional — the hypothesis `hA`
is essential, see `Setup/NOTES_cruxPIT_counterexample.md`).  `R` is a valuation ring which is a
`K`-algebra with `B = A ⊗[K] R` a domain and special fibre `A ⊗_K κ` a domain, `P = m_R·B` the
fibre prime, `N ⊇ P` maximal, and `u ∈ Frac B` a unit at `P` and at every height-one prime
`p ≤ N`.  Then `u` is a unit at `N`.

Both directions are instances of `Work.SpecLin.Alt.refinedHartogs`, the `N`-localised
regularity (Hartogs/`S2`) statement for the relative curve `A ⊗[K] R`: applied to `u` it yields
`u ∈ B_N`, applied to `u⁻¹` it yields `u⁻¹ ∈ B_N`. -/
theorem cruxUnit {K : Type u} [Field K] (A : Type u) [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] [Algebra.Smooth K A] [Ring.KrullDimLE 1 A]
    (hA : ¬ Ring.KrullDimLE 0 A)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    [IsDomain (TensorProduct K A R)]
    [IsDomain (TensorProduct K A (IsLocalRing.ResidueField R))]
    (N : Ideal (TensorProduct K A R)) [N.IsMaximal]
    (hPN : ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))) ≤ N)
    (u : FractionRing (TensorProduct K A R))
    (hP : Work.SpecLin.Alt.IsUnitAt u ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))))
    (hht : ∀ p : Ideal (TensorProduct K A R), p.IsPrime → p.height = 1 → p ≤ N →
      Work.SpecLin.Alt.IsUnitAt u p) :
    Work.SpecLin.Alt.IsUnitAt u N := by
  refine ⟨refinedHartogs A hA R N hPN u hP.1
      (fun p hp hp1 hpN => (hht p hp hp1 hpN).1),
    refinedHartogs A hA R N hPN u⁻¹ hP.2
      (fun p hp hp1 hpN => (hht p hp hp1 hpN).2)⟩

end Work.SpecLin.Alt
