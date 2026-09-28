import Mathlib
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.CapH

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The cap/cup identity at the level of homology

`Work.Cohomology.kronecker_cap_cup` states, on the level of (co)chains, the cap/cup identity

  `⟨β, c ⌢ α⟩ = (α ⌣ β)(c)`

and `Work.Cohomology.kronH` / `Work.Cohomology.capPair` / `Work.Cohomology.cupH'` are the
corresponding pairings on (co)homology: the Kronecker pairing `Hⁿ ⟶ (Hₙ →ₗ R)`, the cap product
`Hⁿ ⟶ H_{n+m} →ₗ H_m` and the cup product `Hⁿ ⟶ Hᵐ →ₗ H^{n+m}`.

This file proves the *homological* form of the identity,

  `⟨β, c ⌢ α⟩ = ⟨α ⌣ β, c⟩`,

i.e. `kronH n β (capPair m n α c) = kronH (m+n) (cupH' m n α β) c`, by picking representatives
of the (co)homology classes and reducing to `kronecker_cap_cup` through the computation rules
`kronH_apply`, `capPair_apply`, `capPairZ_iCycles` and `cupH'_apply'`.

It is the engine of the intersection-form computations of the Milnor exotic sphere chapter: for a
closed manifold it evaluates `⟨y ⌣ z, [M]⟩` as `⟨y, [M] ⌢ z⟩`.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- **The cap/cup identity on homology.**  For cohomology classes `α ∈ Hᵐ(X;R)`,
`β ∈ Hⁿ(X;R)` and a homology class `c ∈ H_{m+n}(X;R)`:

  `⟨β, c ⌢ α⟩ = ⟨α ⌣ β, c⟩`,

the homology-level form of `Work.Cohomology.kronecker_cap_cup`. -/
theorem kronH_capPair_cup (R : Type) [CommRing R] (X : SSet) (m n : ℕ)
    (α : ↑((Work.Cohomology.cochainC R X).homology m))
    (β : ↑((Work.Cohomology.cochainC R X).homology n))
    (c : ↑((Work.Cohomology.chainC R X).homology (m + n))) :
    Work.Cohomology.kronH R X n β (Work.Cohomology.capPair R X m n α c)
      = Work.Cohomology.kronH R X (m + n) (Work.Cohomology.cupH' R X m n α β) c := by
  -- Replace the classes by the classes of explicit (co)cycles.
  obtain ⟨α₀, hα₀, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf R X m α
  obtain ⟨β₀, hβ₀, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf R X n β
  obtain ⟨c₀, hc₀⟩ := (ModuleCat.epi_iff_surjective
    ((Work.Cohomology.chainC R X).homologyπ (m + n))).mp inferInstance c
  rw [← hc₀]
  -- Evaluate the cup product and the cap product on representatives.
  rw [Work.Cohomology.cupH'_apply' R X α₀ β₀ hα₀ hβ₀]
  rw [show Work.Cohomology.cohomologyClassOf R X α₀ hα₀
      = (Work.Cohomology.cochainC R X).homologyπ m (Work.Cohomology.cocycleOf R X α₀ hα₀)
      from rfl]
  rw [Work.Cohomology.capPair_apply R X m n
    (Work.Cohomology.cocycleOf R X α₀ hα₀) c₀]
  -- Both sides are now evaluations of the Kronecker pairing on classes of (co)cycles.
  rw [Work.Cohomology.kronH_apply R X β₀ hβ₀ (Work.Cohomology.capPairZ R X m n
    (Work.Cohomology.cocycleOf R X α₀ hα₀) c₀)]
  rw [Work.Cohomology.kronH_apply R X (Work.Cohomology.cup R X α₀ β₀)
    (Work.Cohomology.cochainDiff_cup_of_cocycles R X α₀ β₀ hα₀ hβ₀) c₀]
  -- Reduce to the cochain-level identity.
  rw [Work.Cohomology.capPairZ_iCycles R X m n (Work.Cohomology.cocycleOf R X α₀ hα₀) c₀]
  rw [Work.Cohomology.iCycles_cocycleOf R X α₀ hα₀]
  exact Work.Cohomology.kronecker_cap_cup R X α₀ β₀
    (((Work.Cohomology.chainC R X).iCycles (m + n)).hom c₀)

end

end Work.Cohomology
