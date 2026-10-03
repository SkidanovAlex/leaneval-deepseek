/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The free case of node N3: `gl.dim K[F(X)] ≤ 1`

The presentation `⟨X | 1⟩` with the single *trivial* relator is the free group `F(X)`, so
`K[PresentedGroup {1}] = K[F(X)]` is the group algebra of a free group.  The main result of this
file is

`Work.ORFinal.FreeCase.globalDim_le_one_free`:
`gl.dim K[F(X)] ≤ 1` for every field `K` and every set of generators `X` (no hypothesis on the
characteristic, and no finiteness of `X`).

The mathematics is the length-one free resolution of the trivial module of a free group algebra:

`0 → K[F(X)]^{(X)} --δ--> K[F(X)] --ε--> K → 0`,  `δ (a_x) = Σ_x a_x (x - 1)`,

i.e. the augmentation ideal `I_{K[F(X)]} = ker ε` is a *free* left `K[F(X)]`-module with basis
`{x - 1 : x ∈ X}`.  This is exactly the statement that `δ` is injective with range `I`, which the
`Work.ORLyndon` development proves (`Work.ORLyndon.lyndon_ker_delta_free`,
`Work.ORLyndon.lyndonDelta_range_eq_augIdeal`), the injectivity being the classical Fox-derivative
argument (`Work.ORFP2.augIdeal_freeGroup_injective`).

Consequently `I_{K[F(X)]}` is projective, the trivial module `K[F(X)]/I` has a projective
resolution of length one, and the transfer step of Jaikin-Zapirain–Linton, Proposition 2.2
(`Work.ORLyndon.hasProjDimLE_of_trivial`), upgrades this to a bound on the projective dimension of
*every* left module; the bridges `Work.ORLyndon.hasProjectiveDimensionLE_of_hasProjDimLE` and
`Work.ORLyndon.globalDim_le_of_forall_projectiveDimension` convert this into the bound on
`Work.ORCoherence.globalDim`.
-/
import Mathlib
import Submission.Work.ORLyndon.All

namespace Work.ORFinal.FreeCase

/-- **The free case of node N3**: the group algebra of the free group on `X` over a field `K` has
global dimension at most one.  Here the presented group `⟨X | 1⟩ = F(X)` is the free group on `X`,
so `K[PresentedGroup {1}]` is the group algebra of a free group.

The augmentation ideal of a free group algebra is free on the elements `x - 1` (that is, the Lyndon
`δ` of the trivial relator is injective with range the augmentation ideal), so the trivial module
has a free resolution of length one; Proposition 2.2 of Jaikin-Zapirain–Linton (the transfer step
`Work.ORLyndon.hasProjDimLE_of_trivial`) then bounds the projective dimension of every module by
one. -/
theorem globalDim_le_one_free (K : Type*) [Field K] (X : Type*) [DecidableEq X] :
    Work.ORCoherence.globalDim
      (MonoidAlgebra K (PresentedGroup ({1} : Set (FreeGroup X)))) ≤ (1 : WithBot ℕ∞) := by
  -- `⟨X | 1⟩` is `Work.ORLyndon.OneRelatorGroup 1`, by definition
  change Work.ORCoherence.globalDim
      (MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup (1 : FreeGroup X))) ≤ (1 : WithBot ℕ∞)
  -- it suffices to bound the projective dimension of every left module by one
  apply Work.ORLyndon.globalDim_le_of_forall_projectiveDimension
  intro M
  refine Work.ORLyndon.hasProjectiveDimensionLE_of_hasProjDimLE ?_
  -- which by the transfer step follows from the trivial module having a resolution of length one
  refine Work.ORLyndon.hasProjDimLE_of_trivial 1 ?_
  -- the Lyndon `δ` of the trivial relator is injective with range the augmentation ideal
  have hker : LinearMap.ker (Work.ORLyndon.lyndonDelta K (1 : FreeGroup X)) = ⊥ :=
    Work.ORLyndon.lyndon_ker_delta_free
  have hrange : LinearMap.range (Work.ORLyndon.lyndonDelta K (1 : FreeGroup X)) =
      Work.ORLyndon.augIdeal K (Work.ORLyndon.OneRelatorGroup (1 : FreeGroup X)) :=
    Work.ORLyndon.lyndonDelta_range_eq_augIdeal (K := K) (1 : FreeGroup X)
  have hinj : Function.Injective (Work.ORLyndon.lyndonDelta K (1 : FreeGroup X)) :=
    LinearMap.ker_eq_bot.mp hker
  -- hence the augmentation ideal is isomorphic to the free module `K[G]^{(X)}`, so it is
  -- projective
  have hpdAug : Work.ORLyndon.HasProjDimLE
      (MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup (1 : FreeGroup X)))
      (Work.ORLyndon.augIdeal K (Work.ORLyndon.OneRelatorGroup (1 : FreeGroup X))) 0 := by
    have e : (X →₀ MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup (1 : FreeGroup X))) ≃ₗ[
        MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup (1 : FreeGroup X))]
        (Work.ORLyndon.augIdeal K (Work.ORLyndon.OneRelatorGroup (1 : FreeGroup X))) :=
      (LinearEquiv.ofInjective (Work.ORLyndon.lyndonDelta K (1 : FreeGroup X)) hinj).trans
        (LinearEquiv.ofEq _ _ hrange)
    exact Work.ORLyndon.HasProjDimLE_of_linearEquiv e
      (Module.Projective.of_free : Module.Projective _ (X →₀ _))
  -- the trivial module is the quotient of the free module `K[G]` by the projective ideal
  refine ⟨_, inferInstance, inferInstance, Module.Projective.of_free,
    Submodule.mkQ (Work.ORLyndon.augIdeal K (Work.ORLyndon.OneRelatorGroup (1 : FreeGroup X))),
    Submodule.mkQ_surjective _, ?_⟩
  rw [Submodule.ker_mkQ]
  exact hpdAug

end Work.ORFinal.FreeCase
