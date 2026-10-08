import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.GlaubermanZJ.pPrimeCore_eq_fitting
import Submission.Work.Fitting.isPSolvable_of_solvable

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.ThmC

/-- Conjugation carries `O_{p'}` to `O_{p'}`: `O_{p'}(X^g) = (O_{p'}(X))^g`, where
`pPrimeCoreSub p X = O_{p'}(X)` as a subgroup of `G` (`Work.ThreePoints.ThmC.Defs`) and
`conj g X = g X g⁻¹` (`Submission.Blueprint.conj`).

Useful ingredients already in the workspace: `Work.GlaubermanZJ.pPrimeCore_eq_fitting` rewrites the
blueprint's `pPrimeCore` into the Feit–Thompson project's `Work.Fitting.pPrimeCore`, and
`Work.Fitting.piCore_map_mulEquiv` computes the image of a `π`-core under a group isomorphism. -/
theorem pPrimeCoreSub_conj {G : Type} [Group G] [Finite G] (p : ℕ) (hp : p.Prime)
    (X : Subgroup G) (g : G) :
    Work.ThreePoints.ThmC.pPrimeCoreSub p (Submission.Blueprint.conj g X) =
      Submission.Blueprint.conj g (Work.ThreePoints.ThmC.pPrimeCoreSub p X) := by
  -- The isomorphism `↥X ≃* ↥(g X g⁻¹)` induced by conjugation; it is the restriction of
  -- the automorphism `MulAut.conj g` of `G`.
  let e : ↥X ≃* ↥(Submission.Blueprint.conj g X) :=
    X.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  -- `O_{p'}` of `↥(g X g⁻¹)` is the image of `O_{p'}(↥X)` under `e`.
  have key : Work.Fitting.pPrimeCore p ↥(Submission.Blueprint.conj g X)
      = (Work.Fitting.pPrimeCore p ↥X).map e.toMonoidHom := by
    unfold Work.Fitting.pPrimeCore
    exact (Work.Fitting.piCore_map_mulEquiv e).symm
  -- Rewrite the two blueprint `pPrimeCore`s into the Feit–Thompson project's `π`-core.
  simp only [Work.ThreePoints.ThmC.pPrimeCoreSub, Submission.Blueprint.conj]
  rw [Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp,
      Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp]
  -- Push the second isomorphism through: `map` composes, and both composites are
  -- `x ↦ g * x * g⁻¹` (the definitional equalities of `Subgroup.map_map` and of the
  -- coercion of `equivMapOfInjective` settle this).
  rw [key, Subgroup.map_map, Subgroup.map_map]
  congr 1

end Work.ThreePoints.ThmC
