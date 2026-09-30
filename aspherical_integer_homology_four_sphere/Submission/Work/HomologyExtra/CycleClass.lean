import Mathlib
import ChallengeDeps
import Submission.Work.Homology.Basic
import Submission.Work.Homology.Pairs
import Submission.Work.Homology.Point
import Submission.Work.Homology.RelChainMap
import Submission.Work.Homology.Corollaries
import Submission.Work.Homology.SingHomologyHomeomorph
import Submission.Work.Homology.HomologyBiprod
import Submission.Work.Homology.SingHomologyClopen
import Submission.Work.Homology.ContractibleHomology
import Submission.Work.Homology.BallHomology
import Submission.Work.Homology.StdSimplexHomology
import Submission.Work.Homology.HomotopyEquivHomology
import Submission.Work.Homology.DeformationRetractHomology
import Submission.Work.Homology.SimplexShim
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Homology.Spheres
import Submission.Work.Homology.MayerVietoris

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option backward.isDefEq.respectTransparency false

/-!
# The homology class of a cycle

For a chain complex `K` of `ℤ`-modules, an element `x : A ⟶ K.X i` with `x ≫ K.d i (next i) = 0`
(a *cycle*) determines a morphism `A ⟶ K.homology i`, its **homology class**.  We package this
construction as `Work.HomologyExtra.cycleClass` together with its naturality in chain maps and its
invariance under adding boundaries; all the explicit "generator" statements of this chapter
(`simplexGenMap`, `simplexBoundaryClass`) are instances of it.

## Main definitions and results

* `cycleClass x hx` — the class of the cycle `x`;
* `cycleClass_eq` — equal cycles have equal classes;
* `cycleClass_naturality` — naturality in chain maps;
* `cycleClass_eq_of_eq_add_boundary` — invariance under adding a boundary.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.HomologyExtra

noncomputable section

/-- **The homology class of a cycle**: for `x : A ⟶ K.X i` with `x ≫ K.d i (next i) = 0`, the
induced morphism `A ⟶ K.homology i`. -/
noncomputable def cycleClass {K : ChainComplex (ModuleCat ℤ) ℕ} {A : ModuleCat ℤ} {i : ℕ}
    (x : A ⟶ K.X i) (hx : x ≫ K.d i ((ComplexShape.down ℕ).next i) = 0) : A ⟶ K.homology i :=
  K.liftCycles x ((ComplexShape.down ℕ).next i) rfl hx ≫ K.homologyπ i

/-- The class of a cycle, as the composite of the lift to the cycles and the projection onto
homology. -/
theorem cycleClass_def {K : ChainComplex (ModuleCat ℤ) ℕ} {A : ModuleCat ℤ} {i : ℕ}
    (x : A ⟶ K.X i) (hx : x ≫ K.d i ((ComplexShape.down ℕ).next i) = 0) :
    cycleClass x hx =
      K.liftCycles x ((ComplexShape.down ℕ).next i) rfl hx ≫ K.homologyπ i := rfl

/-- Equal cycles have equal classes. -/
theorem cycleClass_eq {K : ChainComplex (ModuleCat ℤ) ℕ} {A : ModuleCat ℤ} {i : ℕ}
    {x x' : A ⟶ K.X i} (hx : x ≫ K.d i ((ComplexShape.down ℕ).next i) = 0)
    (hx' : x' ≫ K.d i ((ComplexShape.down ℕ).next i) = 0) (h : x = x') :
    cycleClass x hx = cycleClass x' hx' := by
  subst h
  rfl

end

end Work.HomologyExtra
