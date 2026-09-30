/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area UP — the universal property of the Jacobian: table of contents

Import this module for the whole chapter.
-/
import Submission.Work.Universal.Basic
import Submission.Work.Universal.sumMap_powMap
import Submission.Work.Universal.sumMap_comp_hom
import Submission.Work.Universal.curveIso_sumMap
import Submission.Work.Universal.sumDiv_ptDiv
import Submission.Work.Universal.sumDiv_P0Div
import Submission.Work.Universal.factorCompat_holds
import Submission.Work.Universal.Factor
import Submission.Work.Universal.factor_value
import Submission.Work.Universal.epi
import Submission.Work.Universal.univ

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area UP — the universal property of the Jacobian (the Albanese property)

Area UP of the Jacobian drive, `Submission/Work/NOTES_LEAD_jacobian_GC.md` §3.8; see
`Submission/Work/Universal/NOTES.md` for the full description.

For a curve `C` over a field `K` with a base point `P0`, a chart datum
`D : Work.GroupChunk.Input C P0` (area GC), an instance `U : Work.Universal.Input C P0` of the
area's interface (the named hypotheses of areas GC, KL and SY) and a commutative group scheme
`A` over `K`, this area provides

* `Work.Universal.sumMap D f n : D.Sym n ⟶ A` — the sum morphism `Σᵐ f`, with
  `sumMap_spec`, `sumMap_unique`, `sumMap_powMap` (its value on `powMap`),
  `sumMap_comp_hom` (naturality in a homomorphism) and `curveIso_sumMap` (`Σ¹ f = f`);
* `Work.Universal.sumDiv D f E hE n hn : FPt A F` — the sum `Σ f(E)` of `f` over an effective
  divisor `E` of degree `n`, with `sumMap_fpt`, `sumDiv_eq_of_divOf`, `sumDiv_ptDiv`
  (`Σ f([x]) = f(x)`) and `sumDiv_P0Div` (`Σ f([P0]) = 0` for a pointed `f`);
* `Work.Universal.factor D f : U.glued.G ⟶ A` — the morphism glued from the chart maps
  `D ↦ Σ f(D) / Σ f(E i)`, with `factor_eq_chartMap` (its restriction to the charts) and
  `factor_value` (its value at a point whose class is `[D₁] - [D₂]`);
* `Work.Universal.epi` — `AJ₀` is an epimorphism onto abelian varieties;
* `Work.Universal.univ` — **the universal property**: every pointed `f : C ⟶ A` into an abelian
  variety factors uniquely as `f = AJ₀ ≫ g`.

The interface `Work.Universal.Input`, and the wrappers `prodHom`, `zeroPt`, `divPt`, are in
`Submission.Work.Universal.Basic`.
-/
