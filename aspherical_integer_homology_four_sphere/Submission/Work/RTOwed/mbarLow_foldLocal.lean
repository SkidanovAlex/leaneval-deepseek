import Mathlib
import Submission.Work.RTOwed.mbarLow_foldLocal_helpers
import Submission.Work.RTOwed.mbarLow_foldLocal_aux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

open Set Topology Function Matrix
open scoped Matrix RealInnerProductSpace

noncomputable section

/-! # The cusp chart `mbarLow` is locally Möbius on every fold chart

This file proves `Work.RTOwed.mbarLow_foldLocal`, the field `foldLocal` of `Work.RTOwed.CuspRigid`
for the concrete chart `Work.RTOwed.mbarLow`: for a point `q` of the cusp chimney strictly below the
ceiling whose chart value lies in the source of the fold chart `i`, there are an open neighbourhood
`V` of `q` and a Lorentz matrix `B` with

  `foldChart i (mbarLow v q') = mobius B q'`   for all `q' ∈ V` with `mbarLow v q' ∈ (foldChart i).source`.

The analytic ingredients are the cell identity `mbarLow_eq_cellX` (the chart of any cell whose box
contains the reduced coordinate), the whole-hyperplane wall identity `chartKlein_wall_refl_zero'`
(the far-cell chart is the group translate of the reflected near-cell chart), the Möbius identity
`foldTheta_chartKlein_eq_mobius` and the reflection bookkeeping `uhsXj_reflWall4_sub`, all in
`Submission.Work.RTOwed.mbarLow_foldLocal_helpers`.

The assembly is carried out in the module `Submission.Work.RTOwed.mbarLow_foldLocal_aux` (the same
statement under the name `mbarLow_foldLocal_aux`), whose proof works by shrinking to a neighbourhood
on which the base cube chart stays inside the Voronoi piece `r₀` attached to `q`, and then splitting
`q'` according to which walls of the base cell it has crossed: without crossings the chart is the
base-cell chart, and for each crossed wall the one-wall unfolding plus the reflection identity
`mobius_reflWall_high` propagate the value. -/

theorem mbarLow_foldLocal (v : Fin 5) (i : Fin 98) {q : Work.RTOwed.CuspE4}
    (h1 : 11 / 10 < q 3) (h2 : q 3 < Work.Cusp.beta (Work.Cusp.xOf q))
    (hsrc : Work.RTOwed.mbarLow v q ∈ (Work.FoldInst.foldChart i).source) :
    ∃ (V : Set Work.RTOwed.CuspE4) (B : Matrix (Fin 5) (Fin 5) ℝ), IsOpen V ∧ q ∈ V ∧
      Work.HypModel.IsLorentzMat B ∧
      ∀ q' ∈ V, Work.RTOwed.mbarLow v q' ∈ (Work.FoldInst.foldChart i).source →
        Work.FoldInst.foldChart i (Work.RTOwed.mbarLow v q') = Work.HypModel.mobius B q' :=
  Work.RTOwed.mbarLow_foldLocal_aux v i h1 h2 hsrc

end

end Work.RTOwed
