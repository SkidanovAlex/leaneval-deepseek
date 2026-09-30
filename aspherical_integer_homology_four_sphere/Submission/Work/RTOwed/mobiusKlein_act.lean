/-
# The Klein action commutes with the sign change of the developing matrix

The Klein model action of a Lorentz matrix `K` is

  `mobiusKlein K y = uhsOfHyp (K *ᵥ hypOfKlein y)`,   `hypOfKlein y = (y,1)/√(1−|y|²)`.

A sign change `g : Fin 4 → ZMod 2` acts on the Klein ball by the diagonal `±1` map
`act g y = rot4 (diag (signVec g)) y`, and the Klein lift is *equivariant* under it
(`Work.FoldInst.hypOfKlein_act`):

  `hypOfKlein (act g y) = diagKR (signVec g) *ᵥ hypOfKlein y`.

Here `diagKR` is the real form of the Klein diagonal `diagK`, i.e. the diagonal Lorentz matrix
`diag(signVec g, 1)` (the timelike coordinate `4` is fixed by a sign change).  Substituting into
`mobiusKlein` and using the associativity of `*ᵥ` with the matrix product
(`Matrix.mulVec_mulVec`) gives the statement of this file:

  `mobiusKlein K (act g w) = mobiusKlein (K * diagKR (signVec g)) w`.

This is the algebraic half of the *flip identity* of the fold charts
(`Work.FoldInst.foldTheta_flip`): the sign change of a chart piece can be absorbed into the
developing matrix `N_F D_r` of the chart, on the right.

No hypothesis on `w` is needed: both sides are the same rescaling of the same ray, so the
statement holds also outside the open unit ball (where `hypOfKlein` is not the Klein lift).
-/
import Mathlib
import Submission.Work.RTOwed.Defs
import Submission.Work.RTOwed.ray_act

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

/-- **The Klein action of `K` after a sign change is the Klein action of `K` times the sign
diagonal.**  For every `K : Matrix (Fin 5) (Fin 5) ℝ`, every sign change `g : Fin 4 → ZMod 2` and
every `w : E4`,

  `mobiusKlein K (act g w) = mobiusKlein (K * diagKR (signVec g)) w`.

The two sides agree because the Klein lift is equivariant under a sign change
(`Work.FoldInst.hypOfKlein_act`) and `*ᵥ` is compatible with the matrix product. -/
theorem mobiusKlein_act {K : Matrix (Fin 5) (Fin 5) ℝ} (g : Fin 4 → ZMod 2)
    (w : Work.FoldInst.E4) :
    Work.HypModel.mobiusKlein K (Work.FoldInst.act g w)
      = Work.HypModel.mobiusKlein (K * Work.FoldInst.diagKR (Work.FoldInst.signVec g)) w := by
  rw [Work.HypModel.mobiusKlein, Work.FoldInst.hypOfKlein_act]
  rw [Matrix.mulVec_mulVec]
  rfl

end Work.RTOwed
