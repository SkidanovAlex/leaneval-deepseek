import Mathlib
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL.ParSplit.PackSplit
import Submission.Work.PARIMPL.ParSplit.parNormal_of_splitData

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.PARIMPL

/-- **Hubbard–Schleicher, Prop. 4.1, uniform in the parameter.**  At a root-parabolic parameter
`c₀` of the period-`5` component of the tricorn the second return map
`F c = (T_c)^[10]` admits the parameter normal form of `Work.PARIMPL.ParNormal` on a ball around
`c₀`.

The proof is the composition of the two halves of the parabolic splitting with the assembly:

* `ParSplit.splitPair_exists` — the two fixed points of `F c` into which `z₁` splits are the two
  roots of `(z - m c)² = G c` for continuous `m`, `G` (the midpoint and the squared
  half-difference, symmetric in the two roots, hence free of monodromy), proved with the argument
  principle for `Hp c = F c - X`;
* `ParSplit.wall_factorization` — the real-analyticity of the parameter dependence: `G` factors as
  `A · h` with `A : ℂ → ℝ` and `h` nowhere zero, because the collision locus `Z = {G = 0}` is a
  real curve through `c₀` and the relevant "wall" is `A = (1 - ρ₊)(1 - ρ₋)`;
* `ParSplit.nonempty_splitData` — the continuous square root `Δ := √A·√h` of `G` and the glue that
  turns `(m, Δ)` into `Work.PARIMPL.ParSplit.SplitData`;
* `ParSplit.parNormal_of_splitData` — the chart `ζ ↦ m c + s c·ζ`, the germ `h c`, the phase
  choice of `a c` and the verification of the `25` fields of `ParNormal` from `SplitData`.

See `Submission/Work/PARIMPL/ParSplit/NOTES.md` for the full account and the numerics. -/
theorem exists_parNormal {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) :
    Nonempty (Work.PARIMPL.ParNormal d) :=
  Work.PARIMPL.ParSplit.parNormal_of_splitData d
    (Work.PARIMPL.ParSplit.nonempty_splitData d).some

end Work.PARIMPL
