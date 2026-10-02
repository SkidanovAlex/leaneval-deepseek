/-
# EL nest, part 8 (N3): the uniform pull-back chains of the three arms at `b₂`

The three certified chains `Cert.armChainA/B/C` (six `T`-preimage steps each, from `P₀`, `P₂`, `P₄`
down to the level-`1` arm pairs) are frozen here into recursive constructions on the angle pair,
exactly as `Chain.lean` does for the nest at `z₁`.  Reading the certified arcs
`Cert.armChainXArc j` against the pairs `Cert.armChainX (j+1)` (over ℚ) gives, for each step
`j = 5, …, 0`, whether the arc fed to `pb1Top` is the near arc `(p.2, p.2 + arcLen p.2 p.1)` or the
far arc `(p.1, p.1 + arcLen p.1 p.2)` of the current pair `p`, and the index `k ∈ {0,1}` of the
`T`-preimage arc; with those choices the ten… six steps reproduce `Cert.armChainX` exactly:

* `A`: near at `j = 5, 3`, `k = (1,1,0,1,0,1)` for `j = 0…5`;
* `B`: near at `j = 3, 1`, `k = (0,1,0,1,1,1)`;
* `C`: near at `j = 1`, `k = (0,1,1,1,0,1)`.

`armPairOf near k p` is the pair at step `6 - t` of such a chain (`armPairOf _ _ p 0 = p` is the
top of the chain, `armPairOf _ _ p 6` the next level).
-/
import Mathlib
import Submission.Work.ELNest.Setup
import Submission.Work.ELPull.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELNest

open Work.EL

/-- The near/far choice at step `j` of an arm chain. -/
def armArcOf (near : ℕ → Bool) (j : ℕ) (p : ℝ × ℝ) : ℝ × ℝ :=
  if near j then (p.2, p.2 + Work.EL.arcLen p.2 p.1)
  else (p.1, p.1 + Work.EL.arcLen p.1 p.2)

/-- One step of an arm chain: the pair of the `T`-preimage arc. -/
def armStepOf (near : ℕ → Bool) (k : ℕ → Fin 2) (j : ℕ) (p : ℝ × ℝ) : ℝ × ℝ :=
  let I := armArcOf near j p
  (Int.fract (-(I.2) / 2 + (k j : ℝ) / 2), Int.fract (-(I.1) / 2 + (k j : ℝ) / 2))

/-- The pair at step `6 - t` of an arm chain starting from the pair `p` (the top of the chain). -/
def armPairOf (near : ℕ → Bool) (k : ℕ → Fin 2) (p : ℝ × ℝ) : ℕ → ℝ × ℝ
  | 0 => p
  | t + 1 => armStepOf near k (5 - t) (armPairOf near k p t)

--the three patterns of the certified chains

/-- the near/far pattern of the chain `armChainA`. -/
def nearA : ℕ → Bool := fun j => j = 5 ∨ j = 3

/-- the `k` pattern of the chain `armChainA`. -/
def kA : ℕ → Fin 2 := fun j => if j = 2 ∨ j = 4 then 0 else 1

/-- the near/far pattern of the chain `armChainB`. -/
def nearB : ℕ → Bool := fun j => j = 3 ∨ j = 1

/-- the `k` pattern of the chain `armChainB`. -/
def kB : ℕ → Fin 2 := fun j => if j = 0 ∨ j = 2 then 0 else 1

/-- the near/far pattern of the chain `armChainC`. -/
def nearC : ℕ → Bool := fun j => j = 1

/-- the `k` pattern of the chain `armChainC`. -/
def kC : ℕ → Fin 2 := fun j => if j = 0 ∨ j = 4 then 0 else 1

end Work.ELNest
