/-
# EL nest, part 6: the uniform pull-back chain of the nest at `z₁`

`Exists.lean` reduces the existence of the nest sequence `Qp` to one uniform step: a co-landing
pair with the nest's level-`n` angles pulls back to a co-landing pair with the level-`n+1` angles.
This file *defines* that step, following the certified chain `Cert.uuChain` (the PB1 chain from
the level-`1` `u`-pair up to the `u`-pair) as a purely recursive construction on the angle pair:

* the step `j` of the chain feeds to `pb1Top` the **near arc** of the current pair for
  `j ≡ 3, 4 (mod 5)` and its **far arc** otherwise, and takes the `T`-preimage arc with
  `k = 0` for `j ≡ 2, 4 (mod 5)` and `k = 1` otherwise;
* the pair `p_j` at step `j` is the pair of the angles of that preimage arc, so that
  `p_10` is the input pair and `p_0` the next level (`nestPair p t` is `p_{10-t}`).

The construction reproduces `Cert.uuChain` exactly: starting from the level-`0` pair in the
orientation `(β₀, β₀') = (bAng 0, bAng' 0)` the ten steps give `Cert.uuChain 0, …, Cert.uuChain 10` (checked over ℚ;
the pattern is periodic of period `5`, so the same ten steps apply at every level).  The two
companion lemmas are `nestChain_lands` (the pull-back exists, by ten `pb1Top` applications, given
the `c`-side conditions of the certificate P6/C9) and `nestPair_nest` (`nestPair (bAng' n, bAng n) 10
= (bAng (n+1), bAng' (n+1))`, the self-similarity of the angle formulas).
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

/-- The index of the `T`-preimage arc used at step `j` of the nest chain (certificate `C6`):
`k = 0` for `j ≡ 2, 4 (mod 5)` and `k = 1` otherwise. -/
def nestK (j : ℕ) : Fin 2 := if j % 5 = 2 ∨ j % 5 = 4 then 0 else 1

/-- The arc of the current pair `p` fed to `pb1Top` at step `j` of the nest chain: the near arc
`(p.2, p.2 + arcLen p.2 p.1)` for `j ≡ 3, 4 (mod 5)`, the far arc `(p.1, p.1 + arcLen p.1 p.2)`
otherwise (both unwrapped). -/
def nestArc (j : ℕ) (p : ℝ × ℝ) : ℝ × ℝ :=
  if j % 5 = 3 ∨ j % 5 = 4 then (p.2, p.2 + Work.EL.arcLen p.2 p.1)
  else (p.1, p.1 + Work.EL.arcLen p.1 p.2)

/-- One step of the nest chain: the pair of the angles of the `T`-preimage arc `nestArc j p`. -/
def nestStep (j : ℕ) (p : ℝ × ℝ) : ℝ × ℝ :=
  let I := nestArc j p
  (Int.fract (-(I.2) / 2 + (nestK j : ℝ) / 2), Int.fract (-(I.1) / 2 + (nestK j : ℝ) / 2))

/-- The pair at step `10 - t` of the nest chain starting from the pair `p` (which is the pair at
step `10`).  Thus `nestPair p 0 = p` and `nestPair p 10` is the pair of the next level. -/
def nestPair (p : ℝ × ℝ) : ℕ → ℝ × ℝ
  | 0 => p
  | t + 1 => nestStep (9 - t) (nestPair p t)

theorem nestPair_zero (p : ℝ × ℝ) : nestPair p 0 = p := rfl

end Work.ELNest
