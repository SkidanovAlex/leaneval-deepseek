/-
# ELRig — the strand field of the flower (the one missing field)

`Work.FatouCoord.ParabolicFlower` constrains the repelling coordinate `Ψ` only by its *local germ*
behaviour (`Ψ_diff`, `Ψ_shift`, `Ψ_anti`, `Ψ_small`, `Ψ_inj`, `Ψ_ends`, `cover`); the ray
parametrisation `rayPt θ t` of the dynamical plane rides on the *Böttcher level at infinity*
(`Work.Top.NakaneData.Phi_rayPt`).  Nothing in the flower ties the two together.

`Work.ELRig.FlowerWithStrand d fl` is precisely that missing tie, one field: **the two root rays
meet each repelling half plane `{Re < -R}` in a single arc, transversal to the level** (the deeper
the `Ψ`-preimage, the smaller its level).  Equivalently — Hubbard–Schleicher, `arXiv:1209.1753`,
proof of Theorem 6.1 — the two rays project to simple closed curves in the Ecalle cylinder.  It is
*not* derivable from the flower's fields together with `RootParabolic` and the two landing
hypotheses (`NOTES.md` §6 records the six independent readings and the two failed proof attempts),
so it has to be either proved in an area of its own (the tools are the cylinder machinery of
`Submission/Work/Implosion/` and the ray parametrisation of `Submission/Work/ELTop/`) or admitted
as a field of the flower.

With the field, the contract's theorem is unconditional up to the ELNest/ELPull inputs:

```lean
Work.EL.equatorLeak_of_flowerStrand (hJ) (d) (fl) (nest) (tr) (hf : FlowerWithStrand d fl)
    : ∃ x : ℝ, fl.Ψ (x : ℂ) ∉ Work.EL.K c
```

If the field is added to `Work.FatouCoord.ParabolicFlower` itself, every `fl` of this area carries
it and a `FlowerWithStrand d fl` is the one-liner `⟨fun R => fl.strand R⟩`; no file of this area
needs to change.
-/
import Submission.Work.ELRig.EquatorLeak

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

namespace Work.ELRig

/-- **The strand field of the flower**: the root rays meet the repelling half planes in a single
level-transversal arc (see the file header). -/
structure FlowerWithStrand {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁) :
    Prop where
  /-- the root rays meet the repelling half planes in a single level-transversal arc. -/
  strand : ∀ R : ℝ, RayStrand d fl R

end Work.ELRig

namespace Work.EL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The contract's `equatorLeak` with the strand field**: the only inputs are the root-parabolic
data `d`, the flower with that one extra field, the nest at `z₁` (ELNest) and the tripod data at
`b₂` (ELNest/ELPull). -/
theorem equatorLeak_of_flowerStrand (hJ : Work.Top.JordanForm) {c : ℂ} (d : RootParabolic c)
    (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Z1Nest d.hN d.z₁ fl.Pa)
    (tr : B2Data d.hN d.z₁)
    (hf : Work.ELRig.FlowerWithStrand d fl) :
    ∃ x : ℝ, fl.Ψ (x : ℂ) ∉ K c :=
  equatorLeak_of_strand hJ d fl nest tr hf.strand

end Work.EL
