/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.Lavaurs.Inputs` — the new (single-export) hypothesis list of the endgame

`Submission/Work/NOTES_LEAD_mandelbar_implosion.md` §2.4: the three sibling bundles of chain A
(`MatchExport`, `TransitExport`, `LeakExport.escape`) are **replaced** by

* `UT : Work.PARIMPL2.LavaursPhase d P fl.Pa fl.φa fl.Ψ nIn` — the single analytic export (the
  uniform lock-step transit with the exact real phase `transPh`);
* `leak : ∃ x : ℝ, fl.Ψ x ∉ Work.EL.K c₀` — **ELAssembly**'s equator leak (verbatim);
* `critHeight_zero` — **FinalFix**'s `RootArcHeightZero` (verbatim);

and `nIn` is now **free** (`Work.PARIMPL.nEnter d fl ≤ nIn`), which is what removes F5(a) of the
design note.  `zdecay` is dropped: `noPath` does not use it.

The endgame `noPath` is then `Work.PARIMPL2.Lavaurs.noPath_of_lavaurs`, i.e. here
`Work.PARIMPL2.Lavaurs.noPath_of_inputs`.
-/
import Submission.Work.PARIMPL2.Lavaurs.noPath_of_lavaurs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.Lavaurs

open LeanEval.ComplexAnalysis (Mandelbar)
open Work.PARIMPL (ParNormal entryPt Ft gtc)

variable {c₀ : ℂ}

/-- **The sibling hypothesis list of the redesigned endgame** (design note §2.4). -/
structure LavaursInputs (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Ft c₀) (gtc c₀) d.z₁) (nIn : ℕ) where
  /-- `nIn` is any time at or beyond the first entry of the critical orbit into the petal. -/
  hnIn : Work.PARIMPL.nEnter d fl.toParabolicFlower ≤ nIn
  /-- **the single implosion export** (implosion side). -/
  UT : LavaursPhase d P fl.Pa fl.φa fl.Ψ nIn
  /-- **ELAssembly**: the equator leak. -/
  leak : ∃ x : ℝ, fl.Ψ ((x : ℝ) : ℂ) ∉ Work.EL.K c₀
  /-- **FinalFix**: the critical Écalle height vanishes. -/
  critHeight_zero :
    (fl.φa (entryPt P (Work.PARIMPL.nEnter d fl.toParabolicFlower) c₀)).im = 0

/-- **`noPath` from the new hypothesis list**: unconditional modulo `LavaursInputs`. -/
theorem noPath_of_inputs (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Ft c₀) (gtc c₀) d.z₁) (nIn : ℕ)
    (h : LavaursInputs d P fl nIn) :
    ∀ γ : C(Set.Icc (0:ℝ) 1, ℂ), (∀ t, γ t ∈ Mandelbar) →
      c₀ ∉ closure (Set.range γ ∩ P.Nm) :=
  Work.PARIMPL2.Lavaurs.noPath_of_lavaurs d P fl nIn h.hnIn h.UT h.leak h.critHeight_zero

end Work.PARIMPL2.Lavaurs

end
