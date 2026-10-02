/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.Main` — the assembled `Work.PARIMPL.ParImplInputs`, `impl` and `noPath`

The endgame of the area: from the sibling hypothesis list `Work.PARIMPL2.SiblingInputs` and the
Leau–Fatou flower of the root arc, the delivered holder structure

  `Work.PARIMPL.ParImplInputs`

is produced, and with it the two results that the delivered area was blocked on:

* `Work.PARIMPL2.impl` — `Work.PARIMPL.ImplSide c₀ z₁ P.Nm` (open, accumulating at `c₀`,
  period-5 point gone);
* `Work.PARIMPL2.noPath` — the `hLB` of the endgame in its path form,
  `∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ Mandelbar) → c₀ ∉ closure (range γ ∩ P.Nm)`.

Every field of `ParImplInputs` is now *derived* from an export of another area, and the
hypothesis list is exactly `Work.PARIMPL2.SiblingInputs` (see `NOTES.md` §2):

| field | source |
|---|---|
| `P : ParNormal d` | *parameter* (witness of the proved `Work.PARIMPL.exists_parNormal`) |
| `Pa`, `φa`, `Ψ` | the flower `Work.FatouCoordFix.ParabolicFlowerFix` (FatouCoordFix, delivered) |
| `M : MatchData` | `Work.PARIMPL2.exists_matchData` ← `SiblingInputs.M` (FlowerGlue + Implosion) |
| `T : TransitData` | `Work.PARIMPL2.exists_transitData` ← `SiblingInputs.T`; its `cont` is *proved* |
| `L : LeakData` | `Work.PARIMPL2.exists_leakData` ← `SiblingInputs.L` (ELAssembly + GATE2) |
| `c_mem_closure` | **proved**, `Work.PARIMPL.Nm_mem_closure` (FBif) |
| `fix : FlowerFix` | **proved**, `Work.FlowerGlue.flowerFixOfFix` (FatouCoordFix) |
| `zdecay : ZDecay` | `SiblingInputs.zdecay` (FlowerGlue) |
| `greenOpen` | **proved**, `Work.NAKANE.greenEscapeOpen` (NAKANE) |
| `isOpen_Pa`, `diff_φa`, `entry_mem` | the flower's own fields / `Work.PARIMPL.nEnter_spec` |
| `critHeight_zero` | `SiblingInputs.critHeight_zero` (FQC/FinalFix root export) |
-/
import Submission.Work.PARIMPL2.Data
import Submission.Work.FlowerGlue.ParImplGlue

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

namespace Work.PARIMPL2

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.PARIMPL (ParNormal MatchData TransitData LeakData entryPt Ft gtc)

variable {c₀ : ℂ}

/-- **The assembled `Work.PARIMPL.ParImplInputs`**, from the sibling exports.

`d : Work.EL.RootParabolic c₀` and the flower are the root/seed and FatouCoordFix data;
`nIn := Work.PARIMPL.nEnter d fl` is the entry time fixed by the flower (`Work.PARIMPL.nEnter_spec`
gives `entry_mem` for free). -/
def parImplInputs (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Ft c₀) (gtc c₀) d.z₁)
    (h : SiblingInputs d P fl.Pa fl.φa fl.Ψ (Work.PARIMPL.nEnter d fl)) :
    Work.PARIMPL.ParImplInputs where
  c₀ := c₀
  d := d
  P := P
  Pa := fl.Pa
  φa := fl.φa
  Ψ := fl.Ψ
  M := matchData h.M
  T := transitData (matchData h.M) h.T
  L := leakData fl.Ψ_diff.continuous (matchData h.M) (transitData (matchData h.M) h.T) h.L
  c_mem_closure := Work.PARIMPL.Nm_mem_closure d P
  fix := Work.FlowerGlue.flowerFixOfFix d fl
  zdecay := h.zdecay
  greenOpen := Work.NAKANE.greenEscapeOpen
  isOpen_Pa := fl.isOpen_Pa
  diff_φa := fl.φa_fatou.1.2.1
  entry_mem := Work.PARIMPL.nEnter_spec d fl
  critHeight_zero := h.critHeight_zero

/-- The assembled holder structure, in `Nonempty` form. -/
theorem parImplInputs_nonempty (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Ft c₀) (gtc c₀) d.z₁)
    (h : SiblingInputs d P fl.Pa fl.φa fl.Ψ (Work.PARIMPL.nEnter d fl)) :
    Nonempty Work.PARIMPL.ParImplInputs :=
  ⟨parImplInputs d P fl h⟩

/-- **`impl`, chain A**: the implosion side of the *delivered* structure, unconditional modulo the
sibling exports.  The delivered theorem itself is
`Work.PARIMPL.ParImplInputs.impl (parImplInputs d P fl h)`. -/
theorem implPARIMPL (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Ft c₀) (gtc c₀) d.z₁)
    (h : SiblingInputs d P fl.Pa fl.φa fl.Ψ (Work.PARIMPL.nEnter d fl)) :
    Work.PARIMPL.ImplSide c₀ d.z₁ P.Nm :=
  (parImplInputs d P fl h).impl

/-- **`noPath`, chain A**: the `hLB` of the endgame (path form) for the *delivered* structures,
unconditional modulo the sibling exports.  This is the statement
`Work.TopJordan.mandelbar_not_isPathConnected_of_twoSidedPinch` consumes; the delivered form is
`Work.PARIMPL.ParImplInputs.noPath (parImplInputs d P fl h)`.

(The name `Work.PARIMPL2.noPath` *without* the suffix is the corrected-chain theorem
`Submission/Work/PARIMPL2/PathFix.lean`.) -/
theorem noPathPARIMPL (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Ft c₀) (gtc c₀) d.z₁)
    (h : SiblingInputs d P fl.Pa fl.φa fl.Ψ (Work.PARIMPL.nEnter d fl)) :
    ∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ Mandelbar) →
      c₀ ∉ closure (Set.range γ ∩ P.Nm) :=
  (parImplInputs d P fl h).noPath

end Work.PARIMPL2

end
