/-
# `ELAssembly` — discharging the ELPull-side inputs of the chains from the F-side data

The co-landing of the two nests is obtained by transporting ELPull's two certified chains
(`Work.ELAssembly.NestPairs.ofELPull`).  The inputs of the transport that are *not* certificate
side conditions are themselves consequences of the root-parabolic bundle `d` and of the flower:

| input of `coLand_Q` / `coLand_Z` | here |
|---|---|
| `hNcan : Work.ELPull.DynB c` | `hNcan (d)` — the adapter `Work.PortraitCount.elDynB d` of the area `SeedDyn` |
| `hφcan : IsDynBottcher c (dynPhiOf c)` | `hφcanOf d`, from `d.bottcher` (`DynBottcherExists c` is immediate) |
| `hψ : ∀ z ∉ K c, d.φ z = dynPhiOf c z` | `hψOf d`, from `isDynBottcher_unique` (both are Böttcher coordinates) |
| `htop : Work.ELPull.PB1Top hNcan` | `htopOf`, from `Work.ELPull.pb1Top_of_jordanForm` (ELTop's T6) |
| `hcount : PortraitCount` | `portraitCount_of_crit d fl`, from `SeedDyn`'s `portraitCount` and `d.crit` |

The certificate side conditions (`hcv`, `hcvA/B/C`, the level-`0` bases `hbase`, `hbaseA/B/C`) are
NOT here: they are the rational/side data of the certified chains (C5–C10), recorded in
`NOTES.md` §6 item 8.
-/
import Mathlib
import Submission.Work.ELAssembly.Defs
import Submission.Work.SeedDyn.Portrait
import Submission.Work.ParamRays.isDynBottcher_unique
import Submission.Work.ParamRays.Interface
import Submission.Work.ELPull.pb1Top
import Submission.Work.TopJordan.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ}

/-- The canonical Böttcher coordinate is a Böttcher coordinate, from the root-parabolic bundle
(`d.bottcher` gives `DynBottcherExists c`). -/
theorem hφcanOf (d : Work.EL.RootParabolic c) :
    Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c) :=
  Work.ParamRays.isDynBottcher_dynPhiOf ⟨d.φ, d.bottcher⟩

/-- The `ELPull`-side dynamical Böttcher data at the canonical coordinate, from the root-parabolic
bundle (the `SeedDyn` adapter; its ray-landing relation is the `Work.EL` one,
`Work.PortraitCount.landsN_elDynB`). -/
noncomputable def hNcanOf (d : Work.EL.RootParabolic c) : Work.ELPull.DynB c :=
  Work.PortraitCount.elDynB d

/-- The two Böttcher coordinates agree off the filled Julia set (`z ∉ K c` is `Escaping c z`). -/
theorem hψOf (d : Work.EL.RootParabolic c) :
    ∀ z : ℂ, z ∉ Work.EL.K c → d.φ z = Work.ParamRays.dynPhiOf c z := by
  intro z hz
  refine Work.ParamRays.isDynBottcher_unique d.bottcher (hφcanOf d) ?_
  rw [Work.ParamRays.escaping_iff_not_bounded]
  simpa [Work.EL.K, Work.ParamRays.filledJulia] using hz

/-- The topological input of the one-step pull-back, from the Jordan curve theorem (ELTop's T6). -/
theorem htopOf {c : ℂ} (hN : Work.ELPull.DynB c) :
    Work.ELPull.PB1Top hN :=
  Work.ELPull.pb1Top_of_jordanForm hN Work.TopJordan.jordanForm

/-- **The orbit-portrait count at `c₀` is not an input**: it follows from the flower and the
critical orbit (which enters the attracting petal, `d.crit` + `enters_Pa`).  This is
`Work.PortraitCount.portraitCount` in the form of the assembly. -/
theorem portraitCount_of_crit (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁) :
    Work.ELPull.PortraitCount (hNcanOf d) :=
  Work.PortraitCount.portraitCount d fl (fl.enters_Pa c d.crit.1 d.crit.2)

end Work.ELAssembly
