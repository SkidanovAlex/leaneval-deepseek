/-
# `ELAssembly` — the equator leak at the final parameter

The end of the EL chain: from a `Work.ELNest.NestData c` (the nonempty interface: the two nests,
the side preservation `SP` and the certificate facts) together with the two remaining named
hypotheses of the assembly (`b₂` is not postcritical, and the non-degeneracy of the level-`n`
angles of the nest), plus the Leau–Fatou flower, the equator leak

```lean
∃ x : ℝ, fl.Ψ (x : ℂ) ∉ Work.EL.K c
```

i.e. the field `Work.PARIMPL.LeakData.leak` of the implosion chain and the hypothesis of the
ACCESS case of GATE2.

The proof is a two-line assembly: `Work.EL.equatorLeak_parity` (ELRig) consumes exactly the two
bundles `Work.ELRig.Z1Nest` and `Work.ELRig.B2Data` at the same flower, and those are produced
from the `NestData` by `Work.ELAssembly.toZ1Nest` and `Work.ELAssembly.toB2Data`.
-/
import Mathlib
import Submission.Work.ELAssembly.Z1
import Submission.Work.ELAssembly.B2
import Submission.Work.ELAssembly.Assembly
import Submission.Work.ELAssembly.B2Postcrit
import Submission.Work.ELRig.ParityEnd
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

/-- **The equator leak from a `NestData`.**  Given the two nests at the final parameter (as the
interface `NestData`), the flower `fl` (with the *same* petal `Pa` as the `NestData`'s flower),
the non-degeneracy of the level-`n` angles and the non-postcriticality of `b₂`, the repelling
equator `Ψ (ℝ)` leaves the filled Julia set. -/
theorem equatorLeak_of_nestData {c : ℂ} (S : Work.ELNest.NestData c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) S.d.z₁)
    (hPa : S.fl.Pa = fl.Pa)
    (hnd : ∀ n : ℕ, Work.EL.arcLen (S.Qp n).a (S.Qp n).b ≠ 0)
    (hpost : ∀ n : ℕ, (Tantibar c)^[n] 0 ≠ S.b2) :
    ∃ x : ℝ, fl.Ψ (x : ℂ) ∉ Work.EL.K c :=
  Work.EL.equatorLeak_parity Work.TopJordan.jordanForm S.d fl
    (hPa ▸ toZ1Nest S Work.TopJordan.jordanForm hnd)
    (toB2Data S Work.TopJordan.jordanForm hpost)

/-- The same, with the two named hypotheses of `NestData` discharged by the certificate
identifications `(Qp n).a = βₙ'`, `(Qp n).b = βₙ + 1`. -/
theorem equatorLeak_of_nestData_angles {c : ℂ} (S : Work.ELNest.NestData c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) S.d.z₁)
    (hPa : S.fl.Pa = fl.Pa)
    (hQa : ∀ n : ℕ, (S.Qp n).a = Work.ELNest.bAng' n)
    (hQb : ∀ n : ℕ, (S.Qp n).b = Work.ELNest.bAng n + 1)
    (hpost : ∀ n : ℕ, (Tantibar c)^[n] 0 ≠ S.b2) :
    ∃ x : ℝ, fl.Ψ (x : ℂ) ∉ Work.EL.K c :=
  equatorLeak_of_nestData S fl hPa (fun n => by rw [hQa n, hQb n]; exact arcLen_bAng_ne_zero n)
    hpost


/-- **The equator leak from the assembly inputs.**  From the bundle `AssemblyInputs` at the
final parameter — the two nests, the certificate geometry, the side preservation `SP` and the
named classical hypotheses (`hzero`, `PortraitCount`, `b₂` non-postcritical) — and the
`FlowerGlue` flower `fl₀` (which is the flower of the `NestData` built from the bundle, i.e.
`A.fl = FlowerData.ofFatouCoord fl₀.toParabolicFlower` at the call site), the repelling equator
`Ψ (ℝ)` of `fl₀` leaves the filled Julia set. -/
theorem equatorLeak_of_inputs {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.ELNest.FlowerData c d.z₁} (A : AssemblyInputs c d fl)
    (fl₀ : Work.FatouCoordFix.ParabolicFlowerFix (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (hfl : fl = Work.ELNest.FlowerData.ofFatouCoord fl₀.toParabolicFlower) :
    ∃ x : ℝ, fl₀.Ψ (x : ℂ) ∉ Work.EL.K c := by
  subst hfl
  have hnd : ∀ n : ℕ, Work.EL.arcLen ((NestData.ofInputs A).Qp n).a
      ((NestData.ofInputs A).Qp n).b ≠ 0 := by
    intro n
    rw [show ((NestData.ofInputs A).Qp n).a = Work.ELNest.bAng' n
        from (NestPairs.ofChains (chainInputs_of d A.hzero)).Qpa n,
      show ((NestData.ofInputs A).Qp n).b = Work.ELNest.bAng n + 1
        from (NestPairs.ofChains (chainInputs_of d A.hzero)).Qpb n]
    exact arcLen_bAng_ne_zero n
  have hPa : (NestData.ofInputs A).fl.Pa = fl₀.Pa := rfl
  have h := equatorLeak_of_nestData (NestData.ofInputs A) fl₀.toParabolicFlower hPa hnd
    (b2_not_postcrit_of_inputs A)
  simpa using h

end Work.ELAssembly
