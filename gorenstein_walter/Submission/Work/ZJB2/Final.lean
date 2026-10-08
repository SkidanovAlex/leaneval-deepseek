import Submission.Work.ZJB2.Assembly
import Submission.Work.ZJB2.Step1.Sum
import Submission.Work.ZJB2.Step1.cpInOfSatisfiesProp
import Submission.Work.ZJB2.sylowInInfNormal
import Submission.Work.ZJB2.isSylowInOfLe
import Submission.Work.ZJB2.step2
import Submission.Work.ZJB2.step3
import Submission.Work.ZJB2.ivMethod
import Submission.Work.ZJB2.condExists51
import Submission.Work.ZJB2.frattiniIn
import Submission.Work.ZJB2.normRFactor
import Submission.Work.ZJB2.mRCentralizes
import Submission.Work.ZJB2.case52Proper
import Submission.Work.ZJB2.modPStep
import Submission.Work.ZJB2.pPrimeCentralizes
import Submission.Work.ZJB2.factorPPrime
import Submission.Work.ZJB2.cbarNormalizes
import Submission.Work.ZJB2.condExists52
import Submission.Work.ZJB2.cpOfSylowBot
import Submission.Work.ZJB2.hypAOfCoreBot

/-!
# ZJB2 — the deliverable: `ZJBProp'`

Glauberman 1968, *A characteristic subgroup of a p-stable group*, Theorem B (p. 1125):

> if `G` is `Qd(p)`-free (`p` odd) then `N_G(Z(J(P)))` controls strong fusion in `P`.

`Work.ZJB.ZJBProp'` is the lead's restated contract (product order `N_G(Z(J(P)))·C_G(W)`,
design pass 11 §3.1).  This file assembles it from the leaves:

* `Leaves` collects the twenty design-17 leaves (each proved in `Submission/Work/ZJB2/<leaf>.lean`)
  together with design-11's step-(I) leaves (`Submission/Work/ZJB2/Step1/`, summed up by
  `Work.ZJB2.Step1.step1Prop`) and the two bridges `CpStarInOfCpInProp`,
  `CpInOfSatisfiesProp`;
* `Work.ZJB.theoremB_of_leaves` (`ZJB2/Assembly.lean`, proved) is the strong induction on `|X|`
  over the D-class: hypothesis (a) of Theorem 5.1 in the `O_p(X) = 1` case, Theorem 5.2 in the
  `O_p(X) ≠ 1` case with hypothesis (a) at every subquotient from `ZJAProp` +
  `DihOrCycHeredProp`;
* `Work.ZJB.zjbProp'_of_leaves_pstable` closes it with `ZJAProp` supplied by GLUE
  (`Work.GW2.zjA`) from `PStableProp`.

The main results of this file are `Work.ZJB2.leaves`, `Work.ZJB2.zjbProp'` and
`Work.ZJB2.zjbProp'_of_zjA`.
-/

namespace Work.ZJB2

open Work.GW2

/-- **The full leaf set of ZJB2**, filled in from the individual proved leaves. -/
theorem leaves : Work.ZJB.Leaves where
  step1 := fun G _ _ p _ => Work.ZJB2.Step1.step1Prop (G := G) (p := p)
  l51 := fun G _ _ p _ => Work.ZJB2.Step1.cpStarInOfCpInProp (G := G) (p := p)
  br := fun G _ _ p _ => Work.ZJB2.Step1.cpInOfSatisfiesProp (G := G) (p := p)
  g2 := fun G _ _ p _ => Work.ZJB2.sylowInInfNormal p G
  g3 := fun G _ _ p _ => Work.ZJB2.isSylowInOfLe p G
  step2 := fun G _ _ p _ => Work.ZJB2.step2 p G
  step3 := fun G _ _ p _ => Work.ZJB2.step3 p G
  ivAlg := fun G _ => Work.ZJB.ivMethod G
  ex51 := fun G _ _ p _ => Work.ZJB2.condExists51 p G
  frat := fun G _ _ p _ => Work.ZJB2.frattiniIn p G
  nrf := fun G _ _ p _ => Work.ZJB2.normRFactor p G
  mrc := fun G _ _ p _ => Work.ZJB2.mRCentralizes p G
  lt52 := fun G _ _ p _ => Work.ZJB2.case52Proper p G
  modp := fun G _ _ p _ => Work.ZJB2.modPStep p G
  ppc := fun G _ _ p _ => Work.ZJB2.pPrimeCentralizes p G
  fac := fun G _ _ p _ => Work.ZJB2.factorPPrime p G
  nrm := fun G _ _ p _ => Work.ZJB2.cbarNormalizes p G
  ex52 := fun G _ _ p _ => Work.ZJB2.condExists52 p G
  bot := fun G _ _ p _ => Work.ZJB.cpOfSylowBot p G
  hypA := fun G _ _ p _ => Work.ZJB2.hypAOfCoreBot p G

/-- **The deliverable `ZJBProp'` from `ZJAProp`** (Glauberman's Theorem A) and
`DihOrCycHeredProp` (heredity of the Sylow-2 shape). -/
theorem zjbProp'_of_zjA (hZA : Work.GW2.ZJAProp) (hH : Work.ZJB.DihOrCycHeredProp) :
    Work.ZJB.ZJBProp' :=
  Work.ZJB.zjbProp'_of_leaves leaves hZA hH

/-- **The deliverable `ZJBProp'`**: Glauberman's Theorem B in the lead's restated contract,
from `PStableProp` (area PSTAB) and `DihOrCycHeredProp`; `ZJAProp` is supplied by area GLUE
(`Work.GW2.zjA`). -/
theorem zjbProp' (hPS : Work.GW2.PStableProp) (hH : Work.ZJB.DihOrCycHeredProp) :
    Work.ZJB.ZJBProp' :=
  Work.ZJB.zjbProp'_of_leaves_pstable leaves hPS hH

/-- The per-group form: for every finite group with dihedral or cyclic Sylow 2-subgroups and
every prime `p ≠ 2`, `Z(J(P))` controls strong fusion in `P`. -/
theorem satisfiesCpPaper_of_zjA (hZA : Work.GW2.ZJAProp) (hH : Work.ZJB.DihOrCycHeredProp)
    (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hX : Work.GW2.DihOrCycSylow X) : Work.ZJB.SatisfiesCpPaper p X :=
  Work.ZJB.theoremB_of_leaves leaves hZA hH X p hp hX

/-- The same with `ZJAProp` supplied by area GLUE from `PStableProp`: Glauberman's Theorem B in
the paper's own convention (`ControlsStrongFusionPaper`, product order `c·n`), for every finite
group of the D-class and every prime `p ≠ 2`.  This is the D-class form of
`Work.ZJB.DefsPaper.TheoremBStablePaper`. -/
theorem satisfiesCpPaper_of_pstable (hPS : Work.GW2.PStableProp)
    (hH : Work.ZJB.DihOrCycHeredProp) (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (hX : Work.GW2.DihOrCycSylow X) : Work.ZJB.SatisfiesCpPaper p X :=
  satisfiesCpPaper_of_zjA (Work.GW2.zjA hPS) hH X p hp hX

/-- **The deliverable, spelled out.**  Same statement as `Work.ZJB2.zjbProp'`, written out
without naming `Work.ZJB.ZJBProp'`, so that a caller holding any definitionally equal copy of the
restated contract (e.g. the lead's updated `Work.GW2.ZJBProp` after the body replacement of
`NOTES_LEAD_gw_design11.md` §3.1) can use it directly. -/
theorem zjbProp'_explicit (hPS : Work.GW2.PStableProp) (hH : Work.ZJB.DihOrCycHeredProp) :
    ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime], p ≠ 2 →
      Work.GW2.DihOrCycSylow X →
      ∀ (P : Sylow p X) (W : Set X) (g : X), W.Nonempty → W ⊆ (P : Subgroup X) →
        (∀ w ∈ W, g * w * g⁻¹ ∈ (P : Subgroup X)) →
        ∃ n c : X, n ∈ Subgroup.normalizer (Work.GW2.ZJ (P : Subgroup X) : Set X) ∧
          c ∈ Subgroup.centralizer W ∧ g = n * c :=
  zjbProp' hPS hH

/-- The bundled form of `satisfiesCpPaper_of_pstable`: the D-class version of the paper's
`TheoremBStablePaper`, with `ZJAProp` discharged by `PStableProp`. -/
theorem theoremB_dclass_of_pstable (hPS : Work.GW2.PStableProp)
    (hH : Work.ZJB.DihOrCycHeredProp) :
    ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime], p ≠ 2 →
      Work.GW2.DihOrCycSylow X → Work.ZJB.SatisfiesCpPaper p X :=
  Work.ZJB.theoremB_of_leaves leaves (Work.GW2.zjA hPS) hH

end Work.ZJB2
