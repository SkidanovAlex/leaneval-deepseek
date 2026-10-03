import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.BasinSC.defs
import Submission.Work.BasinSC.cover_basic
import Submission.Work.BasinSC.step
import Submission.Work.BasinSC.tower
import Submission.Work.BasinSC.assembly
import Submission.Work.BasinSC.StepOneCrit.simplyConnected_of_proper_holomorphic_one_crit

/-! Guidance from the project lead (the requester):

AREA BASIN-SC (Lemma 5.2): prove BasinSCStatement. Contracts:
Submission/Work/Interfaces/HornParts.lean (namespace MandelDim). Paper:
REFS/shishikura_math9201282/hdim5.tex (Lemma 5.2, Prop 5.3).

## BasinSC = Lemma 5.2 (B simply connected)

The proof is assembled in `Submission/Work/BasinSC/assembly.lean`:

* `tower f₀ B Ωp n = {z | f₀^[n] z ∈ Ωp} ∩ B` (the increasing exhaustion of `B` by the preimages of
  the petal), open at each level (`Tower/tower_isOpen`), with every level's components simply
  connected by induction (`components_simplyConnected`), using
  * the no-critical-point Riemann–Hurwitz-lite step (`step.lean`),
  * the one-critical-point step (`StepOneCrit/simplyConnected_of_proper_holomorphic_one_crit`,
    which uses the classification of connected covers of the punctured disc,
    `CoverDisc/exists_homeomorph_pow_of_isCoveringMap`),
  * the structural facts of one step of the tower (`Tower/tower_step`);
* consequently *every loop of `B` is null-homotopic* (`path_homotopic_refl`), since its image is
  compact and hence lies in one level, inside one simply connected component; in particular
  `Hom(π₁ B, ℝ) = 0` (`subsingleton_hom`);
* `SimplyConnectedSpace B` follows from Mathlib's
  `simply_connected_iff_loops_nullhomotopic`. -/

namespace Work.BasinSC

open MandelDim

theorem basin_sc : BasinSCStatement :=
  basin_sc_of_steps (honeCrit := by
    intro V V' hVo hVne hVsc hVproper hV'o hV'c p hp hmaps hsurj hprop c₀ hc₀ hdc huniq
    exact Work.BasinSC.StepOneCrit.simplyConnected_of_proper_holomorphic_one_crit hVo hVne hVsc
      hVproper hV'o hV'c hp hmaps hsurj hprop hc₀ hdc huniq)

end Work.BasinSC
