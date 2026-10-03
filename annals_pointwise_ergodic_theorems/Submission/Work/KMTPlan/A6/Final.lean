/-
# The final wiring of Area A6

This module assembles the contract's Area A6 from its two cases and the named inputs of the
high–high sub-contract:

* `Work.KMTPlan.A6.areaA6_of_cases` (`A6/Assembly.lean`) — the (proved) two-case assembly;
* `Work.KMTPlan.A6.highHighCase` (`A6/highHighCase.lean`) — the high–high case, from the inputs
  `Sub.VanishingF/G`, `Sub.BesselF/G`, `Sub.NonAliasingSize`, `Sub.LogGain`, `Sub.GoodScaleArith`
  of `A6/Model.lean`, all of which are supplied by the wrappers of `A6/Props.lean` (proved in
  `A6/projVanishingF.lean`, `A6/projVanishingG.lean`, `A6/besselF.lean`, `A6/besselG.lean`,
  `A6/nonAliasing_of_size.lean`, `A6/logTerm_le_gain.lean`, `A6/goodScaleArith.lean`);
* `Work.KMTPlan.A6.lowCase` (`A6/lowCase.lean`) — the remaining case `CaseRest`, from
  `A6/lowSmallScaled.lean` (§7) and `A6/lowLargeScaled.lean` (§8).

`areaA6_final_of_besselG` is stated with the `Sub.BesselG` input as an explicit hypothesis, so
that it can be checked before `A6/besselG.lean` (a large module, still being completed) is
available; `areaA6_final` is the unconditional form to be used once it is. -/
import Mathlib
import Submission.Work.KMTPlan.A6.Assembly
import Submission.Work.KMTPlan.A6.Props
import Submission.Work.KMTPlan.A6.highHighCase
import Submission.Work.KMTPlan.A6.lowCase

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

/-- **Area A6, with the `Sub.BesselG` input as an explicit hypothesis.** -/
theorem areaA6_final_of_besselG
    (hbesG : ∀ (ρ : ℝ) (P : ℤ[X]), 0 < ρ → ρ ≤ 1 → Work.KMTPlan.Sub.BesselG ρ P) :
    Work.KMTContract.AreaA6 :=
  Work.KMTPlan.A6.areaA6_of_cases
    (fun P hd hA1 hI C₀ r hC₀ hr =>
      Work.KMTPlan.A6.highHighCase P hd r hr hA1 hI C₀ hC₀
        Sub_VanishingF Sub_VanishingG
        (fun ρ hρ hρ1 => Sub_BesselF ρ hρ hρ1)
        (fun ρ hρ hρ1 => hbesG ρ P hρ hρ1)
        (fun ρ hρ hρ1 => Sub_NonAliasingSize ρ hρ hρ1)
        (fun ρ hρ hρ1 c hc R hR => Sub_LogGain ρ hρ hρ1 c hc R hR)
        (fun ρ hρ hρ1 R hR => Sub_GoodScaleArith C₀ hC₀ ρ hρ hρ1 R hR))
    (fun P hd hA1 hI C₀ r hC₀ hr =>
      Work.KMTPlan.A6.lowCase P hd r hr hA1 hI C₀ hC₀)

/-- **Area A6**, from the `Sub.BesselG` wrapper of `A6/besselG.lean`. -/
theorem areaA6_final : Work.KMTContract.AreaA6 :=
  areaA6_final_of_besselG (fun ρ P hρ hρ1 => Sub_BesselG ρ hρ hρ1 P)

end Work.KMTPlan.A6
