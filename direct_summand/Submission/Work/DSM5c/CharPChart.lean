import Submission.Work.DSM5c.CharP
import Submission.Work.DSM5c.Charts

/-!
# DSM5c — the characteristic-`p` input `M5b` at the tilted chart datum

The M5c data are `(Q : PerfectoidData p W, t : ι → W, tr : ι → ℕ → W, j₀, e, h : t j₀ = ϖ 0 ^ e)`.
`Work.DSM5c.chartTiltGen` is the tilted chart generator family: `((ϖ♭) ^ e)` at `j₀` and the tilt of
the given tower everywhere else.  The `j₀`-normalisation makes the hypothesis of `area_M5b` hold *by
construction*, so the characteristic-`p` input applies with `T := ϖ♭` — no hypothesis on the given
root tower is needed (`NOTES.md` §10, correction 1).

* `Work.DSM5c.M5bInput` (`CharP.lean`) is the conclusion of `DSMap.Mix2.area_M5b` at fixed data;
* `Work.DSM5c.m5bInput_chartTiltGen` below instantiates it at the tilted charts.

The complex appearing in `m5bInput_chartTiltGen` is exactly the Čech complex of the perfected tilted
charts used by the chart layer (`Work.DSM5c.tiltChart`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.DSM5c

universe a

open DSMap DSMap.Mix DSMap.Mix2

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
  {ι : Type a} [Finite ι] [DecidableEq ι]

/-- **`M5b` at the tilted chart datum of M5c.**  Taking `M5bInterface` (the node `area_M5b` in
interface form, `CharP.lean`) as a hypothesis, the characteristic-`p` blowup almost-acyclicity holds
for the perfected tilted charts `chartTiltGen` of the M5c data, with almost-vector `(ϖ♭) ^ (1/p^k)`
(the root tower of `T := tiltVarpi Q`).

The hypothesis of `area_M5b` is `chartTiltGen … j₀ = (tiltVarpi Q) ^ e`, which holds by definition of
`chartTiltGen` (it is `Work.DSM5c.chartTiltGen_j₀`). -/
theorem m5bInput_chartTiltGen (hM5b : M5bInterface.{a}) (Q : PerfectoidData p W) (t : ι → W)
    (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k)
    (j₀ : ι) (e : ℕ) :
    M5bInput p (PreTilt W p) (chartTiltGen Q t tr htr0 htr j₀ e) (tiltVarpi Q) :=
  m5bInput_of_interface hM5b _ _ j₀ e (chartTiltGen_j₀ Q t tr htr0 htr j₀ e)

end Work.DSM5c
