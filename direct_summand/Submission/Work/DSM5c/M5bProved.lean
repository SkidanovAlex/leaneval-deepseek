import Submission.Work.DSM5c.CharP
import Submission.Work.DSM5b.Main

/-!
# DSM5c — discharging the characteristic-`p` input with the sibling deliverable

**WARNING (verified).**  `#print axioms DSMap.Mix2.area_M5b_proved` currently reports
`[propext, sorryAx, Classical.choice, Quot.sound]`: `Submission/Work/DSM5b` still carries holes
(`chartCechH0_root_killing.lean`, `honestCechCoordEquiv.lean`, `honestUniformKilling*.lean`, …)
which are transitively in the import closure of `DSMap.Mix2.area_M5b_proved`.  So the discharge
below is **not axiom-clean yet**, and this module must stay *off* the import path of the M5c
assembly: `Submission/Work/DSM5c/Main.lean` does not import it, and the internal lemma
`area_M5c_of_M5bInterface` must take `Work.DSM5c.M5bInterface` as an explicit hypothesis, discharged
here only once the sibling area is clean.

The area `DSM5b` has delivered `DSMap.Mix2.area_M5b_proved`
(`Submission/Work/DSM5b/Main.lean`).  This module uses it to discharge the interface
`Work.DSM5c.M5bInterface` of `Submission/Work/DSM5c/CharP.lean`:

* `Work.DSM5c.m5bInterface_proved : M5bInterface` — no hypothesis;
* `Work.DSM5c.m5bInput_tilt_proved` — the input at the tilted M5c datum, for the canonical root
  tower of `t j₀ = ϖ₀ ^ e` (`tr j₀ k = ϖ k ^ e`, the normalisation of `DEN`/`ROOTS`).

Both are proved *only* through the assembled sibling theorem; no `sorry` of the lead files
(`DSMap.Mix2`) is used. -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.DSM5c

universe a

open CategoryTheory
open DSMap DSMap.Mix DSMap.Mix2

/-- **The characteristic-`p` input `M5b`, proved**: the interface `Work.DSM5c.M5bInterface` is
discharged by the sibling area's deliverable `DSMap.Mix2.area_M5b_proved`. -/
theorem m5bInterface_proved : M5bInterface.{a} := by
  intro p _ R _ _ _ ι _ _ t T j₀ e h
  exact DSMap.Mix2.area_M5b_proved p R t T j₀ e h

section Tilt

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
variable {ι : Type a} [Finite ι] [DecidableEq ι]

/-- **The characteristic-`p` input at the tilted M5c datum, proved** (no hypotheses beyond the M5c
data and the canonical root tower of the generator `t j₀`): the perfected chart complex of the tilt
`W♭` in the tilted generators is almost acyclic along the tower `(ϖ♭) ^ (1/p^k)`. -/
theorem m5bInput_tilt_proved (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (hcanon : ∀ k, tr j₀ k = Q.ϖ k ^ e) :
    M5bInput p (PreTilt W p) (tiltGens t tr htr0 htr) (tiltVarpi Q) :=
  m5bInput_tilt (hM5b := m5bInterface_proved) Q t tr htr0 htr j₀ e hcanon

/-- **The characteristic-`p` input at the tilted M5c datum, with no hypothesis on the tower, proved**
(the unconditional form of `Work.DSM5c.m5bInput_tilt_general`): `area_M5b` is applied with
`T := t♭ j₀`, `e := 1`, which needs no normalisation of the root tower.  The almost-vector is then
the root tower of the *tilted generator* (the tilt of the given tower `tr j₀`), not of `ϖ♭`; see
`Work.DSM5c.m5bInput_tilt_general` and `NOTES.md` §4 for the change-of-almost-vector step that
consumes it together with the frozen statement's vector `QW.ϖ`. -/
theorem m5bInput_tilt_general_proved (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) :
    M5bInput p (PreTilt W p) (tiltGens t tr htr0 htr) (tiltGens t tr htr0 htr j₀) :=
  m5bInput_tilt_general (hM5b := m5bInterface_proved) Q t tr htr0 htr j₀

end Tilt

end Work.DSM5c
