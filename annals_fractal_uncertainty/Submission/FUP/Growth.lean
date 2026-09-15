import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Metric Filter Set
open scoped Real BigOperators Topology

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# The Beurling–Malliavin growth functional

The growth condition of the Beurling–Malliavin theorem (Cohen's `eq:higher_dim_BM_growth_cond`) is

  `G*(r) = sup_{‖x‖ = r} ∫_{1/2}^2 |ω(sx)| ds`,   `∫_0^∞ G*(r)/(1+r²) dr < ∞`.

This module hosts the two objects `Gstar` and `growthFunctional` (moved here, unchanged, from
`Submission.FUP.GrowthSum` and `Submission.FUP.BMReduction` so that they are available to the
*specification* layer `Submission.FUP.Spec`, which must not depend on the paper's definitions),
together with the faithful form of the growth hypothesis.

**Why `HasFiniteGrowth` and not just `growthFunctional ω ≤ Cgr`.**  `growthFunctional` is a
*Bochner* integral of the nonnegative function `r ↦ G*(r)/(1+r²)`.  If that function is **not**
integrable, the Bochner integral takes the junk value `0`, so the hypothesis
`growthFunctional ω ≤ Cgr` is *satisfied* although the growth integral diverges (e.g. for
`ω(x) = -(‖x‖-2)₊`, where `G*(r) ≥ r/2` for `r ≥ 4` but `ω` is 1-Lipschitz and vanishes on `B₂`).
The hypothesis is therefore vacuous in exactly the regime in which the Beurling–Malliavin theorem
needs it.  `HasFiniteGrowth ω Cgr` adds the missing integrability, so it says what the paper says:
the growth integral is finite and at most `Cgr`.
-/

/-- The sup over the sphere of radius `r` of `∫_{1/2}^2 |ω(sx)| ds` — the function whose
half-line integral against `1/(1+r²)` is the Beurling–Malliavin growth functional
(equation (1.6) of the paper). -/
noncomputable def Gstar (w : ℝᵈ → ℝ) (r : ℝ) : ℝ :=
  ⨆ x : {x : ℝᵈ // ‖x‖ = r}, ∫ t in (1 / 2 : ℝ)..2, |w (t • (x : ℝᵈ))|

/-- The Beurling–Malliavin growth functional `∫_0^∞ G*(r)/(1+r²) dr` (equation (1.6) of the
paper). -/
noncomputable def growthFunctional (ω : ℝᵈ → ℝ) : ℝ :=
  ∫ r in Set.Ioi (0 : ℝ), Gstar ω r / (1 + r ^ 2)

/-- **The faithful growth hypothesis**: `r ↦ G*(r)/(1+r²)` is integrable on `(0,∞)` (so that the
Bochner integral in `growthFunctional` is the honest integral) and the growth integral is at most
`Cgr`.  See the module docstring for why the `IntegrableOn` conjunct cannot be dropped. -/
def HasFiniteGrowth (ω : ℝᵈ → ℝ) (Cgr : ℝ) : Prop :=
  IntegrableOn (fun r : ℝ => Gstar ω r / (1 + r ^ 2)) (Set.Ioi (0 : ℝ)) ∧
    growthFunctional ω ≤ Cgr

lemma hasFiniteGrowth_def (ω : ℝᵈ → ℝ) (Cgr : ℝ) :
    HasFiniteGrowth ω Cgr ↔
      IntegrableOn (fun r : ℝ => Gstar ω r / (1 + r ^ 2)) (Set.Ioi (0 : ℝ)) ∧
        growthFunctional ω ≤ Cgr := Iff.rfl

lemma HasFiniteGrowth.integrableOn {ω : ℝᵈ → ℝ} {Cgr : ℝ} (h : HasFiniteGrowth ω Cgr) :
    IntegrableOn (fun r : ℝ => Gstar ω r / (1 + r ^ 2)) (Set.Ioi (0 : ℝ)) := h.1

lemma HasFiniteGrowth.growth_le {ω : ℝᵈ → ℝ} {Cgr : ℝ} (h : HasFiniteGrowth ω Cgr) :
    growthFunctional ω ≤ Cgr := h.2

end Submission.FUP
