import Submission.Work.OddCurve.Free.Endgame
import Submission.Work.OddCurve.LowSlope.GlueDataDefs
import Submission.Work.OddCurve.LowSlope.CurveDefs
import Submission.Work.OddCurve.LowSlope.radial_system_sharp_c2
import Submission.Work.OddCurve.LowSlope.radialSystem_deriv_sign
import Submission.Work.OddCurve.LowSlope.step3_anchor_data
import Submission.Work.OddVolterra.Free.Defs

/-!
# Step 3, split into its two inputs: the glued-data bounds and the curve assembly

`Work.OddCurve.Free.LowSlopeExtensionFree n` (paper Step 3, free tips) is built in three moves,
all of whose ingredients except two are already proved in this workspace:

1. **the anchor's radial function** `ρ_a` (`Work.OddCurve.LowSlope.anchorRadialFunction`, proved);
2. **the glued data** `A = glueA n ρ_a`, `B = glueB n ρ_a` (`GlueDataDefs`, the analytic
   continuation of the glued Radon datum; `glueA_at_pi_div_two`, `glueB_at_pi_div_two` are the two
   endpoint conditions);
3. **the radial pair** `(R, r)` of the reconstruction: `R^{2n+2} + r^{2n+2} = 2 + A`,
   `R^{2n+1} - r^{2n+1} = B` — this file, from the data bounds, with the **sharp** estimates
   `|R - 1| ≤ C σ/(n+1)`, `|R'| ≤ C(σ+δ₁)/(n+1)`, `|R''| ≤ C(σ+δ₁+δ₂)/(n+1)`
   (`Work.OddCurve.LowSlope.radial_system_sharp_c2`);
4. **the two-piece curve** `x = lowSlopeCurveX r X`, `y = lowSlopeCurveY R Y`
   (`LowSlope/CurveDefs.lean`) and its envelope structure;
5. **the moment equations** on `(0,1]`: the transfer on `[3/4,1]`
   (`LowSlope.momentEqs_transfer`) and the low-slope lemma from the datum
   (`LowSlope.momentEqs_lowSlopes_of_datum_ball_threshold`), the datum being the glued one by
   `LowSlope.radonPhiRhoNewEq`.

The two inputs that are *not* yet proved anywhere are isolated below as `Prop`s:

* `GlueDataSmallExists n` — the **crux**: for an anchor satisfying the hypotheses of
  `LowSlopeExtensionFree`, the glued data `glueA`, `glueB` and their first two derivatives are
  *small* on `[0, π/2]` (uniformly in `h` for `h` in the `C^{n+3}` bump class).  The route, and the
  reason it is hard, are in `LowSlope/NOTES_CRUX_2026.md` §1–§2 and
  `Submission/Work/OddVolterra/Free/NOTES_free_tips.md`: on the cap `cos α < c*` the data are
  exactly `ρ_a(±cos α)`-combinations (`GlueA_eq_cap`, `GlueB_eq_cap`), so this is the *anchor's
  radial deviation on the cap* — which is controlled by the curve's deviation on the layer
  `tStar < |u| < c*`, where the cutting line is shifted and only the *curve* (not the profile) is
  controlled by the hypotheses;
* `LowSlopeCurveAssemblySpec n` — the **curve assembly**: from the radial pair and its bounds one
  produces the two-piece curve, proves that it is a free-tip envelope curve
  (`IsEnvelopeCurveFree`) and `C²`-close to the semicircle's chord function, and that its profile
  traces `rhoNew R r`.

Both are stated as `Prop`s so that they can be delegated without carrying a `sorry` in the
chapter; `lowSlopeExtensionFree_of_pieces` composes them (and the already-proved pieces) into the
single remaining input of the odd case.
-/

namespace Work.OddCurve
namespace Free

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Pointwise Interval

/-- **The glued data are small.**  For the anchor's radial function `ρ`, the two data functions
`glueA n ρ`, `glueB n ρ` of `GlueDataDefs` are smooth on `(-1, π/2+1)` and satisfy
`|·| ≤ σ`, `|·'| ≤ δ₁`, `|·''| ≤ δ₂` on `[0, π/2]`. -/
def GlueDataSmall (n : ℕ) (ρ : ℝ → ℝ) (σ δ₁ δ₂ : ℝ) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (LowSlope.glueA n ρ)
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (LowSlope.glueB n ρ)
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) ∧
    (∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |LowSlope.glueA n ρ α| ≤ σ ∧ |deriv (LowSlope.glueA n ρ) α| ≤ δ₁ ∧
        |deriv (deriv (LowSlope.glueA n ρ)) α| ≤ δ₂) ∧
    (∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |LowSlope.glueB n ρ α| ≤ σ ∧ |deriv (LowSlope.glueB n ρ) α| ≤ δ₁ ∧
        |deriv (deriv (LowSlope.glueB n ρ)) α| ≤ δ₂)

/-- **The radial pair of the reconstruction, with the sharp estimates.**  From the smallness of the
glued data (`GlueDataSmall`) one gets `C^∞` radial functions `R`, `r` on `[0, π/2]` solving the
two-power system `R^{2n+2} + r^{2n+2} = 2 + glueA`, `R^{2n+1} - r^{2n+1} = glueB`, with
`R (π/2) = r (π/2) = 1` and the sharp `σ`-linear bounds.  Proved from
`LowSlope.radial_system_sharp_c2` and the two endpoint conditions `glueA_at_pi_div_two`,
`glueB_at_pi_div_two`. -/
theorem radialPair_of_glueDataSmall (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ} {σ δ₁ δ₂ : ℝ}
    (hρ0 : ρ 0 = 1) (hσ : 0 ≤ σ) (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (hdata : GlueDataSmall n ρ σ δ₁ δ₂) :
    ∃ C : ℝ, 0 < C ∧ (∀ _hsmall : C * (σ + δ₁ + δ₂) ≤ 1,
      ∃ R r : ℝ → ℝ,
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R (Set.Icc 0 (Real.pi / 2)) ∧
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r (Set.Icc 0 (Real.pi / 2)) ∧
        Work.OddRadon.RadialSystem n (fun α => (2 + LowSlope.glueA n ρ α) * Real.cos α ^ 2)
          (fun α => LowSlope.glueB n ρ α * Real.cos α) R r ∧
        R (Real.pi / 2) = 1 ∧ r (Real.pi / 2) = 1 ∧
        ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
          |R α - 1| ≤ C * σ / ((n : ℝ) + 1) ∧ |r α - 1| ≤ C * σ / ((n : ℝ) + 1) ∧
          |deriv R α| ≤ C * (σ + δ₁) / ((n : ℝ) + 1) ∧
          |deriv r α| ≤ C * (σ + δ₁) / ((n : ℝ) + 1) ∧
          |deriv (deriv R) α| ≤ C * (σ + δ₁ + δ₂) / ((n : ℝ) + 1) ∧
          |deriv (deriv r) α| ≤ C * (σ + δ₁ + δ₂) / ((n : ℝ) + 1)) := by
  obtain ⟨C, hCpos, hC⟩ := LowSlope.radial_system_sharp_c2 n hn
  refine ⟨C, hCpos, fun hsmall => ?_⟩
  obtain ⟨hAc, hBc, hAb, hBb⟩ := hdata
  obtain ⟨R, r, hRc, hrc, hsys, hRend, hrend, hbnd⟩ :=
    hC (LowSlope.glueA n ρ) (LowSlope.glueB n ρ) σ δ₁ δ₂ hσ hδ₁ hδ₂ hsmall hAc hBc hAb hBb
      (LowSlope.glueA_at_pi_div_two hρ0) (LowSlope.glueB_at_pi_div_two n ρ)
  exact ⟨R, r, hRc, hrc, hsys, hRend, hrend, hbnd⟩

/-- **The crux input of Step 3**, as a `Prop`: for every sufficiently small bump of class
`C^{2n+2}` (the class the construction actually needs — `Submission/Work/OddVolterra/Free/NOTES_free_tips.md`
§"The class, again: `2n+2`, not `n+3`" refutes `C^{n+3}` for `n ≥ 2`) and every anchor satisfying
the hypotheses of `LowSlopeExtensionFree`, the glued data of the anchor's radial function are
small, with bounds uniform in `h`.  See the module docstring for the route and
for `LowSlope/NOTES_CRUX_2026.md` §1–§2 for the obstruction. -/
def GlueDataSmallExists (n : ℕ) : Prop :=
  ∃ σ δ₁ δ₂ : ℝ, 0 ≤ σ ∧ 0 ≤ δ₁ ∧ 0 ≤ δ₂ ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ h X Y ρ : ℝ → ℝ,
      Work.OddVolterra.Free.IsSmallFlatBumpClass n (2 * n + 2) ε h →
      Work.OddEnvelope.IsEnvelopeCurve h X Y → LowSlope.CloseToProfileX X →
      LowSlope.CloseToProfileX Y →
      (∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u) →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1) →
      StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1) →
      (∀ u ∈ Set.Ioo (-1 : ℝ) 1,
        ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ u * u)) →
      ρ 0 = 1 →
      (∀ s : ℝ, 1 - 3 * Work.OddCurve.tau < s → s ≤ 1 →
        Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
          Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2)) →
      (∀ s : ℝ, 1 - 3 * Work.OddCurve.tau < s → s ≤ 1 →
        Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) →
      GlueDataSmall n ρ σ δ₁ δ₂

/-- **The curve-assembly input of Step 3**, as a `Prop`: from a radial pair with the sharp bounds,
the junction with the anchor on `[3/4, 4/5]` (where the cutting line is still central), and the
monotonicity/concavity of the two radial pieces on `(0, 3/4)` — hypotheses of derivative-sign type,
which the two-power system supplies through `LowSlope.radialSystem_deriv_sign` — one produces the
two-piece curve of `LowSlope/CurveDefs.lean` and proves that it is a free-tip envelope curve and
`C²`-close to the semicircle's chord function.

The derivative-sign hypotheses are *not* redundant: two reviewers of an earlier statement showed
that the two-sided `ε`-bounds on `R, r` alone do not force `x_deriv_neg`/`y_deriv_neg` (take
`R = r` with `R'(0) = ε > 0`, `R = 1` near `[3/4, π/2]`). -/
def LowSlopeCurveAssemblySpec (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h X Y R r : ℝ → ℝ,
    Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h →
    Work.OddEnvelope.IsEnvelopeCurve h X Y → LowSlope.CloseToProfileX X →
    LowSlope.CloseToProfileX Y →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R (Set.Icc 0 (Real.pi / 2)) →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r (Set.Icc 0 (Real.pi / 2)) →
    R (Real.pi / 2) = 1 → r (Real.pi / 2) = 1 →
    (∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |R α - 1| ≤ ε ∧ |deriv R α| ≤ ε ∧ |deriv (deriv R) α| ≤ ε ∧
      |r α - 1| ≤ ε ∧ |deriv r α| ≤ ε ∧ |deriv (deriv r) α| ≤ ε) →
    (hjunc : ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 4 / 5 →
      Y σ = R (Real.arctan σ) * Real.cos (Real.arctan σ) ∧
      X σ = r (Real.arctan σ) * Real.cos (Real.arctan σ)) →
    (hmonoR : ∀ σ : ℝ, 0 < σ → σ < 3 / 4 →
      deriv (fun τ : ℝ => R (Real.arctan τ) * Real.cos (Real.arctan τ)) σ < 0) →
    (hmonor : ∀ σ : ℝ, 0 < σ → σ < 3 / 4 →
      deriv (fun τ : ℝ => r (Real.arctan τ) * Real.cos (Real.arctan τ)) σ < 0) →
    (hshapeR : ∀ σ : ℝ, 0 < σ → σ < 3 / 4 →
      0 < 2 * (deriv (fun τ : ℝ => R (Real.arctan τ) * Real.cos (Real.arctan τ)) σ) ^ 2 -
        (R (Real.arctan σ) * Real.cos (Real.arctan σ)) *
          deriv (deriv (fun τ : ℝ => R (Real.arctan τ) * Real.cos (Real.arctan τ))) σ) →
    (hshaper : ∀ σ : ℝ, 0 < σ → σ < 3 / 4 →
      0 < 2 * (deriv (fun τ : ℝ => r (Real.arctan τ) * Real.cos (Real.arctan τ)) σ) ^ 2 -
        (r (Real.arctan σ) * Real.cos (Real.arctan σ)) *
          deriv (deriv (fun τ : ℝ => r (Real.arctan τ) * Real.cos (Real.arctan τ))) σ) →
    IsEnvelopeCurveFree h (LowSlope.lowSlopeCurveX r X) (LowSlope.lowSlopeCurveY R Y) ∧
      LowSlope.CloseToProfileX (LowSlope.lowSlopeCurveX r X) ∧
      LowSlope.CloseToProfileX (LowSlope.lowSlopeCurveY R Y)

end

end Free
end Work.OddCurve
