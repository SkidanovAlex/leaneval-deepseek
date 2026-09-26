import Mathlib
import Submission.Work.Drive.ofatEndgameSOfTopEnd
import Submission.Work.Drive.wideEndGivenC
import Submission.Work.Drive.sweepToNeedleEpsOfSlices_gen

/-!
# The two named inputs of the `OFat` top end

`Work.Drive.ofatEndgameS_of_topEnd` (`Drive/ofatEndgameSOfTopEnd.lean`) reduces the pin
`Work.Drive.OFatCrosscutEndgameS` to a single hypothesis: the **top end** `Work.Drive.NeedleTopEnd`
at a needle slice in the bottom trough of the schedule.  This module names the two analytic inputs
that the top end still consumes, so that they can be built (and delegated) separately:

* `Work.Drive.WideEndUniform` — the **wide-end estimate**, in the quantifier order and with the
  constant-agnostic treatment the `∃`-`lay` flow of the top end needs.  It is the *merge* of the two
  proved estimates of the workspace:
  * `Work.Drive.wideEndPrescribedGen_sigmaFirst` (`Drive/sweepToNeedleEpsOfSlices_gen.lean`) fixes the
    slice `σ₀` *before* the layout `lay` — the order the top end needs — but carries an opaque
    constant `C` quantified *after* `ρ₀, δs, cQ`;
  * `Work.Drive.wideEndGivenC` (`Drive/wideEndGivenC.lean`) frees the constant (`∀ C ≥ Cmin`) but
    takes the slice `σ₀` as an *input*;
  so the merge has `∃ Cmin, 0 < Cmin ∧ ∀ C ≥ Cmin, ∀ ε₁ ∈ (0,C], ∃ σ₀ ∈ (1/2,1), ∀ lay ∈ (0,1/4],
  ∀ ρ₀ cQ > 0, …` — the same proof works: `σ₀` is chosen from `ε₁`, `C` and the modulus of
  continuity of `σ ↦ sweepW' D σ` at `1`, all of which are independent of `lay`, `ρ₀`, `cQ`.

* `Work.Drive.ofatTopEnd_of_wideEnd` — the top end from that estimate (this is the transcription of
  `Work.Drive.sweepToNeedleEpsOfSlices_gen` with its slices clause taken in the `∃`-`lay` form
  produced by `Work.Drive.blurSlices_of_schedSlot`, and with the endpoint moved to the needle by the
  trough identity `Work.Drive.sweepFamOf_schedLoop_eq_needle`).
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The wide-end estimate of the uniform-`ρ₀` design, in the form the top end consumes.**

The constant `C` is *free* (any `C ≥ Cmin` works), the slice `σ₀` is produced **before** the layout
`lay`, `ρ₀`, `cQ` and comes with the *gap bound* `C * (period - sweepW' D σ₀) ≤ ε₁ / 4` (so that the
caller can use it), and the layout only has to satisfy the scalar bound `C * lay ≤ ε₁ / 4`; then the
estimate gives the `C¹`-closeness with tolerance `ε₁`.

**Correction (from the reviewers of the first version).**  In the first version the gap bound
`C * (lay + (period - sweepW' D σ₀)) ≤ ε₁` was a *premise* of the implication, which makes the
statement useless: `σ₀` is existentially bound and the caller cannot select it, so a witness with a
large gap satisfies the statement vacuously and gives nothing at the slice the top end needs.  The
gap bound must therefore be a *conclusion* (together with the "`σ₀` is close to `1`" data) and the
`lay`-side of the budget must be a scalar bound the caller controls. -/
def WideEndUniform (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (δs : ℝ) : Prop :=
  ∃ Cmin : ℝ, 0 < Cmin ∧
    ∀ C : ℝ, Cmin ≤ C → ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ C →
      ∃ σ₀ : ℝ, 1 / 2 < σ₀ ∧ σ₀ < 1 ∧
        C * (period - sweepW' D σ₀) ≤ ε₁ / 4 ∧
        ∀ lay : ℝ, 0 < lay → lay ≤ 1 / 4 → C * lay ≤ ε₁ / 4 →
          ∀ ρ₀ cQ : ℝ, 0 < ρ₀ → 0 < cQ →
            ∀ L : ℝ, 0 < L →
              ∃ (δ₁ δ₂ c : ℝ) (Θ : ℝ → ℝ),
                0 < δ₁ ∧ δ₁ ≤ L ∧ 0 < δ₂ ∧ δ₂ ≤ L ∧
                ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
                (∀ t : ℝ, Θ (t + period) = Θ t + period) ∧
                (∀ t : ℝ, 0 < deriv Θ t) ∧
                (∀ t : ℝ, ‖sweepFamOf
                    (chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D)
                      (schedBeta r lay ρ₀ δs cQ D)) δ₁ δ₂ σ₀ (Θ t)
                  - r (t + c)‖ < ε₁) ∧
                (∀ t : ℝ, ‖deriv (fun u : ℝ => sweepFamOf
                    (chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D)
                      (schedBeta r lay ρ₀ δs cQ D)) δ₁ δ₂ σ₀ (Θ u)) t
                  - velocity r (t + c)‖ < ε₁)

/-! ## How to prove the top end (`Work.Drive.ofatTopEnd_of_wideEnd`) — the recipe

**All the pieces are proved and `sorry`-free**; the proof is a **transcription** of
`Work.Drive.sweepToNeedleEpsOfSlices_gen`'s proof (`Drive/sweepToNeedleEpsOfSlices_gen.lean`, from
its `## (a)` on), with three changes:

1. **the wide end.**  Instead of `wideEndPrescribedGen_sigmaFirst` (whose `C` is quantified after
   `ρ₀, δs, cQ`) use the given `hwide : Work.Drive.WideEndUniform r D δs`: take
   `C := max Cmin 1` from `hwide`'s `∃ Cmin`, `ε₁ := min ε_uc (C / 2)` where `ε_uc` is the threshold
   of `Work.Drive.uniformCorrection_clauses` for the rotated family of `r` (as in the template's
   `## (a)`), and get `σ₀ ∈ (1/2,1)` with `C * (period - sweepW' D σ₀) ≤ ε₁ / 4` **from `hwide`**.
   No phase machinery is needed: the estimate's conclusion *is* the `C¹`-closeness at `σ₀` to a
   rotation of `r`.
2. **the slices clause.**  Instead of an `hsl` hypothesis, use the scheduling slot: with
   `Lmax := min (min Δ (1/4)) (ε₁ / (4 * C))` (positive), `hslot Lmax hLmax ε σ₀ hε0 hεσ₀ hσ₀1`
   gives the slot's `(lay, ρ₀, cQ)`, its injectivity and `ChamferJunctionOK` on the clamped window
   `[ε/2, (1+σ₀)/2]`; then `Work.Drive.chamferLoopGen_slicesClause hr D hδs … hl hJ hI` (**proved**:
   its cone input `Work.Drive.chamferLoopGen_localCone` is now proved) gives the blurred-slices
   clause on `[ε, σ₀]` at that layout.  Since `lay ≤ Lmax ≤ ε₁/(4C)` we have `C * lay ≤ ε₁/4`, so
   `hwide` applies at that layout — this is the template's `## (c)`/`## (e)` with the layout taken
   from the slot rather than chosen.
3. **the endpoint.**  The template stops at `sweepFamOf Γ δ₁ δ₂ ε`; convert it to the needle with
   `Work.Drive.sweepFamOf_schedLoop_eq_needle` (**proved**): `htrough` gives `4 * schedC D σ ≤ δs` on
   `[ε/2, 3ε/2] ⊇ [ε - δ₂, ε + δ₂]` (because `δ₂ ≤ ε/2`), so
   `Work.Drive.schedAlpha_eq_lay_of_schedC` / `schedBeta_eq_lay_of_schedC` put both schedules at
   their floor and the blurred scheduled slice at `ε` *is* `sweepNeedleFam r D lay δ₁ δ₂ ε`.

The rest (the `sweepGlue`/`reparamOfPhase` bookkeeping and the structural clauses of `H`) is
verbatim the template's; `Work.Drive.unknotted_of_needleTrough`
(`Drive/ofatNeedleTroughGlue.lean`) shows the same glue with a prescribed needle slice. -/

end Work.Drive
