import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.UBBInputs2.Arith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs2.Canonical` — the canonicalisation of `BoxSumBound`

Round 1's `BoxSumBound` (`Submission/Work/UBBInputs/Defs.lean`) is the
corpus-side half of FS `eq:BSsliding2`,

    eBf u ≤ 𝒯_B(u) + qLHSwordB(u)      (`hbox`)
    ∫_u qLHSwordB(u) ≤ qLHSword        (`hpot`)
    −C·χ-mass(u) ≤ eBf u               (`hlow`)
    ∫_{Gᶜ} χ-mass ≤ B                  (`hmass`)
    R' − 4πρ²(a v)L³(1+K_B³√(ρ(a v)³)) + C·B ≤ ∫_G eBf   (`hsum`)

with `eBf` a *free* energy word.  `UBBInputs/Comparison.lean` records that the
delivered faithful-word comparison has the *wrong direction* for the field
`hbox` (it bounds the faithful word *above* by the corpus word, while `hbox`
needs the per-box energy *below* the localised corpus word).  This module
resolves that by **canonicalising `eBf`**:

* `BoxSumBoundCanon` — the same bundle with `eBf` **fixed** to the localised
  corpus word `tBwordB u + qLHSwordB u`.  Then `hbox` becomes definitional
  (`le_rfl`) — the direction issue disappears — and two more fields are
  discharged from CLOSED corpus lemmas:
  - `Integrable (fun u => chiMass M L d u)` is
    `Work.SmallBoxSliding.integrable_chiSmallB_mass` (unconditional in
    `1 ≤ M`, `0 < L`, `0 < d`);
  - the free choice of `eBf` is gone, so `hsum` automatically holds for the
    *largest* admissible word, which is the favourable direction for the lower
    bound `hsum` (a larger `eBf` only helps `hsum` and `hlow`).

* `boxSumBound_of_canon` / `boxSumBoundCanon_of_boxSumBound` — **both
  directions are proved**, so the canonicalisation is an equivalence: no content
  is lost, and the free-function slack of `eBf` was never useful.

The remaining content of `BoxSumBoundCanon` is therefore exactly

    `hpot`  (FS `lem:LocPotential`; DELIVERED as
             `Work.SmallBoxSliding.qLHSwordB_integral_u` up to the reference
             word `qLHSwordChi`)
    `hlow`  (the per-box lower bound on the discarded boxes),
    `hmass` (DELIVERED: `Work.SmallBoxSliding.compl_mass_le` gives the explicit
             `B = 12(1+d)²(chiSmallDecay M)⁴C₁(μa³)^{M/3}L³`,
             `boxSumBoundCanon_of_complMass` below),
    `hsum`  (the per-box DL bound integrated over the good set; the
             count↔localised-density bookkeeping).

See `README.md` §"Residual (2)" for the exact remaining ledger.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs2

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.UBBInputs

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The canonicalised `BoxSumBound`**: the per-box energy word is *fixed* to
the localised corpus word `𝒯_B(u) + qLHSwordB(u)`, which makes `hbox`
definitional and removes the free-function slack. -/
def BoxSumBoundCanon (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ)
    (d M : ℕ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ → ∀ Φ : CSBox N L,
    sqNormN N L (Φ : X N → ℝ) = 1 →
    WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
    ∃ (ε c C B : ℝ),
      0 ≤ C ∧
      ((∫ u : ℝ³, Work.SmallBoxSliding.qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ))
        ≤ qLHSword (N := N) L (dens N L) (wPairC L v) (wPairC L (g0 v h))
            (Φ : X N → ℝ)) ∧
      Integrable (fun u : ℝ³ => Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)) ∧
      Integrable (fun u : ℝ³ => Work.SmallBoxSliding.qLHSwordB h M L d (dens N L) u
        (Φ : X N → ℝ)) ∧
      (∀ u : ℝ³, - C * Work.SmallBoxSliding.chiMass M L d u
        ≤ Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)
          + Work.SmallBoxSliding.qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ)) ∧
      ((∫ u in (Work.SmallBoxSliding.goodSet L d (dens N L))ᶜ,
          Work.SmallBoxSliding.chiMass M L d u) ≤ B) ∧
      (R' - 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
          * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)) + C * B
        ≤ ∫ u in Work.SmallBoxSliding.goodSet L d (dens N L),
            (Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)
              + Work.SmallBoxSliding.qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ)))

/-- **The canonicalised bundle implies round 1's bundle** — the direction that
the chain consumes.  `eBf` is instantiated at the localised corpus word (so
`hbox` is `le_rfl`), and the `Integrable chiMass` field is discharged from the
CLOSED `Work.SmallBoxSliding.integrable_chiSmallB_mass`. -/
theorem boxSumBound_of_canon {v : ℝ³ → ℝ} {h : ScatSol v}
    {b K_B R' J ε₀ : ℝ} {d M : ℕ} (hM : 1 ≤ M) (hd : (0 : ℝ) < d)
    (hcanon : BoxSumBoundCanon v h b K_B R' J ε₀ d M) :
    BoxSumBound v h b K_B R' J ε₀ d M := by
  intro L hL N hN Φ hnorm hlow
  obtain ⟨ε, c, C, B, hC, hpot, hintt, hintq, hlowu, hmass, hsum⟩ :=
    hcanon L hL N hN Φ hnorm hlow
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  refine ⟨ε, c, C, B,
    (fun u : ℝ³ => Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)
      + Work.SmallBoxSliding.qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ)),
    hC, (fun u => le_refl _), hpot, hintt, hintq, hintt.add hintq,
    Work.SmallBoxSliding.integrable_chiSmallB_mass hM hLpos hd, hlowu, hmass, hsum⟩

/-- **The converse**: round 1's bundle implies the canonicalised one (take the
same witnesses; `hbox` transfers `hlow`, and `hsum` transfers by monotonicity of
the set integral).  Hence the canonicalisation is an *equivalence*. -/
theorem boxSumBoundCanon_of_boxSumBound {v : ℝ³ → ℝ} {h : ScatSol v}
    {b K_B R' J ε₀ : ℝ} {d M : ℕ}
    (hB : BoxSumBound v h b K_B R' J ε₀ d M) :
    BoxSumBoundCanon v h b K_B R' J ε₀ d M := by
  intro L hL N hN Φ hnorm hlow
  obtain ⟨ε, c, C, B, eBf, hC, hbox, hpot, hintt, hintq, hintf, _hintmass,
    hlowu, hmass, hsum⟩ := hB L hL N hN Φ hnorm hlow
  refine ⟨ε, c, C, B, hC, hpot, hintt, hintq, (fun u => le_trans (hlowu u) (hbox u)),
    hmass, ?_⟩
  have hG : MeasurableSet (Work.SmallBoxSliding.goodSet L d (dens N L)) :=
    Work.SmallBoxSliding.measurableSet_goodSet L d (dens N L)
  have hmono : (∫ u in Work.SmallBoxSliding.goodSet L d (dens N L), eBf u)
      ≤ ∫ u in Work.SmallBoxSliding.goodSet L d (dens N L),
          (Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)
            + Work.SmallBoxSliding.qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ)) :=
    MeasureTheory.setIntegral_mono_on hintf.integrableOn ((hintt.add hintq).integrableOn)
      hG (fun u _ => hbox u)
  linarith [hsum, hmono]

/-- **`BoxSumBoundCanon` with the discarded-mass bound discharged** from the
CLOSED `Work.SmallBoxSliding.compl_mass_le`: the field `hmass` of
`BoxSumBoundCanon` holds at the *explicit* `B` of FS `eq:badset` once the
regime data of the bad-band law is supplied.  (This is a field-discharge, not a
change of residual: it shows that `hmass` carries no mathematical content
beyond the delivered bad-band estimate.) -/
theorem hmass_of_complMass {M : ℕ} (hM : 1 ≤ M) {ℓ d μ a C₁ : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (hμ : 0 < μ) (ha : 0 ≤ a) (hC₁ : 0 ≤ C₁)
    (hAδ : 0 ≤ (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ))
    (hEst : (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) * μ ^ (-1 / 3 : ℝ) * ℓ ^ 2
        ≤ C₁ * (μ * a ^ 3) ^ ((M : ℝ) / 3) * ℓ ^ 3) :
    (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ, Work.SmallBoxSliding.chiMass M ℓ d u)
      ≤ 12 * (1 + d) ^ 2 * chiSmallBandDecay M d * C₁ * (μ * a ^ 3) ^ ((M : ℝ) / 3)
          * ℓ ^ 3 := by
  simpa only [Work.SmallBoxSliding.chiMass_def] using
    (Work.SmallBoxSliding.compl_mass_le (M := M) hM hℓ hd hμ ha hC₁ hAδ hEst)

end Work.UBBInputs2
