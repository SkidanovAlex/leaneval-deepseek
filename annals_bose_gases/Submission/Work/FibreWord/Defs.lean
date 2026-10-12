import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SlotWord.fibreAmpDecay
import Submission.Work.SlotWord.integrable_fibre_tBdiagFormInd_of_decay
import Submission.Work.SlotWord.integrable_tBdiagFibreJoint_of_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.FibreWord.Defs` — the fibre-word chapter: vocabulary

## What this chapter is for

`Work.SlotWord` reduces the lead's `hsum` residual chain to the single per-fibre input

    Work.SlotWord.FibreWordBoundAt h M L d ε c N Φ
      (fun k => Work.BlockBound4.diagWeBAt k (L·d) (dens N L) v h c (tbGapCoeff (L·d) ε)) ,

i.e. *for a.e. good `u`, every nonempty slot set `S`, every `e`, a.e. outside `y`:
the fibre mass of the slot piece times the delivered count-indexed per-box ground energy is
dominated by the sliding word of the fibre*.  This chapter is the area of mathematics of that
statement: its vocabulary, the reductions that turn it into the shape a trial-state argument can
attack, the geometric/mass identities the reduction consumes, and the precise residual.

## The central mathematical point of the chapter

`diagWeBAt k s …` is a **variational infimum** — the ground energy of the small-box Hamiltonian,
`⨅_{ψ ∈ CSBox k s} blockE(ψ)/‖ψ‖²` (`Work.KinPSuperadd.slotEB`, `Work.MGroupInput.slotEB_le_quot_ofFun`).
An *upper* bound on an infimum therefore has exactly one shape: exhibit a trial state.  The fibre
itself is the natural trial state, but the fibre of the *slot piece* carries the box indicator
`1_{B(u)^{S}}` and is not smooth, so it is not a member of the corpus trial space `CSBox`.

The two named residuals of `Work.SlotWord.Trial` (`FibreWordApprox`, `FibreWordCompare`) are the
state-level rendering of that step.  This chapter re-renders it in the **trial-state shape** —
which is strictly weaker, and is the shape in which FS's `thm:smallbox` is actually proved:

* `FibreTrialAt v h M L d ε c N Φ` — for a.e. `u`, `S`, `e`, a.e. `y` there is a *smooth* trial
  state `ψ ∈ CSBox S.card (L·d)` whose box energy, in the correct mass ratio, is dominated by the
  fibre's sliding word.  `fibreWordBoundAt_of_trial` **proves** `FibreWordBoundAt` from it, using
  `slotEB_le_quot_ofFun` (the defining property of the infimum).
* `shiftFibre S e Φ w y` — the **explicit candidate**: the fibre of the *state* translated by
  `w = (L·d)•u` into the centred cube.  Unlike the fibre of the piece it **is** smooth
  (`contDiff_shiftFibre`), and its mass over the centred cube dominates the fibre mass
  (`fibMass_le_shiftFibre`, a genuine geometric fact: `B(u) ⊆ (L·d)•u + acube (L·d)` by
  `Submission.BoseGases.mem_dlBox_iff`).
* `FibreShiftBound v h M L d ε c N Φ` — the **residual**: the state-level comparison
  `fibreMass·faithEnergy(shiftFibre) ≤ ‖shiftFibre‖²·word(fibre)` at the explicit candidate.
  `fibreTrialAt_of_shiftBound` **proves** `FibreTrialAt` from it.

So the whole chapter is

    FibreShiftBound  ⟹  FibreTrialAt  ⟹  FibreWordBoundAt  ⟹  SlotWordBoundDiag  ⟹  the hsum chain

with the three middle implications proved here (the last in `Work.SlotWord.Core`), and the first
named, decomposed (`FibreWordLeShift` + `fibWord_nonneg`), and documented (`README.md` §3).

## Conventions

* `ℝ³ = EuclideanSpace ℝ (Fin 3)`, `X N = Fin N → ℝ³`, `abox N L` the centred box of side `L`,
  `acube L = abox 1 L`, `dlBox L d u = acube L ∩ ((L·d)•u + acube (L·d))` the sliding box;
* `k = S.card` is the **count** of the fibre; the box side of the delivered word is `s = L·d`;
* the sliding word of the fibre lives at the *ambient* box `L`, the sliding window `chiB L d u`
  (supported in `dlBox L d u`) and the localised kernels `wSmallPair M L d u v`,
  `wSmall1Pair h M L d u`; the faithful word lives at the centred box of side `L·d` with the
  sharp kernels `wPairC (L·d) v`, `wPairC (L·d) (g0 v h)`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.FibreWord

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.PerSector
open Work.UBB
open Work.SmallBoxSliding
open Work.UBBInputs8
open Work.FockBridge
open Work.BlockBound4
open Work.KinPSuperadd
open Work.SlotWord
open Work.SmallBoxTBWord
open Classical

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-! ## 1  The two fibres, their masses, and the two words -/

/-- **The fibre of the slot piece** (the object the delivered bound is about): the slot piece
`1_{slotSet B S}·Φ` evaluated along the reassembly map, transported to `X S.card` along
`e : SlotIn N S ≃ Fin S.card`.  It vanishes off `B^{S}`.  (`= Work.SlotWord.pieceFibre`.) -/
def fibPiece (L d : ℝ) (u : ℝ³) (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card)
    (Φ : X N → ℝ) (y : SlotOut N S → ℝ³) : X S.card → ℝ :=
  pieceFibre (dlBox L d u) S e Φ y

/-- **The fibre of the state** (the smooth companion): `z ↦ Φ (slotComb S z y)`.  It agrees with
`fibPiece` on the box `B^{S}` and is smooth whenever `Φ` is.  (`= Work.PerSector.slotFibreState`.) -/
def fibState (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card) (Φ : X N → ℝ)
    (y : SlotOut N S → ℝ³) : X S.card → ℝ :=
  slotFibreState S e Φ y

/-- **The fibre mass**: the box `L²`-mass of the fibre of the slot piece.  This is the
normalisation of the per-fibre residual, and it is the field whose `y`-integral is the slot mass
(`Work.SlotWord.integral_slotFibreMassReal_piece_eq_slotMass`). -/
def fibMass (L d : ℝ) (u : ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ)
    (y : SlotOut N S → ℝ³) : ℝ :=
  slotFibreMassReal (dlBox L d u) S (slotPiece (dlBox L d u) S Φ) y

/-- **The sliding word at particle number `k`** — the right-hand side of the per-fibre residual
(the FS-faithful `𝒯_{B(u)}` word plus the localised potential word).  (`= fibreWord`.) -/
def fibWord {v : ℝ³ → ℝ} (h : ScatSol v) (M : ℕ) (k : ℕ) (L d ε c μ : ℝ) (u : ℝ³)
    (Ψ : X k → ℝ) : ℝ :=
  fibreWord h M k L d ε c μ u Ψ

/-- **The faithful word at the centred box of side `s`** (the delivered `diagWWord`). -/
def faithWord (s c cgap : ℝ) (k : ℕ) (Ψ : X k → ℝ) : ℝ :=
  diagWWord s c cgap k Ψ

/-- **The faithful small-box energy** at the centred box of side `s`, chemical potential `μ` and
the sharp kernels: `diagWWord + qLHSword`.  This is the numerator of the quotient whose infimum is
`Work.BlockBound4.diagWeBAt`. -/
def faithEnergy (s μ : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v) (c cgap : ℝ) (k : ℕ)
    (Ψ : X k → ℝ) : ℝ :=
  diagWWord s c cgap k Ψ
    + qLHSword (N := k) s μ (wPairC s v) (wPairC s (g0 v h)) Ψ

/-- `faithEnergy` is the corpus `blockE` at the faithful word (definitional). -/
theorem faithEnergy_eq_blockE (s μ : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v) (c cgap : ℝ) (k : ℕ)
    (Ψ : X k → ℝ) :
    faithEnergy s μ v h c cgap k Ψ
      = blockE s μ (wPairC s v) (wPairC s (g0 v h)) (diagSlotWord s c cgap) k Ψ := rfl

/-- `faithEnergy` unfolded into its two pieces. -/
theorem faithEnergy_eq (s μ : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v) (c cgap : ℝ) (k : ℕ)
    (Ψ : X k → ℝ) :
    faithEnergy s μ v h c cgap k Ψ
      = diagWWord s c cgap k Ψ
        + qLHSword (N := k) s μ (wPairC s v) (wPairC s (g0 v h)) Ψ := rfl

/-- **The explicit trial candidate: the translated smooth fibre.**  With `w = (L·d)•u` this is
`x ↦ Φ (slotComb S (x∘e + w) y)`, i.e. the fibre of the *state* shifted so that its support lands
in the centred cube `acube (L·d)^{S}`.  (`= Work.SlotWord.centreFibre` with the slot piece
replaced by the state.) -/
def shiftFibre (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card) (Φ : X N → ℝ) (w : ℝ³)
    (y : SlotOut N S → ℝ³) : X S.card → ℝ :=
  fun x => slotFibreState S e Φ y (x + fun _ => w)

/-- The pointwise unfolding of `shiftFibre`. -/
theorem shiftFibre_apply (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card) (Φ : X N → ℝ)
    (w : ℝ³) (y : SlotOut N S → ℝ³) (x : X S.card) :
    shiftFibre S e Φ w y x = Φ (slotComb S (fun i : SlotIn N S => x (e i) + w) y) := rfl

/-! ## 2  The residuals, in increasing order of strength

`FibreShiftBound ⟹ FibreTrialAt ⟹ FibreWordBoundAt`, all three proved in the sibling modules.
-/

/-- **The residual (state-level)**: the explicit smooth candidate `shiftFibre` satisfies the
mass-normalised comparison.  With `ψ := shiftFibre S e Φ ((L·d)•u) y`, `f := fibMass` and
`W := fibWord … (fibPiece …)` this is

    f · faithEnergy (L·d) … ψ  ≤  (∫_{abox k (L·d)} ψ²) · W .

It is *provable* from the state-level comparison `faithEnergy ψ ≤ W` together with
`0 ≤ W` and `f ≤ ∫ψ²` (`shiftBound_of_wordLe`), or from `faithEnergy ψ ≤ 0 ≤ W`
(`shiftBound_of_nonpos`); both reductions are in `Arith.lean`. -/
def FibreShiftBound (v : ℝ³ → ℝ) (h : ScatSol v) (M : ℕ) (L d ε c : ℝ) (N : ℕ)
    (Φ : X N → ℝ) : Prop :=
  ∀ᵐ u ∂(volume.restrict (goodSet L d (dens N L))),
    ∀ S : Finset (Fin N), 0 < S.card → ∀ e : SlotIn N S ≃ Fin S.card,
      ∀ᵐ y ∂(volume.restrict (slotOutside L (dlBox L d u) S)),
        fibMass L d u S Φ y
            * faithEnergy (L * d) (dens N L) v h c (tbGapCoeff (L * d) ε) S.card
                (shiftFibre S e Φ ((L * d) • u) y)
          ≤ (∫ x in abox S.card (L * d), (shiftFibre S e Φ ((L * d) • u) y x) ^ 2)
            * fibWord h M S.card L d ε c (dens N L) u (fibPiece L d u S e Φ y)

/-- **The residual (state-level, sharp form)**: the faithful energy of the translated fibre is
dominated by the fibre's sliding word.  This is the "kernel/word comparison at the sliding box"
read at a *smooth* state — the `Work.BlockBound4.Repoint` / `Work.DLWire` route.  Together with
the nonnegativity of the sliding word it gives `FibreShiftBound` (`shiftBound_of_wordLe`). -/
def FibreWordLeShift (v : ℝ³ → ℝ) (h : ScatSol v) (M : ℕ) (L d ε c : ℝ) (N : ℕ)
    (Φ : X N → ℝ) : Prop :=
  ∀ᵐ u ∂(volume.restrict (goodSet L d (dens N L))),
    ∀ S : Finset (Fin N), 0 < S.card → ∀ e : SlotIn N S ≃ Fin S.card,
      ∀ᵐ y ∂(volume.restrict (slotOutside L (dlBox L d u) S)),
        faithEnergy (L * d) (dens N L) v h c (tbGapCoeff (L * d) ε) S.card
            (shiftFibre S e Φ ((L * d) • u) y)
          ≤ fibWord h M S.card L d ε c (dens N L) u (fibPiece L d u S e Φ y)

/-- **The nonnegativity of the sliding word at the fibre of the slot piece** — the second half of
the sharp form of the residual.  (`tBwordBInd ≥ 0` is `Work.UBBInputs9.A.tBwordBInd_nonneg`; the
potential word `qLHSwordB` is not sign-definite, so this is a genuine condition, and it is
*not* assumed anywhere in the corpus.) -/
def FibreWordNonneg {v : ℝ³ → ℝ} (h : ScatSol v) (M : ℕ) (L d ε c : ℝ) (N : ℕ)
    (Φ : X N → ℝ) : Prop :=
  ∀ᵐ u ∂(volume.restrict (goodSet L d (dens N L))),
    ∀ S : Finset (Fin N), 0 < S.card → ∀ e : SlotIn N S ≃ Fin S.card,
      ∀ᵐ y ∂(volume.restrict (slotOutside L (dlBox L d u) S)),
        0 ≤ fibWord h M S.card L d ε c (dens N L) u (fibPiece L d u S e Φ y)

/-- **The residual in trial-state shape** (the shape FS's `thm:smallbox` has): for a.e. good `u`,
every nonempty `S`, every `e`, a.e. outside `y`, there is a *smooth* trial state
`ψ ∈ CSBox S.card (L·d)` whose box energy, in the mass ratio
`fibreMass / ‖ψ‖²`, is dominated by the fibre's sliding word:

    fibMass · faithEnergy ψ  ≤  (∫_{abox k (L·d)} ψ²) · word(fibre) .

Since `diagWeBAt` is the infimum of `faithEnergy ψ / ∫ψ²` over `CSBox`, this **implies**
`FibreWordBoundAt` (`fibreWordBoundAt_of_trial`), while the trial state is smooth by construction —
so the whole content is the exhibition of the state, not the smoothness of the fibre. -/
def FibreTrialAt (v : ℝ³ → ℝ) (h : ScatSol v) (M : ℕ) (L d ε c : ℝ) (N : ℕ)
    (Φ : X N → ℝ) : Prop :=
  ∀ᵐ u ∂(volume.restrict (goodSet L d (dens N L))),
    ∀ S : Finset (Fin N), 0 < S.card → ∀ e : SlotIn N S ≃ Fin S.card,
      ∀ᵐ y ∂(volume.restrict (slotOutside L (dlBox L d u) S)),
        ∃ ψ : CSBox S.card (L * d),
          fibMass L d u S Φ y
              * faithEnergy (L * d) (dens N L) v h c (tbGapCoeff (L * d) ε) S.card
                  (ψ : X S.card → ℝ)
            ≤ (∫ x in abox S.card (L * d), ((ψ : X S.card → ℝ) x) ^ 2)
              * fibWord h M S.card L d ε c (dens N L) u (fibPiece L d u S e Φ y)

/-- **The residual in the form the lead's chain consumes** — `Work.SlotWord.FibreWordBoundAt` at
the delivered count function `k ↦ diagWeBAt k (L·d) …`, re-exported so that this chapter's
interface is self-contained. -/
abbrev FibreWordBoundAtDiag {v : ℝ³ → ℝ} (h : ScatSol v) (M : ℕ) (L d ε c : ℝ) (N : ℕ)
    (Φ : X N → ℝ) : Prop :=
  FibreWordBoundAt h M L d ε c N Φ
    (fun k => diagWeBAt k (L * (d : ℝ)) (dens N L) v h c (tbGapCoeff (L * (d : ℝ)) ε))

end Work.FibreWord
