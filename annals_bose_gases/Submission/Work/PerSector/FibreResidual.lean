import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.PerSector.Support
import Submission.Work.PerSector.contDiff_slotFibre
import Submission.Work.PerSector.measurable_slotFibre_pair
import Submission.Work.PerSector.slotMassENN_eq_fibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.PerSector.FibreResidual` — the residual in fibre form

The Fubini decomposition of `Fibre.lean` exhibits the `k`-th occupancy sector piece as a measurable
field `y ↦ slotFibre S Φ y` of `k`-particle functions on the box `B(u)`.  This module puts the
per-fibre *state* and the per-fibre *residual* on record, so that the remaining analytic gap of
`README.md` §6(R1) can be stated in the vocabulary of the fibre rather than of the big-box sector
piece:

* `slotFibreState S e Φ y` — the fibre transported to `X |S|` along a bijection `e : SlotIn N S ≃
  Fin |S|` (the object the delivered per-box theorems are stated for);
* `slotFibreMassReal B S Φ y` — the real box mass of the fibre;
* **`FibreWordBound`** — *the per-fibre per-box residual*: for a.e. good `u`, every nonempty slot
  set `S` and a.e. outside configuration `y`, the delivered count-indexed per-box ground energy
  `Work.BlockBound4.diagWeBAt |S|` is dominated by the `|S|`-particle word of the fibre, normalised
  by the fibre's box mass.  This is FS's `thm:smallbox` read at the fibre, i.e. the second missing
  piece of the lead's `FockBridge/README.md` §6 in its sharpest form.

The passage `FibreWordBound ⟹ SlotWordBoundDiag` is the *fibre factorisation of the word*
(`word(slotPiece S Φ) = ∫_y word(fibre_y)`), whose proof needs the integrability bookkeeping of
`README.md` §6(R3) — the Bochner integral convention (`∫ = 0` for a non-integrable function) means
the identity can only be stated under that bookkeeping; the pointwise/Fubini content itself is the
same argument as `slotMassENN_eq_fibre`.  See the README for the honest ledger.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.PerSector

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.FockBridge
open Work.UBBInputs8
open Work.SmallBoxSliding
open Work.UBB
open Classical

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-! ## 1. The fibre as a `k`-particle state -/

/-- **The fibre transported to `X |S|`.**  Along a bijection `e` of the in-box slots of `S` with
`Fin |S|`, the fibre `slotFibre S Φ y` becomes a function on the configuration space `X |S|` of the
`|S|`-particle box — the trial space of the delivered per-box theorems
(`Work.BlockBound4.diagWeBAt`). -/
def slotFibreState (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card) (Φ : X N → ℝ)
    (y : SlotOut N S → ℝ³) : X S.card → ℝ :=
  fun x => slotFibre S Φ y (fun i : SlotIn N S => x (e i))

theorem slotFibreState_apply (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card) (Φ : X N → ℝ)
    (y : SlotOut N S → ℝ³) (x : X S.card) :
    slotFibreState S e Φ y x = Φ (slotComb S (fun i : SlotIn N S => x (e i)) y) := rfl

/-- The transferred fibre is smooth whenever the state is. -/
theorem contDiff_slotFibreState (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card)
    {Φ : X N → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (y : SlotOut N S → ℝ³) :
    ContDiff ℝ ∞ (slotFibreState S e Φ y) := by
  have hT : ContDiff ℝ ∞ (fun x : X S.card => fun i : SlotIn N S => x (e i)) := by
    refine contDiff_pi.mpr (fun i => ?_)
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin S.card => ℝ³) (e i)).contDiff
  exact (contDiff_slotFibre S hΦ y).comp hT

/-- **The real box mass of the fibre** — the normalisation of the per-fibre statement. -/
noncomputable def slotFibreMassReal (B : Set ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ)
    (y : SlotOut N S → ℝ³) : ℝ :=
  (slotFibreMass B S Φ y).toReal

theorem slotFibreMassReal_nonneg (B : Set ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ)
    (y : SlotOut N S → ℝ³) : 0 ≤ slotFibreMassReal B S Φ y := ENNReal.toReal_nonneg

/-! ## 2. The per-fibre per-box residual -/

/-- **The per-fibre per-box residual.**  For a.e. good `u`, every *nonempty* slot set `S` of size
`k`, every bijection `e : SlotIn N S ≃ Fin k`, and a.e. outside configuration `y`, the fibre's box
mass times the **delivered** count-indexed per-box ground energy `Work.BlockBound4.diagWeBAt k` is
dominated by the `k`-particle word of the fibre:

    slotFibreMassReal · diagWeBAt k  ≤  tBwordBInd k … (slotFibreState …) + qLHSwordB k … .

This is FS `thm:smallbox` at the fibre — the form in which the delivered bound applies (the fibre is
a legitimate smooth box state, `contDiff_slotFibreState`) — and the sharpest named form of the
remaining analytic gap.  The parameters of the faithful word are pinned as in `SlotWordBoundDiag`
(`cgap := tbGapCoeff (L·d) ε`, `c₀ := c`), and the ambient box of the `k`-particle word is the same
`L` (so that the slot-volume normalisation `(L³)⁻¹` matches). -/
def FibreWordBound (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ) (d M : ℕ)
    (L : ℝ) (N : ℕ) (Φ : CSBox N L) (ε c B : ℝ) : Prop :=
  0 ≤ ε ∧ 0 ≤ c ∧ 0 ≤ B ∧
  ((∫ u in (goodSet L d (dens N L))ᶜ, chiMass M L d u) ≤ B) ∧
  (∀ᵐ u ∂(volume.restrict (goodSet L d (dens N L))), ∀ S : Finset (Fin N), 0 < S.card →
    ∀ e : SlotIn N S ≃ Fin S.card,
      ∀ᵐ y ∂(volume.restrict (slotOutside L (dlBox L d u) S)),
        slotFibreMassReal (dlBox L d u) S (Φ : X N → ℝ) y
            * Work.BlockBound4.diagWeBAt S.card (L * (d : ℝ)) (dens N L) v h c
                (Work.SmallBoxTBWord.tbGapCoeff (L * (d : ℝ)) ε)
          ≤ tBwordBInd S.card L d ε c u (slotFibreState S e (Φ : X N → ℝ) y)
            + qLHSwordB h M L d (dens N L) u (slotFibreState S e (Φ : X N → ℝ) y))

end Work.PerSector
