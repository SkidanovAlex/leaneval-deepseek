import ChallengeDeps
import Submission.Work.ESYStage.neuMode_integral_zero
import Submission.Work.PerSector.FibreResidual
import Submission.Work.PerSector.SlotAdditive
import Submission.Work.PerSector.aemeasurable_slotFibreMass
import Submission.Work.PerSector.sum_tBamp_normSq_slotPiece
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.SlotWord.Defs` — the slot-word (fibre) chapter: vocabulary

**Read `Submission/Work/PerSector/README.md` §6 first.**  That section names the three remaining
obligations of the `hsum` discharge:

* **(R1)** `SlotWordBoundDiag` / `FibreWordBound` — *the kernel/word comparison at the count*.  It
  splits into
  * **(R1)(a)** the **fibre factorisation of the word**: the localised per-box word of a slot piece
    is the `y`-integral of the `k`-particle word of its fibre,
    `word(slotPiece B S Φ) = ∫_y word(fibre_y)`;
  * **(R1)(b)** the **delivered bound at the fibre**: `diagWeBAt k ≤ word(fibre_y)/fibreMass_y`;
* **(R2)** the numeric input `hdel` and the volume bookkeeping (`chiMass` vs the box volume);
* **(R3)** the integrability side conditions.

This chapter supplies the vocabulary for all three and, in the sibling modules, the proved parts.

## The vocabulary of this module

* `fibreWord h M K L d ε c μ u Ψ` — **the sliding word at particle number `K`**:
  `tBwordBInd K L d ε c u Ψ + qLHSwordB h M L d μ u Ψ`.  At `K = N` and `Ψ = slotPiece …` this is
  the right-hand side of `SlotWordBoundDiag`; at `K = S.card` and `Ψ =` the fibre it is the object
  of the per-fibre residual.
* `pieceFibre B S e Φ y` — **the fibre of the slot piece**, transported to `X S.card` along `e`.
  This — and *not* the fibre of the state `Φ` — is the legitimate box state of the delivered
  bound: it vanishes off `B^{S}`, so its `L²` mass over the translated box equals
  `slotFibreMassReal B S (slotPiece B S Φ) y`; see `PerSector/README.md` §6(R1)(b).
* `WordFibreFactorisation h M L d ε c μ u N Φ` — **(R1)(a)**, as a `Prop`: for every nonempty slot
  set `S` and every `e`, the `N`-particle word of the slot piece equals the `y`-integral of the
  `S.card`-particle word of the fibre.
* `FibreWordBoundAt h M L d ε c μ N Φ β` — **(R1)(b)**, as a `Prop`: for a.e. good `u`, every
  nonempty `S`, every `e`, and a.e. outside configuration `y`,
  `fibreMass_y·β ≤ fibreWord(fibre_y)`.
* `tBdiagFibreJoint …` — the joint `(p,y)`-integrand of the spectral piece, the object whose
  integrability is the (R3)-coupling of the spectral factorisation.
* `SlotWordBoundV …` — **the residual at the delivered volume** (R2): the same shape as
  `PerSector.SlotWordBound` but with the DL threshold read at `V := (L·d)³` (the volume of the box
  side used in `diagWeBAt`) and at the full symbol
  `Γ := (R/(L·d))² + dlGamma K_B (dens N L) (a v)`, which is exactly the reading of the delivered
  `Submission.BoseGases.smallbox_dl_energy_bound_at_count`.  See `Volume.lean` and the README §R2.

## Conventions

* `ℝ³ = EuclideanSpace ℝ (Fin 3)`, `X N = Fin N → ℝ³`, `abox N L` the centred box;
* `B = dlBox L d u` is the sliding box, `boxMass L d u = |B|` its volume, `chiMass M L d u` the
  `χ`-mass of `chiSmallB M L d u`;
* `slotPiece B S Φ = 1_{slotSet B S}·Φ` and `slotFibre S Ψ y = fun z => Ψ (slotComb S z y)`;
* the parameters of the sliding word: ambient box `L`, small-box scale `d`, `𝒯_B`-gap `ε`,
  spectral cutoff `c`, chemical potential `μ`, box position `u`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SlotWord

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.PerSector
open Work.UBB
open Work.SmallBoxSliding
open Work.UBBInputs8
open Work.FockBridge

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-! ## 1. The sliding word at a general particle number -/

/-- **The sliding word of the whole chapter**, at particle number `K` and state `Ψ`:
the FS-faithful `𝒯_{B(u)}` word `Work.UBBInputs8.tBwordBInd` plus the localised potential word
`Work.SmallBoxSliding.qLHSwordB`, both at the ambient box `L`, the small-box scale `d`, the
position `u`, the gap `ε`, the spectral cutoff `c` and the chemical potential `μ`. -/
noncomputable def fibreWord {v : ℝ³ → ℝ} (h : ScatSol v) (M : ℕ) (K : ℕ)
    (L d ε c μ : ℝ) (u : ℝ³) (Ψ : X K → ℝ) : ℝ :=
  tBwordBInd K L d ε c u Ψ + qLHSwordB h M L d μ u Ψ

/-- The sliding word at the parameters of `SlotWordBoundDiag` (count `N`, density `dens N L`). -/
theorem fibreWord_diag {v : ℝ³ → ℝ} (h : ScatSol v) (M : ℕ) (L d ε c : ℝ) (u : ℝ³)
    (N : ℕ) (Ψ : X N → ℝ) :
    fibreWord h M N L d ε c (dens N L) u Ψ
      = tBwordBInd N L d ε c u Ψ + qLHSwordB h M L d (dens N L) u Ψ := rfl

/-! ## 2. The fibre of a slot piece -/

/-- **The fibre of the slot piece**, transported to `X S.card` along a bijection
`e : SlotIn N S ≃ Fin S.card`.  This is the legitimate `S.card`-particle box state of the
delivered bound: it is smooth (`PerSector.contDiff_slotFibreState`) and it vanishes off the box
`B^{S}`, so its `L²`-mass over the translated box `B(u)` is exactly the fibre mass. -/
def pieceFibre (B : Set ℝ³) (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card)
    (Φ : X N → ℝ) (y : SlotOut N S → ℝ³) : X S.card → ℝ :=
  slotFibreState S e (slotPiece B S Φ) y

theorem pieceFibre_apply (B : Set ℝ³) (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card)
    (Φ : X N → ℝ) (y : SlotOut N S → ℝ³) (x : X S.card) :
    pieceFibre B S e Φ y x = slotPiece B S Φ (slotComb S (fun i => x (e i)) y) := rfl

/-- On the box the fibre of the piece is the fibre of the state: the two differ only off `B^{S}`,
where the piece vanishes. -/
theorem pieceFibre_eq_slotFibreState {B : Set ℝ³} (S : Finset (Fin N))
    (e : SlotIn N S ≃ Fin S.card) (Φ : X N → ℝ) (y : SlotOut N S → ℝ³) (x : X S.card)
    (hz : ∀ i : SlotIn N S, x (e i) ∈ B) (hy : ∀ j : SlotOut N S, y j ∉ B) :
    pieceFibre B S e Φ y x = slotFibreState S e Φ y x := by
  rw [pieceFibre_apply, slotFibreState_apply]
  exact slotPiece_slotComb B S Φ _ y hz hy

/-- The fibre of the *state* (as opposed to of the piece) is smooth when the state is — this is
`Work.PerSector.contDiff_slotFibreState`, re-exported.  It is the smoothness that makes the fibre
an admissible `CSBox` state; the fibre *of the piece* is the indicator `1_{B^{S}}·` of it, so the
delivered bound at the fibre is applied to the state's fibre and the two are identified on the box
by `pieceFibre_eq_slotFibreState`. -/
theorem contDiff_slotFibreState' (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card)
    {Φ : X N → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (y : SlotOut N S → ℝ³) :
    ContDiff ℝ ∞ (slotFibreState S e Φ y) :=
  Work.PerSector.contDiff_slotFibreState S e hΦ y

/-! ## 3. (R1)(a): the fibre factorisation of the word -/

/-- **(R1)(a) — the fibre factorisation of the word.**  For a given `u`, state `Φ` and every
nonempty slot set `S` and bijection `e`, the `N`-particle sliding word of the slot piece equals the
`y`-integral (over the outside configurations) of the `S.card`-particle sliding word of the fibre.

The three pieces of the identity (gap / spectral / potential) are the theorems
`cnPlusBoxInd_slotFibre`, `tBdiagFormInd_slotFibre`, `qLHSword_slotFibre` of this chapter; the
spectral one carries the joint `(p,y)`-integrability of `tBdiagFibreJoint` (the (R3)-coupling). -/
def WordFibreFactorisation {v : ℝ³ → ℝ} (h : ScatSol v) (M : ℕ) (L d ε c μ : ℝ) (u : ℝ³)
    (N : ℕ) (Φ : X N → ℝ) : Prop :=
  ∀ S : Finset (Fin N), 0 < S.card → ∀ e : SlotIn N S ≃ Fin S.card,
    tBwordBInd N L d ε c u (slotPiece (dlBox L d u) S Φ)
        + qLHSwordB h M L d μ u (slotPiece (dlBox L d u) S Φ)
      = ∫ y in slotOutside L (dlBox L d u) S,
          fibreWord h M S.card L d ε c μ u (pieceFibre (dlBox L d u) S e Φ y)

/-! ## 4. (R1)(b): the delivered bound at the fibre -/

/-- **(R1)(b) — the delivered bound at the fibre** (the per-fibre residual).  For a.e. good `u`,
every nonempty slot set `S` of size `k`, every `e`, and a.e. outside configuration `y`, the local
mass of the fibre times the delivered count-indexed per-box ground energy `diagWeBAt k …` is
dominated by the `k`-particle sliding word of the fibre.

This is FS `thm:smallbox` read at the fibre: the fibre is a smooth box state
(`contDiff_pieceFibre`), so the *trial-state* (Rayleigh) direction of `diagWeBAt` applies to it;
the analytic content is the comparison of the delivered faithful word with the sliding word at the
sliding box (the `DLWire` route) together with the translation/normalisation bookkeeping between
`B(u)` and the centred cube.  See `Trial.lean` and the README §R1(b). -/
def FibreWordBoundAt {v : ℝ³ → ℝ} (h : ScatSol v) (M : ℕ) (L d ε c : ℝ) (N : ℕ)
    (Φ : X N → ℝ) (β : ℕ → ℝ) : Prop :=
  ∀ᵐ u ∂(volume.restrict (goodSet L d (dens N L))),
    ∀ S : Finset (Fin N), 0 < S.card → ∀ e : SlotIn N S ≃ Fin S.card,
      ∀ᵐ y ∂(volume.restrict (slotOutside L (dlBox L d u) S)),
        slotFibreMassReal (dlBox L d u) S (slotPiece (dlBox L d u) S Φ) y * β S.card
          ≤ fibreWord h M S.card L d ε c (dens N L) u (pieceFibre (dlBox L d u) S e Φ y)

/-! ## 4b. The joint `(p,y)`-integrand of the spectral piece -/

/-- **The joint `(p,y)`-integrand of the spectral factorisation.**  For each slot `i : Fin S.card`
it is `F ‖p‖·(L³)⁻¹·∫_{abox S.card L}‖tBamp χ_B p (Q_{B(u),i}(fibre_y)) i z‖²`, i.e. the
`p`-integrand of `tBdiagFormInd` at the fibre.  Its integrability on `ℝ³ × slotOutside` is the
(R3)-coupling of the spectral factorisation `tBdiagFormInd_slotFibre`: the Bochner convention
`∫ = 0` for a non-integrable function means the `p`-`y` exchange needs it. -/
noncomputable def tBdiagFibreJoint (L d : ℝ) (u : ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ)
    (e : SlotIn N S ≃ Fin S.card) (F : ℝ → ℝ) (p : ℝ³) (y : SlotOut N S → ℝ³) : ℝ :=
  ∑ i : Fin S.card, F ‖p‖ * ((L ^ 3)⁻¹ *
    ∫ z in abox S.card L,
      ‖Work.SmallBoxTBWord.tBamp (chiB L d u) p
          (Work.UBBInputs8.boxQInd (boxMass L d u) (dlBox L d u) i
            (pieceFibre (dlBox L d u) S e Φ y)) i z‖ ^ 2)

/-! ## 5. (R2): the residual at the delivered volume -/

/-- **The per-slot residual at the delivered volume** (the (R2)-corrected reading of
`PerSector.SlotWordBound`).  Identical to `Work.PerSector.SlotWordBound` except that

* the DL threshold is read at `V := (L·d)³` — the volume `(box side)³` of the delivered
  `Submission.BoseGases.smallbox_dl_energy_bound_at_count` at box side `L·d`, *not* at the
  `χ`-mass `chiMass M L d u`; and
* the symbol is the full `Γ := (R/(L·d))² + dlGamma K_B (dens N L) (a v)`, exactly the `Γ` of the
  delivered theorem (`dlGamma` alone is the `K_B`-part).

With this reading the delivered theorem gives the `hdel` hypothesis *verbatim* (`Volume.lean`). -/
def SlotWordBoundV (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R R' J ε₀ : ℝ) (d M : ℕ)
    (L : ℝ) (N : ℕ) (Φ : CSBox N L) (ε c C B : ℝ) : Prop :=
  0 ≤ ε ∧ 0 ≤ c ∧ 0 ≤ C ∧ 0 ≤ B ∧
  ((∫ u in (goodSet L d (dens N L))ᶜ, chiMass M L d u) ≤ B) ∧
  (∀ᵐ u ∂(volume.restrict (goodSet L d (dens N L))), ∀ S : Finset (Fin N), 0 < S.card →
    slotMass L (dlBox L d u) S (Φ : X N → ℝ)
        * dlThreshold c C (dens N L) (a v) ((L * (d : ℝ)) ^ 3)
            ((R / (L * (d : ℝ))) ^ 2 + dlGamma K_B (dens N L) (a v)) (S.card : ℝ)
      ≤ tBwordBInd N L d ε c u (slotPiece (dlBox L d u) S (Φ : X N → ℝ))
        + qLHSwordB h M L d (dens N L) u (slotPiece (dlBox L d u) S (Φ : X N → ℝ)))

end Work.SlotWord
