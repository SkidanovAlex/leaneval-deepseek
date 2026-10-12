import ChallengeDeps
import Submission.Work.SmallBoxA0.VZero
import Submission.Work.UBBInputs.Chain
import Submission.Work.UBBInputs.Comparison
import Submission.Work.UBBInputs.Shape
import Submission.Work.UBBInputs.shape.slidingSumData_forces_Rprime_nonpos
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.UBBInputs2` — round 2 of the UBB inputs: the three residuals

The previous round (`Submission/Work/UBBInputs/`, read `README.md` there first)
delivered the three non-ESY inputs of `Work.DLWire.hpres_of_dlSlide` in their
normalisation-correct (covariant) form and reduced them to four named
propositions, each a hypothesis of a proved theorem:

| residual | FS reference | module |
|---|---|---|
| `WordBridgeResidual` | `thm:CompareBoxEnergy` + `eq:CompareGC` | `WordBridgeFile` |
| `SlidingLocalisation` | `eq:BSsliding2` (cited from Bratteli–Solovej Thm 3.10, = FS `lem:LocKinEn`) | `Defs` |
| `BoxSumBound` | the corpus-side half of `eq:BSsliding2` | `Defs` |
| `BogoliubovLowCov` / `BogoliubovGain` | FS §9–11 | `Defs`/`Bogoliubov` |

**This round's job** is to *close* those residuals from the delivered corpus
pieces — or, where the analytic content is not in the corpus, to reduce each of
them to a strictly smaller residual at the corpus's own objects, with the
reduction **proved**, and to name the irreducible stage honestly.

## What this chapter adds

### Residual (1) `WordBridgeResidual` — closed *by elimination* (Route H)

FS's own route to `thm:CompareBoxEnergy` is the operator localisation
`H_{μ,N}(Ω) ≥ ∫_u (H_{Λ,u}(μ))_N du ≥ (ℓ^{-3}|Ω+B(0,ℓ/2)|)·E_Λ(μ)` (FS's proof
of `thm:CompareBoxEnergy`, using `lem:LocKinEn` + `lem:LocPotential`), and
`eq:CompareGC` is the variational identity
`⟨Ψ,H_NΨ⟩ = ⟨Ψ,H_{μ,N}Ψ⟩ + 8πaμN` read at `μ = ρ`.  The corpus's delivered
grand-canonical interface `Submission.UBBtoGc.hpres_of_UBB` /
`Work.UBB.Consumer.hpres_of_spectralH` runs `hpres` directly from the
**Hamiltonian**-carrier input `Work.UBB.SpectralInputH` — no word/Hamiltonian
dictionary, hence no (1).  So (1) is *unnecessary* once (2) and (3) are stated
at the Hamiltonian, which is also the normalisation FS actually use
(`eq:aprioriPsi` is an inequality on `⟨Ψ,H_Λ(μ)Ψ⟩`).  This chapter:

* introduces the Hamiltonian-carrier inputs `LowStateH` (FS `eq:aprioriPsi`),
  `AprioriNPlusH` (FS `eq:apriorinn+`, conjunct 2), `BogoliubovLowH`,
  `BogoliubovWindowedH` (FS §9–11 under the window alone), `DLSlideCovH`
  (FS `eq:BSsliding2` at the Hamiltonian) and `LocMatricesResidual`
  (FS §7 `lem:LocMatrices`);
* proves the *arithmetic* chain
  `DLSlideCovH ⟹ AprioriNPlusH` (FS's `eq:BSsliding2 ⟹ eq:apriorinn+`),
  `AprioriNPlusH + BogoliubovLowH ⟹ SpectralInputH`,
  `LocMatricesResidual + BogoliubovWindowedH ⟹ SpectralInputH`
  (the `eq:LargeMatricesNew` absorption step),
  and hence `UBB` and `hpres` (`Chain.lean`) — all through the DELIVERED
  interfaces, i.e. exactly the "grand-canonical/pressure" route of the brief.

### Residual (2) `SlidingLocalisation` + `BoxSumBound` — canonicalised

* `KineticLocalisation d b` names FS `lem:LocKinEn` (Bratteli–Solovej Thm 3.10)
  **once**: it is literally the corpus's `Work.SmallBoxTBWord.tBLocalisation`
  quantified over all box data, and the *same* proposition is FS's kinetic
  localisation at *every* scale (the big box of `thm:CompareBoxEnergy` and the
  small boxes of `eq:BSsliding2`) — recorded in `KineticLocalisation.lean` with
  the no-substitute analysis of `Work/SmallBoxTBWord/NOTES.md` §4.
* `BoxSumBoundCanon` — the canonicalisation of `BoxSumBound`: the free per-box
  energy word `eBf` is **fixed** to the localised corpus word
  `tBwordB u + qLHSwordB u`, which makes the `hbox` field definitional (the
  direction fix flagged by `UBBInputs/Comparison.lean`), and two more fields
  (`Integrable chiMass`, and — in `BoxSumBoundCount` — the discarded-mass
  bound) are *discharged* from the CLOSED corpus lemmas
  `Work.SmallBoxSliding.integrable_chiSmallB_mass` and
  `Work.SmallBoxSliding.compl_mass_le`.  Both directions of the canonicalisation
  are proved (`Canonical.lean`).

### Residual (3) `BogoliubovLowCov` / `BogoliubovGain` — split at `lem:LocMatrices`

`Bogoliubov.lean` states FS §9–11 at the Hamiltonian, in the *gain* form (the
sharp `lhyC` additive over the free background `−4πρ²(a v)`), and proves the
absorption arithmetic behind FS's `eq:LargeMatricesNew`: the located state's
energy loss `4πρ²(a v)K̃(ρ(a v)³)^{1/2+η₀}L³` is *exactly* the shift of the
coefficient `C ↦ C + K̃` in `Λ`.  Hence
`LocMatricesResidual + BogoliubovWindowedH ⟹ SpectralInputH`, with
`BogoliubovWindowedH` being FS §9–11 with the window hypothesis only — the form
in which the delivered D1/`w₂`-mass/`LhyIntegral` per-small-box layers enter.

## Single import point

`import Submission.Work.UBBInputs2.All`.
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

/-! ## 0. The covariant normalisation slot -/

/-- The squared **box norm** `⟪Ψ,Ψ⟫_{N,L} = ∫_{box N L} Ψ²` of a canonical box
state — the denominator of `Work.UBB.Rayl`, and hence the correct covariant
normalisation for the excited-count window (FS's `eq:apriorinn+` is stated for
*normalised* states; for an arbitrary state its content is
`cnPlus ≤ W·⟪Ψ,Ψ⟫`). -/
noncomputable def boxSq (N : ℕ) (L : ℝ) (Ψ : CInfty0Box N L) : ℝ :=
  ∫ x in box N L, ((Ψ : X N → ℝ) x) ^ 2

/-- `⟪Ψ,Ψ⟫_{N,L} > 0` for a corpus box state. -/
theorem boxSq_pos {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) :
    0 < boxSq N L Ψ := by
  simpa only [boxSq] using box_integral_sq_pos (N := N) (L := L) hL Ψ

/-! ## 1. The shared kinetic localisation (FS `lem:LocKinEn`, BS Thm 3.10) -/

/-- **The kinetic localisation, named once** — FS `lem:LocKinEn`
(*"It was proved in [BS] Theorem 3.10 that …"*; FS cite Lemma 3.7 of
Bratteli–Solovej for the estimate `∫_u 𝒯_u du ≤ −Δ`), in the corpus's own
shape `Work.SmallBoxTBWord.tBLocalisation`:

    (b/2ℓ²)·cnPlus ℓ Φ + ∫_u 𝒯_{B(u)}(Φ) du ≤ kinWord N ℓ Φ ,

quantified over the particle number, the box side, the cutoff parameters and
the state.  `Work/SmallBoxTBWord/NOTES.md` §4 records (with machine-checked
support: `Free.kinWordB_projection_free`,
`SmallBoxSliding.kinWordBoxInd_integral_u`) why this is *not* a word-level
consequence of anything in the corpus and why it is the one genuinely external
input: the `Q_B`-projection is free for the slot derivative and the plain
indicator-box kinetic integrates *exactly* to `kinWord`, so the room for the
gap `(b/2ℓ²)cnPlus` comes only from the spectral cutoff and the functional
calculus of `√−Δ` with the sliding `Q_{B(u)}`-projections (BS Lemma 3.3).

It is *the same proposition* that `WordBridgeResidual`'s proof
(`WordBridgeResidual` = a per-state version of FS `thm:CompareBoxEnergy`,
which FS prove from `lem:LocKinEn` + `lem:LocPotential`) and
`SlidingLocalisation` (FS `eq:BSsliding2`, the same localisation applied
inside `Λ`) both consume: FS's `lem:LocKinEn` is stated for every `ℓ`. -/
def KineticLocalisation (d b : ℝ) : Prop :=
  ∀ (N : ℕ) (L ε c : ℝ) (Φ : X N → ℝ),
    Work.SmallBoxTBWord.tBLocalisation N L d b ε c Φ

/-- `KineticLocalisation` **is** `SlidingLocalisation` (the round-1 name) —
they are the same quantified proposition, recorded here so that a caller can
use either name for the *single* external input. -/
theorem kineticLocalisation_iff_slidingLocalisation (d b : ℝ) :
    KineticLocalisation d b ↔ SlidingLocalisation d b := Iff.rfl

/-! ## 2. The Hamiltonian-carrier vocabulary (FS's own normalisation) -/

/-- **FS's a-priori low-state condition `eq:aprioriPsi`** at the canonical box
Hamiltonian: the state's `H_Λ(ρ)`-expectation (`ρ := dens N L`, so that the
chemical potential is the box density `N/L³`)

    ⟨Ψ, H_Λ(ρ)Ψ⟩ = ⟨Ψ,H_N Ψ⟩ − 8π(a v)ρN = Rayl N L v Ψ − 8π(a v)ρ²L³

is at most the FS threshold `−4πρ²(a v)L³(1 − J(ρ(a v)³)^{1/2})`.  (The
`L³`-multiple of `Theta`; `lowStateH_iff_density` in `Arith.lean` shows this is
the density form `Rayl/L³ − 8π(a v)ρ² ≤ Theta (a v) J ρ`.) -/
def LowStateH (v : ℝ³ → ℝ) (N : ℕ) (L J : ℝ) (Ψ : CInfty0Box N L) : Prop :=
  Rayl N L v Ψ - 8 * π * (a v) * (dens N L) ^ 2 * L ^ 3
    ≤ Theta (a v) J (dens N L) * L ^ 3

/-- **FS `eq:BSsliding2` at the Hamiltonian, as consumed by the a-priori
bound** — the per-state sliding inequality of FS `thm:aprioriHLambda` step 2.
Two FS ingredients sit inside it: the *operator* localisation
`H_Λ(μ) ≥ (b/2)ℓ⁻²Q_Λ + ∫_u H_{B(u)}(m(u)μ)du` (FS `lem:LocKinEn`,
Bratteli–Solovej Thm 3.10) and the application of the *per-box* bound
`thm:smallbox` to each `H_{B(u)}` (whence the explicit background
`−4πρ²(a v)L³(1+K_B³√(ρ(a v)³))`).  Written with the corpus word replaced by
the canonical shifted box energy:
`R' + (b/2L²)cnPlus − 4πρ²(a v)L³(1+K_B³(ρ(a v)³)^{1/2}) ≤ ⟨Ψ,H_Λ(ρ)Ψ⟩`.
This is the form in which FS state `thm:aprioriHLambda` step 2 (their `Ψ` is a
normalised box state and their Hamiltonian is `H_Λ(μ)`), so no
word/Hamiltonian dictionary (residual (1)) is needed to *state* it. -/
def DLSlideCovH (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
    ∀ Ψ : CInfty0Box N L, LowStateH v N L J Ψ →
      R' + (b / (2 * L ^ 2)) * (cnPlus L (Ψ : X N → ℝ) / boxSq N L Ψ)
        - 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
            * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ))
        ≤ Rayl N L v Ψ - 8 * π * (a v) * (dens N L) ^ 2 * L ^ 3

/-- **FS `eq:apriorinn+`, second conjunct, at the Hamiltonian**: a low box state
has at most `W N L` excited particles.  (`W` is shared with the Bogoliubov
input; `Chain.lean` instantiates it at the FS window `fsWindow v b J K_B`.) -/
def AprioriNPlusH (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ : ℝ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
    ∀ Ψ : CInfty0Box N L, LowStateH v N L J Ψ →
      cnPlus L (Ψ : X N → ℝ) ≤ W N L * boxSq N L Ψ

/-- **FS §9–11 at the Hamiltonian, under the shared window** (second
quantisation `prop:Hamilton2ndQuant`, `c`-number substitution `thm:Kafz`,
Bogoliubov diagonalisation `thm:BogHamDiag`/`lem:BogIntegral`,
`thm:Control3Q`): a low state inside the `n₊`-window has shifted energy
`≥ Λ·L³`.  This is `Work.UBB.SpectralInputH` with the window hypothesis. -/
def BogoliubovLowH (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ η₀ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
      ∀ Ψ : CInfty0Box N L,
        cnPlus L (Ψ : X N → ℝ) ≤ W N L * boxSq N L Ψ → LowStateH v N L J Ψ →
        Lambda (a v) C η₀ (dens N L) * L ^ 3
          ≤ Rayl N L v Ψ - 8 * π * (a v) * (dens N L) ^ 2 * L ^ 3

/-- **FS §9–11 at the Hamiltonian with the window hypothesis ONLY** — i.e. the
Bogoliubov bound for the *localised* state produced by `lem:LocMatrices`
(FS §9–11 is applied after the localisation, at the start of the proof of
`thm:LHY-Box`).  This is the form in which the delivered per-small-box D1 /
`w₂`-mass / `LhyIntegral` layers enter (the passage from the small-box
analysis to this box-level statement is the one layer *not* in the corpus:
FS §9–10 read at the box scale). -/
def BogoliubovWindowedH (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ η₀ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
      ∀ Ψ : CInfty0Box N L,
        cnPlus L (Ψ : X N → ℝ) ≤ W N L * boxSq N L Ψ →
        Lambda (a v) C η₀ (dens N L) * L ^ 3
          ≤ Rayl N L v Ψ - 8 * π * (a v) * (dens N L) ^ 2 * L ^ 3

/-- **FS §7 `lem:LocMatrices`** (`thm:Localizing large matrices` of
Liebs–Solovej, the only estimate in FS that depends on `∫v` and not only on
`a`): from a low box state `Ψ` one obtains a normalised box state `Ψloc` whose
excited count is inside the window `W`, at an energy cost which in FS's
`eq:EnergyBound` is `CK_M^{-2}μ²ℓ³(μa³)^{1/2}∫v` and which appears in
`eq:LargeMatricesNew` as `CX²R·μ²aℓ³(μa³)^{1/2}`.

The error is carried here at the exponent `1/2 + η₀` — the exponent of the
target `Λ`'s error term — because that is exactly what the absorption
`C ↦ C + K̃` of `Arith.lean` consumes (FS's "the error term is consistent with
the error term in Theorem `LHY-Box`"; the reduction of the exponent `1/2` error
to `1/2+η₀` is the *same* absorption that turns FS's `X²R(μa³)^{1/2}` into an
admissible error, and is recorded in `Bogoliubov.lean` §"no-a-priori-bound"). -/
def LocMatricesResidual (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ η₀ : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
      ∀ Ψ : CInfty0Box N L, LowStateH v N L J Ψ →
        ∃ Psit : CInfty0Box N L,
          Rayl N L v Psit
              ≤ Rayl N L v Ψ
                + 4 * π * (dens N L) ^ 2 * (a v) * K
                    * (dens N L * (a v) ^ 3) ^ (1 / 2 + η₀) * L ^ 3
          ∧ cnPlus L (Psit : X N → ℝ) ≤ W N L * boxSq N L Psit

/-! ## 3. The gain form of the Hamiltonian Bogoliubov bound -/

/-- **FS §9–11 at the Hamiltonian in the *gain* form**: the sharp LHY constant
`lhyC = 128/(15√π)` sits *additively* over the free background
`−4πρ²(a v)L³`, with the only rigid data being `lhyC` and the exponent
`1/2 + η₀` (the coefficient `K` is free). -/
def BogoliubovGainH (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ η₀ : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
      ∀ Ψ : CInfty0Box N L,
        cnPlus L (Ψ : X N → ℝ) ≤ W N L * boxSq N L Ψ → LowStateH v N L J Ψ →
        - (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3)
          + 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 * lhyC
              * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)
          - 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 * K
              * (dens N L * (a v) ^ 3) ^ (1 / 2 + η₀)
          ≤ Rayl N L v Ψ - 8 * π * (a v) * (dens N L) ^ 2 * L ^ 3

end Work.UBBInputs2
