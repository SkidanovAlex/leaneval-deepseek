import ChallengeDeps
import Submission.Work.UBB.Assembly
import Submission.Work.UBB.wordInf_eq_eB_div
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.DLRepoint.UBBChain` — the end-to-end chain at the faithful energy

This module closes item 3 of the re-point: it runs the UBB chain *from the
faithful per-box energy* and records precisely which named inputs remain for
the lead's final wiring of `Submission.lean`'s `hpres`.

## What is built here (all PROVED)

The faithful per-box dictionary:

| name | meaning |
|---|---|
| `diagEnergy N s μ v h c₀ cgap Φ` | FS's per-box energy word at particle count `N` (`cgap·cnPlus + pDiagForm s (fsKinCoeff c₀) + qLHSword`), the `N`-indexed form of `Work.BlockBound4.diagWEnergy` |
| `diagWordDens N L μ v h c₀ cgap Φ` | its density quotient `energy / (L³·∫Φ²)` — the faithful sibling of `Work.UBB.WordDens` |
| `diagWordInf N L μ v h c₀ cgap` | the infimum of `diagWordDens` over `CSBox N L` — the faithful `Work.UBB.wordInf` |
| `diagWordInf_eq_diagWeBAt_div` | `diagWordInf = diagWeBAt N L … / L³` — the faithful sibling of `Work.UBB.wordInf_eq_eB_div` (a `sorry`-free `OrderIso` computation) |

and the assembly, mirroring `Work.UBB.Assembly` verbatim:

* `DiagSpectral v h J ε₀ η₀ c₀ cgap` — the faithful per-state spectral input
  (FS `eq:ToProve` at the faithful word);
* `DiagFSShapeE` — its infimum form (`Lambda ≤ diagWordInf`);
* `DiagWordBridge` — the faithful per-box passage to the canonical Hamiltonian
  (`diagWordInf ≤ boxEnergy/L³ − 8πaρ²`, the faithful `Work.UBB.WordBridge`);
* `diagFSShapeE_of_diagSpectral` — the dichotomy (PROVED, via
  `Work.UBB.theta_ge_lambda`/`le_ciInf`);
* `fsShape_of_diagFSShapeE` — the bridge (PROVED, one-line);
* **`UBB_of_diagInputs`** — `UBB v η₀` from the two faithful named inputs
  (`DiagWordBridge` and `DiagSpectral`) and the arithmetic `lhyC ≤ J`, via the
  delivered `Work.UBB.boxShape_iff_fsShape`;
* `diagSpectral_of_pieces` — the decomposition of `DiagSpectral` into the
  faithful a-priori window `DiagAprioriNPlus` (FS `thm:aprioriHLambda`) and the
  faithful Bogoliubov window bound `DiagBogoliubovLow` (FS §9–11) — the exact
  faithful analogue of `Work.UBB.Assembly.spectralInput_of_pieces`.

## The ledger of what remains (for the lead's `hpres` wiring)

1. **`DiagWordBridge`** — the passage from the faithful per-box word to the
   canonical box Hamiltonian (`𝓗` of `ChallengeDeps`): the faithful sibling of
   `Work.UBB.WordBridge`.  Its proof is the same corpus infrastructure (the
   `∫w₁ = 8πa` kernel normalisation, the sector/chemical-potential shift, and
   the infimum comparison) with `sboxE ↦ diagEnergy`.  NAMED.
2. **`DiagAprioriNPlus`** — the a-priori `n₊` window for faithful *low* states.
   Its arithmetic core is CLOSED (`Work.SmallBoxSliding.cnPlus_and_R_le`,
   `Work.UBB.Apriori.cnPlus_le_window_of_low`); the per-state sliding input is
   `Work.SmallBoxTBWord.Sliding.tBLocalisation` (FS `eq:BSsliding2`, the
   Bratteli–Solovej localisation) instantiated at the faithful per-box word —
   the re-point of `Work.BlockBound4/README.md` §4 item 4, where
   `Work.BlockBound4.diagWWord_le_kinWord_gap` converts the faithful word's
   localisation into the honest one, and `smallbox_dl_energy_bound`
   (`Submission/Work/SmallBoxDLBound.lean`, re-pointed, PROVED) supplies the
   per-box bound.  NAMED.
3. **`DiagBogoliubovLow`** — FS §9–11 (second quantisation + `c`-number
   substitution + Bogoliubov diagonalisation) *under* the window, at the
   faithful word: the sibling `Work.SmallBoxBogoliubov*` chapter's statement.
   This is where the sharp `lhyC = 128/(15√π)` enters; the exponent is
   `1/2 + η₀` explicitly.  NAMED.
4. **The `hEgc` side** (`eq:aprioriPsi`, the trial-state/ESY upper bound) is the
   `Work.SecondOrder`/`Work.TrialState`/ESYRound5 sibling's and is NOT touched
   here: it enters only through `DiagAprioriNPlus`'s low-state hypothesis.

With those three named inputs, `UBB_of_diagInputs` gives `Work.UBB.UBB v η₀`,
and the delivered `Work.UBB.Consumer.hpres_of_UBB` then gives the paper's
`hpres`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.DLRepoint

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The faithful per-box energy word at particle count `N`** (the `N`-indexed
form of `Work.BlockBound4.diagWEnergy`): the faithful word
`cgap·cnPlus + pDiagForm s (fsKinCoeff c₀)` plus the `qLHSword` potential word. -/
noncomputable def diagEnergy (N : ℕ) (s μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ)
    (Φ : X N → ℝ) : ℝ :=
  Work.KinPSuperadd.blockE s μ (wPairC s v) (wPairC s (g0 v h))
    (Work.KinPSuperadd.diagSlotWord s c₀ cgap) N Φ

/-- `diagEnergy` unfolds to the faithful word plus the potential word. -/
lemma diagEnergy_eq (N : ℕ) (s μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ)
    (Φ : X N → ℝ) :
    diagEnergy N s μ v h c₀ cgap Φ
      = cgap * cnPlus s Φ + pDiagForm s (fsKinCoeff c₀) Φ
        + qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
  rw [diagEnergy, Work.KinPSuperadd.blockE_eq]
  rfl

/-- **`diagWeBAt` is the infimum of `diagEnergy`-quotients** (definitional). -/
lemma diagWeBAt_eq (N : ℕ) (s μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ) :
    Work.BlockBound4.diagWeBAt N s μ v h c₀ cgap
      = ⨅ Φ : CSBox N s, diagEnergy N s μ v h c₀ cgap (Φ : X N → ℝ) /
          (∫ x in abox N s, ((Φ : X N → ℝ) x) ^ 2) := rfl

/-- **The faithful per-box density** of a box state: FS's shifted energy density
at chemical potential `μ`, `diagEnergy / (L³·∫Φ²)`.  The faithful sibling of
`Work.UBB.WordDens`. -/
noncomputable def diagWordDens (N : ℕ) (L μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ)
    (Φ : X N → ℝ) : ℝ :=
  diagEnergy N L μ v h c₀ cgap Φ / (L ^ 3 * ∫ x in abox N L, (Φ x) ^ 2)

/-- **The faithful per-box density infimum** — the faithful sibling of
`Work.UBB.wordInf`. -/
noncomputable def diagWordInf (N : ℕ) (L μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ) : ℝ :=
  ⨅ Φ : CSBox N L, diagWordDens N L μ v h c₀ cgap (Φ : X N → ℝ)

/-- **`diagWordInf` is `diagWeBAt` per unit volume** — the faithful sibling of
`Work.UBB.wordInf_eq_eB_div` (the same `OrderIso.mulRight₀` argument: the
volume normalisation is division by the positive constant `L³`). -/
theorem diagWordInf_eq_diagWeBAt_div {N : ℕ} {L μ : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) {c₀ cgap : ℝ}
    (hL : 0 < L)
    (hbd : BddBelow (Set.range (fun Φ : CSBox N L =>
      diagEnergy N L μ v h c₀ cgap (Φ : X N → ℝ) /
        (∫ x in abox N L, ((Φ : X N → ℝ) x) ^ 2)))) :
    diagWordInf N L μ v h c₀ cgap = Work.BlockBound4.diagWeBAt N L μ v h c₀ cgap / L ^ 3 := by
  haveI : Nonempty (CSBox N L) := nonempty_CSBox N hL
  have hpt : ∀ Φ : CSBox N L, diagWordDens N L μ v h c₀ cgap (Φ : X N → ℝ) =
      (diagEnergy N L μ v h c₀ cgap (Φ : X N → ℝ) /
        (∫ x in abox N L, ((Φ : X N → ℝ) x) ^ 2)) / L ^ 3 := by
    intro Φ
    unfold diagWordDens
    rw [mul_comm (L ^ 3) (∫ x in abox N L, ((Φ : X N → ℝ) x) ^ 2), div_div]
  have hword : diagWordInf N L μ v h c₀ cgap =
      ⨅ Φ : CSBox N L, (diagEnergy N L μ v h c₀ cgap (Φ : X N → ℝ) /
        (∫ x in abox N L, ((Φ : X N → ℝ) x) ^ 2)) / L ^ 3 := by
    unfold diagWordInf
    exact iInf_congr hpt
  rw [hword, diagWeBAt_eq]
  simp only [div_eq_mul_inv]
  exact ((OrderIso.mulRight₀ ((L ^ 3)⁻¹) (inv_pos.mpr (by positivity))).map_ciInf hbd).symm

/-! ## The faithful named inputs and the assembly -/

/-- **The faithful bridge (named input)** — the faithful per-box density
infimum is below the canonical box-energy density minus the exact chemical
potential shift `8π(a v)ρ²`.  The faithful sibling of `Work.UBB.WordBridge`. -/
def DiagWordBridge (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (c₀ cgap : ℝ) : Prop :=
  ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ,
    diagWordInf N L (Work.UBB.dens N L) v h c₀ cgap
      ≤ boxEnergy N L v / L ^ 3 - 8 * π * (a v) * (Work.UBB.dens N L) ^ 2

/-- **The faithful per-state spectral input (named input)** — FS `eq:ToProve` at
Door 4's faithful word: every *low* faithful box state already obeys FS's
`thm:LHY-Box` bound. -/
def DiagSpectral (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (J ε₀ η₀ c₀ cgap : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, Work.UBB.dens N L * (a v) ^ 3 ≤ ε₀ →
      ∀ Φ : CSBox N L,
        diagWordDens N L (Work.UBB.dens N L) v h c₀ cgap (Φ : X N → ℝ)
            ≤ Work.UBB.Theta (a v) J (Work.UBB.dens N L) →
        Work.UBB.Lambda (a v) C η₀ (Work.UBB.dens N L)
          ≤ diagWordDens N L (Work.UBB.dens N L) v h c₀ cgap (Φ : X N → ℝ)

/-- **The faithful `FSShapeE`**: FS's box theorem at the corpus per-box level,
for the faithful density infimum. -/
def DiagFSShapeE (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (C ε₀ η₀ c₀ cgap : ℝ) : Prop :=
  ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, Work.UBB.dens N L * (a v) ^ 3 ≤ ε₀ →
    Work.UBB.Lambda (a v) C η₀ (Work.UBB.dens N L)
      ≤ diagWordInf N L (Work.UBB.dens N L) v h c₀ cgap

/-- **`DiagFSShapeE` from the faithful per-state spectral input** — the faithful
analogue of `Work.UBB.Assembly.fsShapeE_of_inputs` and of
`Work.UBB.lambda_le_wordInf_of_spectral`: the low states are handled by the
spectral input, the rest already dominate the threshold `Theta ≥ Lambda`
(`Work.UBB.theta_ge_lambda`). -/
theorem diagFSShapeE_of_diagSpectral {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {J ε₀ η₀ c₀ cgap : ℝ} (hA : 0 ≤ a v) (hJ : Work.UBB.lhyC ≤ J)
    (hspec : DiagSpectral v h J ε₀ η₀ c₀ cgap) :
    ∃ C : ℝ, 0 ≤ C ∧ DiagFSShapeE v h C ε₀ η₀ c₀ cgap := by
  obtain ⟨C, hC, hspec⟩ := hspec
  refine ⟨C, hC, ?_⟩
  intro L hL N hN
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL
  haveI : Nonempty (CSBox N L) := nonempty_CSBox N hLpos
  have hρ : 0 ≤ Work.UBB.dens N L := Work.UBB.dens_nonneg N hLpos.le
  have hkey : Work.UBB.Lambda (a v) C η₀ (Work.UBB.dens N L)
      ≤ Work.UBB.Theta (a v) J (Work.UBB.dens N L) :=
    Work.UBB.theta_ge_lambda hA hρ hC hJ
  unfold diagWordInf
  refine le_ciInf (fun Φ => ?_)
  by_cases hlow : diagWordDens N L (Work.UBB.dens N L) v h c₀ cgap (Φ : X N → ℝ)
      ≤ Work.UBB.Theta (a v) J (Work.UBB.dens N L)
  · exact hspec L hL N hN Φ hlow
  · exact le_trans hkey (le_of_lt (not_le.mp hlow))

/-- **The bridge step**: the faithful `DiagFSShapeE` plus the faithful
`DiagWordBridge` give FS's `FSShape` (the Hamiltonian shape). -/
theorem fsShape_of_diagFSShapeE {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {C ε₀ η₀ c₀ cgap : ℝ} (hE : DiagFSShapeE v h C ε₀ η₀ c₀ cgap)
    (hbr : DiagWordBridge v h c₀ cgap) : Work.UBB.FSShape v (a v) C ε₀ η₀ := by
  intro L hL N hN
  linarith [hE L hL N hN, hbr L hL N]

/-- **`UBB` from the faithful named inputs** — the headline of the re-point's
end-to-end chain: with `0 < ε₀`, `0 ≤ a v`, `lhyC ≤ J`, the faithful bridge and
the faithful per-state spectral input, the uniform dilute box bound `UBB v η₀`
holds.  (The passage to the canonical `BoxShape`/`lhyRhs` normalisation is the
delivered `Work.UBB.boxShape_iff_fsShape`.) -/
theorem UBB_of_diagInputs {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {J ε₀ η₀ c₀ cgap : ℝ} (hε₀ : 0 < ε₀) (hA : 0 ≤ a v) (hJ : Work.UBB.lhyC ≤ J)
    (hbridge : DiagWordBridge v h c₀ cgap)
    (hspec : DiagSpectral v h J ε₀ η₀ c₀ cgap) :
    Work.UBB.UBB v η₀ := by
  obtain ⟨C, hC, hE⟩ := diagFSShapeE_of_diagSpectral hA hJ hspec
  exact ⟨ε₀, hε₀, C, hC, Work.UBB.boxShape_iff_fsShape.mpr
    (fsShape_of_diagFSShapeE hE hbridge)⟩

/-! ## The decomposition of `DiagSpectral` (the ledger of named inputs) -/

/-- **The faithful a-priori `n₊` window (named input)** — FS
`thm:aprioriHLambda`/`eq:apriorinn+` for faithful *low* states. -/
def DiagAprioriNPlus (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (J : ℝ)
    (W : ℕ → ℝ → ℝ) (ε₀ c₀ cgap : ℝ) : Prop :=
  ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, Work.UBB.dens N L * (a v) ^ 3 ≤ ε₀ →
    ∀ Φ : CSBox N L,
      diagWordDens N L (Work.UBB.dens N L) v h c₀ cgap (Φ : X N → ℝ)
          ≤ Work.UBB.Theta (a v) J (Work.UBB.dens N L) →
      cnPlus L (Φ : X N → ℝ) ≤ W N L

/-- **The faithful Bogoliubov window bound (named input)** — FS §9–11 at the
faithful word: below the shared window `W`, a low state's faithful energy
density is at least `Lambda`. -/
def DiagBogoliubovLow (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (J : ℝ)
    (W : ℕ → ℝ → ℝ) (ε₀ η₀ c₀ cgap : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, Work.UBB.dens N L * (a v) ^ 3 ≤ ε₀ →
      ∀ Φ : CSBox N L,
        cnPlus L (Φ : X N → ℝ) ≤ W N L →
        diagWordDens N L (Work.UBB.dens N L) v h c₀ cgap (Φ : X N → ℝ)
            ≤ Work.UBB.Theta (a v) J (Work.UBB.dens N L) →
        Work.UBB.Lambda (a v) C η₀ (Work.UBB.dens N L)
          ≤ diagWordDens N L (Work.UBB.dens N L) v h c₀ cgap (Φ : X N → ℝ)

/-- **The decomposition of the faithful spectral input** — the exact faithful
analogue of `Work.UBB.Assembly.spectralInput_of_pieces`: the a-priori window
produces exactly the `n₊`-hypothesis the Bogoliubov window bound consumes. -/
theorem diagSpectral_of_pieces {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {J ε₀ η₀ c₀ cgap : ℝ} {W : ℕ → ℝ → ℝ}
    (ha1 : DiagAprioriNPlus v h J W ε₀ c₀ cgap)
    (ha2 : DiagBogoliubovLow v h J W ε₀ η₀ c₀ cgap) :
    DiagSpectral v h J ε₀ η₀ c₀ cgap := by
  obtain ⟨C, hC, hlow⟩ := ha2
  refine ⟨C, hC, ?_⟩
  intro L hL N hN Φ hΦ
  exact hlow L hL N hN Φ (ha1 L hL N hN Φ hΦ) hΦ

/-! ## The a-priori layer at the faithful energy (FS `thm:aprioriHLambda`)

The DL bound feeds the a-priori step: a *low* state's faithful energy density
plus the sliding localisation controls its excited count.  Everything here is
the verbatim faithful transcription of `Work.UBB.Apriori`
(`energyWord_le_of_wordDens_le`, `cnPlus_le_window_of_low`,
`aprioriNPlus_of_state`), with `Work.SmallBoxSliding.cnPlus_and_R_le` (CLOSED
corpus arithmetic) on the faithful energy word. -/

/-- The faithful energy *word* of a box state (the numerator of `diagWordDens`
times `L³`): the faithful sibling of `Work.UBB.EnergyWord`. -/
noncomputable def diagEnergyWord (N : ℕ) (L μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ)
    (Φ : CSBox N L) : ℝ :=
  diagEnergy N L μ v h c₀ cgap (Φ : X N → ℝ) /
    (∫ x in abox N L, ((Φ : X N → ℝ) x) ^ 2)

/-- `diagWordDens` is `diagEnergyWord` per unit volume. -/
lemma diagWordDens_eq (N : ℕ) (L μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ)
    (Φ : CSBox N L) :
    diagWordDens N L μ v h c₀ cgap (Φ : X N → ℝ)
      = diagEnergyWord N L μ v h c₀ cgap Φ / L ^ 3 := by
  unfold diagWordDens diagEnergyWord
  rw [mul_comm (L ^ 3) (∫ x in abox N L, ((Φ : X N → ℝ) x) ^ 2), div_div]

/-- **The low-state condition in energy form** — the faithful sibling of
`Work.UBB.energyWord_le_of_wordDens_le`. -/
theorem diagEnergyWord_le_of_low {N : ℕ} {L μ : ℝ} {v : ℝ³ → ℝ}
    {h : Work.UBB.ScatSol v} {c₀ cgap J : ℝ} (hL : 0 < L) {Φ : CSBox N L}
    (hΦ : diagWordDens N L μ v h c₀ cgap (Φ : X N → ℝ)
        ≤ Work.UBB.Theta (a v) J μ) :
    diagEnergyWord N L μ v h c₀ cgap Φ
      ≤ -4 * π * μ ^ 2 * (a v) * L ^ 3 * (1 - J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) := by
  have hL3 : 0 < L ^ 3 := pow_pos hL 3
  rw [diagWordDens_eq] at hΦ
  rw [Work.UBB.Theta] at hΦ
  rw [Real.sqrt_eq_rpow] at hΦ
  rw [div_le_iff₀ hL3] at hΦ
  have hkey : -(4 * π * μ ^ 2 * (a v) * (1 - J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) * L ^ 3
      = -4 * π * μ ^ 2 * (a v) * L ^ 3 * (1 - J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) := by
    ring
  rwa [hkey] at hΦ

/-- **The faithful per-state sliding localisation (named input)** — FS
`eq:BSsliding2` instantiated at Door 4's faithful per-box word: the energy of a
low state dominates `(b/2L²)·cnPlus` plus the sliding average of the per-box
energies minus the `4πρ²a`-background with the FS error bracket.

Its proof is the re-point of `Work.BlockBound4/README.md` §4 item 4: the
sliding-sum identity of `Work.SmallBoxSliding` at the faithful per-box word,
with `smallbox_dl_energy_bound` (PROVED, re-pointed) supplying the per-box
bound and `Work.BlockBound4.diagWWord_le_kinWord_gap` converting the faithful
localisation into the honest one. -/
def DiagSlide (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (b K_B R' J ε₀ c₀ cgap : ℝ) : Prop :=
  ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, Work.UBB.dens N L * (a v) ^ 3 ≤ ε₀ →
    ∀ Φ : CSBox N L,
      diagWordDens N L (Work.UBB.dens N L) v h c₀ cgap (Φ : X N → ℝ)
          ≤ Work.UBB.Theta (a v) J (Work.UBB.dens N L) →
      R' + (b / (2 * L ^ 2)) * cnPlus L (Φ : X N → ℝ)
          - 4 * π * (Work.UBB.dens N L) ^ 2 * (a v) * L ^ 3
              * (1 + K_B ^ 3 * (Work.UBB.dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ))
        ≤ diagEnergyWord N L (Work.UBB.dens N L) v h c₀ cgap Φ

/-- **The faithful a-priori window from the per-state sliding localisation** —
the verbatim faithful analogue of `Work.UBB.Apriori.aprioriNPlus_of_state`: the
low-state condition and the sliding inequality give
`cnPlus ≤ (2L²/b)·4πρ²(a v)L³(J+K_B³)(ρ(a v)³)^{1/2}`, i.e. FS
`eq:apriorinn+`'s excited-count window. -/
theorem diagAprioriNPlus_of_slide {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {J b K_B ε₀ R' c₀ cgap : ℝ} (hb : 0 < b) (ha : 0 ≤ a v) (hR' : 0 ≤ R')
    (hslide : DiagSlide v h b K_B R' J ε₀ c₀ cgap) :
    DiagAprioriNPlus v h J
      (fun N L => (2 * L ^ 2 / b) * (4 * π * (Work.UBB.dens N L) ^ 2 * (a v) * L ^ 3
        * (J + K_B ^ 3) * (Work.UBB.dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ))) ε₀ c₀ cgap := by
  intro L hL N hN Φ hΦ
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL
  have hE := diagEnergyWord_le_of_low (v := v) (h := h) (c₀ := c₀) (cgap := cgap)
    (J := J) (μ := Work.UBB.dens N L) hLpos hΦ
  have hcn : 0 ≤ cnPlus L (Φ : X N → ℝ) := Work.SmallBoxSliding.cnPlus_nonneg L
  have hmain := Work.SmallBoxSliding.cnPlus_and_R_le (N := N) (ℓ := L)
    (μ := Work.UBB.dens N L) (b := b) hLpos hb (a := a v) (R := R') (J := J)
    (K_B := K_B) ha hR' hcn hE (hslide L hL N hN Φ hΦ)
  have hne : (0 : ℝ) < 2 * L ^ 2 / b := by positivity
  have h2 : (b / (2 * L ^ 2)) * cnPlus L (Φ : X N → ℝ)
      ≤ 4 * π * (Work.UBB.dens N L) ^ 2 * (a v) * L ^ 3 * (J + K_B ^ 3)
        * (Work.UBB.dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ) := by
    linarith [hmain.1, hR']
  have h3 := mul_le_mul_of_nonneg_left h2 hne.le
  have heq : (2 * L ^ 2 / b) * ((b / (2 * L ^ 2)) * cnPlus L (Φ : X N → ℝ))
      = cnPlus L (Φ : X N → ℝ) := by
    field_simp
  rwa [heq] at h3

end Work.DLRepoint
