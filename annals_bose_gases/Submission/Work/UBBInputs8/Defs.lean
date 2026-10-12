import ChallengeDeps
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.LocRepoint.convScale_cube_lower
import Submission.Work.UBBInputs7.Finding.aemeasurable_marginal_lintegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.UBBInputs8.Defs` — round 8: the clause grind

Round 7 (`Submission/Work/UBBInputs7/README.md`) reduced the paper's `hpres` to the two clause
lists `AprioriClauses` (A) and `BogoliubovMinimal` (B) plus the delivered word dictionary, and
recorded, clause by clause, which members are *delivered* by the corpus and which are
*rational*.  Round 8 attacks the members.

## What round 8 adds (this directory)

**(A) the potential side — the `hpot` field and the lift clause are CLOSED.**  Round 7 kept
FS `lem:LocPotential` as a field of `BoxSumBoundCanon` (`hpot`), and split off the lift clause
`HpotLift` because the round-6 route to `hpot` (the sliding telescoping identity
`Work.SmallBoxSliding.qLHSwordB_integral_u`) needed the *joint* integrability of the localised
integrand on `ℝ³ × X N` — which `Work.UBBInputs7.Finding.not_integrable_qLHSBIntegrand_const`
refutes at the constant state.  The repair is to run the *same* identity with the integrability
taken over the *analysis box* only (`vol.prod (vol.restrict (abox N L))`):

* `A.integrable_qLHSBIntegrand_box` — the box-restricted integrand is `Integrable` for every
  *continuous* `Φ` (no support condition: continuity gives boundedness on the compact box and
  `v ∈ L¹` gives the pair term);
* `A.qLHSwordB_integral_u_box` — the telescoping identity with that weaker hypothesis (the
  delivered proof already factors through the box-restricted measure, so this is the *same*
  identity at the *correct* hypothesis);
* `A.hpotAll_of_locPotentialCorpus` — hence `HpotAll` (FS `lem:LocPotential` for **every**
  corpus trial state, no support or decay condition) from the one word comparison
  `LocPotentialCorpus`, and `A.hpotLift_holds` — the round-7 lift clause itself.

So in round 8 the (A) list loses `hlift`, loses the `hint`/`hintRef` bookkeeping and loses the
supported-state restriction: what remains is the *kernel* bundle `BoxSumBoundKernel` and the
word comparison `LocPotentialCorpus`.

**(A) the kinetic side — the Bratteli–Solovej citation, audited.**  `KineticLocalisation` is
the corpus rendering of FS `lem:LocKinEn` (cited from Bratteli–Solovej Thm 3.10 / Lemma 3.7) at
the sliding family `B(u) = dlBox ℓ d u`.  Round 8 proves the *defect* of that rendering:

* `A.dlBox_eq_empty_of_mem_farSet`, `A.boxMass_eq_zero_of_mem_farSet`,
  `A.cnPlusBoxB_const_of_mem_farSet`, `A.not_integrable_tBwordB_const` — on the far set
  `|(ℓd)•u|_∞ > ½ℓ(1+d)` the corpus box `dlBox ℓ d u` is empty, so the corpus's mean-free
  projection `boxQ` (which, unlike FS's `Q_B = 1_B − P_B`, carries **no** box indicator) acts
  as the identity: `tBwordB N ℓ d ε c u (const 1) = tbGapCoeff·N·|abox| > 0` on a set of
  infinite measure, so the *integrand of the residual is not `Integrable` at the constant state*
  whenever `ε > 0`.  Since `KineticLocalisation` quantifies over **all** `ε`, the Lean reading of
  the residual at those parameters is decided by the `integral_undef` convention (`∫ = 0` for a
  non-integrable function) and **not** by the localisation inequality it is meant to express.
  This is the round-7 disease (the corpus trial space is larger than FS's state class) appearing
  at the kinetic clause, and — unlike round 7's `hint` — it is *the same* witness state;
* `A/Defs.lean`: the **FS-faithful repair**, `boxQInd = 1_A·Φ − P_B` (FS's `Q_B` with the box
  indicator, `eq:HBU`), with `cnPlusBoxInd`, `tBwordInd`, `tBwordBInd` and the repaired residual
  `tBLocalisationInd`.  `A.tBwordBInd_const_zero`, `A.cnPlus_at_const_zero`,
  `A.tBLocalisationInd_const` verify the repaired residual at the constant state — this time for
  the *mathematical* inequality (`tBwordBInd u (const 1) = 0` identically, no convention).

**(B) the Bogoliubov side.**  The (B) layer is FS §9–11 at the box; round 8 adds
`B.twoTermErrorCov_vZero` and `B.bogoliubovMinimal_vZero`: the list is **inhabited** at the zero
potential (`Λ`, the LHY gain and the error coefficient all carry `a v = 0`), i.e. the round-7 (B)
list is not an empty hypothesis list; and `B.twoTermErrorCov_iff_sharpCoeff`, which identifies
the layer with the *sharp* two-term bound at the effective coefficient `c₁(1 − E)`, i.e. pins
the layer's error bookkeeping to the corpus's `LhyIntegral` constant.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs8

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.UBBInputs
open Work.UBBInputs2
open Work.UBBInputs4
open Work.UBBInputs5
open Work.UBBInputs6
open Work.UBBInputs7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The FS-faithful box projection (with the box indicator)

FS `eq:HBU` define the *box* condensate projection as a rank-one projection onto the box
indicator, `P_{B}φ = |B|⁻¹⟨1_B,φ⟩1_B`, and the mean-free projection as
`Q_{B}φ = 1_Bφ − P_Bφ` — **both** carry the box indicator.  The corpus's
`Work.SmallBoxTBWord.boxP`/`boxQ` carry it in neither.  The two agree on states supported in
the box but differ — decisively, see the far-set lemmas of `A` — outside it. -/

/-- **FS's `P_{B,i}`** (`= |B|⁻¹⟨1_B,·⟩1_B` in slot `i`), with the box indicator. -/
noncomputable def boxPInd (volA : ℝ) (A : Set ℝ³) {N : ℕ} (i : Fin N)
    (Φ : X N → ℝ) : X N → ℝ :=
  fun x => (1 / volA) * (∫ z in A, Φ (Function.update x i z)) * A.indicator (fun _ => 1) (x i)

/-- **FS's `Q_{B,i} = 1_{B,i} − P_{B,i}`**, with the box indicator in both terms. -/
noncomputable def boxQInd (volA : ℝ) (A : Set ℝ³) {N : ℕ} (i : Fin N)
    (Φ : X N → ℝ) : X N → ℝ :=
  fun x => A.indicator (fun _ => 1) (x i) * Φ x - boxPInd volA A i Φ x

/-- The FS-faithful excited count `n₊(B) = Σ_i‖Q_{B,i}Ψ‖²` over the ambient box. -/
noncomputable def cnPlusBoxInd (a : ℝ) (A : Set ℝ³) (volA : ℝ) {N : ℕ}
    (Ψ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∫ x in abox N a, (boxQInd volA A i Ψ x) ^ 2

/-- The FS-faithful `p`-diagonal kinetic form (the `Q_B`-projected version of
`Work.SmallBoxTBWord.tBdiagForm`). -/
noncomputable def tBdiagFormInd (a : ℝ) (A : Set ℝ³) (volA : ℝ) (χ : ℝ³ → ℝ)
    (F : ℝ → ℝ) {N : ℕ} (Ψ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ((2 * Real.pi) ^ 3)⁻¹ *
    ∫ p : ℝ³, F ‖p‖ *
      ((a ^ 3)⁻¹ * ∫ x in abox N a,
        ‖Work.SmallBoxTBWord.tBamp χ p (boxQInd volA A i Ψ) i x‖ ^ 2)

/-- The FS-faithful spectral half of `𝒯_B`. -/
noncomputable def tBwordKinInd (a : ℝ) (A : Set ℝ³) (volA : ℝ) (χ : ℝ³ → ℝ)
    (c : ℝ) {N : ℕ} (Ψ : X N → ℝ) : ℝ :=
  tBdiagFormInd a A volA χ (Submission.BoseGases.fsKinCoeff c) Ψ

/-- **`𝒯_B` with FS's box projection**: `½ε_T(1+π⁻²)⁻¹s⁻²·n₊(B) + Q_Bχ_B[√−Δ−c]₊²χ_BQ_B`. -/
noncomputable def tBwordInd (a : ℝ) (A : Set ℝ³) (volA : ℝ) (χ : ℝ³ → ℝ)
    (s ε c : ℝ) {N : ℕ} (Ψ : X N → ℝ) : ℝ :=
  Work.SmallBoxTBWord.tbGapCoeff s ε * cnPlusBoxInd a A volA Ψ
    + tBwordKinInd a A volA χ c Ψ

/-- The sliding instantiation of `tBwordInd` (the FS-faithful `𝒯_{B(u)}`). -/
noncomputable def tBwordBInd (N : ℕ) (ℓ d ε c : ℝ) (u : ℝ³) (Φ : X N → ℝ) : ℝ :=
  tBwordInd ℓ (dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u) (chiB ℓ d u) (ℓ * d) ε c Φ

/-- **The repaired (A)-kinetic clause**: FS `lem:LocKinEn` / Bratteli–Solovej Thm 3.10 with
FS's own box projection (`Q_{B(u)} = 1_{B(u)} − P_{B(u)}`).  Unlike the corpus's
`Work.SmallBoxTBWord.tBLocalisation` (whose integrand is *not* integrable at the constant state
when `ε > 0`, see `A/Defs.lean`), the FS-faithful integrand vanishes identically outside the
box, so the statement is the operator inequality it is meant to express. -/
def tBLocalisationInd (N : ℕ) (ℓ d b ε c : ℝ) (Φ : X N → ℝ) : Prop :=
  (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ +
      (∫ u : ℝ³, tBwordBInd N ℓ d ε c u Φ) ≤ kinWord N ℓ Φ

/-- The FS-faithful kinetic localisation, quantified as in round 1/2 (`KineticLocalisation`). -/
def KineticLocalisationInd (d b : ℝ) : Prop :=
  ∀ (N : ℕ) (ℓ ε c : ℝ) (Φ : X N → ℝ), tBLocalisationInd N ℓ d b ε c Φ

/-! ## 2. The round-8 (A) list

`BoxSumBoundCore` is round 2's `BoxSumBoundKernel` with the two per-state integrability fields
*dropped*: the `qLHSwordB`-field is a theorem (`A.integrable_qLHSwordB_u`), and the
`tBwordB`-field is the *witness-dependent* integrability that the round-8 finding shows cannot
hold at the constant state for `ε > 0` (it is met at `ε = 0`, where the gap term is switched
off).  So the core list is the honest mathematical content of FS `thm:smallbox` at the sliding
geometry. -/

/-- **The mathematical content of `BoxSumBoundKernel`** — the per-box trial-state/ESY bundle
with the `qLHSwordB`-integrability field *dropped*: that field is a theorem
(`A.integrable_qLHSwordB_u`, from the box-restricted integrability
`A.integrable_qLHSBIntegrand_box` by Fubini), so `A.boxSumBoundKernel_of_core` promotes this
core back to `BoxSumBoundKernel` with no extra hypothesis beyond the sliding regime data.

The remaining fields are the genuine per-state content of FS `thm:smallbox` at the sliding
geometry: the discarded-box lower bound `hlow`, the discarded mass `hmass` (delivered,
`Work.UBBInputs2.hmass_of_complMass`) and the per-box bound integrated over the good set
`hsum` (the count ↔ localised-density bridge).  The *witness-dependent* integrability of
`tBwordB` is kept as a field: it cannot be discharged uniformly in `ε` — see
`A.not_integrable_tBwordB_const`. -/
def BoxSumBoundCore (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ)
    (d M : ℕ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ → ∀ Φ : CSBox N L,
    sqNormN N L (Φ : X N → ℝ) = 1 →
    WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
    ∃ (ε c C B : ℝ),
      0 ≤ C ∧
      Integrable (fun u : ℝ³ => Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)) ∧
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

/-- **The round-8 (A) list**: the sliding geometry, FS `lem:LocKinEn` (Bratteli–Solovej
Thm 3.10) as `KineticLocalisation`, the per-box bundle `BoxSumBoundCore` (FS `thm:smallbox`)
and FS `lem:LocPotential` as the one word comparison `LocPotentialCorpus`.

Compared with round 7's `AprioriClauses`: the `hpot` field of `BoxSumBoundCanon` is supplied by
`A.hpotAll_of_locPotentialCorpus` (so it is *not* a member), the lift clause `HpotLift` is proved
(`A.hpotLift_holds`), and one of the two per-state integrability fields of `BoxSumBoundKernel`
is proved outright (`A.integrable_qLHSwordB_u`) — leaving the core bundle `BoxSumBoundCore`
together with the one word comparison `LocPotentialCorpus`.  `A.aprioriClauses_of_aprioriClauses8`
shows that this list *implies* round 7's `AprioriClauses`: it is a relaxation. -/
structure AprioriClauses8 (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ) (d M : ℕ)
    (R0 : ℝ) : Prop where
  hb : 0 < b
  ha : 0 ≤ a v
  hR' : 0 ≤ R'
  hM : 1 ≤ M
  hd : (0 : ℝ) < (d : ℝ)
  hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0
  hR0 : 0 < R0
  hdR : ∀ L : ℝ, 1 ≤ L → R0 ≤ (L * (d : ℝ)) / 16
  hv1 : MemLp v 1
  hloc : KineticLocalisation (d : ℝ) b
  hcore : BoxSumBoundCore v h b K_B R' J ε₀ d M
  hdRχ : ∀ L : ℝ, 1 ≤ L → R0 ≤ L * chiR0

/-! ## 3. The round-8 (B) side

The (B) list is round 7's; round 8 adds its *inhabitation* at the zero potential and the
effective-coefficient form of its layer. -/

/-! ## 4. The round-8 input bundle -/

/-- **The round-8 input bundle** (single window): the repaired (A) list `AprioriClauses8` at
FS's a-priori window `fsWindowC`, round 6's (B) list, and the pinning of the shared window.
`Work.UBBInputs8.Chain.hpres_of_round8Inputs` consumes it. -/
structure Round8Inputs (v : ℝ³ → ℝ) (h : ScatSol v) (J ε₀ η₀ c₁ : ℝ) (W : ℕ → ℝ → ℝ)
    (b K_B R' : ℝ) (d M : ℕ) (R0 : ℝ) (E : ℕ → ℝ → ℝ) : Prop where
  apriori : AprioriClauses8 v h b K_B R' J ε₀ d M R0
  bogoliubov : BogoliubovResiduals v h J W ε₀ η₀ c₁ E
  window : W = fsWindowC v b J K_B

end Work.UBBInputs8
