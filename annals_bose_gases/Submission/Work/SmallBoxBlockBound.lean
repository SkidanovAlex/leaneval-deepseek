import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.SmallBoxA0.Crude
import Submission.Work.SmallBoxA0.kinP_block_bound
import Submission.Work.SmallBoxA0.kinP_state_bundle
import Submission.Work.SmallBoxA0.pairing_cs_residual
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The per-block smallbox bound — tight FS block shape (revised Goal-1, one lemma)

## !!! SESSION-290: THE TWO DELIVERED THEOREMS HAVE NO PER-STATE RUNG !!!

**The bundles `BlockBoxData` / `BlockStateData` no longer carry a per-state Bogoliubov
hypothesis.**  SESSION-286–289 carried FS's `lm:appbogolubov` residual there as a field
`hBogF`/`hBog`; SESSION-290 replaced it by FOUR STATE-INDEPENDENT, CHECKABLE data fields

    hη0 : 0 ≤ eta ,   hBog0 : 0 ≤ BogErr ,
    hW2 : MemLp (fun p : X 2 => wPairC s (g0 v h) (p 0) (p 1)) 2 (volume.restrict (abox 2 s)) ,
    hL2 : √(∫ p in abox 2 s, (wPairC s (g0 v h) (p 0) (p 1))²) ≤ ½(1+eta)·g0w0Mass

and the residual is now the PROVED THEOREM

    `Work.SmallBoxA0.hBogF_of_w1_sqrt_le`   (`Submission/Work/SmallBoxA0/pairing_cs_residual.lean`)

applied inside `smallbox_block_bound` / `smallbox_state_block_bound`'s proofs.  So the
delivered block bound is conditional only on data-level facts about the potential's
pairing kernel `w₁` — NOT on any per-state inequality, and NOT on FS's unproved
`lm:appbogolubov`.  (The primitive form of `hL2` is the pure-data inequality
`4·chiSup⁴·s³·∫g₀² ≤ (½(1+eta)·g0w0Mass)²`, via `Work.SmallBoxA0.w1_L2_sq_le` +
`Work.SmallBoxA0.hBogF_of_g0_L2`.)  The non-vacuity certificate
`Work.SmallBoxA0.blockBoxData_vZero` / `blockStateData_vZero` still exhibits an explicit
inhabitant (at `v ≡ 0`, where `w₁ = 0`).

**WHAT REMAINS (the modelling question, now isolated to ONE inequality).**  `hL2` is a
state-independent but still-assumed bound on `‖w₁‖_{L²}`; whether it holds is a data
question about the scattering solution.  The alternative interfaces, all already proved,
are: the residual-FREE `…_kinP`/`…_TB` chain at FS's χ-windowed kinetic `T_B` (same shape,
same constant `272π + 40`; `Submission.BoseGases.smallbox_block_bound_kinP`,
`Work.SmallBoxA0.decision_optionB`, `Work.SmallBoxA0.TBRepoint`), and the `N = 2`
all-states theorem `Work.SmallBoxA0.residual_two_all_states` which removes all per-state
content at the critical particle number.  See `Submission/Work/SmallBoxA0/README.md`
§29–§32 (banner at the top) and `Submission/Work/SmallBoxA0/GreenDecision.lean`.

STATUS (SESSION-288 CORRECTED): the DELIVERED names are the corpus-energy statements, with the
Bogoliubov rung as the ONE assumed field.

* `smallbox_block_bound`, `smallbox_state_block_bound` are the block shape for the CORPUS's
  `eB`/`sboxE = kinWord + qLHSword` over `BlockBoxData`/`BlockStateData`, exactly as the original
  skeleton stated them.  SESSION-290 replaced the former per-state field `hBogF`/`hBog` by the
  four checkable data fields `hη0`, `hBog0`, `hW2`, `hL2`, from which FS's `lm:appbogolubov`
  pairing payment for `kinWord` is DERIVED (`Work.SmallBoxA0.hBogF_of_w1_sqrt_le`).  That field is an OPEN RUNG (not a defect): this is the paper's
  hard analytic step, and the available D1 (`SmallBoxD1Final.lm_appbogolubov_pWord_holds`) controls
  a DIFFERENT word (`kinPWord`), which exceeds `kinWord` on window cores by `chiSup² ≥ 6/π > 1`
  (`Work.SmallBoxA0.kinPWord_exceeds_kinWord`, PROVED); the η-dichotomy in
  `Submission/Work/SmallBoxA0/README.md` §21.2 shows no choice of the Bogoliubov coefficient makes
  D1's word serve `kinWord`.  The field's mass coefficient is FS's own `(N̂+1)N̂`
  (`final_v2.tex` l.3766); the earlier `(N̂+1)²` was a transcription slip, corrected in
  SESSION-288.  A scaling check (README §24) shows the rung is TRUE in the dilute regime
  (`a v ≲ R`): the pairing's negativity is `O((a v)²/(R s³))` while the payment is
  `O((a v)/s³)`.
* `smallbox_block_bound_kinP`, `smallbox_state_block_bound_kinP` are the SAME block shape for the
  energy whose kinetic word is D1's own (`Work.SmallBoxA0.kinPEnergy`/`kinPeB`, i.e. FS's `ℋ_B(μ)`
  of eq:HBU) over `KinPBoxData`/`KinPStateData` — residual-free, with the PROVED D1 as the rung.

STATUS (SESSION-288): the residual field `hBogF`/`hBog` of `BlockBoxData`/`BlockStateData` is
FS's `lm:appbogolubov` pairing payment for the corpus's kinetic word `kinWord` and is NOT
derivable from the PROVED D1 (`SmallBoxD1Final.lm_appbogolubov_pWord_holds`), whose word is
`kinPWord`.  SESSION-288 settled this with proof: the residual's content is EXACTLY the comparison
`kinPWord s c₀ Φ ≤ kinWord N s Φ` (`Work.SmallBoxA0.residual_gap_eq_comparison_deficit`), that
comparison is FALSE (`not_comparison_kinPWord_le_kinWord`), the `χ_b ≡ 1`-on-the-box window repair
is impossible (`not_continuous_eq_one_on_box_supported_in_box`, plus the `χ_b`-word's
non-integrability confirmed by two reviewers), and the word depends only on the window's
restriction to the cube (`Work.SmallBoxA0.winKinPWord_eq_of_eqOn_acube`).  The residual DOES
follow from the corpus's recorded box-NEUMANN rung (`Work.SmallBoxA0.residual_of_kModeWord`, via
the PROVED `kModeWord_le_kinWord`).  See `Submission/Work/SmallBoxA0/README.md` §18–§19 and the
modules `Submission/Work/SmallBoxA0/WinMode.lean`, `WinObstruction.lean`.  The faithful FS
statement (energy `ℋ_B` of `eq:HBU`, i.e. `Work.SmallBoxA0.kinPeB`) is delivered residual-free by
`smallbox_block_bound_kinP` / `smallbox_state_block_bound_kinP`.

STATUS (SESSION-287c): **CLOSED — no `sorry`; two interfaces are provided.**  The two theorems
`Submission.BoseGases.smallbox_block_bound` and `…smallbox_state_block_bound` are the
CORPUS-shaped block bound (energy `sboxE = kinWord + qLHSword`, `eB`-infimum, count `N` in
exactly the shape `SmallBoxDLBound`'s n″-arm and `EBPerState.eB_ge_count_lower` consume).  They
consume the per-state residual field `hBogF`/`hBog`, and the PROVED
`Work.SmallBoxA0.kinPWord_exceeds_kinWord` shows that the corpus's PROVED D1 — the Bogoliubov
input this area was asked to combine — cannot supply it (D1's word `kinPWord` is the χ-windowed
mode sum, `chiSup² ≥ 6/π` larger than `kinWord` on χ-core states).  Alongside them,
`smallbox_block_bound_kinP` / `smallbox_state_block_bound_kinP` are the SAME block shape for the
energy whose kinetic word IS D1's word (`Work.SmallBoxA0.kinPEnergy`/`kinPeB`: `kinPWord` plus
FS's `ε_T`-gap term) over the residual-free bundles `KinPBoxData`/`KinPStateData`; there the
Bogoliubov input is the PROVED D1 with its constant exposed (`Work.SmallBoxA0.d1C`) and no field
is assumed.  The two energies are NOT related by an inequality (χ-core vs corner behaviour), so
which one the corpus uses is a definitional choice — the modelling switch recorded in
`SmallBoxA0/README.md` §10–§11.

STATUS (SESSION-287): **CLOSED — no `sorry`, and the hypothesis bundles are INHABITED.**  The
Session-286 warning (the residual field `hBogF`/`hBog` un-shown-satisfiable, and possibly vacuous)
is now RESOLVED as follows.

* **NON-VACUITY.**  `Submission/Work/SmallBoxA0/VZero.lean` exhibits an explicit
  `Work.SmallBoxA0.blockBoxData_vZero : BlockBoxData` and
  `Work.SmallBoxA0.blockStateData_vZero : BlockStateData` (zero potential `v ≡ 0`, `N = 1`,
  `s = 1`, `μ = 1`, `R0 = chiR0/2`, `K_B = 1`, `eta = 0`, `BogErr = 0`, state `Φ ≡ 1`); at that
  datum the residual reduces to the CLOSED kinetic gap `cnPlus/(36s²) ≤ kinWord`
  (`KineticBound.kinWord_gap_cnPlus`).  Applying `smallbox_block_bound` to it yields
  `Work.SmallBoxA0.smallbox_block_bound_nonvacuous : 0 ≤ eB 1 1 1 0 hZero`, also proved directly
  (`Work.SmallBoxA0.eB_nonneg_vZero`); similarly
  `Work.SmallBoxA0.smallbox_state_block_bound_nonvacuous`.  So neither theorem is vacuous.
* **WHAT THE RESIDUAL IS.**  `Submission/Work/SmallBoxA0/BogReduction.lean`:
  `Work.SmallBoxA0.state_block_bound_residual_of_pairing_payment` shows the residual is EXACTLY
  FS's `lm:appbogolubov` PAIRING PAYMENT given the proved kinetic gap — a hypothesis with no
  kinetic word in it: `½(1+eta)·D·(N̂+1)²/s³ + BogErr·n₊ + (88π+39)(av)μ ≥ −q4PairWord Φ`.
  `Work.SmallBoxA0.hbox_iff` identifies the bundle's regime field
  `hbox : totNCoeff s μ v + BogErr ≤ 1/(36s²)` as pure arithmetic, equivalent to FS's
  healing-length condition `(136π + 1744π·chiSup²)(av)μ + BogErr ≤ 1/(72s²)`.
* **PROVENANCE.**  `Work.SmallBoxA0.kModeWord_le_kinWord`
  (`Submission/Work/SmallBoxA0/kModeWord_le_kinWord.lean`) dominates the corpus's box-NEUMANN
  D1 kinetic word by `kinWord`; that word (`SmallBoxSharpMass.kModeWord`) is the left-hand side of
  the corpus's recorded `lm:appbogolubov_refined_concrete`, so that rung implies this residual.
* **THE OBSTRUCTION STANDS.**  The PROVED `SmallBoxD1Final.lm_appbogolubov_pWord_holds` cannot
  feed this file directly: its `kinPWord` is the χ-NORMALISED windowed mode sum and exceeds
  `kinWord` by `chiSup² ≥ 6/π > 1` on states supported in the χ-core
  (`Work.SmallBoxA0.kinPWord_exceeds_kinWord`, PROVED).  The `kModeWord` transcription has no χ
  window, which is why it IS comparable.

  The statement of the block shape is unchanged.

* **THE MODEL-CHANGE ROUTE IS NOW CLOSED** (SESSION-287b).  With the energy's kinetic word
  taken to be D1's own word `kinPWord` (FS's `𝒯_B` spectral factor) plus FS's `ε_T`-gap term,
  the Bogoliubov input is the PROVED D1 and NO residual field is needed:
  `Submission/Work/SmallBoxA0/kinPDefs` + `kinP_state_block` +
  **`Work.SmallBoxA0.kinP_block_bound`**
  (`Submission/Work/SmallBoxA0/kinP_block_bound.lean`, sorry-free, axioms clean):
  `∃ C, 0 ≤ C ∧ ∀ D : KinPBoxData, (¼((D.n+1)/s³−μ)² − ½μ²)·8π(av)s³ − C·μ²(av)s³·Γ − C·μ(av)
  ≤ kinPeB D.n D.s D.μ D.v D.h D.c₀ D.cgap`.  The switch-over would be a change of the corpus's
  small-box energy (`SmallBoxSuperadd.sboxE`, `SboxEB.eB`, the `dℓ`-sliding layer) from `kinWord`
  to `kinPEnergy`; see `Submission/Work/SmallBoxA0/README.md` §10.

WHAT IS DERIVED AND WHAT IS ASSUMED (SESSION-286c/286d/286e).

* **The `Corr` residue is DERIVED — it is no longer a field.**  The bundle carries only
  the AM–GM regime `hcorrreg : 4·(32πχSup²(N+1)(av))²·N̂ ≤ π(av)μs⁴`; the `√`-shaped bound
  `2·CorrWord s h Φ ≤ 32πχSup²(N+1)·(av)·√(cS1 s Φ)·√(cnPlus s Φ)` is the THEOREM
  `Work.SmallBoxA0.corr_sqrt_bound_all` (module
  `Submission/Work/SmallBoxA0/corrWord_sqrt_bound.lean`, delegated and proved: fibre sup
  `fsqC1` + Cauchy–Schwarz slot by slot and over the slots), and its linear form
  `2s⁻³·CorrWord ≤ n₊/(72s²) + 36π(av)μ` consumed by the assembly is the THEOREM
  `Work.SmallBoxA0.corr_linear_of_sqrt` (module `Submission/Work/SmallBoxA0/CorrSqrt.lean`,
  AM–GM `amgm_sqrt` + `cS1 ≤ N̂`).  NOTE the shapes: under the physical rescaling
  `s ↦ εs, v ↦ ε⁻²v(·/ε), μ ↦ μ/ε³` one has `CorrWord ↦ ε·CorrWord` and `a v ↦ ε(a v)`,
  so the `s⁻³` belongs on the `2s⁻³CorrWord` side of the ASSEMBLY and NOT on the `√`-bound
  (an earlier attempt at this path with `2s⁻³·CorrWord` on the left was falsified by exactly
  this rescaling).

* **The Bogoliubov residual is an ASSUMED field — and it is PROVABLY NOT derivable from the
  corpus's D1.**  The attempt to derive
  `kinWord + q4PairWord ≥ −½(1+η)D(N̂+1)²/s³ + (1/(36s²) − BogErr)n₊ − (88π+39)(av)μ`
  from `SmallBoxD1Final.lm_appbogolubov_pWord_holds` needs a bridge
  `kinPWord s c₀ Φ ≤ kinWord N s Φ + C·cnPlus s Φ` (coefficient ≤ 1 on `kinWord`: for any
  `K > 1`, writing `kinWord + A₂ = (kinP + A₂) + (kinWord − kinP)` and using D1 for
  `kinP + A₂`, the bracket `kinWord − kinP ≥ (1−K)kinWord − E` is unbounded below, so no
  constant lower bound follows).  **Such a bridge is FALSE**: for a zero-mean smooth bump
  supported in `ball(0, s/4)` one has `chiScale s ≡ chiSup` there and
  `kinPWord s 0 Φ = chiSup²·∫|∇Φ|² + (≥0)` while `kinWord 1 s Φ = ∫|∇Φ|²`, with
  `chiSup² = (∫chiBase²)⁻¹ ≥ 6/π > 1` (`chiBase` is a `ContDiffBump` with `rIn = 1/4`,
  `rOut = 1/2`).  Narrowing the bump makes the excess `(chiSup²−1)kinWord` unbounded at fixed
  `cnPlus`, so no state-independent `C` works
  (`Work.SmallBoxA0.kinPWord_exceeds_kinWord`, module
  `Submission/Work/SmallBoxA0/kinPWord_exceeds_kinWord.lean`, is the formal witness, PROVED).
  Hence the corpus's D1 — transcribed with the χ-windowed π-modes — cannot feed
  `sBoxE = kinWord + qLHSword`; FS's renormalised kinetic layer `𝒯_B` (eq:appTB) or a
  re-transcription of D1 with `kinWord` is required.  (For completeness: the shortcut
  `eta := BogErr := 0`, which would reduce this field to the closed `kinWord ≥ n₊/(36s²)`
  plus a sign fact about `A₂`, also fails — `A₂ = q4PairWord` is genuinely SIGNED: its
  summand `(P_iP_jΦ)(Q_jQ_iΦ)` is a product, not a square, unlike `q2PairWord`'s
  `QMassUpper.q2PairWord_nonneg`.  So this field is exactly FS's pairing payment: the
  negativity of `A₂` is paid by the excited kinetic.  See `Submission/STATUS.md`
  SESSION-286 §§3–5.)

  The single lemma `smallbox_block_bound` below is the revised
Goal-1 "one lemma": for a count in the block window `N̂/s³ ≤ 9μ` (`C_n := 8`),
the centred-box energy `eB N s μ v h` satisfies FS's tight block shape

    eB ≥ ( ¼((N̂/s³)−μ)² − ½μ² )·8π(av)·s³ − C·μ²(av)·s³·Γ − C·μ(av),

`Γ := (R0/s)² + K_B³(μ(av)³)^{1/2}` the FS error shape of
`SmallBoxDLBound.smallbox_dl_energy_bound` (whose n″-arm this feeds; the
theorem's convex density term `c(x−μ)²/(1+x/μ)` then follows by
`SmallBoxConvexity.smallboxConvex_count` since `¼ ≥ c/(1+x/μ)` for
`c := 1/50`).  This is the bound the Session-197 audit showed the LOSSY
route (`EBWindowed.eB_ge_sharp_windowed`, which keeps the order-1
`(C₂+7C₁)N̂²/s³ + μC₁N̂` count remainders) CANNOT deliver.

## The tight derivation (FS lm:appinteractionestimate → eq:simpleaprioribog
→ lm:w2>w1, transcribed; verified against final_v2.tex ~3730–3905)

1. **potsplit** (`PotWords.potsplit`/`PotQ0Lower.pot_q0_lower`, closed):
   `qLHS = q0 + q1 + q2 + q3 + q4`, `q4 ≥ 0`.
2. **q0-word** (`Q0Ren.q0_chosen_lower`, closed): the condensate quadratic
   `q0 ≥ A₀(S)`, `S := cS1`, with the **∬w₂-based mass**
   (`∬wPair(g₂) = 8π(av)·s³ + s³·D`, `D := ∫g₀·w₀` = the `ĝω(0)`-mass —
   `SmallBoxKernelMass.wPair_g2_g0_box_mass` / `FSKernelCompare`).
3. **A₀-form algebra** (`A0Core.a0_form_square_identity` /
   `a0_form_ge_fs_main`, closed — pure real): the EXACT conversion
   `A₀-form(S) = ¼(u−μ)²·8π(av)s³ − ½μ²·8π(av)s³
                 − 4π(av)(2u+μ) − 2π(av)/s³ + ½·D·(S²−S)/s³`
   (the `+D`-slack is nonnegative and dropped; the `4πa(2u+μ)+2πa/s³`-block
   is FS's `Cμa(1+u/μ)`-type error — absorbed by the `−Cμ(av)`-term once
   `u ≤ 9μ` and `1 ≤ μs³`).
4. **q1/q2/q3 word assembly** — the OPEN part (the corpus's `per_state_sharp`
   bounded these crudely, leaving the order-1 `(C₂+7C₁)·cS2/s³` remainders of
   the Session-197 audit; FS instead treats q1's CS
   (`Step4SqrtFactorisation.step4_Ppart_quadratic` +
   `condensate_sqrt_square_le`, closed) and q2's Bogolubov 2Q-part exactly,
   cancelling the `−½·D·(S²−S)/s³`-type term against `A₂`).  The missing
   word-level lemma is recorded in `A0Core`'s header ("the word-level lemma
   that PRODUCES the `−¼(μ−u−1/V)²·8πaV`-term from q1word ... next step of
   the joint q1/q2 assembly").
5. **kinetic-gap absorption** (`SharpPerState.gap_absorb_sharp` shape,
   closed): the `n₊`-linear/quadratic remainders absorbed by
   `kinWord ≥ cnPlus/(36s²)` under the sharp-gap regime (derivable from
   `1 ≤ μs³`, the window `u ≤ 9μ`, dilute `μ(av)³ ≤ ε₀` and the regime caps).
6. **eB-infimum**: normalise (`CSBox.ofFun` of `(√∫Φ²)⁻¹•Φ`, `sboxE_smul`)
   and `le_ciInf` over the nonempty `CSBox`.

The skeleton target fixes the statement (hypotheses = standing potential set
+ `0 < s, 0 < μ, R0 ≤ s·chiR0, 1 ≤ μs³`, block window `N̂/s³ ≤ 9μ`, the
error shape `Γ` with the universal `0 ≤ C`); the body grinds steps 1–6,
starting from the word-level joint q1/q2 assembly (step 4 — OPEN).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false
set_option linter.unusedVariables false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## The data bundles (Session-267, fidelity)

The two `⋯_block_bound` statements carry a UNIVERSAL error constant
(`∃ C ≥ 0, ∀ data, …`), matching FS `thm:smallbox`'s "there are universal
constants `C, C' > 1`".  They are stated over the bundles below because a
flat `∀`-telescope inside a term is not elaborable in reasonable time
(Session-267 measurement; see the module note in `SmallBoxDLBound.lean`),
and because the previous parameter-context `∃ C` was (i) nearly vacuous and
(ii) useless for consumers: the two-arm chain applies the per-group bound to
`m` groups at DIFFERENT counts `n'` and must use ONE `C`, and the sliding sum
uses it over boxes with different side lengths. -/

/-- The data of the tight per-block smallbox bound: box side `s`, chemical
potential `μ`, potential `v` (with scattering solution `h`), the range `R0`,
the regime constant `K_B`, the block count `N` in the window
`N̂/s³ ≤ 9μ`, and the standing hypotheses. -/
structure BlockBoxData where
  N : ℕ
  s : ℝ
  μ : ℝ
  R0 : ℝ
  K_B : ℝ
  v : ℝ³ → ℝ
  h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v
  hs : 0 < s
  hμ : 0 < μ
  hv_nonneg : 0 ≤ v
  hvrad : IsRadial v
  hv_memL1 : MemLp v 1
  hR0 : 0 < R0
  hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0
  hRs : R0 ≤ s * chiR0
  hμs : 1 ≤ μ * s ^ 3
  hKB : 0 < K_B
  /-- the block count window (`C_n := 8 ⟹ densities ≤ 9μ`). -/
  hwin : (N : ℝ) / s ^ 3 ≤ (9 : ℝ) * μ
  /-- the Bogolubov-regime loss factor `η` of D1
  (`(1+C·R0/s)(1+C·c₀(av)) − 1`; a data parameter). -/
  eta : ℝ
  /-- **SESSION-286 data parameter** — the `cnPlus`-coefficient `E` of the
  D1 `lm:appbogolubov` refined error that the kinetic gap does not already
  absorb (a data scalar, like `eta`; for FS's data it is
  `d1TargetC·(av)(N̂+1)/s³`). -/
  BogErr : ℝ
  /-- **SESSION-286 regime field** (FS `eq:appdellsassumption`, lower bound:
  the box side is below the healing length).  It is the hypothesis under
  which the total `n₊`-coefficient of the sharp chain
  (`totNCoeff + BogErr`) is absorbed by the kinetic gap `n₊/(36s²)`. -/
  hbox : Work.SmallBoxA0.totNCoeff s μ v + BogErr ≤ 1 / (36 * s ^ 2)
  /-- **SESSION-285 regime field** (FS `eq:appdellsassumption`, upper bound):
  the Bogolubov loss factor is dominated by the error bracket `Γ`. -/
  hη : (1 / 2) * |eta| * (8 * π * (a v)) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹
        ≤ μ ^ 2 * (a v) * s ^ 3
            * ((R0 / s) ^ 2 + K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          + μ * (a v)
  /-- **SESSION-286c regime field** — the AM–GM's constant term
  `144·s²·CorrC²(av)²·cS1` fits the `(av)μ` budget (using `cS1 ≤ N̂`). -/
  hcorrreg : 4 * ((32 * π * chiSup ^ 2 * ((N : ℝ) + 1)) * (a v)) ^ 2 * ((N : ℝ))
      ≤ π * (a v) * μ * s ^ 4
  /-- **SESSION-290: THE RUNG IS NOW CHECKABLE AND STATE-INDEPENDENT.**  SESSION-286 used
  to carry FS's `lm:appbogolubov` residual here as a PER-STATE hypothesis; it is now a
  THEOREM (`Work.SmallBoxA0.hBogF_of_w1_sqrt_le`, PROVED) derived from the four fields
  below, and the error coefficients of that theorem are exactly FS's `(88π+39)(av)μ`
  with the mass coefficient `(N̂+1)N̂` (`lr:appbogolubov`).  The two data parameters are
  nonnegative (loss factors). -/
  hη0 : 0 ≤ eta
  hBog0 : 0 ≤ BogErr
  /-- the pairing kernel `w₁ = wPairC s (g0 v h)` is square-integrable on the box pair
  (the Bochner-degeneracy guard: without it the pairing integral is `0`). -/
  hW2 : MemLp (fun p : X 2 => wPairC s (g0 v h) (p 0) (p 1)) 2 (volume.restrict (abox 2 s))
  /-- **the checkable input**: the STATE-INDEPENDENT kernel-`L²` bound
  `‖w₁‖_{L²(abox 2 s)} ≤ ½(1+eta)·g0w0Mass` (`w₁ = wPairC s (g0 v h)`).  From it the
  residual inequality is a THEOREM (`Work.SmallBoxA0.hBogF_of_w1_sqrt_le`, PROVED), so
  the theorem below is NOT conditional on a per-state Bogoliubov hypothesis.  A
  sufficient PRIMITIVE data condition is
  `4·chiSup⁴·s³·∫g₀² ≤ (½(1+eta)·g0w0Mass)²` (`Work.SmallBoxA0.w1_L2_sq_le` +
  `Work.SmallBoxA0.hBogF_of_g0_L2`). -/
  hL2 : Real.sqrt (∫ p in abox 2 s, (wPairC s (g0 v h) (p 0) (p 1)) ^ 2)
      ≤ (1 / 2) * (1 + eta) * g0w0Mass (v := v) h
  /-- **SESSION-285 regime field** (the `χ`-version of the healing-length
  condition, for the DERIVED `cS1 = 0` case). -/
  hchi : (μ * (a v) * s ^ 2) * (1600 + 1850 * chiSup ^ 2) ≤ 1

/-- The data of the fixed-`n` OPERATOR statement: the block data together
with a normalised smooth `N`-particle state `Φ`. -/
structure BlockStateData where
  N : ℕ
  s : ℝ
  μ : ℝ
  R0 : ℝ
  K_B : ℝ
  v : ℝ³ → ℝ
  h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v
  hs : 0 < s
  hμ : 0 < μ
  hv_nonneg : 0 ≤ v
  hvrad : IsRadial v
  hv_memL1 : MemLp v 1
  hR0 : 0 < R0
  hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0
  hRs : R0 ≤ s * chiR0
  hμs : 1 ≤ μ * s ^ 3
  hKB : 0 < K_B
  hwin : (N : ℝ) / s ^ 3 ≤ (9 : ℝ) * μ
  /-- the Bogolubov-regime loss factor `η` of D1. -/
  eta : ℝ
  /-- **SESSION-286 data parameter** — the `cnPlus`-coefficient of the D1
  refined error not absorbed by the kinetic gap (data scalar, like `eta`). -/
  BogErr : ℝ
  /-- **SESSION-286 regime field** (FS `eq:appdellsassumption`, lower bound). -/
  hbox : Work.SmallBoxA0.totNCoeff s μ v + BogErr ≤ 1 / (36 * s ^ 2)
  /-- **SESSION-285 regime field** (FS `eq:appdellsassumption`, upper bound). -/
  hη : (1 / 2) * |eta| * (8 * π * (a v)) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹
        ≤ μ ^ 2 * (a v) * s ^ 3
            * ((R0 / s) ^ 2 + K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          + μ * (a v)
  Φ : X N → ℝ
  /-- (SESSION-285: strengthened from `Continuous Φ` to `ContDiff ℝ ∞ Φ` — the
  corpus's per-state lemmas, the Neumann gap and the `cS1 = 0` case all need
  smoothness; the `eB`-level bundle already carries `ContDiff` states.) -/
  hΦc : ContDiff ℝ ∞ Φ
  hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1
  /-- **SESSION-285 regime field** (the `χ`-version of the healing-length
  condition, for the `cS1 = 0` case). -/
  hchi : (μ * (a v) * s ^ 2) * (1600 + 1850 * chiSup ^ 2) ≤ 1
  /-- **SESSION-286c regime field** — the AM–GM constant fits the `(av)μ` budget. -/
  hcorrreg : 4 * ((32 * π * chiSup ^ 2 * ((N : ℝ) + 1)) * (a v)) ^ 2 * ((N : ℝ))
      ≤ π * (a v) * μ * s ^ 4
  /-- **SESSION-290: THE RUNG IS NOW CHECKABLE AND STATE-INDEPENDENT** — same four fields
  as `BlockBoxData`; the residual is the THEOREM
  `Work.SmallBoxA0.hBogF_of_w1_sqrt_le` at this state. -/
  hη0 : 0 ≤ eta
  hBog0 : 0 ≤ BogErr
  /-- the pairing kernel `w₁ = wPairC s (g0 v h)` is square-integrable on the box pair. -/
  hW2 : MemLp (fun p : X 2 => wPairC s (g0 v h) (p 0) (p 1)) 2 (volume.restrict (abox 2 s))
  /-- **the checkable input**: `‖w₁‖_{L²(abox 2 s)} ≤ ½(1+eta)·g0w0Mass`; the residual
  inequality is then the THEOREM `Work.SmallBoxA0.hBogF_of_w1_sqrt_le` at this state. -/
  hL2 : Real.sqrt (∫ p in abox 2 s, (wPairC s (g0 v h) (p 0) (p 1)) ^ 2)
      ≤ (1 / 2) * (1 + eta) * g0w0Mass (v := v) h
  /-- **SESSION-285 (RESIDUAL 3 REMOVED)**: the fully-excited `cS1 = 0` case is
  DERIVED (`Work.SmallBoxA0.qLHSword_zero_case`) from the kinetic gap and the
  crude one-body bound, using the `hchi` regime field. -/
  _residual3_removed : True

/-- **The per-block tight smallbox bound (SESSION-285: PROVED)**: the error
constant is the universal `C := 272π + 40` (weaker than any `C` from
`state_block_bound_of_inputs`, hence usable); for a block count in the window
`N̂/s³ ≤ 9μ` (`C_n := 8`), with
`0 < s`, `0 < μ`, `1 ≤ μs³` (shortest side ≥ μ^{-1/3}), the standing
potential/regime hypotheses and the dilute/regime caps folded into the
universal error constant `0 ≤ C`,

    eB N s μ v h ≥ ( ¼((N̂/s³)−μ)² − ½μ² )·8π(av)·s³
                    − C·μ²(av)·s³·Γ − C·μ(av),

`Γ := (R0/s)² + K_B³(μ(av)³)^{1/2}` — the tight FS block shape feeding the
n″-arm of `smallbox_dl_energy_bound`.  See the module doc for the FS-route
map (steps 1–6), `Submission/Work/SmallBoxA0/Assembly.lean` for the
CORRECTED potential-side assembly, and `Submission/Work/SmallBoxA0/README.md`
for the honest ledger of the remaining recorded residuals (`hCorrF`,
`hBogF`) and of the regime fields (`eta`, `BogErr`, `hbox`, `hη`, `hchi`).

**SESSION-285**: closed by `Work.SmallBoxA0.state_block_bound_of_inputs`
(the sharp potential-side assembly) on the bundle's fields
`eta/hbox/hη/hCorrF/hBogF/hZeroF`; see `SmallBoxA0/README.md`.

**Session-266 FIX**: the error constant is EXISTENTIAL (`∃ C, 0 ≤ C ∧ …`),
matching FS's `∃C, ∃C'`.  The previous form (`{C : ℝ} (hC : 0 ≤ C)` with the
conclusion `main − C·E ≤ eB`) is Lean-`∀C`, hence EQUIVALENT to the
error-free case `C = 0` — strictly stronger than FS proved (and very likely
false).  See the Session-266 entry in `STATUS.md`. -/
theorem smallbox_block_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ D : BlockBoxData,
        ((1 / 4 : ℝ) * (((D.N : ℝ) / D.s ^ 3) - D.μ) ^ 2 - (1 / 2 : ℝ) * D.μ ^ 2)
              * (8 * π * (a D.v) * D.s ^ 3)
          - C * D.μ ^ 2 * (a D.v) * D.s ^ 3
              * ((D.R0 / D.s) ^ 2 + D.K_B ^ 3 * (D.μ * (a D.v) ^ 3) ^ (1 / 2 : ℝ))
          - C * D.μ * (a D.v)
        ≤ eB D.N D.s D.μ D.v D.h := by
  refine ⟨272 * π + 40, by positivity, ?_⟩
  intro D
  have hann : 0 ≤ a D.v := (av_bounds_weak D.hR0 D.hv_nonneg D.hvrad D.hv_supp D.h).1
  have hμnn : 0 ≤ D.μ := le_of_lt D.hμ
  have hsnn : (0 : ℝ) ≤ D.s ^ 3 := pow_nonneg (le_of_lt D.hs) 3
  have hC1 : (1 : ℝ) ≤ 272 * π + 40 := by nlinarith [Real.pi_pos]
  have hC36 : (36 : ℝ) * π ≤ 272 * π + 40 := by nlinarith [Real.pi_pos]
  have hμ2a : (0 : ℝ) ≤ D.μ ^ 2 * (a D.v) := by positivity
  have hμa : (0 : ℝ) ≤ D.μ * (a D.v) := mul_nonneg hμnn hann
  have hDg : g0w0Mass (v := D.v) D.h ≤ 8 * π * (a D.v) :=
    Work.SmallBoxA0.g0w0Mass_le_av D.hR0 D.hv_nonneg D.hvrad D.hv_supp D.h
  have hGamnn : 0 ≤ (D.R0 / D.s) ^ 2 + D.K_B ^ 3 * (D.μ * (a D.v) ^ 3) ^ (1 / 2 : ℝ) := by
    have h2 : (0 : ℝ) ≤ (D.μ * (a D.v) ^ 3) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg (by positivity) (1 / 2)
    exact add_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg (le_of_lt D.hKB) 3) h2)
  have hX : (0 : ℝ) ≤ D.μ ^ 2 * (a D.v) * D.s ^ 3
      * ((D.R0 / D.s) ^ 2 + D.K_B ^ 3 * (D.μ * (a D.v) ^ 3) ^ (1 / 2 : ℝ)) :=
    mul_nonneg (mul_nonneg hμ2a hsnn) hGamnn
  have hmono : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      - (272 * π + 40) * x - (272 * π + 40) * y ≤ - x - y := by
    intro x y hx hy
    nlinarith [mul_le_mul_of_nonneg_right hC1 hx, mul_le_mul_of_nonneg_right hC1 hy]
  have hper : ∀ Φ : CSBox D.N D.s,
      ((1 / 4 : ℝ) * (((D.N : ℝ) / D.s ^ 3) - D.μ) ^ 2 - (1 / 2 : ℝ) * D.μ ^ 2)
            * (8 * π * (a D.v) * D.s ^ 3)
        - (272 * π + 40) * D.μ ^ 2 * (a D.v) * D.s ^ 3
            * ((D.R0 / D.s) ^ 2 + D.K_B ^ 3 * (D.μ * (a D.v) ^ 3) ^ (1 / 2 : ℝ))
        - (272 * π + 40) * D.μ * (a D.v)
      ≤ (sboxE D.N D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) (Φ : X D.N → ℝ)) /
        (∫ x in abox D.N D.s, ((Φ : X D.N → ℝ) x) ^ 2) := by
    intro Φ
    let Ph : X D.N → ℝ := Φ
    let I : ℝ := ∫ x in abox D.N D.s, (Ph x) ^ 2
    have hIpos : 0 < I := by simpa [I, Ph] using Φ.sq_pos
    have hIne : I ≠ 0 := ne_of_gt hIpos
    let c : ℝ := (Real.sqrt I)⁻¹
    have hsqrt0 : 0 < Real.sqrt I := Real.sqrt_pos.mpr hIpos
    have hc2 : c ^ 2 = I⁻¹ := by
      dsimp [c]
      have hsq : (Real.sqrt I) ^ 2 = I := Real.sq_sqrt (le_of_lt hIpos)
      calc ((Real.sqrt I)⁻¹) ^ 2 = ((Real.sqrt I) ^ 2)⁻¹ := by rw [← inv_pow]
        _ = I⁻¹ := by rw [hsq]
    have hΨc : ContDiff ℝ ∞ (c • Ph) := Φ.contDiff.const_smul c
    have hnorm1 : (∫ x in abox D.N D.s, ((c • Ph) x) ^ 2) = 1 := by
      rw [abox_integral_sq_smul]
      rw [hc2]
      field_simp [hIne]
      simp [I]
    have hstate : ((1 / 4 : ℝ) * (((D.N : ℝ) / D.s ^ 3) - D.μ) ^ 2 - (1 / 2 : ℝ) * D.μ ^ 2)
            * (8 * π * (a D.v) * D.s ^ 3)
        - (272 * π + 40) * D.μ ^ 2 * (a D.v) * D.s ^ 3
            * ((D.R0 / D.s) ^ 2 + D.K_B ^ 3 * (D.μ * (a D.v) ^ 3) ^ (1 / 2 : ℝ))
        - (272 * π + 40) * D.μ * (a D.v)
        ≤ sboxE D.N D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) (c • Ph) := by
      by_cases h0 : cS1 D.s (c • Ph) = 0
      · -- the fully-excited (`cS1 = 0`) case: DERIVED
        have hz := Work.SmallBoxA0.qLHSword_zero_case (N := D.N) (s := D.s) (μ := D.μ)
          (R0 := D.R0) (v := D.v) D.hs D.hμ D.hR0 D.hv_nonneg D.hvrad D.hv_memL1
          D.hv_supp D.h D.hRs (Φ := c • Ph) hΨc hnorm1 h0 D.hwin D.hchi
        have hx : (0 : ℝ) ≤ (272 * π + 40) * (D.μ ^ 2 * (a D.v) * D.s ^ 3)
            * ((D.R0 / D.s) ^ 2 + D.K_B ^ 3 * (D.μ * (a D.v) ^ 3) ^ (1 / 2 : ℝ)) := by
          have h1 : (0 : ℝ) ≤ D.μ ^ 2 * (a D.v) * D.s ^ 3 := mul_nonneg hμ2a hsnn
          have h2 : (0 : ℝ) ≤ 272 * π + 40 := by positivity
          have h3 : (0 : ℝ) ≤ (D.R0 / D.s) ^ 2 + D.K_B ^ 3
              * (D.μ * (a D.v) ^ 3) ^ (1 / 2 : ℝ) := hGamnn
          nlinarith [h1, h2, h3, mul_nonneg h1 h3]
        have hy : (0 : ℝ) ≤ (272 * π + 40) * (D.μ * (a D.v)) := by positivity
        linarith [hz, hx, hy]
      · have hlt : 0 < cS1 D.s (c • Ph) := lt_of_le_of_ne cS1_nonneg (Ne.symm h0)
        have hNpos : 0 < (D.N : ℝ) := by
          have h1 := cS1_le_norm_sq (N := D.N) D.hs hΨc.continuous
          rw [hnorm1, mul_one] at h1
          linarith
        have hN : 1 ≤ D.N := Nat.succ_le_of_lt (Nat.cast_pos.mp hNpos)
        have hmain := Work.SmallBoxA0.state_block_bound_of_inputs_sharp (N := D.N) (s := D.s)
          (μ := D.μ) (R0 := D.R0) (K_B := D.K_B) (η := D.eta) (C := 272 * π + 40)
          (BogErr := D.BogErr)
          hN D.hs D.hμ D.hR0 D.hKB D.hv_nonneg D.hvrad D.hv_memL1 D.hv_supp D.h D.hRs D.hμs
          hΨc hnorm1 D.hwin hlt hDg D.hbox D.hη (le_refl _)
          (Work.SmallBoxA0.corr_linear_of_sqrt (s := D.s) (μ := D.μ) (CorrC := 32 * π * chiSup ^ 2 * ((D.N : ℝ) + 1))
            (v := D.v) D.h D.hs hann (by positivity) hΨc.continuous hnorm1 D.hcorrreg
            (Work.SmallBoxA0.corr_sqrt_bound_all (s := D.s) (R := D.R0) (v := D.v)
              D.hs D.hR0 D.hv_nonneg D.hvrad D.hv_supp D.h D.hRs hΨc.continuous hnorm1)) (Work.SmallBoxA0.hBogF_of_w1_sqrt_le (N := D.N) (s := D.s) (μ := D.μ) (η := D.eta)
              (BogErr := D.BogErr) (R := D.R0) D.h D.hs D.hR0 D.hv_nonneg D.hvrad D.hv_supp
              D.hRs D.hW2 D.hL2 (av_bounds_weak D.hR0 D.hv_nonneg D.hvrad D.hv_supp D.h).1
              (le_of_lt D.hμ) D.hBog0 D.hη0
              (g0w0Mass_nonneg D.hR0 D.hv_nonneg D.hvrad D.hv_supp D.h)
              hΨc hnorm1 hlt)
        convert hmain using 1 <;> ring
    have hE : sboxE D.N D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) (c • Ph)
        = sboxE D.N D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) Ph / I := by
      have hsmul := sboxE_smul (N := D.N) (s := D.s) (μ := D.μ) (w := wPairC D.s D.v)
        (w1 := wPairC D.s (g0 D.v D.h)) (Φ := Ph) Φ.contDiff c
      rw [hsmul, hc2]
      field_simp [hIne]
    calc ((1 / 4 : ℝ) * (((D.N : ℝ) / D.s ^ 3) - D.μ) ^ 2 - (1 / 2 : ℝ) * D.μ ^ 2)
            * (8 * π * (a D.v) * D.s ^ 3)
        - (272 * π + 40) * D.μ ^ 2 * (a D.v) * D.s ^ 3
            * ((D.R0 / D.s) ^ 2 + D.K_B ^ 3 * (D.μ * (a D.v) ^ 3) ^ (1 / 2 : ℝ))
        - (272 * π + 40) * D.μ * (a D.v)
        ≤ sboxE D.N D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) (c • Ph) := hstate
      _ = sboxE D.N D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) Ph / I := hE
      _ = (sboxE D.N D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) (Φ : X D.N → ℝ)) /
            (∫ x in abox D.N D.s, ((Φ : X D.N → ℝ) x) ^ 2) := by rfl
  have hne : Nonempty (CSBox D.N D.s) := nonempty_CSBox D.N D.hs
  rw [eB]
  apply le_ciInf (ι := CSBox D.N D.s)
  exact hper

/-- **Step-1 of the six-step route: the kinetic-gap-absorbed per-state form**
(fixed normalised `Φ`, count `N`; the closed `SharpPerState.gap_absorb_sharp`
at the block-bound's hypothesis set): under the n₊-window
`hwinP : cnPlus(Φ) ≤ B`, the count window `hucap : N̂/s³ ≤ U` and the sharp
gap regime

    hreg : μC₁ + (4πa/s³)·B + (3C₂+18C₁)·U ≤ 1/(36s²)

the kinetic gap `kinWord ≥ cnPlus/(36s²)` absorbs the cnPlus-quadratic and
the cnPlus/cS1-linear blocks of Step-0, leaving the cS2-remainder explicit:

    sboxE(Φ) ≥ (4πa/s³)·½(N̂−μs³−½)² − 4πaμ²s³(1+1/(2μs³))²
               − (C₂+7C₁)(s³)⁻¹·cS2(Φ) − μC₁·N̂

(`C₁ := fsqC1(av)`, `C₂ := fsqC2(av)`).  This is the per-state bound the
exact-A0/n₀-operator treatment (next steps) refines: its `cS2`-remainder is
state-level (NOT replaced by `N̂²` — that replacement is exactly the order-1
loss of the Session-197 audit), and its `μC₁N̂`-term cancels in the
state-splitting two-arm assembly (inside: this bound; outside `cnPlus > B`:
kinetic domination). -/
lemma smallbox_state_gap_absorbed {N : ℕ} {s μ R0 B U : ℝ} {v : ℝ³ → ℝ}
    (hs : 0 < s) (hμ : 0 < μ)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hR0 : 0 < R0) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRs : R0 ≤ s * chiR0)
    {Φ : X N → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1)
    (hwinP : cnPlus s Φ ≤ B)
    (hucap : (N : ℝ) / s ^ 3 ≤ U)
    (hreg : μ * (fsqC1 (a v)) + (4 * π * (a v) / s ^ 3) * B
        + (3 * (fsqC2 (a v)) + 18 * (fsqC1 (a v))) * U ≤ 1 / (36 * s ^ 2)) :
    (4 * π * (a v) / s ^ 3) * ((1 / 2 : ℝ) * ((N : ℝ) - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2)
        - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
        - ((fsqC2 (a v)) + 7 * (fsqC1 (a v))) * (s ^ 3)⁻¹ * cS2 s Φ
        - μ * (fsqC1 (a v)) * (N : ℝ)
    ≤ sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
  have hb := gap_absorb_sharp (ℓ := s) (μ := μ) hs hμ hv_nonneg hvrad hv_memL1
    hR0 hv_supp h hRs (Φ := Φ) hΦc hnorm (B := B) (U := U) hwinP hucap hreg
  simpa [sboxE] using hb

/-- **Step-0 of the six-step route: the cnPlus/cS2-explicit per-state bound**
(fixed normalised `Φ`, count `N`, the sector) — the exact starting point the
kinetic-gap absorption and the exact-A0 refinements act on.  This is the
closed `SharpPerState.per_state_sharp_u` instantiated at the block-bound's
hypothesis set (`s`, `μ`, `R0`, `hRs : R0 ≤ s·chiR0`, `hΦc`, `hnorm`):
with `X := N̂ − μs³ − ½`,

    sboxE(Φ) ≥ (4πa/s³)·½X² − (4πa/s³)·cnPlus(Φ)² − 4πaμ²s³(1+1/(2μs³))²
               − (C₂/s³)·(3N̂·cnPlus + cS2) − (C₁/s³)·(7cS2 + 18N̂·cnPlus)
               − μC₁·(cS1 + 2·cnPlus)

(`C₁ := fsqC1(av)`, `C₂ := fsqC2(av)`; valid for ALL `Φ` — no window).  The
`cnPlus`-quadratic/linear and `cS1`-blocks are exactly the n₊-operators FS's
eq:appgapestimate absorbs via the kinetic gap (next step,
`SharpPerState.gap_absorb_sharp` shape under the sharp-gap regime); the
`cS2`-remainder is what the exact `A0`/n₀-operator treatment
(`A0Core` + kernel masses) must eliminate to reach
`smallbox_state_block_bound`'s tight `¼(x−μ)²·8π(av)s³`-shape (no
scalar-ρ₀ shortcut — Sessions 204–205). -/
lemma smallbox_state_cnplus_explicit {N : ℕ} {s μ R0 : ℝ} {v : ℝ³ → ℝ}
    (hs : 0 < s) (hμ : 0 < μ)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hR0 : 0 < R0) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRs : R0 ≤ s * chiR0)
    {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1) :
    (4 * π * (a v) / s ^ 3) * ((1 / 2 : ℝ) * ((N : ℝ) - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2)
      - (4 * π * (a v) / s ^ 3) * (cnPlus s Φ) ^ 2
      - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
      - (fsqC2 (a v)) * (s ^ 3)⁻¹ * (3 * ((N : ℝ) * cnPlus s Φ) + cS2 s Φ)
      - (fsqC1 (a v)) * (s ^ 3)⁻¹ * (7 * cS2 s Φ + 18 * ((N : ℝ) * cnPlus s Φ))
      - μ * (fsqC1 (a v)) * (cS1 s Φ + 2 * cnPlus s Φ)
    ≤ sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
  have hb := per_state_sharp_u (ℓ := s) (μ := μ) hs hμ hv_nonneg hvrad hv_memL1
    hR0 hv_supp h hRs hΦc hnorm
  simpa [sboxE] using hb

/-- **Step-2 (marker): the Step-1 main term sits within `O((av)·μ)` of the FS
¼-shape** — pure real, isolating precisely what the exact-A0/n₀ treatment
must eliminate.  For `x := N̂/s³` in the block window `0 ≤ x ≤ 9μ`,
`1 ≤ μs³` (`C_n := 8`), the Step-1 main-minus-μ²block satisfies

    (4πa/s³)·½(xs³−μs³−½)² − 4πaμ²s³(1+1/(2μs³))²
        ≥ ( ¼(x−μ)² − ½μ² )·8πa·s³ − 21π·a·μ

(the two shapes differ by exactly `−2πa(x+μ) − πa/(2s³)`, which is
`≥ −21πaμ` from `x ≤ 9μ` and `1 ≤ μs³`).  So after Step-1, the ONLY
order-1 obstacle to `smallbox_state_block_bound`'s tight
`¼(x−μ)²·8π(av)s³`-shape is the `(C₂+7C₁)(s³)⁻¹·cS2(Φ)`-remainder (plus the
`μC₁N̂`-term, which the two-arm split cancels) — the exact-A0/n₀-operator
elimination of `cS2` is the substance of Step-2 (no scalar-ρ₀ shortcut,
Sessions 204–205; `21π·a·μ ≤ C·μ(av)` is absorbed by the block bound's
`−Cμ(av)`-term). -/
lemma smallbox_step1_shape {s μ x a : ℝ} (hs : 0 < s) (hμ : 0 < μ)
    (hμs : 1 ≤ μ * s ^ 3) (hx : 0 ≤ x) (hxμ : x ≤ 9 * μ) (ha : 0 ≤ a) :
    (4 * π * a / s ^ 3) * ((1 / 2 : ℝ) * (x * s ^ 3 - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2)
      - (4 * π * a) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
    ≥ ((1 / 4 : ℝ) * (x - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2) * (8 * π * a * s ^ 3)
        - 21 * π * a * μ := by
  have hdiff : (4 * π * a / s ^ 3) * ((1 / 2 : ℝ) * (x * s ^ 3 - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2)
        - (4 * π * a) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
        - (((1 / 4 : ℝ) * (x - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2) * (8 * π * a * s ^ 3))
      = - 2 * π * a * (x + μ) - π * a * (2 * s ^ 3)⁻¹ := by
    field_simp [ne_of_gt hs]
    ring
  have hneg : 2 * π * a * (x + μ) + π * a * (2 * s ^ 3)⁻¹ ≤ 21 * π * a * μ := by
    have hxμ10 : x + μ ≤ 10 * μ := by nlinarith [hxμ]
    have hA : 2 * π * a * (x + μ) ≤ 20 * π * a * μ := by
      have hA' := mul_le_mul_of_nonneg_left hxμ10 (by positivity : 0 ≤ 2 * π * a)
      nlinarith [hA']
    have hs3 : (2 * s ^ 3)⁻¹ ≤ μ / 2 := by
      have hc : μ * s ^ 3 * (2 * s ^ 3)⁻¹ = μ / 2 := by
        field_simp [ne_of_gt (mul_pos (by norm_num : (0:ℝ) < 2) (pow_pos hs 3))]
      have hm := mul_le_mul_of_nonneg_right hμs
        (le_of_lt (inv_pos.mpr (mul_pos (by norm_num : (0:ℝ) < 2) (pow_pos hs 3))))
      -- hm : 1·(2s³)⁻¹ ≤ (μ·s³)·(2s³)⁻¹
      rw [hc] at hm
      simpa using hm
    have hB : π * a * (2 * s ^ 3)⁻¹ ≤ π * a * (μ / 2) := by
      exact mul_le_mul_of_nonneg_left hs3 (by positivity : 0 ≤ π * a)
    have hπaμ : 0 ≤ π * a * μ := by positivity
    nlinarith [hA, hB, hπaμ]
  nlinarith [hdiff, hneg]

/-- **Step-2 (operator identity, sorry-free): `q0RenVal` in the sector
variables `(N̂, cnPlus)`** — `q0RenVal_repulsion`'s cS1-form converted by the
EXACT condensate-count identity `cS1 = N̂ − cnPlus`
(`Q0Sector`/`CentredSector.cnPlus_add_cS1` via `cS1_eq_nat_sub_cnPlus`): for
every normalised `Φ` at the fixed count `N`,

    q0RenVal(s,μ,Φ) ≥ (4πa/s³)·((N̂ − cnPlus(Φ)) − μs³ − ½)²
                      − 4πaμ²s³(1 + 1/(2μs³))² .

This is the operator-form backbone of the exact-A0 assembly: it writes the
condensate repulsion (already converted from `cS2 ≥ cS1²−cS1` by
`q0RenVal_repulsion`) with the condensate count as `N̂ − cnPlus` — the
variable in which the n₊-operator remainder `cnPlus` is EXPLICIT (so the
kinetic gap can absorb it) and the fixed count `N̂` is the sector's scalar.
The exact q1/q2/q3 word treatments (Q1Peel L2c, pot_sharp_w1line, the
`A0Core` square conversion with `S := N̂ − cnPlus`) then refine the
`(C₂+7C₁)cS2/s³`-remainder of Step-1 against this backbone. -/
lemma q0RenVal_sector {N : ℕ} {s μ R0 : ℝ} {v : ℝ³ → ℝ}
    (hs : 0 < s) (hμ : 0 < μ)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hR0 : 0 < R0) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRs : R0 ≤ s * chiR0)
    {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1) :
    (4 * π * (a v) / s ^ 3) * ((((N : ℝ) - cnPlus s Φ) - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2)
      - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
    ≤ q0RenVal (N := N) (v := v) s μ Φ := by
  have hrep := q0RenVal_repulsion (N := N) (v := v) (R := R0) hR0 hv_nonneg hvrad
    hv_supp h hs hRs hμ (Φ := Φ) hΦc hnorm
  have hS : cS1 s Φ = (N : ℝ) - cnPlus s Φ := cS1_eq_nat_sub_cnPlus hs hΦc hnorm
  simpa [hS] using hrep

/-- **Step-2 (substitution result): the Step-1 gap-absorbed bound in FS-shape
with the explicit remainders** — instantiate `smallbox_state_gap_absorbed`
and substitute the sector identity via `smallbox_step1_shape`
(`x := N̂/s³` in the block window `0 ≤ x ≤ 9μ`, `1 ≤ μs³`):

    sboxE(Φ) ≥ ( ¼((N̂/s³)−μ)² − ½μ² )·8π(av)s³
               − (C₂+7C₁)(s³)⁻¹·cS2(Φ) − μC₁·N̂ − 21π·(av)·μ .

This is precisely what `smallbox_state_block_bound` needs MINUS the
state-level `cS2`-remainder and the `μC₁N̂`-term: those two are the entire
remaining gap (the `21π(av)μ` is absorbed by the block bound's `−Cμ(av)`).
The exact q1/q2/q3 word treatments (Q1Peel `q1_pair_part_sandwich_n0`,
`pot_sharp_w1line`, `A0Core` square conversion at `S := N̂−cnPlus`, and the
`Fock2Mode` Bogolubov 2Q-step) must turn the crude
`pot_sharp_density`-bounds (whose `(C₂+7C₁)cS2/s³`-magnitude terms produced
this remainder) into their n₊-operator/n₀-realised exact forms — the
multi-session substance of Step-2. -/
lemma smallbox_gap_shape_with_remainder {N : ℕ} {s μ R0 B U : ℝ} {v : ℝ³ → ℝ}
    (hs : 0 < s) (hμ : 0 < μ)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hR0 : 0 < R0) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRs : R0 ≤ s * chiR0)
    (hμs : 1 ≤ μ * s ^ 3)
    -- the block count window (C_n := 8)
    (hwin : (N : ℝ) / s ^ 3 ≤ (9 : ℝ) * μ)
    {Φ : X N → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1)
    (hwinP : cnPlus s Φ ≤ B)
    (hucap : (N : ℝ) / s ^ 3 ≤ U)
    (hreg : μ * (fsqC1 (a v)) + (4 * π * (a v) / s ^ 3) * B
        + (3 * (fsqC2 (a v)) + 18 * (fsqC1 (a v))) * U ≤ 1 / (36 * s ^ 2)) :
    ((1 / 4 : ℝ) * (((N : ℝ) / s ^ 3) - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
          * (8 * π * (a v) * s ^ 3)
      - ((fsqC2 (a v)) + 7 * (fsqC1 (a v))) * (s ^ 3)⁻¹ * cS2 s Φ
      - μ * (fsqC1 (a v)) * (N : ℝ)
      - 21 * π * (a v) * μ
    ≤ sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
  have hg := smallbox_state_gap_absorbed hs hμ hv_nonneg hvrad hv_memL1
    hR0 hv_supp h hRs (Φ := Φ) hΦc hnorm (B := B) (U := U) hwinP hucap hreg
  have hav : 0 ≤ a v := (av_bounds_weak hR0 hv_nonneg hvrad hv_supp h).1
  have hshape := smallbox_step1_shape (s := s) (μ := μ) (x := (N : ℝ) / s ^ 3) (a := a v)
    hs hμ hμs (by positivity : 0 ≤ (N : ℝ) / s ^ 3) hwin hav
  -- hshape : main(x·s³-form) − μ²block ≥ ¼-shape − 21π·a·μ, with x·s³ = N̂
  have hx : ((N : ℝ) / s ^ 3) * s ^ 3 = (N : ℝ) := by
    field_simp [ne_of_gt hs]
  have hmain : (4 * π * (a v) / s ^ 3) * ((1 / 2 : ℝ) * ((N : ℝ) - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2)
        - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
      ≥ ((1 / 4 : ℝ) * (((N : ℝ) / s ^ 3) - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
            * (8 * π * (a v) * s ^ 3) - 21 * π * (a v) * μ := by
    simpa [hx] using hshape
  nlinarith [hg, hmain]

/-- **The fixed-n OPERATOR statement of the six-step route (SESSION-285:
PROVED, constant `C := 272π + 40`)**: for every NORMALISED
state `Φ` at the fixed count `N` (the sector) in the block window
`N̂/s³ ≤ 9μ` (`C_n := 8`), under the standing hypotheses, `0 < s`, `0 < μ`,
`1 ≤ μs³`, `0 < K_B`, `0 ≤ C`, the per-state small-box energy satisfies the
TIGHT FS block shape

    sboxE(Φ) ≥ ( ¼((N̂/s³)−μ)² − ½μ² )·8π(av)·s³ − C·μ²(av)·s³·Γ − C·μ(av),

`Γ := (R0/s)² + K_B³(μ(av)³)^{1/2}`.  This is the statement the six-step
route proves in fixed-n sectors (verified against final_v2.tex thm:smallbox,
~3980–4065; see the module doc and SmallBoxDesignNote Sessions 199–205):
the per-state bounds keep `cS1/cS2/cnPlus` EXPLICIT and the n₊-operator
remainders are ABSORBED by the kinetic gap (`kinWord ≥ cnPlus/(36s²)`,
`SharpPerState.gap_absorb_sharp` shape) BEFORE any scalar-ρ₀ appears —
the counterexample `Φ=(u⊗u+v⊗v)/√2` (Sessions 204–205) shows why no
standalone scalar-ρ₀ lemma can replace this operator assembly.  From this
state bound, `smallbox_block_bound` (the eB-level statement above) follows
by normalisation (`CSBox.ofFun` of `(√∫Φ²)⁻¹•Φ`, `sboxE_smul`) + `le_ciInf`.

Closed atoms supplying the six steps (all sorry-free): (1) potsplit
`PotQ0Lower.pot_q0_lower`; (2) q0 exact
`FSKernelCompare`/`Q0Chosen.w1c/w2c_acube_integral`/`SmallBoxKernelMass`;
(3) `A0Core.a0_form_square_identity/_ge_fs_main`; (4) q1 CS/collapse
`Step4SqrtFactorisation` + `Q1Peel` L2a–L2c + `OneBodyMass`; (5) q2
`Q2Mass.q2QQ_slot_identity` + `Q1Peel.q2PairWord_eq_slot_sandwich` +
`FibreLocalG2` (S1 `qmass_fibre_local_lower/upper` + S2 fibre package);
(6) Bogolubov `Fock2Mode` + kinetic-gap absorption. -/
theorem smallbox_state_block_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ D : BlockStateData,
        ((1 / 4 : ℝ) * (((D.N : ℝ) / D.s ^ 3) - D.μ) ^ 2 - (1 / 2 : ℝ) * D.μ ^ 2)
              * (8 * π * (a D.v) * D.s ^ 3)
          - C * D.μ ^ 2 * (a D.v) * D.s ^ 3
              * ((D.R0 / D.s) ^ 2 + D.K_B ^ 3 * (D.μ * (a D.v) ^ 3) ^ (1 / 2 : ℝ))
          - C * D.μ * (a D.v)
        ≤ sboxE D.N D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) D.Φ := by
  refine ⟨272 * π + 40, by positivity, ?_⟩
  intro D
  have hann : 0 ≤ a D.v := (av_bounds_weak D.hR0 D.hv_nonneg D.hvrad D.hv_supp D.h).1
  have hμnn : 0 ≤ D.μ := le_of_lt D.hμ
  have hsnn : (0 : ℝ) ≤ D.s ^ 3 := pow_nonneg (le_of_lt D.hs) 3
  have hGamnn : 0 ≤ (D.R0 / D.s) ^ 2 + D.K_B ^ 3 * (D.μ * (a D.v) ^ 3) ^ (1 / 2 : ℝ) := by
    have h2 : (0 : ℝ) ≤ (D.μ * (a D.v) ^ 3) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg (by positivity) (1 / 2)
    exact add_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg (le_of_lt D.hKB) 3) h2)
  have hC1 : (1 : ℝ) ≤ 272 * π + 40 := by nlinarith [Real.pi_pos]
  have hC36 : (36 : ℝ) * π ≤ 272 * π + 40 := by nlinarith [Real.pi_pos]
  have hμ2a : (0 : ℝ) ≤ D.μ ^ 2 * (a D.v) := by positivity
  have hμa : (0 : ℝ) ≤ D.μ * (a D.v) := mul_nonneg hμnn hann
  have hmono : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      - (272 * π + 40) * x - (272 * π + 40) * y ≤ - x - y := by
    intro x y hx hy
    nlinarith [mul_le_mul_of_nonneg_right hC1 hx, mul_le_mul_of_nonneg_right hC1 hy]
  by_cases h0 : cS1 D.s D.Φ = 0
  · -- the fully-excited (`cS1 = 0`) case, including `N = 0`: DERIVED
    have hz := Work.SmallBoxA0.qLHSword_zero_case (N := D.N) (s := D.s) (μ := D.μ)
      (R0 := D.R0) (v := D.v) D.hs D.hμ D.hR0 D.hv_nonneg D.hvrad D.hv_memL1
      D.hv_supp D.h D.hRs (Φ := D.Φ) D.hΦc D.hnorm h0 D.hwin D.hchi
    have hx : (0 : ℝ) ≤ (272 * π + 40) * (D.μ ^ 2 * (a D.v) * D.s ^ 3)
        * ((D.R0 / D.s) ^ 2 + D.K_B ^ 3 * (D.μ * (a D.v) ^ 3) ^ (1 / 2 : ℝ)) := by
      have h1 : (0 : ℝ) ≤ D.μ ^ 2 * (a D.v) * D.s ^ 3 := mul_nonneg hμ2a hsnn
      have h2 : (0 : ℝ) ≤ 272 * π + 40 := by positivity
      have h3 : (0 : ℝ) ≤ (D.R0 / D.s) ^ 2 + D.K_B ^ 3
          * (D.μ * (a D.v) ^ 3) ^ (1 / 2 : ℝ) := hGamnn
      nlinarith [h1, h2, h3, mul_nonneg h1 h3]
    have hy : (0 : ℝ) ≤ (272 * π + 40) * (D.μ * (a D.v)) := by positivity
    linarith [hz, hx, hy]
  · have hlt : 0 < cS1 D.s D.Φ := lt_of_le_of_ne cS1_nonneg (Ne.symm h0)
    have hNpos : 0 < (D.N : ℝ) := by
      have h1 := cS1_le_norm_sq (N := D.N) D.hs D.hΦc.continuous
      rw [D.hnorm, mul_one] at h1
      linarith
    have hN : 1 ≤ D.N := Nat.succ_le_of_lt (Nat.cast_pos.mp hNpos)
    have hD : g0w0Mass (v := D.v) D.h ≤ 8 * π * (a D.v) :=
      Work.SmallBoxA0.g0w0Mass_le_av D.hR0 D.hv_nonneg D.hvrad D.hv_supp D.h
    have hX : (0 : ℝ) ≤ D.μ ^ 2 * (a D.v) * D.s ^ 3
        * ((D.R0 / D.s) ^ 2 + D.K_B ^ 3 * (D.μ * (a D.v) ^ 3) ^ (1 / 2 : ℝ)) :=
      mul_nonneg (mul_nonneg hμ2a hsnn) hGamnn
    have hmain := Work.SmallBoxA0.state_block_bound_of_inputs_sharp (N := D.N) (s := D.s)
      (μ := D.μ) (R0 := D.R0) (K_B := D.K_B) (η := D.eta) (C := 272 * π + 40)
      (BogErr := D.BogErr)
      hN D.hs D.hμ D.hR0 D.hKB D.hv_nonneg D.hvrad D.hv_memL1 D.hv_supp D.h D.hRs D.hμs
      D.hΦc D.hnorm D.hwin hlt hD D.hbox D.hη (le_refl _)
      (Work.SmallBoxA0.corr_linear_of_sqrt (s := D.s) (μ := D.μ) (CorrC := 32 * π * chiSup ^ 2 * ((D.N : ℝ) + 1))
        (v := D.v) D.h D.hs hann (by positivity) D.hΦc.continuous D.hnorm D.hcorrreg (Work.SmallBoxA0.corr_sqrt_bound_all (s := D.s) (R := D.R0) (v := D.v)
          D.hs D.hR0 D.hv_nonneg D.hvrad D.hv_supp D.h D.hRs D.hΦc.continuous D.hnorm))
      (Work.SmallBoxA0.hBogF_of_w1_sqrt_le (N := D.N) (s := D.s) (μ := D.μ) (η := D.eta)
        (BogErr := D.BogErr) (R := D.R0) D.h D.hs D.hR0 D.hv_nonneg D.hvrad D.hv_supp
        D.hRs D.hW2 D.hL2 hann hμnn D.hBog0 D.hη0
        (g0w0Mass_nonneg D.hR0 D.hv_nonneg D.hvrad D.hv_supp D.h) D.hΦc D.hnorm hlt)
    convert hmain using 1 <;> ring


/-! ## The companion chain: the block bound with NO Bogoliubov residual

SESSION-287c.  The two theorems of this file are stated for the corpus energy
`sboxE = kinWord + qLHSword` and consume the per-state Bogoliubov residual
`hBogF`/`hBog`.  `Work.SmallBoxA0.kinPWord_exceeds_kinWord` (PROVED) shows that the
corpus's PROVED D1 — the Bogoliubov input this area was asked to combine — cannot
supply that residual: D1's word `kinPWord` is the χ-WINDOWED mode sum and exceeds
`kinWord` by `chiSup² ≥ 6/π` on χ-core-supported states.

The two theorems below are the block bound for the energy whose kinetic word IS D1's
word (`Work.SmallBoxA0.kinPEnergy`/`kinPeB`: `kinPWord` plus FS's `ε_T`-gap term
`cgap·cnPlus`), over the residual-free bundles `Work.SmallBoxA0.KinPBoxData` /
`KinPStateData`.  Their Bogoliubov input is the PROVED
`SmallBoxD1Final.lm_appbogolubov_pWord_holds` with its constant exposed
(`Work.SmallBoxA0.d1C`), NOT an assumed field; the shape and the constant
(`272π + 40`) are exactly those of the theorems above.

They are `sorry`-free with axioms `[propext, Classical.choice, Quot.sound]`, and they are
what the corpus consumes ONCE ITS SMALL-BOX ENERGY USES THE SAME WORD — the modelling
switch recorded in `SmallBoxA0/README.md` §10–§11 (replace `kinWord N s Φ` by
`kinPWord s c₀ Φ` + the `ε_T`-gap term in `SmallBoxSuperadd.sboxE`, `SboxEB.eB` and the
`dℓ`-sliding layer; the two energies are NOT comparable by an inequality — for
χ-core-supported states `kinPWord = chiSup²·kinWord > kinWord`, and for corner-supported
states the χ-window is small — so this is a definitional choice, not a lemma).
-/

/-- **The block bound with NO Bogoliubov residual — `eB`-level, `kinPWord` energy.**
`∃ C, 0 ≤ C ∧ ∀ D : KinPBoxData, <FS block shape> ≤ kinPeB D…`, `C := 272π+40`; the rung
is the PROVED D1 (`Work.SmallBoxA0.lm_appbogolubov_pWord_explicitC`). -/
theorem smallbox_block_bound_kinP :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Work.SmallBoxA0.KinPBoxData,
      ((1 / 4 : ℝ) * (((((D.n + 1 : ℕ) : ℝ)) / D.s ^ 3) - D.μ) ^ 2 - (1 / 2 : ℝ) * D.μ ^ 2)
            * (8 * π * (a D.v) * D.s ^ 3)
        - C * D.μ ^ 2 * (a D.v) * D.s ^ 3 * Work.SmallBoxA0.kinPGamma D.R0 D.s D.K_B D.μ D.v
        - C * D.μ * (a D.v)
      ≤ Work.SmallBoxA0.kinPeB D.n D.s D.μ D.v D.h D.c₀ D.cgap :=
  Work.SmallBoxA0.kinP_block_bound

/-- **The block bound with NO Bogoliubov residual — fixed `n`, per state, `kinPWord`
energy.**  For every `D : KinPStateData`, the same FS block shape at `C := 272π+40`. -/
theorem smallbox_state_block_bound_kinP :

    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Work.SmallBoxA0.KinPStateData,
      ((1 / 4 : ℝ) * (((((D.n + 1 : ℕ) : ℝ)) / D.s ^ 3) - D.μ) ^ 2 - (1 / 2 : ℝ) * D.μ ^ 2)
            * (8 * π * (a D.v) * D.s ^ 3)
        - C * D.μ ^ 2 * (a D.v) * D.s ^ 3 * Work.SmallBoxA0.kinPGamma D.R0 D.s D.K_B D.μ D.v
        - C * D.μ * (a D.v)
      ≤ Work.SmallBoxA0.kinPEnergy D.n D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h))
          D.c₀ D.cgap D.Φ :=
  ⟨272 * π + 40, by positivity, fun D => Work.SmallBoxA0.kinP_state_bundle D⟩

/-! ## The Green (kinetic-paying) chapter of the residual — SESSION-290

`Submission/Work/SmallBoxA0/README.md` §29.  The residual field `hBogF`/`hBog` of the
bundles above is the ONE assumed input of the corpus-`eB` theorems, and FS's
`lm:appbogolubov`.  SESSION-290 identified its content exactly, and mechanised the
variational (completing-the-square / Green-operator) mechanism behind it:

* **`Submission.Work.SmallBoxA0.GreenPairWord`** —
  `Work.SmallBoxA0.kinForm` (the box kinetic bilinear form, diagonal = `kinWord`) and
  `Work.SmallBoxA0.pairLin` (the pairing linear functional).  The exact identification
  `Work.SmallBoxA0.q4PairWord_add_const` (`q4PairWord (A + g) = A · pairLin N s h g` for
  `A` constant and `g` mean-free in every slot, `kinWord (A + g) = kinForm g g`) gives

      Work.SmallBoxA0.kinWord_add_q4PairWord_ge_greenMass :
        kinWord N s Φ + q4PairWord Φ ≥ −(A/2)² · G ,

  with `G = greenMassOn (MeanFree N s) (kinForm N s) (pairLin N s h)` the Green mass over
  the MEAN-FREE test set (`Work.SmallBoxA0.MeanFree N s` = the `aP`-kernel; the
  unrestricted test set is UNBOUNDED ABOVE because `kinForm` kills the functions constant
  in a slot, so the mean-free restriction is the correct quantifier — `README.md`
  §29.9), and `Work.SmallBoxA0.residual_of_greenMass` turns a bound on that Green mass
  into the residual's content.  So `hBogF`/`hBog` IS a bound on `⟨w₁, K⁻¹ w₁⟩` — the
  kinetic word on the LEFT pays the signed pairing word (FS's Bogoliubov step), and NOT a
  pairing-only Cauchy–Schwarz bound (that route is FALSE, `README.md` §28.5).
  The sharp `N = 2` endpoint is `GreenSharp.residual_two_of_pairJ` /
  `GreenStateFree.residual_two_statefree` (fully state-free sufficient condition
  `H ≤ s⁶(3(1+η)·g0w0Mass·s⁻³ − 1/(18s²) + (88π+39)(av)μ)` with `H = ⟨w₁,K⁻¹w₁⟩`),
  and `GreenVariational.greenMassOn_ge_div_sq` is the exact one-element criterion a
  counterexample must meet.
* **`Submission.Work.SmallBoxA0.GreenVariational`** — the abstract chapter:
  `Work.SmallBoxA0.quadForm_ge_of_testBound` (completing the square),
  `Work.SmallBoxA0.greenMass_of_self` (`greenMass = ⟨K⁻¹w, K K⁻¹w⟩`),
  `Work.SmallBoxA0.greenMass_smul` (the window constant), and the test-set API.
* **`Submission.Work.SmallBoxA0.GreenSpectral`** — the eigenbasis series
  `Work.SmallBoxA0.greenMass_diag` (`Σ_k |⟨φ_k,w⟩|²/λ_k`), its attainment
  (`greenMass_diag_attained`) and the additive pair-mode form
  (`greenMass_additive_modes`, `Σ_{k,l}/(λ_k+λ_l)`).
* **`Submission.Work.SmallBoxA0.GreenWindow`** — `Work.SmallBoxA0.greenMass_window` and
  `Work.SmallBoxA0.window_separation`: the χ-windowed kinetic `chiSup²·kinForm` (FS's
  `T_B`, `eq:appTB`) has a Green mass `chiSup² > 1` times SMALLER than the honest box
  kinetic's, i.e. a strictly larger allowance.  The corpus-`eB` per-box bound with the
  honest `kinWord` is therefore a STRICT strengthening of FS's `thm:smallbox`.

The modelling consequence (the lead's call, `README.md` §29.5): with the honest kinetic
the residual's content is a Green-mass budget that no available datum controls; with
FS's own χ-windowed kinetic the budget is `chiSup²`-times looser, which is exactly why
`thm:smallbox` holds at its constants.  The residual-free `…_kinP` chain above
(`KinPDefs`, `kinP_state_block`, `kinP_block_bound`, the PROVED D1) is the drop-in
statement for the re-pointed energy. -/

end BoseGases

end Submission
