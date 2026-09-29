import Mathlib
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Helpers
import Submission.Work.CRed.c_li_of_pos
import Submission.Work.CAsm.c_pos
import Submission.Work.Holonomy3.holonomy_bound_l2
import Submission.Work.ZeroEst.zero_estimate
import Submission.Work.C17.seventeen_indep
import Submission.Work.C7.lemma_seven
import Submission.Work.CDen.c_denoms
import Submission.Work.Pure.pure_facts
import Submission.Work.CDcl.c_dclosed
import Submission.Work.CPull.c_pullbacks
import Submission.Work.CLift.p_lift_cont
import Submission.Work.OdeCont.ode_continuation
import Submission.Work.CRad.p_radius
import Submission.Work.CNum.c_numerics
import Submission.Work.CLoc.c_location
import Submission.Work.Haupt.haupt_facts
import Submission.Work.CPsi.psiC_facts
import Submission.Work.CPhi.phi_lift
import Submission.Work.Tau.tau_values
import Submission.Transcendence.LindemannC
import Submission.Transcendence.LindemannWeierstrass
import Submission.CDT.TheoremA_leaf
import Submission.CDT.L2chi3Real
import Submission.CDT.L2chi3Corollary
import Submission.CDT.ZagierH
import Submission.CDT.ZagierHBC
import Submission.CDT.EichlerInput
import Submission.CDT.L2chi3Cintegral
import Submission.CDT.L2chi3Zagier
import Submission.CDT.ZagierWZ
import Submission.CDT.SympH
import Submission.CDT.SympDescent
import Submission.CDT.SympZagier
import Submission.CDT.SympExplicitode
import Submission.CDT.SympExplicitodeBridge
import Submission.CDT.SympExplicitodeFinal
import Submission.CDT.LogPowersIndependence
import Submission.CDT.LogPowersFunctional
import Submission.CDT.SympPullback
import Submission.CDT.SympDenom
import Submission.CDT.LogHadamard
import Submission.CDT.LogUnlikelyG
import Submission.CDT.LogMIdentities
import Submission.CDT.CintegralOne
import Submission.CDT.CintegralCore
import Submission.CDT.CintegralGeneral
import Submission.CDT.Aintegral
import Submission.CDT.AintegralAssembled
import Submission.CDT.AintegralUntransformed
import Submission.CDT.OrderFrobenius
import Submission.CDT.RatFuncOrder
import Submission.CDT.RatFuncDeriv
import Submission.CDT.EulerIndicial
import Submission.CDT.EliminationData
import Submission.CDT.ElimOperator
import Submission.CDT.OrdAtT
import Submission.CDT.FrobeniusLocal
import Submission.CDT.ElimReduction
import Submission.CDT.EliminationDataC
import Submission.CDT.ElimOperatorC
import Submission.CDT.ElimReductionC
import Submission.CDT.FrobeniusApply
import Submission.CDT.FrobeniusBeta
import Submission.CDT.FrobeniusGeneric
import Submission.CDT.DivisorBound
import Submission.CDT.DnumDegree
import Submission.CDT.InfinityBound
import Submission.CDT.FinalStep
import Submission.CDT.FinalLinear
import Submission.CDT.RelationToSystem
import Submission.CDT.RatFuncConstants
import Submission.CDT.FuncFieldTranscendence
import Submission.CDT.DerivOrderAt
import Submission.CDT.LogTranscendence
import Submission.CDT.Residue
import Submission.CDT.ResidueMul
import Submission.CDT.LogMultiplicative
import Submission.CDT.LogMultiplicativeField
import Submission.CDT.LogRelation
import Submission.CDT.LogProduct
import Submission.CDT.LogIndependence
import Submission.CDT.WeightTwo
import Submission.CDT.DifferentialConstants
import Submission.CDT.LogProductIndependence
import Submission.CDT.KolchinHeart
import Submission.CDT.KolchinField
import Submission.CDT.KolchinAlgebraic
import Submission.CDT.KolchinTranscendental
import Submission.CDT.RatFuncDifferential
import Submission.CDT.LogAlgIndependent
import Submission.CDT.LogAlgLW
import Submission.CDT.LLData
import Submission.CDT.CsideLocal
import Submission.CDT.CsideInfty
import Submission.CDT.CsideDivisor
import Submission.CDT.Discrepancy
import Submission.CDT.DiscrepancyFour
import Submission.CDT.PureDenom
import Submission.CDT.LocationSing
import Submission.CDT.LcmGe
import Submission.CDT.BorelSimple
import Submission.CDT.LcmUniform
import Submission.CDT.LcmGeUniform
import Submission.CDT.LcmLe
import Submission.CDT.Lcm2Bound
import Submission.CDT.IntegratedLcm
import Submission.CDT.MvVanishing
import Submission.CDT.MvVanishingCount
import Submission.CDT.MvVanishingCartesian
import Submission.CDT.StepRiemann
import Submission.CDT.RiemannSum
import Submission.CDT.ModelRiemann
import Submission.CDT.FineHolonomy
import Submission.CDT.Rearrangement
import Submission.CDT.EtaleCover
import Submission.Work.AAsm.a_leaf
import Submission.Work.A14.fourteen_indep
import Submission.Work.ADen.a_denoms
import Submission.Work.ADcl.a_dclosed
import Submission.Work.APull.a_pullbacks
import Submission.Work.PScale.pullback_scale
import Submission.Work.ALift.h_lift_cont
import Submission.Work.APhi.phi_lift_gen
import Submission.Work.PureP.pure_pullbacks
import Submission.Work.APsi.psiA_facts
import Submission.Work.ANum.a_numerics
import Submission.Work.ZagBI.zagier_b_integrality
import Submission.Work.ZagC.zagier_c_integrality

/-!
**STATUS (2026-09-29): `cdt_linearIndependent` is PROVED, with no `sorry` and axioms
`[propext, Classical.choice, Quot.sound]` only.**  The two deep leaves described below
(`cdt_theoremA_leaf_gap`, `cdt_theoremC_li`) are closed by the paper's arithmetic-holonomy method in
`Submission/Work/*`: holonomy bound with `l ≤ 2` and Lang's zero estimate, D-closedness and
`[1..n]²`-denominators of the Zagier series, the 14/17-function independence, pullbacks along explicit
slit/lune conformal maps, and certified numerics (for Theorem A an integer ball-arithmetic certificate
checked by `decide +kernel`, `Submission/Work/Cert`).  Historical notes below that speak of open
leaves or remaining `sorry`s predate this and are kept only as a record.

# `Submission.cdt_linearIndependent`

Theorems **A** and **C** of Calegari–Dimitrov–Tang,
*The linear independence of 1, ζ(2), and L(2, χ₋₃)*, arXiv:2408.15403.

## What the statement is

With `χ : ZMod 3 → ℂ := ![0, 1, -1]` (the nontrivial Dirichlet character
mod 3, `χ₋₃`), the claim is the conjunction of

* **Theorem A** (`cdt_theoremA` below): `1, ζ(2), L(2, χ₋₃)` are
  `ℚ`-linearly independent in `ℂ`; equivalently (via
  `Submission.Helpers.linearIndependent_cons3_iff` and
  `riemannZeta_two`) the number `L(2,χ₋₃)/π²` is irrational and
  `L(2,χ₋₃)` is not of the form `a + b·ζ(2)`, `a,b ∈ ℚ`.
* **Theorem C** (`cdt_theoremC` below): for integers `m,n ∉ {-1,0}` with
  `10⁶·|m-n| < |n|` the product `lm·ln` of `lm = log(1+1/m)`,
  `ln = log(1+1/n)` is irrational, and for `m ≠ n` the four numbers
  `1, lm, ln, lm·ln` are `ℚ`-linearly independent.

## Why the proof is not yet complete

Theorems A and C are the main results of the 2024 paper; both are proved
there by a new method (arithmetic holonomy bounds for holonomic functions,
with §6 multivariable / §7 Arakelov–Bost paths), and neither result nor its
prerequisites exist in the pinned Mathlib (in particular Mathlib at this
revision contains only the analytic part of Lindemann–Weierstrass, and no
transcendence or irrationality results for `L(2,χ₋₃)` or for products of
logarithms of rationals).  After full leaf-decomposition and assembly,
exactly **two** deep leaves remained; **both are now PROVED** (see the status note at the top of
this docstring), so `cdt_linearIndependent` is proved in full.  The two former leaves were:

```lean
-- Theorem A is ASSEMBLED in full below (`cdt_theoremA`, no `sorry`) modulo
-- its single isolated atomic leaf (CDT mainA):
lemma cdt_theoremA_leaf_gap : Submission.CDT.theoremA_leaf := by
  -- deep: L(2,χ₋₃) ∉ ℚ + ℚ·ζ(2), CDT Theorem mainA (arithmetic holonomy)

-- Theorem C, m ≠ n: the irrationality half `cdt_theoremC_irr_ne` is
-- ASSEMBLED in full below (no `sorry`) as the `d`-coefficient case of the
-- four-number independence leaf (`irr_of_cons4_li`); the single remaining
-- m ≠ n obstruction is:
lemma cdt_theoremC_li (m n : ℤ) : ... (m ≠ n → LinearIndependent ℚ ![1, lm, ln, lm * ln]) := by
  -- deep: CDT Theorem logsmain part 2 (arXiv:2408.15403 §"Products of two logarithms")
```

**What is proved around them.**  The `m = n` degenerate case of the
irrationality half is CLOSED: the paper dismisses it as "a trivial
consequence of the transcendence of `log r` for `r > 0` in `ℚ \{1\}`",
and that transcendence is fully formalized in the Lindemann–Weierstrass
chapter (`LindemannC.cexp_transcendental_of_algebraic_ne_zero` →
`LindemannC.transcendental_log_rat` →
`LindemannC.irrational_log_one_add_inv_sq`), giving
`cdt_theoremC_irr_self`.  Moreover the whole `m ≠ n` irrationality half
`cdt_theoremC_irr_ne` is PROVED: it is exactly the `d`-coefficient case of
the four-number independence leaf `cdt_theoremC_li` (`irr_of_cons4_li`),
so the full irrationality half `cdt_theoremC_irr` is PROVED once
`cdt_theoremC_li` is.  Theorem A's three-term statement `cdt_theoremA` is
assembled in full from `cdt_theoremA_leaf_gap` via the proved equivalence
`Submission.CDT.theoremA_iff_leaf` (the `1, ζ(2)` part is killed by the
transcendence of `ζ(2)` from the Lindemann–Weierstrass chapter).

Everything else about the statements (definitional shape of `ZMod 3`, the
meaning of `ZMod.LFunction χ 2` as the classical series `Σ χ(n)/n²`,
`riemannZeta 2 = π²/6`, the component form of the independence assertions,
and the elementary `ℤ`-arithmetic of the hypothesis) is recorded and proved
in `Submission.Helpers`.  **No axiom, `sorry`, or other unsound step is
used anywhere in this repository**; the two former leaves
(`cdt_theoremA_leaf_gap`, `cdt_theoremC_li`) are proved below: Theorem A by
`Work.AAsm.a_leaf`, Theorem C by `Work.CRed.c_li_of_pos`.
-/

namespace Submission

open Complex
open scoped BigOperators

/-- **The former isolated obstruction of Theorem A — now PROVED** (CDT `mainA`,
arXiv:2408.15403): the *atomic leaf* `theoremA_leaf` of
`Submission.CDT.TheoremA_leaf` — the claim that `L(2,χ₋₃)` is not a
rational linear combination of `1` and `ζ(2)`:

```lean
lemma cdt_theoremA_leaf_gap : Submission.CDT.theoremA_leaf
-- theoremA_leaf : ∀ a b : ℚ, ZMod.LFunction χ₋₃ 2 ≠ (a : ℂ) + (b : ℂ) * riemannZeta 2
```

Everything else about Theorem A is PROVED: the three-term statement
`LinearIndependent ℚ ![1, ζ(2), L(2,χ₋₃)]` is equivalent to this leaf
(`Submission.CDT.theoremA_iff_leaf`, both directions — the `1, ζ(2)`
part is killed by the transcendence of `ζ(2)`, proved in the
Lindemann–Weierstrass chapter), and the assembly of that equivalence into
`cdt_theoremA` below is completed here.

**Why this leaf is open — precise dismantling.**  The paper (`mainA`)
proves the leaf by contradiction from the absurd `ℚ`-dependence, through
the following chain (see the "proof of mainA, dismantled" section of the
`TheoremA_leaf` module docstring for the node-by-node annotation with
formal statuses): (1) *functionsH/defabc*: `H = aH_A + bH_B + cH_C ∈
ℚ⟦x⟧` with denominators `[1..n]²`, ODE `L(H) = b + c/(1−x)`, and
overconvergence of `H_B − (L/2)H_A`, `H_C − (ζ(2)/4)H_A` through `1/9` —
the recurrences/ODE half is PROVED (`ZagierH`, `ZagierHBC`), the *`H_B`
overconvergence half is now PROVED too* (`overconvergesB_proved`, from the
fully proved `(Cintegral)` identity — see ledger item 2), so what remains of
node 1 is the Γ₀(6) Eichler-integral (modular) `[1..n]²`-integrality of
`bₙ`, `cₙ` together with the `H_C`-overconvergence, both absent from the
pinned Mathlib (`H_C`: the ζ-side analogue `Submission.CDT.Aintegral` states
the corresponding `(Aintegral)` identity and its overconvergence
reduction); (2) *defG*: `G = Sym⁺H`,
denominator type `[1..2n]²` — the symmetrization algebra (descent,
integrality of `G_A`, descent coefficients `g₀..g₁₁`, order-4 ODE
machinery, `Sym⁺`-linearity incl. the decomposition
`sympSym_ZagierH`) is PROVED.  The paper's own order-4 display
`(explicitode)` (`GA_odeLHS = 0`, target of module
`Submission.CDT.SympExplicitode`) is **NOW FULLY PROVED**
(`Submission.CDT.GA_odeLHS_eq_zero`, module
`Submission.CDT.SympExplicitodeFinal`, all three modules zero-`sorry`): the
Möbius pullback of the paper's operator, cleared to polynomials by
`(x-1)^19·Y'^7`, is an order-4 operator `Σ_j Mp_j d^j` (the *bridge*,
`Submission.CDT.SympExplicitodeBridge.cleared_pullback`, proved from the
chain-rule recursion `E_{i+1} = y′E_i′ − (2i−1)y″E_i` and the cleared
expansions `(x−1)^{3(i−1)}E_i = G_i`), and that operator is reduced to zero
on `F_0 = H_A + H_A∘σ = G_A∘Y` through the second-order ODEs of the two
branches `H_A` (`HA_ode`) and `H_A∘σ`
(`Commons.Analysis.Differential.ode_pullback_involution`) via the ODE
chains `a₂^k f^{(k+1)} = r_k f′ + s_k f` (`k ≤ 3`); injectivity of
`y ↦ sympY` then gives `GA_odeLHS = 0`.  The machine-checked certificate
that this argument was found from is in `Scratch/explicitode/README.md` +
`verify_all.py`.  The denominator-type/analytic claims are still
blocked by (1); (3) *Lemma `seven`* (the "pure functions" `Bᵢ(y)`): its first step — the
`ℚ(x)`-linear independence of the powers `1, log(1−x), …, log(1−x)^k`, which
the paper derives from the transcendence of `log` of a rational — is now
**PROVED** (`Submission.CDT.log_powers_linearIndependent`, module
`Submission.CDT.LogPowersIndependence`, built on the formalized
Lindemann–Weierstrass `transcendental_log_rat`); the remaining steps
(`Li₂(x)`, `J(x)`, the monodromy arguments of Lemma `seven` and of
*Lemma `14functions`* (functional linear
independence incl. the pure functions `Bᵢ`) — needs complex-analytic
monodromy/polylog theory, absent; (4) *arithmetic holonomy bounds*
(Bost–Charles slopes / Arakelov heights; τ-values `191/49`, `27/80`)
giving `m < 14` — ~150 pages absent.  Hence `cdt_theoremA_leaf_gap`
remains the single genuine gap of Theorem A; every surrounding provable
sub-lemma has been formalized and committed.

**Missing-lemma ledger (A-leaf; each entry is the exact statement the node
needs, with its discharge status).**
1. `EichlerInputB`, `EichlerInputC` (`Submission.CDT.EichlerInput`): the
   Γ₀(6)/Eichler-integral `[1..n]²`-integrality of `bₙ`, `cₙ` —
   *external modular input* (ground-checked through `n = 8`:
   `HB_denomType_five/six/seven/eight`, `HC_denomType_six/seven/eight`);
2. the `(Cintegral)` identity `CintegralIdentity`
   (`Submission.CDT.L2chi3Cintegral`) — Beukers double-integral evaluation;
   **NOW PROVED FOR ALL `n`** (`CintegralAssembled.CintegralIdentity_proved`),
   from the explicit parametric divergence certificate
   `Commons.Analysis.Integral.cintegral_recurrence_parametric` (fleet L130)
   through `CintegralIdentity_of_recurrence`; consequently the *analytic
   half* of `EichlerInputB` is unconditional
   (`overconvergesB_proved : OverconvergesUnit eichlerDiffB`) and
   `EichlerInputB` follows from the modular `[1..n]²`-integrality alone
   (`eichlerInputB_of_modular`);
   its `n = 0` **and `n = 1`** cases are PROVED
   (`CintegralIdentity_zero`: `J₀ = L(2,χ₋₃)` via the commons
   double-square-integral identity L61; `CintegralIdentityOne`:
   `3L − 2 = J₁` = `cintegral_identity_one`, module
   `Submission.CDT.CintegralOne` — the binomial-series double-integral
   evaluation `cintegralJ_one_eq_sum_W`; `cintegral_identity_le_one`
   assembles every `n ≤ 1`); the `n = 2` case is PROVED too
   (`CintegralIdentityAt_two`: `15L − 23/2 = J₂` =
   `cintegralJ_two_eq_sum_W`, module `Submission.CDT.CintegralTwo`, and
   `CintegralIdentityAt_three`: `93L − 145/2 = J₃` =
   `cintegralJ_three_eq_sum_W`, module `Submission.CDT.CintegralThree`,
   both driven by the commons creative-telescoping identities
   `sum_cintegralTwo_core_corrected` / `sum_cintegralThree_core`, and
   `CintegralIdentityAt_four`: `639L − 3993/8 = J₄` =
   `cintegralJ_four_eq_sum_W`, module `Submission.CDT.CintegralFour`
   (commons `sum_cintegralFour_core`)); and the cases `n = 5, 6, 7` are
   PROVED too — `CintegralIdentityAt_five`: `4653L − 727059/200 = J₅` =
   `cintegralJ_five_eq_sum_W` (module `Submission.CDT.CintegralFive`,
   commons `sum_cintegralFive_core`), `CintegralIdentityAt_six`:
   `35169L − 5495507/200 = J₆` (module `Submission.CDT.CintegralSix`,
   commons `sum_cintegralSix_core`), `CintegralIdentityAt_seven`:
   `272835L − 417806469/1960 = J₇` (module `Submission.CDT.CintegralSeven`,
   commons `sum_cintegralSeven_core`) — assembled as
   `cintegral_identity_le_seven : ∀ n ≤ 7, CintegralIdentityAt n` (module
   `Submission.CDT.CintegralAssembled`); and `CintegralIdentityAt_eight`:
   `2157759L − 66085799967/39200 = J₈` (module
   `Submission.CDT.CintegralEight`, commons `sum_cintegralEight_core`),
   `CintegralIdentityAt_nine`: `17319837L − 530455590781/39200 = J₉`
   (module `Submission.CDT.CintegralNine`, commons
   `sum_cintegralNine_core`), `CintegralIdentityAt_ten`:
   `140668065L − 4308248502993/39200 = J₁₀` (module
   `Submission.CDT.CintegralTen`, commons `sum_cintegralTen_core`),
   `CintegralIdentityAt_eleven`: `1153462995L − 4274588067098379/4743200 = J₁₁`
   (module `Submission.CDT.CintegralEleven`, commons
   `sum_cintegralEleven_core`), `CintegralIdentityAt_twelve`:
   `9533639025L − 1413218448827853/189728 = J₁₂` (module
   `Submission.CDT.CintegralTwelve`, commons `sum_cintegralTwelve_core`),
   `CintegralIdentityAt_thirteen`: `79326566595L − 49681644752988856791/801600800 = J₁₃`
   (module `Submission.CDT.CintegralThirteen`, commons
   `sum_cintegralThirteen_core`), `CintegralIdentityAt_fourteen`:
   `663835030335L − 415754993154999572883/801600800 = J₁₄` (module
   `Submission.CDT.CintegralFourteen`, commons `sum_cintegralFourteen_core`),
   `CintegralIdentityAt_fifteen`:
   `5582724468093L − 699283848231726007461/160320160 = J₁₅` (module
   `Submission.CDT.CintegralFifteen`, commons `sum_cintegralFifteen_core`),
   `CintegralIdentityAt_sixteen`:
   `47152425626559L − 2147724879365145978567/58298240 = J₁₆` (module
   `Submission.CDT.CintegralSixteen`, commons `sum_cintegralSixteen_core`),
   `CintegralIdentityAt_seventeen`:
   `399769750195965L − 11577240673264126122251355/37066020992 = J₁₇` (module
   `Submission.CDT.CintegralSeventeen`, commons `sum_cintegralSeventeen_core`),
   assembled as `cintegral_identity_le_seventeen : ∀ n ≤ 17` (module
   `Submission.CDT.CintegralAssembled`); **NEW**: the instances at
   `n = 18, …, 27` are PROVED too
   (`CintegralIdentityAt_eighteen` … `_twentyseven`, commons
   `sum_cintegral{Eighteen,...,TwentySeven}_core`), assembled as
   `cintegral_identity_le_thirtyFive : ∀ n ≤ 35` (degrees 28–35 added by the
   fleet cores `sum_cintegral{TwentyEight,...,ThirtyFive}_core`) — for `n ≤ 19` the
   per-degree analytic template that realised `Jₙ = Σₘ Wₙ(m)` inside the
   module is archived in `Scratch/archive_heavy/`, and every module
   `CintegralTwo`–`CintegralTwentyThree` is now the ~90-line *light* module
   generated by `Scratch/cintegral_generator/mklight_all.py` (it derives
   `CintegralIdentityAt n` from the general expansion below plus the
   commons core); and the tail is *reduced to
   a single parametric statement* by module `Submission.CDT.CintegralGeneral`:
   the **general-`n` Beukers expansion**
   `cintegralJ_eq_sum_W_gen : ∀ n, cintegralJ n = ∑' m, genW n m` with
   `genW n m = 9ⁿC(m+2n,2n)Σᵢ₌₀^{2n+1}(−1)ⁱC(2n+1,i)(3ⁿn!/∏_{k≤n}(3m+n+1+3k+i))²`,
   so that `CintegralIdentity_of_genW_sum` (in the same module) derives all
   of `CintegralIdentity` from the single `m`-sum evaluation
   `∀n, Σ'ₘ genW n m = L(2,χ₋₃)aₙ − 2bₙ`; equivalently
   `CintegralIdentity_of_recurrence` (`CintegralAssembled`) derives it from
   the single Zagier recurrence `(n+1)²J_{n+1} = (10n²+10n+3)Jₙ − 9n²J_{n−1}`
   for `J` (kernel bound `cubeKernel_le` PROVED via L57);
   `cintegralJ_bound` — PROVED (`cintegralJ_bound'`);
   together with the identity they discharge `OverconvergesUnit
   eichlerDiffB` (`overconvergesB_of_cintegral` PROVED);
   the **ζ-side** of the same node is now stated too (module
   `Submission.CDT.Aintegral`): the Möbius-transforms `G_A = mobTrans H_A`,
   `G_C = mobTrans H_C` of the paper's `(Gs)` display, the double integrals
   `Iₙ = ∫∫(1−s²)ⁿ(1−t²)ⁿ/(1−st)^{n+1}` with the paper's kernel bound
   (`|Iₙ| ≤ ζ(2)`, `zetaJ_bound` PROVED), the `n = 0` evaluation
   `I₀ = ζ(2)` (`zetaJ_zero_eq`), the **ζ-side recurrence PROVED**
   (`zetaJ_recurrence`: `(n+1)²I_{n+1} = −(7n²+7n+2)Iₙ + 8n²I_{n−1}`, from
   the commons `zetaintegral_recurrence_parametric`, fleet L136), the
   identity target `AintegralIdentity`
   **NEW (this session): the ζ-side identity `AintegralIdentity` is PROVED
   FOR ALL `n`** (module `Submission.CDT.AintegralAssembled`):
   `AintegralIdentity_proved : ζ(2)·[xⁿ]G_A − 4·[xⁿ]G_C = (−1)ⁿIₙ`, hence —
   with the kernel bound `zetaJ_bound` — the *transformed* ζ-side
   overconvergence `overconvergesCtr_proved : OverconvergesUnit
   (G_C − (ζ(2)/4)G_A)`, the ζ-side mirror of `overconvergesB_proved`.
   Ingredients: the Möbius pullback of the ODE (commons
   `ode_pullback_mobius`, fleet L137) gives `ODE78 G_A = 0` and
   `ODE78 G_C = 1` for the `(7,−8,2)`-operator; the coefficient extraction
   (commons `ode_78_coeff`, fleet L144) gives the paper's `(7,−8,2)`
   recurrence `(n+1)²g_{n+1} = (7n²+7n+2)gₙ + 8n²g_{n−1}` for both
   coefficient streams (`G_A` = Zagier's sequence **A** = Franel numbers
   `1,2,10,56,…`, all `n`; `G_C` = `0,1,4,208/9,…` for `n ≥ 1`), the signed
   integrals `Kₙ = (−1)ⁿIₙ` satisfy the same recurrence
   (`zetaJK_recurrence`), and the two initial values agree: `n = 0` is
   `I₀ = ζ(2)` and `n = 1` is the elementary evaluation
   `I₁ = ∫∫(1−s²)(1−t²)/(1−st)² = 4 − 2ζ(2)` (`zetaJ_one_eq`, from the
   commons `doubleIntegral_zetaJ_one`, fleet L141, which expands
   `1/(1−st)² = Σ(k+1)(st)^k` termwise and evaluates
   `Σ_k 4/((k+1)(k+3)²) = 4 − 2ζ(2)`); two-step induction then does the
   rest;
   **and the *untransformed* ζ-side overconvergence is PROVED too** (module
   `Submission.CDT.AintegralUntransformed`):
   `overconvergesC_proved : OverconvergesUnit eichlerDiffC`, i.e. the paper's
   `defabc`(iii) claim that `H_C − (ζ(2)/4)H_A` has radius of convergence
   `1` — the `H_C` mirror of `overconvergesB_proved`.  The route inverts the
   Möbius transform (`mobTrans_inv`, the commons
   `coeff_mobiusTransformInv`, fleet L151): the untransformed coefficients
   are the binomial transforms `cₙ = ΣₖC(n,k)[xᵏ]G_C`, `aₙ = ΣₖC(n,k)[xᵏ]G_A`
   (`HA_coeff_eq_btSum`/`HC_coeff_eq_btSum`), so the *proved* `(Aintegral)`
   identity turns the untransformed difference into
   `cₙ − (ζ(2)/4)aₙ = −(1/4)·Jₙ` with the **new** kernel
   `B(s,t) = (1−st) − (1−s²)(1−t²) = s²+t²−st−s²t²`:
   `Jₙ = ∫₀¹∫₀¹Bⁿ/(1−st)^{n+1} = ΣₖC(n,k)(−1)ᵏIₖ` (binomial theorem, a
   *finite* sum — commons `doubleIntegral_Bkernel_binom`, fleet L152), and
   `0 ≤ B ≤ 1−st` gives the uniform bound `|Jₙ| ≤ ∫₀¹∫₀¹dsdt/(1−st) = ζ(2)`
   (commons `doubleIntegral_Bkernel_bound`, fleet L153), hence
   `|eichlerDiffC n| ≤ ζ(2)/4`: the untransformed coefficients are
   *bounded*, far more than `OverconvergesUnit` asks.  Consequently
   `eichlerInputC_of_modular : ModularIntegralityC → EichlerInputC` (the
   `H_C` mirror of `eichlerInputB_of_modular`) and
   `functionsH_overconverges_of_modular`: **the overconvergence half of
   Proposition `functionsH` now needs only the modular `[1..n]²`-integrality**
   of `H_B`/`H_C`, both analytic halves being unconditional;
   and the reduction `overconvergesCtr_of_aintegral` (identity + bound ⟹
   radius-≥1 overconvergence of the transformed difference
   `G_C − (ζ(2)/4)G_A`);
3. `Gdenominatortype` (denominator type `[1..2n]²` of `G = Sym⁺H` under
   `Sym⁺`-descent, given the node-(2) inputs) — **PROVED** (module
   `Submission.CDT.SympDenom`): `sympDescCoeff_denomType` (the descent
   coefficients of a `[1..n]²`-denominator series have denominator type
   `[1..2n]²`, by induction from the triangular descent recursion and
   `[1..2m] ∣ [1..2n]`), `HasDenomTypeSq_subst` (denominator type is
   preserved by integer-coefficient substitutions), `sympSym_denomType`
   (the same for `Sym⁺H`), and `Gdenominatortype` (the paper's lemma for
   `H = aH_A + bH_B + cH_C`, using `functionsH_denomtype_int`);
4. Lemma `seven`/Lemma `14functions` (functional independence of the pure
   functions `Bᵢ` and of the 14 functions with `G, G′, G″, G‴` and the
   three integrals).  **NEW (this stretch)**: the *first step* of Lemma
   `seven` is closed in *functional form* — `Submission.CDT.LogPowersFunctional`
   (`log_powers_independent_on_Ioo`): a polynomial combination
   `Σ_i pᵢ(x)·log(1−x)^i` (`pᵢ ∈ ℚ[x]`) which vanishes on all of `(0,1)` has
   all `pᵢ = 0`, i.e. `1, log(1−x), …, log(1−x)^{K-1}` are `ℚ[x]`-linearly
   independent as functions.  The paper justifies this by the transcendence of
   `log(1−x)` over `ℚ(x)` (function-field Lindemann–Weierstrass); the
   formalized proof replaces that by evaluation at `x = 1 − 1/n` (`n ≥ 2`),
   where the number-theoretic Lindemann–Weierstrass chapter applies (via the
   sampled form `Submission.CDT.log_powers_linearIndependent`).
   **The function-field Lindemann–Weierstrass theorem (logarithmic case)** — general form in
   `Submission.CDT.LogTranscendence`, the paper's `f = 1 − y` instantiation in
   `Submission.CDT.FuncFieldTranscendence`:
   * `not_exists_dRat_eq_dRat_div` : for **every nonconstant** `f ∈ K(X)` (`K` a field of
     characteristic `0` in which every nonconstant polynomial has a root) the logarithmic
     derivative `(dRat f)/f` is **not** a derivative in `K(X)`: `dRat g ≠ (dRat f)/f` for all `g`;
   * `exists_deriv_of_deriv_eq_of_isAlgebraic` (commons) : **"no new integration"** — if `x` is
     algebraic over `K` in a differential field extension and `x' = a ∈ K`, then `a` is the
     derivative of an element of `K` (proof: `P^{(D)} + a·P'` has degree `< deg P` and vanishes
     at `x`, so it is `0`; its `T^{deg P − 1}`-coefficient gives
     `a = −(P.coeff (deg P − 1))'/deg P`);
   * `transcendental_of_deriv_eq_dRat_div` : hence **`log f` is transcendental over `K(X)`** for
     every nonconstant `f` (any `ℓ` in a differential extension with `ℓ' = (dRat f)/f` is
     transcendental), and `linearIndependent_powers_of_deriv_eq_dRat_div` : the powers
     `1, log f, …, log^{n−1} f` are `K(X)`-linearly independent — the form of the theorem the
     paper invokes for the first step of Lemma `seven`;
   * the `f = 1 − y` special case `not_exists_dRat_eq_neg_inv_one_sub` /
     `transcendental_of_deriv_eq_neg_inv_one_sub` /
     `linearIndependent_powers_of_deriv_eq_neg_inv_one_sub` is now a five-line corollary (and the
     "simple pole" phenomenon behind it is the general `ordAt_dRat_div_self` of
     `Submission.CDT.DerivOrderAt`, superseding the direct
     `Commons.Algebra.Polynomial.not_dvd_of_derivative_eq` argument used before).
   The monodromy/polylog half is *external complex
   analysis*; the **algebraic second half** of Lemma `14functions` (the
   Frobenius/pole-order argument of the paper, which reduces to the
   non-existence of a rational `b₃` with a given divisor) is **complete** in
   this repository (see `Submission.CDT.FinalLinear`, `Submission.CDT.RelationToSystem` and item 3).  The two layers now in place (all zero-`sorry`):

   * `Submission.CDT.OrderFrobenius` — the *formal-power-series* leading-term
     (Frobenius) calculus: `order_iterate_derivative_ge` (the `j`-th
     derivative lowers the order by at most `j`),
     `order_sum_mul_iterate_derivative_eq` (if `j₀` is the *unique* index
     minimizing `order(Q_j) + (order f - j)`, then
     `order (Σ_j Q_j f^{(j)}) = order(Q_{j₀}) + (order f - j₀)`), and the
     polynomial-coefficient special case
     `order_sum_poly_mul_iterate_derivative_eq`; commons companions
     `Commons.RingTheory.PowerSeries.order_iterate_derivative` (L167) and
     `order_finset_sum_eq_of_forall_lt` (L168);
   * `Submission.CDT.RatFuncOrder` — the *rational-function* valuation
     calculus `ordAt α x : ℤ` (order of vanishing at `α`; negative = pole)
     with `ordAt_algebraMap` (= root multiplicity on polynomials),
     `ordAt_mul`/`ordAt_inv`/`ordAt_div`/`ordAt_neg`/`ordAt_pow`,
     `min_ordAt_le_ordAt_add` (the `min` lower bound for sums) and the
     strict-dominance rule `ordAt_add_of_lt`; commons companion
     `Commons.Algebra.Polynomial.rootMultiplicity_add_eq_of_lt` (L169).
     **DONE (this stretch)**: the next layer — the *`ordAt`-calculus of the
     derivation* — is `Submission.CDT.DerivOrderAt`: `ordAt_dRat_eq_sub_one`
     (`ordAt α (dRat f) = ordAt α f - 1` whenever `ordAt α f ≠ 0`; the ledger's
     `ordAt α (dRat b) ≥ ordAt α b - 1`, sharpened to an equality),
     `ordAt_dRat_ne_neg_one` (**`dRat g` never has a simple pole**),
     `ordAt_dRat_div_self` (`ordAt α ((dRat f)/f) = -1` at every zero and pole
     of `f`) and `exists_ordAt_ne_zero_of_dRat_ne_zero` (a nonconstant rational
     function has a zero or a pole).  The local input is the commons lemma
     `Commons.Algebra.Polynomial.rootMultiplicity_derivative_num`;
   * `Submission.CDT.Residue` — the **residue calculus of `K(X)`** at a point `α`: `polePart α c
     = c/(X−α)`, the relation `ResidueAt α r c` ("`r` has at most a simple pole at `α` with
     residue `c`"), with uniqueness, additivity, `K`-homogeneity, `residueAt_polePart`,
     `zero_le_ordAt_dRat_div_self_of_ordAt_eq_zero` (a function that is finite and nonzero at `α`
     has holomorphic logarithmic derivative) and the structure theorem
     **`residueAt_dRat_div_self`**: `ResidueAt α ((dRat f)/f) (ordAt α f)` — the logarithmic
     derivative of `f` has the simple pole `ordAt α f/(X−α)` at every zero or pole of `f` and is
     holomorphic elsewhere.  Plus the quotient-rule companions `dRat_inv`, `dRat_mul_div`
     (logarithmic derivative of a product), `dRat_pow_div`, `dRat_inv_div`;
   * `Submission.CDT.LogMultiplicative` — **the function-field Lindemann–Weierstrass theorem in
     multiplicative-dependence form**: `prod_zpow_const_of_sum_dRat_div` — for a finite family
     `fᵢ ≠ 0` in `K(X)` (`K` algebraically closed of characteristic `0`) and integer coefficients
     `cᵢ`, if `Σᵢ cᵢ·(dRat fᵢ)/fᵢ` is a derivative in `K(X)` then **`∏ᵢ fᵢ^{cᵢ}` is a nonzero
     constant** (the proof: the residue of the combination is `Σᵢ cᵢ·ordAt α fᵢ`, which must
     vanish by `ordAt_dRat_ne_neg_one`; then `∏ fᵢ^{cᵢ}` has order `0` at every point).  The
     corollaries `exists_const_mul_of_dRat_div_eq` (two rational functions with the same
     logarithmic derivative differ by a nonzero constant) and
     `exists_const_of_dRat_div_eq_dRat` (a rational function whose logarithmic derivative is a
     derivative is constant) with their helper `ordAt_zpow`/`ordAt_prod`/`ResidueAt.sum`.  The
     *rational*-coefficient form `exists_int_prod_zpow_const_of_sum_dRat_div_rat` (clearing
     denominators via the commons `Commons.Data.Rat.exists_nat_mul_eq_int`), the converse
     `sum_dRat_div_eq_zero_of_prod_zpow_const` (`∏ fᵢ^{mᵢ}` constant ⟹ `Σᵢ mᵢ(dRat fᵢ)/fᵢ = 0`:
     the integer multiplicative relations span *all* log-relations), and — in
     `Submission.CDT.LogMultiplicativeField` — the **field-coefficient form
     `exists_int_prod_zpow_const_of_sum_dRat_div_field`**: for arbitrary `c : ι → K` with `c ≠ 0`
     one still gets a nontrivial *integer* multiplicative relation, since the residue relation
     `Σᵢ cᵢ·ordAt α fᵢ = 0` is a `K`-linear relation among integer vectors and hence has a nonzero
     rational solution (`Commons.LinearAlgebra.linearIndependent_map_of_linearIndependent_fintype`;
     the coordinates are restricted to the finite set `zerosPoles f` of zeros and poles), with the
     companion `exists_const_mul_zpow_of_dRat_div_eq` (`(dRat f)/f = n·(dRat g)/g` ⟹
     `f = C·g^n`) and `exists_const_mul_of_dRat_div_add` (`(dRat f)/f + (dRat g)/g` a derivative ⟹
     `f·g ∈ K`); and — in `Submission.CDT.LogRelation` — the **classical logarithmic form
     `exists_int_prod_zpow_const_of_logRelation`**: in a differential field extension `L ⊇ K(X)`
     whose derivation restricts to `dRat`, a nonzero `K`-linear relation
     `Σᵢ cᵢ·ℓᵢ ∈ K(X)` among elements with `ℓᵢ' = (dRat fᵢ)/fᵢ` (i.e. `ℓᵢ` playing the role of
     `log fᵢ`) forces the `fᵢ` to be multiplicatively dependent; differentiating the relation
     (`sum_dRat_div_eq_of_sum_log_eq`) reduces it to the derivative form.  Plus
     `exists_dRat_div_eq_natCast_mul_of_logDeriv_mem` — the **algebraic case**: if `x ≠ 0` lies in a
     finite extension of `K(X)` and its logarithmic derivative is a rational function `a`, then
     `m·a = (dRat u)/u` for some `u ∈ K(X)`, `u ≠ 0` and some `m > 0` (from the commons
     `Commons.FieldTheory.Differential.exists_logDeriv_eq_natCast_mul_of_logDeriv_mem`, proved by
     the norm formula `logDeriv (norm x) = trace (logDeriv x)`).  `Submission.CDT.Residue` additionally proves **existence** of residues
     (`exists_residueAt`: every `r` with `ordAt α r ≥ -1` has one — `valueAt α g = g.num(α)/g.denom(α)`
     at a point where `g` is finite and nonzero, and `valueAt` subtracted lowers the order at least
     once, `one_le_ordAt_sub_valueAt`), so that `ResidueAt` is a *function* of `(α, r)` for
     `ordAt α r ≥ -1`;
   * **THE WEIGHT-TWO REFINEMENT (SESSION 32) — all zero `sorry`:**
     * `Submission.CDT.ResidueMul` — the residue calculus *multiplicatively refined*:
       `zero_le_ordAt_sub_valueAt`, **`ResidueAt.mul`** (if `ordAt α r = 0` and `ResidueAt α s d`
       then `ResidueAt α (r·s) (valueAt α r · d)`: a residue is multiplied by the *value* of the
       other factor), and the two logarithmic specialisations `residueAt_mul_dRat_div_self`
       (`r·(f'/f)` has residue `valueAt α r · ordAt α f`) and
       `residueAt_dRat_div_self_mul_dRat_div_self` (`(f'/f)·(g'/g)` has residue
       `(g'/g)(α) · ordAt α f` when `(g'/g)` is finite and nonzero at `α`, and `0` when `f` is also
       finite there).  This is the local input of *weight-two* Lindemann–Weierstrass;
       the accompanying **weight-two obstruction** `dRat_ne_mul_dRat_div_self_div_self`: at a zero
       or pole `α` of `f` where the logarithmic derivative of `g` is finite *and nonzero*, the
       product `(f'/f)·(g'/g)` is not the derivative of any rational function (its residue at `α`
       is the nonzero number `(g'/g)(α)·ordAt α f`, while `dRat h` never has a simple pole);
     * `Submission.CDT.LogProduct` — **weight-two function-field Lindemann–Weierstrass**:
       `not_exists_mul_eq_algebraMap`: if `u' = (dRat f)/f` and `v' = (dRat g)/g` in a differential
       extension of `K(X)` with `f, g` nonconstant, then `u·v` is **not** a rational function.  The
       proof is three lines: differentiating `u·v = r₀` and multiplying by `v` gives the *quadratic*
       equation `(dRat f)/f·v² − (dRat r₀)·v + r₀·(dRat g)/g = 0` for `v`, whose leading
       coefficient is nonzero, so `v` would be algebraic — contradicting
       `transcendental_of_deriv_eq_dRat_div` (no multiplicative-independence hypothesis is needed);
     * `Submission.CDT.WeightTwo` — **the weight-two residue relation**
       `residueAt_weight_two_eq_zero`: for a weight-two relation
       `Σᵢⱼ cᵢⱼ·(fᵢ'/fᵢ)(fⱼ'/fⱼ) = dRat h` in `K(X)`, at a point `α` which is a zero or pole of exactly
       one of the functions `f k` (all other `f i` finite there with finite nonzero logarithmic
       derivative) and with the diagonal coefficient `c k k = 0`, the residues force
       `Σ_{i ≠ k} (cᵢₖ + cₖᵢ)·(fᵢ'/fᵢ)(α) = 0`: every term has order `≥ -1` at `α`, the residue of the
       diagonal term is `0`, and the two cross terms `(i,k)` and `(k,i)` each contribute
       `(f k'/f k)(α)·(fᵢ'/fᵢ)(α)` (the private helper `sum_double_ite` splits the double sum), so the
       total residue vanishes only if that number does — while `dRat h` never has a simple pole.
       Corollary `weight_two_value_eq_zero`: if only one index `i₀ ≠ k` carries a nonzero coefficient
       `cᵢ₀ₖ + cₖᵢ₀`, then `(fᵢ₀'/fᵢ₀)(α) = 0`;
     * `Submission.CDT.LogIndependence` — the *independence* corollaries of the weight-one theorem:
       `transcendental_notMem_range` and `transcendental_pow_notMem_range` (a transcendental element
       and its positive powers are not rational functions), and **`not_exists_sum_eq_algebraMap`**:
       if the nonzero `fᵢ ∈ K(X)` admit no nontrivial multiplicative relation with constant value,
       then no nonzero `K`-linear combination of the logarithms `ℓᵢ` (with `ℓᵢ' = (dRat fᵢ)/fᵢ`) is a
       rational function;
       plus the two-logarithm specialisation `not_exists_add_eq_algebraMap` (`ℓ₁ + ℓ₂ ∉ K(X)` when
       `f^m·g^n` is never a nonzero constant for `(m,n) ≠ 0`);
     * `Submission.CDT.DifferentialConstants` — **Kolchin's lemma, constant-coefficient case**
       ("no new constants"): if `D` is a `K`-derivation of a field extension `L`, `x ∈ L` is
       transcendental over `K` and `D x = a` for a nonzero `a ∈ K`, then a rational function `P(x)/Q(x)`
       (`Q ≠ 0`) with vanishing derivative is a constant: `∃ c, P(x) = c·Q(x)`.  Assembled from three
       commons lemmas proved this stretch — the chain rule `Commons.RingTheory.Derivation.aeval_derivative`
       (`D (P(x)) = a·P'(x)`), the quotient rule `Commons.RingTheory.Derivation.map_div`, and the
       polynomial Wronskian lemma `Commons.Algebra.Polynomial.exists_eq_C_mul_of_derivative_mul_eq`
       (`P'·Q = P·Q'` with `Q ≠ 0` ⟹ `P` is a constant multiple of `Q`).
     * **THE WEIGHT-TWO INDEPENDENCE STATEMENT (SESSION 33) — zero `sorry`:
       `Submission.CDT.LogProductIndependence`**: `LogProduct` proves that the *product* `u·v`
       of two logarithms is irrational, and this module upgrades that to the full **quadratic**
       independence statement — *no* expression `c₀·u·v + c₁·u + c₂·v` with `c₀ ≠ 0` is a rational
       function, for `u' = (dRat f)/f`, `v' = (dRat g)/g` and `f, g` nonconstant:
       **`not_exists_quadratic_eq_algebraMap`**.  Unlike the weight-one statement
       (`not_exists_sum_eq_algebraMap`, which needs the multiplicative independence of `f, g`) no
       independence hypothesis is required: the quadratic term forces the contradiction by itself.
       Two *abstract* lemmas carry the proof, both for an arbitrary differential field extension
       `R ⊆ L` of characteristic zero:
         * `deriv_algebraMap_mul` — the derivative of `algebraMap a * z`;
         * **`exists_algebraMap_of_quadratic_relation`** (`W ≠ 0` case) — if
           `A₁'A₂ - A₁A₂' ≠ 0` then two differentiations of the relation give the linear system
           `c₀A₂·u + c₀A₁·v = γ`, `c₀A₂'·u + c₀A₁'·v = δ` (`γ = r₀' - c₁A₁ - c₂A₂`,
           `δ = γ' - 2c₀A₁A₂`), and Cramer's rule (determinant `-c₀²(A₁'A₂ - A₁A₂')`) exhibits `v`
           as an element of `R`;
         * **`isAlgebraic_of_proportional_quadratic`** (degenerate case, *purely algebraic*) — if
           in addition `v + λ·u = α ∈ R` with `λ ≠ 0`, then `u` is **algebraic over `R`**: with
           `μ := v - λu` the relation is the quadratic `c₀λu² + (c₀μ+c₁+c₂λ)u + c₂μ = r₀` for `u`
           while `2λu = α - μ`, and eliminating `u` (multiplying by `4λ²` and substituting
           `4λ²u² = (α-μ)²`, `4λ²u = 2λ(α-μ)`) exhibits `μ` as a root of the explicit quadratic
           `-c₀λ·X² + 2λ(c₂λ-c₁)·X + (c₀λα² + 2λc₁α + 2c₂λ²α - 4λ²r₀)` over `R`, whence `u` too
           (`IsIntegral`/`isAlgebraic_iff_isIntegral`).
       The rational-function theorem then splits on the Wronskian
       `W = A₁'A₂ - A₁A₂'` of the logarithmic derivatives `A₁ = (dRat f)/f`, `A₂ = (dRat g)/g`:
       if `W ≠ 0` the elimination makes `v` rational, contradicting the transcendence of `v`
       (weight-one Lindemann–Weierstrass), while if `W = 0` then `dRat (A₂/A₁) = 0`, so
       `A₂ = λ·A₁` for a constant `λ ∈ K` (`exists_const_of_dRat_eq_zero`), differentiating the
       relation once more shows `v + λ·u ∈ K(X)`, and `isAlgebraic_of_proportional_quadratic`
       makes `u` algebraic over `K(X)` — contradicting the transcendence of `u`.
       The companion **`exists_int_prod_zpow_const_of_logDeriv_eq_smul`** records the weight-one
       consequence of proportionality (`dRat g/g = λ·(dRat f)/f` forces a nontrivial multiplicative
       relation `f^m·g^n ∈ K`, via
       `exists_int_prod_zpow_const_of_sum_dRat_div_field`).
     * **KOLCHIN'S LEMMA (SESSION 33) — `Submission.CDT.KolchinHeart` and
       `Submission.CDT.KolchinField`, both zero `sorry`**:
       `Submission.CDT.DifferentialConstants` proves the *constant-coefficient* case of "no new
       constants" (the base is a field of constants).  The general case — the classical
       **Kolchin lemma** `C_{K(x)} = C_K` when `x'` is not a derivative in `K` — is now proved for
       function fields:
       * `Submission.CDT.KolchinField` **`kolchin_no_new_constants`** (`exists_const_of_deriv_div_aeval_eq_zero`):
         let `L` be a differential field extension of `K(X)`, `x ∈ L` transcendental over `K(X)`
         with `x' = a ∈ K(X)` *not* the derivative of any element of `K(X)`.  Then a rational
         function `P(x)/Q(x)` of `x` (`Q ≠ 0`) with vanishing derivative is a constant of `K`:
         `P(x)/Q(x) = algebraMap (algebraMap c)` for some `c : K`.  (The hypothesis is necessary:
         if `a = b'` then `x - b` is a new constant — see the docstring of
         `Submission.CDT.DifferentialConstants`.)  The proof assembles the chain rule
         `Differential.deriv_aeval_eq` (Mathlib) with the quotient rule `map_div'` and the algebraic
         heart below, and the resulting polynomial identity of `K(X)[X]` is pulled back along
         `aeval x` with `Commons.FieldTheory.Transcendental.aeval_eq_zero_iff`;
       * `Submission.CDT.KolchinHeart` — the **algebraic heart**
         `exists_algebraMap_C_mul_of_relation`: for a characteristic-zero differential field `R`
         whose constants are the image of a field `K` (`hconst`, `hconst'`), if `a ∈ R` is not a
         derivative and `P, Q ∈ R[X]` satisfy
         `(mapCoeffs P)·Q - P·(mapCoeffs Q) + a·(P'·Q - P·Q') = 0`
         (`∂(P/Q) + a·(P/Q)' = 0`), then `P = (algebraMap c)·Q` for some `c : K`.
         The proof is a two-coefficient comparison: the `X ^ (p+q)` coefficients give
         `(∂lp)·lq = lp·(∂lq)` (`leadingCoeff_deriv_relation`), so `λ := lp/lq` is a constant, and
         the `X ^ (p+q-1)` coefficients give `∂(ν/lq) = -a·(p-q)·λ` with
         `ν = (P.coeff (p-1)) - λ·(Q.coeff (q-1))`, exhibiting `a` as the derivative
         `∂(-ν/((p-q)·λ·lq))` — a contradiction
         (`exists_deriv_of_relation_of_natDegree_lt'`, whose `deg Q = 0` case is reduced by the
          homogeneous degree-`2` rescaling `(P,Q) ↦ (PX, QX)`).  Hence `deg P ≤ deg Q`; swapping the
         roles of `P` and `Q` (the identity changes sign) gives `deg P = deg Q`, and then
         `P - (algebraMap c)·Q` has smaller degree and satisfies the same identity, contradicting
         the same argument.  Everything is stated for a general differential field `R`, so it is
         reusable; the helper `coeff_mul_sub_one'` extracts the second coefficient of a product
         (also when the second factor is a constant).
       This is the missing "no new constants" theorem behind the function-field
       Lindemann–Weierstrass hierarchy (`LogTranscendence`, `LogRelation`, `LogProduct`,
       `LogProductIndependence`): it is the induction step in the usual proof that the logarithms of
       multiplicatively independent functions are algebraically independent over `K(X)`.
     * **KOLCHIN'S LEMMA, BOTH CASES (SESSION 34) — `Submission.CDT.KolchinAlgebraic` and
       `Submission.CDT.KolchinTranscendental`, both zero `sorry`** — the two steps of the classical
       proof that the logarithms of multiplicatively independent functions are algebraically
       independent:

       * `Submission.CDT.KolchinAlgebraic` (**the algebraic case**):
         `exists_deriv_add_eq_zero_of_isIntegral` — for `R ⊆ S` characteristic-zero differential
         fields with `DifferentialAlgebra R S`, if `u ∈ S` is algebraic over `R` (`IsIntegral`)
         with `u′ = a ∈ R`, then `u` differs from an element of `R` by a **constant**:
         `∃ b : R, (u + b)′ = 0`; and `exists_algebraMap_of_isIntegral_of_deriv_mem` — if moreover
         `Differential.ContainConstants R S` (every constant of `S` is in the image of `R`), then
         `u` itself is in the image of `R`.  Proof: the minimal polynomial `m` of `u` is annihilated
         by the polynomial `mapCoeffs m + C a * m′` of strictly smaller degree (chain rule
         `Differential.deriv_aeval_eq` + `minpoly.dvd`), whose `X^(D-1)`-coefficient then gives
         `(m_{D-1})′ = -a·D`, whence `b = m_{D-1}/D` has `b′ = -a`
         (helper `natDegree_mapCoeffs_lt_of_monic`).

       * `Submission.CDT.KolchinTranscendental` (**the transcendental case**):
         `exists_add_mul_of_deriv_div_mem` — for `R ⊆ S` as above with
         `Differential.ContainConstants R S`, if `u` is **transcendental** over `R` with
         `u′ = a ∈ R` and `v = P(u)/Q(u)` (`P, Q ∈ R[X]`, `Q ≠ 0`, `IsCoprime P Q`) has
         `deriv v ∈ R`, then `v` is affine in `u`: `v = r₀ + c·u` with `r₀ ∈ R` and
         `deriv (algebraMap c) = 0`; hence the elements of `R(u)` with derivative in `R` are
         exactly `R + C_S·u`.  Proof: the total derivative
         `Phi a Z := mapCoeffs Z + C a * Z′` (`aeval_Phi`, `Phi_eq_C_of_deriv_eq`); in the
         polynomial case `Phi a P = C ρ`, and `deg P ≥ 2` forces `u + P_{d-1}/(d·P_d)` to be a new
         constant (coefficient comparison), contradicting transcendence, so `deg P ≤ 1` and the
         `X^1`-coefficient is a constant; in the rational case the quotient-rule identity
         `Φ(P)·Q - P·Φ(Q) = C ρ·Q²`
         (`Commons.RingTheory.Derivation.mapCoeffs_mul_sub_of_deriv_div`) gives `Q ∣ Φ(Q)` and then
         `Φ(Q) = Q·C s` with `s = (lc Q)′/(lc Q)`, so `Q * C (lc Q)⁻¹` is monic with vanishing `Φ`,
         whence `Q̃(u)` is a constant and, again by `ContainConstants` and transcendence, `Q` is a
         constant polynomial; the polynomial case applied to `P·C q⁻¹` concludes
         (helper `Phi_mul_C`).

     * **THE OSTROWSKI–KOLCHIN ASSEMBLY (SESSION 35) — `Submission.CDT.LogAlgIndependent`, zero
       `sorry`** — the induction assembling the two cases of Kolchin's lemma into the classical
       theorem.  For `F ⊆ L` characteristic-zero differential fields with
       `Differential.ContainConstants F L`:

       * `deriv_mem_adjoin`, `deriv_mem_adjoin_range` — the derivation preserves `F(u₁, …, uₙ)`
         when all `uᵢ′ ∈ F`;
       * `differentialAlgebra_subfield`, `differentialAlgebra_val`, `containConstants_val` — the
         plumbing transferring the inherited `Differential` structure of a derivation-closed
         intermediate field (`Commons...exists_differential_of_closed`);
       * `step` — one step (adjoin a single generator; the algebraic case uses
         `Commons...kolchin_algebraic`, the transcendental case
         `Submission.CDT.KolchinTranscendental.exists_add_mul_of_deriv_div_mem` together with
         `Commons.FieldTheory.Transcendental.exists_coprime_aeval_div_eq`);
       * **`exists_span_of_deriv_mem`** — the main theorem: if `u : Fin n → L` with `uᵢ′ ∈ F`, then
         every `v ∈ F(u₁, …, uₙ)` with `v′ ∈ F` is `r + Σᵢ cᵢ·uᵢ` with `r ∈ F` and `cᵢ ∈ F`
         *constants*; `exists_span_of_deriv_mem_top` and the equivalent set form
         **`deriv_mem_range_iff`** specialise this to `F(u₁, …, uₙ) = L`;
       * **`algebraicIndependent_of_linearIndependent`** — the Lindemann–Weierstrass form: if no
         nontrivial `C_F`-linear combination of the `uᵢ` lies in `F`, then `u₁, …, uₙ` are
         algebraically independent over `F` (`optionEquivFin` plus Mathlib's
         `AlgebraicIndependent.option_iff` and `IntermediateField.transcendental_adjoin_iff` drive
         the induction; the algebraic case of the step contradicts the linear-independence
         hypothesis via the span theorem).
     * **THE FUNCTION-FIELD LINDEMANN–WEIERSTRASS THEOREM (SESSION 35) —
       `Submission.CDT.LogAlgLW`, zero `sorry`** — `algebraicIndependent_log_of_multiplicativeIndependent`:
       for `K` algebraically closed of characteristic `0`, multiplicatively independent nonzero
       `f₁, …, fₙ ∈ K(X)` (no nontrivial `∏ fᵢ^{mᵢ} ∈ K`), and `ℓ₁, …, ℓₙ` in a differential field
       extension `L ⊇ K(X)` with `ℓᵢ′ = (dRat fᵢ)/fᵢ` and `Differential.ContainConstants K(X) L`,
       the `ℓᵢ` are algebraically independent over `K(X)`.  The linear-independence hypothesis is
       supplied by `LogRelation.sum_dRat_div_eq_of_sum_log_eq` +
       `LogMultiplicativeField.exists_int_prod_zpow_const_of_sum_dRat_div_field` (a nonzero
       `K`-linear relation among logarithmic derivatives forces a multiplicative relation), and the
       constants of `K(X)` are identified by `RatFuncConstants.exists_const_of_dRat_eq_zero`.
     * **`Submission.CDT.RatFuncDifferential` (SESSION 35)** — the **canonical `Differential`
       structure on `K(X)`**: `dRat` (`Submission.CDT.RatFuncDeriv`) is packaged as a
       `Derivation ℤ (RatFunc K) (RatFunc K)` (`dRatDeriv`) and installed as a global instance of
       `Differential (RatFunc K)`, with `deriv_ratFunc_eq_dRat : Differential.deriv f = dRat f`
       holding by `rfl`.  This removes the hypothesis `∀ r, Differential.deriv r = dRat r` from
       every statement about differential extensions of `K(X)` (`Submission.CDT.LogAlgLW` now uses
       the instance).  Two technical points: the `Algebra ℤ (RatFunc K)` instance used by
       `Differential` is `Ring.toIntAlgebra`, which is *propositionally* but not definitionally
       equal to the one coming from `RatFunc.instAlgebraOfPolynomial`; the file therefore raises the
       local instance priority of `Ring.toIntAlgebra`, and proves `dRat (n : RatFunc K) = 0` for
       `n : ℤ` (`dRat_intCast`, via `dRat (algebraMap K _ c) = 0` and `map_intCast`) to handle the
       `ℤ`-scalar action.  In addition `differential_ratFunc_unique` shows that a `Differential`
       structure on `K(X)` agreeing with the formal derivative on `K[X]` is the canonical one
       (from the commons `Commons.FieldTheory.RatFunc.differential_ratFunc_ext`).
     * **`Submission.CDT.LogAlgIndependent`, further corollaries (SESSION 35)** — the
       transcendence-degree forms `trdeg_le_card_of_adjoin_top` (`trdeg_F L ≤ #(Set.range u)`
       whenever the `uᵢ` generate `L`; Mathlib's `Algebra.IsAlgebraic.trdeg_le_cardinalMk`) and
       **`trdeg_eq_card_range_of_adjoin_top`** (`trdeg_F L = #(Set.range u)` for algebraically
       independent generators, from `AlgebraicIndependent.coe_range` +
       `cardinalMk_le_trdeg`), and the arbitrary-finite-index version
       `exists_span_of_deriv_mem_fintype` of the span theorem (reduction to `Fin (card ι)` via
       `Fintype.equivFin` and `Equiv.sum_comp`).  (The `Cardinal`-valued statements use
       `Cardinal.mk (Set.range u)` rather than `IsTranscendenceBasis.cardinalMk_eq_trdeg`, whose
       index type shares the universe of the target ring.)
   * `Submission.CDT.RatFuncDeriv` — the derivation `dRat` on `RatFunc K`
     (`RatFunc.liftOn'` applied to the quotient-rule formula, well-defined by
     scaling invariance `dRatF_scale`), with the API `dRat_mk`, `dRat_div`
     (`dRat (p/q) = (p'q − pq')/q²`), `dRat_algebraMap`, additivity
     `dRat_add`, the Leibniz rule `dRat_mul`, `dRat_neg/sub/pow` and
     `dRat_poly_mul`; **zero `sorry`**;
   * `Submission.CDT.EulerIndicial` — the *Euler cascade*: `fallFact`,
     `dnum p q j` (the numerator `C_j` of the `j`-th derivative,
     `f^{(j)} = C_j/q^{j+1}`, `dRat_iterate_dnum`), `DbN z p q F j` and the
     recursion **`DbN_rec`** `D_{j+1} = F_j q^j(z(p'q−pq')−Npq) + zD_j'q −
     (j+1)zD_j q' − jD_j q`; **zero `sorry`**;
   * `Submission.CDT.EliminationData` (namespace `Submission.CDT.Elim14`) —
     the explicit `c0..c4`, `P0..P3`, `D1` and the four coefficient identities
     `coeff_ident_zero/one/two/three` (by `ring`) expressing that the operator
     produced by the *system* equals `Σ_j Q_j D^j` with `Q_j = 2P_j/Δ₁^{4−j}`
     and `Q_4 = −1`; **zero `sorry`**;
   * commons: `Commons.Algebra.Polynomial.eulerOperator_factor` (Lemma (P):
     `z(p'q−pq') − (a−b)pq = z^{a+b+1}r`), and the four indicial non-vanishing
     facts `Commons.Analysis.Arithmetic.indicial_{zero,four,neg_inv72,infty}_ne_zero`;
     the Frobenius divisibility `z^{a+jb+1} ∣ z^jC_j − (N)_j p q^j`
     (`Commons.Algebra.Polynomial.euler_cascade_dvd`, PROVED) and (new this
     stretch) `Commons.Algebra.Polynomial.rootMultiplicity_pow` (L178).
     **NEW (this stretch), the Frobenius/indicial engine — all zero `sorry`:**
   * `Submission.CDT.OrdAtT` — the `WithTop ℤ`-valued order `ordAtT` (with
     `ordAtT α 0 = ⊤`), its `min` rule `ordAtT_add_ge` with *no* side
     condition, additivity/materiality `ordAtT_mul`, `ordAtT_algebraMap`, the
     strict-dominance rule `ordAtT_add_eq_of_le_succ` and the `Finset`
     versions `le_ordAtT_finset_sum`, `ordAtT_finset_sum_eq`;
   * `Submission.CDT.FrobeniusLocal` — the local theorems:
     `residual_bound` (the cascade bound `ord_α(z^j f^{(j)} − (N)_j f) ≥ N+1`
     for `f = p/q`, from `euler_cascade_dvd`), `ordAtT_iterate_dRat_ge`
     (`ord_α f^{(j)} ≥ N − j`) and, for a pole, the exact
     `ordAtT_iterate_dRat_eq` (`ord_α f^{(j)} = N − j` when `N < 0`),
     **`frobenius_tie`** (all indicial exponents tie at `α`: if
     `σ = Σ_j (N)_{e j} B_j(α) ≠ 0` then the operator has order exactly `N`),
     **`frobenius_unique`** (unique minimising index), and the one-sided
     `frobenius_order_ge`;
   * `Submission.CDT.ElimOperator` (and the base-changed `ElimOperatorC`) —
     the *operator identity* `D[u f] − D²[v f] + D³[w f] − D⁴ f − z f
     = Σ_j (2P_j/D1^{4−j}) f^{(j)}` (`elim_operator`), proved by Leibniz
     expansion plus the four coefficient identities of `EliminationData`
     (`coeff_three/two/one/zero` as `RatFunc` statements; the `ℂ`-versions
     `EliminationDataC`, `ElimOperatorC` are the base change used for the
     cubic-root analysis);
   * `Submission.CDT.ElimReduction` (+ `ElimReductionC`) — from the paper's
     system `(b₀,b₁,b₂,b₃)` to the eliminated equation:
     `elim_from_system`, `elim_equation` (`Σ_j Q_j b₃^{(j)} = R`) and the
     cleared `elim_equation_cleared` (`Σ_j A_j b₃^{(j)} = D1⁴·R`,
     `A_j = 2P_jD1^j`, `A₄ = −D1⁴`);
   * `Submission.CDT.FrobeniusApply` — the *local pole bounds*.  The engine is
     `tie_bound` (given `D1 = z·Q` at `α`, `Afun j = z^j·B j`, `σ_α(N) ≠ 0` for
     `N ≤ K` and `K < 4·ord_α(D1) + ord_α R`, conclude `ord_α b₃ > K`).
     Three of the five points are done:
     **`zero_local`** (`2 ≤ ord_0 b₃`; `D1 = X·Q0`,
     `σ_0(N) = 256·(−225/4 + 189/4(N)₁ − 77/4(N)₂ + 5(N)₃ − (N)₄)`, nonzero for
     `N ≤ 1` by `Commons.Analysis.Arithmetic.indicial_zero_ne_zero`);
     **`four_local`** (`2 ≤ ord_4 b₃`; `D1 = (X−4)·Q4`, `Q4(4) = 8941660`,
     `σ_4(N) = 8941660⁴·(−45/2 + 21(N)₁ − 39/4(N)₂ + 3(N)₃ − (N)₄)`, nonzero for
     `N ≤ 1` by `indicial_four_ne_zero`);
     **`m72_local`** (`1 ≤ ord_{−1/72} b₃`; `D1 = (X+1/72)·Qm`,
     `σ(N) = (989398410206816318208241/75814101413145870336)·(−18 + 18(N)₁ − 9(N)₂
     + 3(N)₃ − (N)₄)`, nonzero for `N ≤ 0` by `indicial_neg_inv72_ne_zero`).
     **NEW (this stretch), the cubic-root bound, the generic-point bound and
     the divisor bound — all zero `sorry`:**
   * `Submission.CDT.FrobeniusBeta` — the Frobenius analysis at a root `β` of
     the cubic.  The explicit derivative polynomials `dP` (= `D1'`) and `cubP`
     (= `cub'`) are connected to `Polynomial.derivative` (`dP_eq_derivative`,
     `cubP_eq_derivative`); the Bezout identity `bezout`
     (`(2909012 − 3897936y)·cub + (1299312y² − 1336606y + 776401)·cubP
     = 88706306`) makes `cub` squarefree at every root (`cubP_eval_ne_zero`);
     the four *leading-coefficient congruences* modulo `cub`
     `2P_j ≡ a_j·(D1')^{4−j}` with `(a_0,a_1,a_2,a_3) = (6,−6,3,−1)`
     (`cong_zero/one/two/three`, with the explicit quotients `H0..H3`) are
     verified by `ring`; with `Qmb β = y(y−4)(72y+1)·(cub /ₘ (X−Cβ))`
     (`D1 = (X−Cβ)·Qmb β`, `Qmb β(β) = D1'(β) = dP.eval β`) this gives
     `sigma_beta_val`:
     `Σ_j (N)_j B_j(β) = −(dP.eval β)⁴·(N−3)(N−2)(N−1)(N+1)`, nonzero for
     every integer `N ≤ −2`; **`beta_local`** : `−1 ≤ ord_β b₃`;
   * `Submission.CDT.FrobeniusGeneric` — **`generic_local`** : at any `α` with
     `Δ₁(α) ≠ 0` the operator has a unique minimising index `j = 4`, so
     `frobenius_unique` gives `ord_α(Σ_j A_j b₃^{(j)}) = ord_α b₃ − 4`; since
     `Δ₁⁴R` is regular there, `0 ≤ ord_α b₃`;
   * `Submission.CDT.DivisorBound` — **`divisor_bound`** : from the five local
     bounds (at `0`, `4`, `−1/72`, the roots of `cub`, and the generic points)
     one gets `cub·b₃ = y²(y−4)²(y + 1/72)·Q` with `Q` a polynomial
     (`Commons.Algebra.Polynomial.dvd_of_forall_rootMultiplicity_le` makes
     `cub·b₃` a polynomial, and the pairwise-coprime linear factors give the
     divisibility).
   * `Submission.CDT.DnumDegree` — the general Frobenius-cascade degree
     theorem `dnum_natDegree_leadingCoeff` : for `q` of degree `3` and `p` of
     positive degree, `natDegree (dnum p q j) = p.natDegree + 2j` and
     `leadingCoeff (dnum p q j) = (leadingCoeff q)^j·(N)_j·leadingCoeff p`
     with `N = p.natDegree − 3` (the non-resonant case `N − k ≠ 0`, `k < j`);
   * `Submission.CDT.InfinityBound` — **the bound at `∞`** `deg Q ≤ 2`
     (the paper's `N_∞ ≤ 4`).  The ansatz `b₃ = y²(y−4)²(y+1/72)Q/cub` turns
     the eliminated equation into the polynomial identity
     `POLYq Q · y² = w⁴·cub⁵·Rnum` (`POLYq_mul_X2`, obtained by clearing the
     `dRat^[j]` denominators via `dRat_iterate_dnum` and cancelling `cub⁴`),
     where `POLYq Q = ∑_j Acoef j·dnum (Pz Q) cub j` is the cascaded numerator.
     Since all five summands have the same degree `deg Q + 25`, the leading
     coefficient of `POLYq Q` is
     `leadingCoeff (Pz Q) · ∑_j (fallFact N j)·(Afun j).leadingCoeff`
     with `N = deg Q + 2`, and this indicial sum equals
     `10368⁴·(−144 + 108(N)₁ − 38(N)₂ + 8(N)₃ − (N)₄)`
     (`sigma_infty_val`), nonzero for `N ≥ 5` by
     `Commons.Analysis.Arithmetic.indicial_infty_ne_zero`.  Comparing degrees
     in `POLYq Q · y² = w⁴·cub⁵·Rnum` then forces `deg Q = deg Rnum ≤ 2`
     whenever `deg Q ≥ 3`, and **`infty_bound`** is the resulting bound
     `deg Q ≤ 2`.
   * `Submission.CDT.FinalStep` — the reduction of the ansatz to a
     divisibility: `dnum` is linear in its first argument (`dnum_add`,
     `dnum_smul`); `cub` is a unit modulo `X` (`cub_bezout_X`,
     `isCoprime_cub_X`); and **`cub_pow_five_dvd_POLYq`** : the cleared identity
     `POLYq Q · y² = w⁴·cub⁵·Rnum` forces `cub⁵ ∣ POLYq Q`.
     NOTE: the paper's indicial display at `α = ∞` has a typo; the correct
     polynomial is `−(N−3)²(N−4)²`;
   * `Submission.CDT.FinalLinear` — **the final linear algebra**, the last
     missing piece of the algebraic half of Lemma `14functions`:
     `POLYq` is additive and `ℂ`-homogeneous in `Q` (`POLYq_add`, `POLYq_smul`,
     `POLYq_eq_linear`), and `72·Pz = PzI := y²(y−4)²(72y+1)` is integral
     (`Pz_mul_72`, `Pz_eq_inv72_smul`, `mul72_dnum`), so the cascade ran on
     `PzI·y^k` has *integer* coefficients: the fifteen explicit polynomials
     `Ct k j = dnum (PzI·y^k) cub j` (`k ≤ 2`, `j ≤ 4`, degrees 5–15) are
     **machine-verified** to satisfy the cascade recursion
     `C_{j+1} = C_j'·cub − (j+1)·C_j·cub'` (`dnum_PzI_kj`), the integral
     numerators `INTQ k = 72·POLYq (y^k)` and the explicit remainders `RR k`
     and quotients `SS k` with
     `Dv·INTQ k − RR k = cub⁵·SS k`, `Dv = 72·78364164096`
     (`cub5_dvd_INTQ_k`, plain `ring` identities), give
     `cub⁵ ∣ Σ_k q_k·RR k` for `Q = q₀ + q₁y + q₂y²`; since `deg (RR k) ≤ 14`
     (`RR k`_natDegree_le) this forces `Σ_k q_k·RR k = 0`, and the `3×3` minor
     of `(RR k).coeff i` (`i,k ≤ 2`) has non-zero determinant (`hdet`,
     evaluated by `norm_num`), giving `q₀ = q₁ = q₂ = 0` and hence
     **`eq_zero_of_cub5_dvd_POLYq`** : `deg Q ≤ 2` and `cub⁵ ∣ POLYq Q` imply
     `Q = 0`.  Combining this with `divisor_bound`, `infty_bound`,
     `POLYq_mul_X2`, `cub_pow_five_dvd_POLYq` and the five local bounds gives
     **`no_solution`** : the paper's system
     `b₃' + b₂ − W b₃ = 0`, …, `b₀' − Z b₃ = (a₀y²+a₁y+a₂)/y²` has no solution
     with `b₃ ≠ 0` and `(a₀,a₁,a₂) ≠ 0` — i.e. the algebraic half of Lemma
     `14functions` is now **complete** (zero `sorry`), the numerical data being
     reproducible from `Scratch/lemma14/gen_data.py`;
   the elimination of the paper's system `(b₀,b₁,b₂,b₃)` into a 4th-order
   operator for `b₃` (the explicit `Q₀..Q₄` are computed, with
   `Q₄ = -1` and `Q_j` having denominator `(y(y−4)(72y+1)·cubic)^j`,
   `cubic = 144y³−122y²+118y−1`) and the pole bounds
   `N₀ ≥ 2, N₄ ≥ 2, N_{−1/72} ≥ 1, N_β ≥ −1, N_∞ ≤ 4`
   (the indicial coefficients at `y = 0, 4, −1/72, β` verified against the
   paper: `−(3−N)²(5−2N)²/4`, `−(3−N)(2−N)(5−2N)(3−2N)/4`,
   `−(3−N)²(2−N)(1−N)`, and `(3−N)(2−N)(1−N)(1+N)`) are all **DONE**, and
   the final contradiction is **`no_solution`** of
   `Submission.CDT.FinalLinear`: the machine-verified computation of the
   paper's `(degree12)` display (equivalently `cub⁵ ∣ POLYq Q` for
   `Q = q₀+q₁y+q₂y²`) is carried out by explicit linear algebra.
   The whole algebraic second half of Lemma `14functions` is therefore
   **complete (zero `sorry`)**; what remains of Lemma `14functions` is only
   its *functional-independence* half (monodromy of the order-4 operator +
   the pure functions `Bᵢ`, i.e. Nielsen polylog theory);
   * **NEW, `Submission.CDT.RelationToSystem`** — **the paper's reduction
     `(todiff) ⟹ system`, and the full *functional-independence* statement of
     Lemma `14functions` in its algebraic form.**  In the abstract setting of
     an `RF`-module `M` (`RF = ℂ(y)`) with a derivation-like map `δ`,
     `δ (r • m) = (dRat r) • m + r • δ m`, and elements
     `u 0,…,u 3` (the solution `Δ,Δ',Δ'',Δ'''` of the order-`4` operator) and
     `v 0,v 1,v 2` (the three integrals `∫Δ, ∫Δ/y, ∫Δ/y²`) satisfying
     `δ (u 0) = u 1`, `δ (u 1) = u 2`, `δ (u 2) = u 3`,
     `δ (u 3) = −(Zz•u 0 + Uu•u 1 + Vv•u 2 + Ww•u 3)` and
     `δ (v 0) = u 0`, `δ (v 1) = y⁻¹•u 0`, `δ (v 2) = y⁻²•u 0`:
     * `deriv_relation` : differentiating a relation
       `Σ_j A_j • v_j = Σ_i b_i • u_i` (`A_j ∈ ℂ[y]`) replaces the `A_j` by
       their derivatives, at the cost of the explicit inhomogeneity
       `Σ_k (qv b k − ![Aterm,0,0,0] k) • u_k` (this is the paper's identity
       `(remaining)`, including the replacement of `Δ⁗` by
       `−(c₀Δ+…+c₃Δ''')/c₄`);
     * `system_of_relation` : a relation with *constant* integral coefficients
       (polynomial `A` of degree `0`) has **`b` satisfying the paper's system**
       `b₃' + b₂ − Ww·b₃ = 0`, `b₂' + b₁ − Vv·b₃ = 0`,
       `b₁' + b₀ − Uu·b₃ = 0`, `b₀' − Zz·b₃ = a₀ + a₋₁/y + a₋₂/y²`
       — the paper's step "differentiating `(todiff)` one more time … we
       deduce the simultaneous equations";
     * `exists_poly_relation` (clearing denominators: a relation with
       coefficients in `ℂ(y)` can be scaled to one with coefficients in
       `ℂ[y]`, via `RatFunc.num/denom`) and `exists_degree_zero_relation`
       (the paper's "after repeated differentiation we may assume that the
       coefficients of the three integral terms are all constants":
       descent on the measure `Σ_j deg (A_j)`, each step differentiating);
     * **`relation_trivial`** : *no* relation
       `Σ_j A_j • v_j = Σ_i B_i • u_i` with `A ≠ 0` exists — combining the
       two reductions above with `system_of_relation` and the final
       linear-algebra contradiction `FrobeniusApply.no_solution`;
      * `no_relation_const` : the same statement in the paper's own form, where the
        coefficients of the three integrals are *complex* constants
        (`∑_j (a_j : ℂ(y)) • v_j = ∑_i B_i • u_i` with `a : Fin 3 → ℂ` forces
        `a = 0` and `B = 0`);
      * `Submission.CDT.RatFuncConstants` (same node): **the constants of `K(X)`**
        — a rational function with vanishing derivative is a constant
        (`exists_const_of_dRat_eq_zero`, `dRat_eq_zero_iff_exists_const`),
        from the commons lemma
        `Commons.Algebra.Polynomial.eq_C_of_derivative_mul_eq`;
     * **`linearIndependent_seven`** : the seven elements
       `v₀,v₁,v₂,u₀,u₁,u₂,u₃` are `ℂ(y)`-linearly independent.
     This is exactly the second (functional-independence) half of the paper's
     Lemma `14functions` *after* the monodromy argument that produces the
     relation and the `ℂ(y)`-independence of `Δ,Δ',Δ'',Δ'''` (`hindep`, from
     the irreducibility of the order-`4` operator): those two inputs, the
     pure-function independence (Lemma `seven`), the modular integrality of
     `functionsH`/`defabc` and the arithmetic-holonomy bounds are what remains
     of the A-side;
5. the arithmetic-holonomy bound for the `typesA` array / `e`-vector
   (`τᵇ = 191/49`, `τ♯ = 27/80`, `m < 14`) — *external
   Bost–Charles/Arakelov machinery*.
Assembly: node 1 ∧ nodes 2–3 supply Proposition `functionsH`/`defG`;
then 4 ∧ 5 refute the absurd dependence, closing the leaf.
-/
lemma cdt_theoremA_leaf_gap : Submission.CDT.theoremA_leaf :=
  Work.AAsm.a_leaf (Work.Holonomy3.holonomy_bound_l2 Work.ZeroEst.zero_estimate)
    (Work.A14.fourteen_indep Work.C7.lemma_seven)
    (Work.ADen.a_denoms Work.Pure.pure_facts Work.ZagBI.zagier_b_integrality Work.ZagC.zagier_c_integrality)
    (Work.ADcl.a_dclosed Work.Pure.pure_facts)
    (Work.APull.a_pullbacks
      (Work.ALift.h_lift_cont Work.OdeCont.ode_continuation Work.ANum.a_numerics Work.Haupt.haupt_facts
        Work.APsi.psiA_facts)
      (Work.APhi.phi_lift_gen Work.Haupt.haupt_facts) Work.PureP.pure_pullbacks Work.Haupt.haupt_facts
      Work.APsi.psiA_facts Work.ANum.a_numerics)
    Work.PScale.pullback_scale Work.ANum.a_numerics Work.Tau.tau_values Work.APsi.psiA_facts
    Work.Haupt.haupt_facts

/-- Theorem A of Calegari–Dimitrov–Tang (arXiv:2408.15403): with
`χ₋₃ = ![0, 1, -1] : ZMod 3 → ℂ`, the numbers `1, ζ(2), L(2, χ₋₃)` are
linearly independent over `ℚ`.  **Assembled here in full** modulo the
single atomic leaf `cdt_theoremA_leaf_gap` (≡ CDT `mainA`, proved in the
paper by arithmetic holonomy bounds): the three-term statement is the
component form of `theoremA_leaf` (`Submission.CDT.theoremA_iff_leaf`),
and the proof below re-runs that equivalence inside the statement's own
character `χ = ![0, 1, -1]`.  Everything except the leaf is proved. -/
lemma cdt_theoremA :
    letI χ : ZMod 3 → ℂ := ![0, 1, -1]
    LinearIndependent ℚ ![1, riemannZeta 2, ZMod.LFunction χ 2] := by
  classical
  -- Theorem A ⟺ the atomic leaf `L(2,χ₋₃) ∉ ℚ + ℚ·ζ(2)` (the component
  -- form is `theoremA_iff_leaf`, proved in `Submission.CDT.TheoremA_leaf`).
  rw [Submission.Helpers.linearIndependent_cons3_iff (x := (1 : ℂ)) (y := riemannZeta 2)
      (z := ZMod.LFunction (N := 3) (![0, 1, -1] : ZMod 3 → ℂ) 2)]
  intro p q r hrel
  have hleaft : ∀ a b : ℚ, ZMod.LFunction (N := 3) (![0, 1, -1] : ZMod 3 → ℂ) 2 ≠ (a : ℂ) + (b : ℂ) * riemannZeta 2 := by
    intro a b hbad
    exact cdt_theoremA_leaf_gap a b (by
      have hL' : ZMod.LFunction (Submission.CDT.chi3) 2 = ZMod.LFunction (N := 3) (![0, 1, -1] : ZMod 3 → ℂ) 2 := by rfl
      rwa [hL'])
  by_cases hr : r = 0
  · -- the `L(2,χ₋₃)`-coefficient vanishes: `p + q·ζ(2) = 0` is killed by
    -- the transcendence of `ζ(2)` (Lindemann–Weierstrass chapter).
    have hpq : (p : ℂ) + (q : ℂ) * riemannZeta 2 = 0 := by
      simpa [hr, Algebra.smul_def] using hrel
    rcases Submission.CDT.pair_indep_comp (riemannZeta 2) Submission.CDT.zeta2_transcendental p q hpq with ⟨hp, hq⟩
    exact ⟨hp, hq, hr⟩
  · -- `r ≠ 0`: divide the relation by `r` to exhibit
    -- `L(2,χ₋₃) = −(p/r) − (q/r)·ζ(2)`, contradicting the leaf.
    have hrel' : (p : ℂ) + (q : ℂ) * riemannZeta 2 + (r : ℂ) * (ZMod.LFunction (N := 3) (![0, 1, -1] : ZMod 3 → ℂ) 2) = 0 := by
      simpa [Algebra.smul_def] using hrel
    have hcastp : ((p / r : ℚ) : ℂ) = (p : ℂ) / (r : ℂ) := by rw [Rat.cast_div]
    have hcastq : ((q / r : ℚ) : ℂ) = (q : ℂ) / (r : ℂ) := by rw [Rat.cast_div]
    have hrℂ : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    have h1' : (r : ℂ) * (ZMod.LFunction (N := 3) (![0, 1, -1] : ZMod 3 → ℂ) 2) + (p : ℂ) + (q : ℂ) * riemannZeta 2 = 0 := by
      linear_combination hrel'
    have h1'' : (r : ℂ) * (ZMod.LFunction (N := 3) (![0, 1, -1] : ZMod 3 → ℂ) 2) + ((p : ℂ) + (q : ℂ) * riemannZeta 2) = 0 := by
      simpa [add_assoc] using h1'
    have h1 : (r : ℂ) * (ZMod.LFunction (N := 3) (![0, 1, -1] : ZMod 3 → ℂ) 2) = -((p : ℂ) + (q : ℂ) * riemannZeta 2) := by
      exact eq_neg_of_add_eq_zero_left h1''
    have hL : ZMod.LFunction (N := 3) (![0, 1, -1] : ZMod 3 → ℂ) 2 =
        (-(p / r : ℚ) : ℂ) + (-(q / r : ℚ) : ℂ) * riemannZeta 2 := by
      calc
        ZMod.LFunction (N := 3) (![0, 1, -1] : ZMod 3 → ℂ) 2
            = (r : ℂ)⁻¹ * ((r : ℂ) * (ZMod.LFunction (N := 3) (![0, 1, -1] : ZMod 3 → ℂ) 2)) := by
              rw [← mul_assoc, inv_mul_cancel₀ hrℂ, one_mul]
        _ = (r : ℂ)⁻¹ * (-((p : ℂ) + (q : ℂ) * riemannZeta 2)) := by rw [h1]
        _ = -(p : ℂ) / (r : ℂ) - (q : ℂ) * riemannZeta 2 / (r : ℂ) := by
              field_simp [hrℂ]
              ring
        _ = (-(p / r : ℚ) : ℂ) + (-(q / r : ℚ) : ℂ) * riemannZeta 2 := by
              rw [hcastp, hcastq]
              ring
    exact False.elim (hleaft (-(p / r : ℚ)) (-(q / r : ℚ)) (by simpa using hL))

/-- Theorem C (irrationality half), **degenerate case `m = n`**: for
`m ∈ ℤ \ {-1, 0}`, `(log(1+1/m))²` is irrational.  This is the case the
paper dismisses as "a trivial consequence of the transcendence of
`log r` for `r > 0` in `ℚ \ {1}`"; it is PROVED here by the
Lindemann–Weierstrass chapter (`LindemannC.irrational_log_one_add_inv_sq`,
built on `cexp_transcendental_of_algebraic_ne_zero`). -/
lemma cdt_theoremC_irr_self (m : ℤ) (hm : m ≠ -1) (hm0 : m ≠ 0) :
    Irrational (Real.log (1 + 1 / (m : ℝ)) * Real.log (1 + 1 / (m : ℝ))) := by
  simpa [pow_two] using (Submission.Transcendence.irrational_log_one_add_inv_sq m hm hm0)

/-- **The former isolated obstruction of Theorem C, `m ≠ n` — now PROVED** (CDT `logsmain`,
part 2; arXiv:2408.15403 §"Products of two logarithms"): under
`m, n ∈ ℤ \{-1, 0\}`, `10⁶·|m−n| < |n|` and `m ≠ n`, the four numbers
`1, log(1+1/m), log(1+1/n), log(1+1/m)·log(1+1/n)` are linearly
independent over `ℚ`.  This is the single deep leaf of the whole `m ≠ n`
part of Theorem C: the product-irrationality half `cdt_theoremC_irr_ne` is
its `d`-coefficient case (`irr_of_cons4_li`), and the `m = n` degenerate
case is already settled (`cdt_theoremC_irr_self`).

**Route (the paper's §"Products of two logarithms", Theorems `logsmain` /
`logsmainagain`).**  Reparametrize `a = 1+2m`, `b = 1+2n` (odd,
`a,b ∉ {±1}`, `a/b` close to `1`) and write `η_a := ½·log((a+1)/(a−1))`
(= `½·log(1+1/m)`), so the claim is the `ℚ`-independence of
`1, η_a, η_b, η_a·η_b`, i.e. the *absence of any nonzero `ℤ`-relation*
(eq. (rabc)) `r_a·η_a + r_b·η_b + r_ab·η_a·η_b = r_0`.  Assuming such a
relation, the paper builds an **unlikely `G`-function** and refutes it:

1. the Beukers pair `A(a,x) = Σuₙxⁿ` (`= 1/√(1−2ax+x²)`, `uₙ ∈ ℤ` for odd
   `a`) and `H(a,x) = Σvₙxⁿ = A(a,x)·∫₀ˣ dt/A(a,t)` with `[1..n]·vₙ ∈ ℤ`,
   whose **Apéry limit** `vₙ/uₙ → η_a` is exponential — the rational and
   analytic core of this pair (recurrences, closed form, integrality
   `uₙ ∈ ℤ`, the companion `H = A·∫A`, the `[1..n]·vₙ` denominator claim,
   `beukers_apéry_limit` with the coefficient-growth bound) is formalized
   in `Submission.CDT.Beukers`;
2. **Hadamard products** `P_A = A(a) ⋆ A(b)`,
   `P_a = (H(a)−η_aA(a)) ⋆ A(b)`, `P_b = A(a) ⋆ (H(b)−η_bA(b))`,
   `P_ab = H(a) ⋆ H(b) − η_{a,b}·P_A` are holonomic (order-2 ODE,
   eq. (ODE), whose four nonzero finite singularities are the products
   `(a±√(a²−1))(b±√(b²−1))`, grouped near `0`, near `1` (twice), and near
   `∞`) and **overconvergent** beyond the smallest cusp — both formalized in
   `Submission.CDT.LogHadamard`: the order-2 ODE `M_{a,b}(P_A) = 0`
   (`logPA_ode`, from the commons creative-telescoping certificate
   `Commons.RingTheory.PowerSeries.logPA_ode`), and the coefficient bounds
   `beukersPaCoeff_beyond_cusp` / `beukersPbCoeff_beyond_cusp` /
   `beukersPabCoeff_beyond_cusp` (`|coeffₙ| ≤ C·sⁿ` with
   `s·ρ_a·ρ_b < 1`, `ρ_a := a−√(a²−1)` — the smallest cusp), whose engine
   is the sharp `u`-growth `beukersUR_cauchy_growth` (Cauchy + the
   slit-plane/sup-bound pair `beukersQuadC_mem_slitPlane_of_norm_le`,
   `beukersAComplex_norm_le`) times the sharp `d`-decay
   `beukersD_sharp_decay`;
3. the `ℤ`-combination (eq. (defP))
   `P = r_aP_a + r_bP_b + r_abP_ab + r_0P_A = Σcₙxⁿ` has rational
   coefficients `cₙ` with denominator type `[1..n]²`
   (`[1,2,…,n]²·cₙ ∈ ℤ`), is overconvergent, and satisfies a known
   non-homogeneous ODE — *contingent on the absurd relation (rabc)*.
   **NEW: the coefficient/denominator/overconvergence half of this step is
   now PROVED** in `Submission.CDT.LogUnlikelyG`
   (`logPCoeff_eq_rat`: under (rabc) the coefficients of
   `r_aP_a + r_bP_b + r_abP_ab` are the rational numbers
   `r_avₙ(a)uₙ(b) + r_buₙ(a)vₙ(b) + r_abvₙ(a)vₙ(b) − r₀uₙ(a)uₙ(b)`;
   `logPCoeffQ_denom`/`logP_denomTypeSq`: `[1..n]²·cₙ ∈ ℤ` for odd `a,b`,
   from the Beukers-pair integrality; `logPCoeff_beyond_cusp`:
   overconvergence beyond the smallest cusp; `logP_unlikely` the packaged
   statement; and `logP_symm_denomType` — the arithmetic half of the paper's
   Proposition `fictive G`: `G = Sym⁺P` has denominator type `[1..2n]²` while
   `G_A = Sym⁺P_A` has integer coefficients).  This step is now **CLOSED**:
   `Submission.CDT.LogMIdentities` proves the three `M`-identities of the
   paper's §"The overconvergent space" — `M(H(a)⋆A(b)) = −b+3aX−3bX²+aX³`
   (`logM_vu`), `M(A(a)⋆H(b)) = −a+3bX−3aX²+bX³` (`logM_uv`),
   `M(H(a)⋆H(b)) = −1+2X²−X⁴` (`logM_vv`), plus `M(A(a)⋆A(b)) = 0` in the
   same normal form (`logM_uu`, from `logPA_ode`) — as power-series
   identities over `ℚ` for the sequences `vₙ(a)uₙ(b)`, `uₙ(a)vₙ(b)`,
   `vₙ(a)vₙ(b)`.  Both `u` and `v` satisfy the three-term Legendre
   recurrence `RecProp` (`RecProp_beukersU`/`RecProp_beukersV`), so the
   fleet lemma `Commons.RingTheory.PowerSeries.coeff_LHS_general` (`claim7`
   for an *arbitrary* `RecProp` pair, proved this stretch) kills every
   coefficient `n ≥ 7`; the seven small coefficients `n ≤ 6` are computed
   explicitly from the first nine values of `u` and `v`
   (`coeff_LHS_{vu,uv,vv}_small`).  Linearity of the operator in its series
   argument (`logPAODE_add/sub/C_mul`) then gives **`logP_ode`**: the rational
   unlikely function `logP` satisfies
   `M(logP) = r_a(−b+3aX−3bX²+aX³) + r_b(−a+3bX−3aX²+bX³) + r_ab(−1+2X²−X⁴)`,
   a polynomial with rational coefficients — the paper's `M(P) ∈ ℚ[X]`.
   **What remains of the Theorem-C route** is step 5 (the explicit
   pushforward `ℒ` of `M` under the symmetrisation, and the
   arithmetic-holonomy bounds) together with the functional-independence
   half of Lemma `17functions`;
4. **symmetrization**: `G(y) := P(x) + P(x/(x−1)) ∈ ℚ[[y]]` and
   `G_A(y) := P_A(x) + P_A(x/(x−1)) ∈ ℤ[[y]]` in the coordinate
   `y = x²/(x−1)` — the formal descent machinery for exactly this step
   (φ-invariance ⟹ unique series in `y`) is DONE in
   `Submission.CDT.{SympH, SympDescent, SympZagier}`
   (`symp_descent`, `sympSym`, `sympSym_int`);
5. the pushforward `LL` of the ODE under `π : x ↦ y` gives `LL(G_A) = 0`
   and `LL(G) ∈ ℚ[y]`, both of denominator type `[1..2n]²` and ``close
   to'' the `𝐏¹∖{0,4,∞}` pure-function space of the paper's
   §"Functional Linear Independence" — the arithmetic-holonomy bounds
   (the ~200-page Bost-slopes/Arakelov machinery, §6/§7 of the paper)
   then refute the existence of such a `G`.  This final refutation is the
   deep missing content of `cdt_theoremC_li`.

**The first split (d = 0 vs d ≠ 0) — where this lemma decomposes.**  Via
`Submission.Helpers.linearIndependent_cons4_iff`, a `ℚ`-relation among
`1, lm, ln, lm·ln` splits by its `lm·ln`-coefficient:
* the **`d = 0` slice** — the `ℚ`-independence of `1, lm, ln` — is
  **CLOSED** (`Submission.CDT.TwoLogs.twoLogs_linearIndependent`, module
  `Submission.CDT.TwoLogs`): clear denominators to an integer relation
  `A + B·lm + C·ln = 0` (ℚ-clearing via the commons
  `Commons.Data.Rat.den_mul_self`), exponentiate with
  `Complex.exp_int_mul` to `e^A·r₁^B·r₂^C = 1`, kill `A ≠ 0` by LW
  (`cexp_transcendental_of_algebraic_ne_zero`), and finish by the
  multiplicative crux `r₁^B·r₂^C = 1 ⟹ B = C = 0`
  (`Commons.Data.Int.oneAddInvPowEq`, using the gap hypothesis).  The
  `d = 0` result reduces the four-number statement to:
* the **`d ≠ 0` product leaf**: `lm·ln` is not a `ℚ`-linear combination of
  `1, lm, ln` — the paper's (rabc)-refutation, which is where the deep
  §"Products of two logarithms" machinery (steps 1–5 above) attaches.
-/

lemma cdt_theoremC_li (m n : ℤ) (hm : m ≠ -1) (hm0 : m ≠ 0) (hn : n ≠ -1)
    (hn0 : n ≠ 0) (hgap : 10 ^ 6 * |m - n| < |n|) (hne : m ≠ n) :
    LinearIndependent ℚ ![1, Real.log (1 + 1 / (m : ℝ)),
      Real.log (1 + 1 / (n : ℝ)),
      Real.log (1 + 1 / (m : ℝ)) * Real.log (1 + 1 / (n : ℝ))] := by
  exact Work.CRed.c_li_of_pos
    (Work.CAsm.c_pos (Work.Holonomy3.holonomy_bound_l2 Work.ZeroEst.zero_estimate)
      (Work.C17.seventeen_indep Work.C7.lemma_seven)
      (Work.CDen.c_denoms Work.Pure.pure_facts) (Work.CDcl.c_dclosed Work.Pure.pure_facts)
      (Work.CPull.c_pullbacks
        (Work.CLift.p_lift_cont Work.OdeCont.ode_continuation Work.CRad.p_radius
          Work.CNum.c_numerics Work.CLoc.c_location Work.Haupt.haupt_facts Work.CPsi.psiC_facts)
        (Work.CPhi.phi_lift Work.Haupt.haupt_facts Work.CPsi.psiC_facts)
        Work.Haupt.haupt_facts Work.CPsi.psiC_facts Work.CNum.c_numerics)
      Work.CNum.c_numerics Work.Tau.tau_values Work.CPsi.psiC_facts Work.Haupt.haupt_facts)
    m n hm hm0 hn hn0 hgap hne

/-- The irrationality of a product `x·y` is the `d`-coefficient case of the
`ℚ`-independence of `1, x, y, x·y`: if `x·y = q ∈ ℚ` then
`q·1 + 0·x + 0·y + (−1)·(x·y) = 0` is a nontrivial `ℚ`-relation. -/
lemma irr_of_cons4_li (x y : ℝ)
    (h : LinearIndependent ℚ ![1, x, y, x * y]) : Irrational (x * y) := by
  rw [Irrational]
  intro hq
  rcases hq with ⟨q, hq⟩
  have hrel : (q : ℚ) • (1 : ℝ) + (0 : ℚ) • x + (0 : ℚ) • y + (-1 : ℚ) • (x * y) = 0 := by
    simp [hq]
  have hcomp := (Submission.Helpers.linearIndependent_cons4_iff (w := (1 : ℝ)) (x := x)
    (y := y) (z := x * y)).mp h q 0 0 (-1) hrel
  rcases hcomp with ⟨_, _, _, hd⟩
  norm_num at hd

/-- Theorem C (irrationality half) of Calegari–Dimitrov–Tang for `m ≠ n`:
under `m, n ∈ ℤ \{-1, 0\}` with `10⁶·|m−n| < |n|`, the product
`log(1+1/m)·log(1+1/n)` is irrational.  **Assembled here in full** from
the four-number independence leaf `cdt_theoremC_li` (the product
irrationality is exactly the `d`-coefficient case of that independence,
`irr_of_cons4_li`); `cdt_theoremC_li` is CDT Theorem `logsmain`, part 2,
whose proof is the deep arithmetic-holonomy content (see its docstring).
The `m = n` degenerate case is settled by Lindemann–Weierstrass in
`cdt_theoremC_irr_self` (so the full irrationality half `cdt_theoremC_irr`
is PROVED once `cdt_theoremC_li` is). -/
lemma cdt_theoremC_irr_ne (m n : ℤ) (hm : m ≠ -1) (hm0 : m ≠ 0) (hn : n ≠ -1)
    (hn0 : n ≠ 0) (hgap : 10 ^ 6 * |m - n| < |n|) (hne : m ≠ n) :
    Irrational (Real.log (1 + 1 / (m : ℝ)) * Real.log (1 + 1 / (n : ℝ))) := by
  exact irr_of_cons4_li (Real.log (1 + 1 / (m : ℝ))) (Real.log (1 + 1 / (n : ℝ)))
    (cdt_theoremC_li m n hm hm0 hn hn0 hgap hne)

/-- Theorem C (irrationality half) of Calegari–Dimitrov–Tang: for
`m, n ∈ ℤ \ {-1, 0}` with `10⁶·|m−n| < |n|`, `log(1+1/m)·log(1+1/n)`
is irrational.  Split: `m = n` is `cdt_theoremC_irr_self` (proved, by
Lindemann–Weierstrass); `m ≠ n` is `cdt_theoremC_irr_ne`, proved as the
`d`-coefficient case of the four-number independence leaf
`cdt_theoremC_li`. -/
lemma cdt_theoremC_irr (m n : ℤ) (hm : m ≠ -1) (hm0 : m ≠ 0) (hn : n ≠ -1)
    (hn0 : n ≠ 0) (hgap : 10 ^ 6 * |m - n| < |n|) :
    Irrational (Real.log (1 + 1 / (m : ℝ)) * Real.log (1 + 1 / (n : ℝ))) := by
  by_cases hne : m = n
  · subst n
    exact cdt_theoremC_irr_self m hm hm0
  · exact cdt_theoremC_irr_ne m n hm hm0 hn hn0 hgap hne



/-- Theorem A ∧ Theorem C of Calegari–Dimitrov–Tang (arXiv:2408.15403). -/
theorem cdt_linearIndependent :
    letI χ : ZMod 3 → ℂ := ![0, 1, -1]
    LinearIndependent ℚ ![1, riemannZeta 2, ZMod.LFunction χ 2] ∧
    ∀ m n : ℤ, m ≠ -1 → m ≠ 0 → n ≠ -1 → n ≠ 0 → 10 ^ 6 * |m - n| < |n| →
      letI lm := Real.log (1 + 1 / m)
      letI ln := Real.log (1 + 1 / n)
      Irrational (lm * ln) ∧
      (m ≠ n → LinearIndependent ℚ ![1, lm, ln, lm * ln]) := by
  -- Assembly of the two deep theorems; the deep theorems themselves are the
  -- open gap (see module docstring above).
  constructor
  · exact cdt_theoremA
  · intro m n hm hm0 hn hn0 hgap
    constructor
    · exact cdt_theoremC_irr m n hm hm0 hn hn0 hgap
    · intro hne
      exact cdt_theoremC_li m n hm hm0 hn hn0 hgap hne


/-! ### SESSION 38 — the Weyl algebra of differential operators, and the holonomic toolkit
(SHARED COMMONS)

This session added ~45 lemmas to the *commons* only; **the submission chain above is unchanged**
(`lake build Submission` is green with exactly the same two leaf `sorry`s).  The chapter answers
"what is the algebraic home of a linear differential operator with polynomial coefficients?" —
the Weyl algebra `A₁(K) = K⟨X, ∂⟩/(∂X − X∂ − 1)`, realised as the `K`-subalgebra of
`Module.End K (K⟦X⟧)` generated by `∂ = d/dX` and by `X·`.

* `Commons.Algebra.Weyl.*`: `derivative_mul_mulLeft_X` (`∂ * X· = X· * ∂ + 1`),
  `pow_mul_pow_eq_sum` (`d^j x^k = ∑_m C(j,m)(k)_m x^{k-m} d^{j-m}` for an abstract Weyl pair),
  `mem_adjoin_imp_mem_span` / `mem_adjoin_imp_mem_span_dual` (spanned by `x^i d^j` resp. `d^i x^j`),
  `mulLeft_mem_adjoin`, `sum_mulLeft_deriv_pow_mem_adjoin` and `mem_adjoin_exists_normalForm`
  (normal form `∑_{j≤r} P_j(X) ∂^j`, `P_j ∈ K[X]`), `mul_eq_sum_normalForm` (the order filtration
  is multiplicative: the top coefficient of a product is `P_r·Q_s`) and
  `mul_ne_zero_of_last_ne_zero` (no zero divisors in normal form).
* `Commons.RingTheory.PowerSeries.*`: the *faithfulness* of that normal form
  (`sum_mulLeft_deriv_pow_eq_zero_iff`, characteristic `0`), `iterate_derivative_X_pow`, and the
  **operator form of holonomy `isDFinite_iff_exists_adjoin`**:
  `IsDFinite f ↔ ∃ L ∈ A₁(K), L ≠ 0 ∧ L f = 0`.
* the `θ = X·∂` layer: `theta_pow_apply_X_pow`, `theta_form_faithful_charZero`,
  `x_pow_mul_deriv_pow_eq_sum_theta`, `isDFinite_iff_exists_theta_ode`,
  `isDFinite_subst_X_pow` (dilation);
* closure of `IsDFinite`: `isDFinite_exp`, `isDFinite_sin`, `isDFinite_cos`, `isDFinite_log`,
  `isDFinite_mk_factorial`, `isDFinite_mk_choose_two_mul`, `isDFinite_mk_choose_two_mul_sq`
  (Apéry), `isDFinite_map_catalanSeries`, `isPrecursive_factorial`, `isPrecursive_choose_two_mul`,
  `isPrecursive_catalan`, `isDFinite_section` / `isPrecursive_section`,
  `isDFinite_of_derivative`, `isDFinite_pow`, `isDFinite_subst_C_mul_X_iff`,
  `isDFinite_of_X_pow_mul`, `isDFinite_of_mul_polynomial`, `exists_minimal_ode`,
  **`isDFinite_of_algebraic_of_relation`** (the general "algebraic ⟹ D-finite": *any* nonzero
  polynomial relation `P(f) = 0` over `K[X]`, no monicity needed) and
  **`isDFinite_comp_ratFunc`** (composition with a rational function with zero constant term);
  the last two use the new dependence device
  `Commons.LinearAlgebra.Module.dependence_of_smul_mem` (linear dependence over `Frac K[X]`,
  cleared denominators) — the missing tool for every `K(X)`-span argument.
* `Commons.RingTheory.MvPowerSeries.*` (new area): the diagonal `diag` of a bivariate formal power
  series, `diag_add`, `diag_mul_eq_hadamard` (`diag(f(X)g(Y)) = f ⊙ g`),
  `diag_inv_one_sub_X0_sub_X1` (`diag (1−X₀−X₁)⁻¹ = ∑ C(2n,n)Xⁿ`) and
  `isDFinite_diag_inv_one_sub_X0_sub_X1` (a first "diagonal of a rational function is D-finite").
* `Commons.Algebra.Polynomial.eval_prod_X_sub_C_range`.

Negative reconnaissance recorded in `Scratch/lemma14/README.md` (sections "SESSION 38" and the
addenda): `IsDFinite` is **not** closed under reciprocal (`1/(1+eˣ)` is not holonomic), and the
"diagonal of a rational series" landmark needs honest residue calculus — `CT_y R(x/y,y)` is *not*
the two-variable constant term for a rational `R`.
-/


/-! ### SESSION 39 — the differential operator algebra `K(X)[∂; d/dX]` (SHARED COMMONS)

This session added ~55 lemmas to the *commons* (a new area `Commons.Algebra.WeylOps`, plus
additions to `Commons.RingTheory.RatFunc`); **the submission chain is unchanged** and
`lake build Submission` stays green with the same two leaf `sorry`s — none of the new material is
imported by `Submission.lean`.

The object is the first Weyl algebra *over the field `K(X)`*, i.e. the Ore extension
`K(X)[∂; d/dX]`, represented faithfully on `K(X)` itself.  `Commons.Algebra.WeylOps.opOf D P`
(`P : Polynomial (RatFunc K)`) is the `K`-linear endomorphism `Σ_i P_i · D^i` of `K(X)`
(`D : Derivation K (RatFunc K) (RatFunc K)`); the chapter is the "linear algebra of linear
differential operators":

* *faithfulness and normal form*: `opOf_injective` (`opOf D P = 0 → P = 0`, characteristic `0`),
  `opOf_apply`, `opOf_add`/`_sub`/`_sum`/`_zero`/`_one`/`_C`/`_X`/`_monomial`/`_C_mul`,
  `opOf_starPow`;
* *the twisted product* (`starMul`, the multiplication of the Ore extension transported to the
  coefficient polynomial): `opOf_mul` (`opOf P * opOf Q = opOf (P ⋆ Q)`), `starMul_assoc`,
  `starMul_add_left`/`_right`/`_sub_left`/`_sub_right`/`_smul_left`/`_C_left`/`_C_mul_left`,
  `starMul_zero_left`/`_zero_right`/`_one_right` (the constant `1` is a two-sided identity),
  the Ore relations `starMul_X_left` (`X ⋆ P = X·P + P′`) and
  `starMul_mul_X`/`starMul_X_pow_right` (`P ⋆ X = P·X`), and the **order calculus**
  `starMul_natDegree` (`deg (P ⋆ Q) = deg P + deg Q`), `starMul_natDegree_le`,
  `starMul_leadingCoeff` (`lc (P ⋆ Q) = lc P · lc Q`), `starMul_ne_zero` (no zero divisors) and
  `starPow_natDegree`;
* *Euclidean structure*: `starMul_div` (division with remainder `Q = S ⋆ P + R`, `deg R < deg P`),
  `exists_gcrd` (the Bezout form of the greatest common right divisor: `G = A ⋆ P + B ⋆ Q`, with
  `P`, `Q` right multiples of `G`), `exists_principal_generator` (**the left ideal generated by
  two operators is principal** — the Bezout-domain property), `exists_lclm` (**least common left
  multiples exist with order at most `deg P + deg Q`**, by a dimension count) and
  `exists_annihilator_principal` (every `f ∈ K(X)` is annihilated by a nonzero operator, and its
  annihilator is principal);
* *conjugation and pushforward*: `conjOp D σ c M` (replace `∂` by `(1/c)∂` and every coefficient
  by its `σ`-image), `opOf_conjOp` (`(opOf (conjOp … M)) (σ g) = σ ((opOf M) g)` whenever
  `D (σ f) = c · σ (D f)`), `exists_pushforward`, and finally
  **`pushforward_annihilates_symmetrization`**: for an involutive `σ`, a pushforward
  `A ⋆ M = B ⋆ (conjOp D σ c M)` annihilates the *symmetrization* `f + σ f` of every solution `f`
  of `opOf M`.  This is the abstract form of the paper's `LL(G_A(y)) = 0`;
* *derivations of `K(X)`*: `derivation_eq_smul_deriv` (they form a one-dimensional `K(X)`-vector
  space), `deriv_comp_algEquiv` (composing a derivation with a `K`-algebra automorphism gives a
  scalar multiple) and `iterate_deriv_algebraMap` (`D^i` of a polynomial is the `i`-th polynomial
  derivative);
* *order of vanishing at a point* (`Commons.FieldTheory.RatFunc.*`): `ordAt α x`
  (`= rootMultiplicity α x.num − rootMultiplicity α x.denom`) with its calculus
  `ordAt_algebraMap`, `ordAt_one`, `ordAt_mul`, `ordAt_inv`, `ordAt_div`, `ordAt_pow`,
  `ordAt_neg`, `min_ordAt_le_ordAt_add` and `ordAt_add_of_lt` — the valuation calculus behind the
  Frobenius/indicial (pole-order) analysis of a rational solution of a linear ODE.
-/


/-! Addendum to SESSION 39 (same session, after the block above): two further commons packages.

* The `WithTop ℤ`-valued valuation: `Commons.FieldTheory.RatFunc.ordAtT` (`↑(ordAt α x)`, `⊤` at
  `0`) with `ordAtT_def`, `ordAtT_eq_top_iff`, `ordAtT_neg`, `ordAtT_add_ge`, `ordAtT_mul`,
  `ordAtT_inv`, `ordAtT_div`, `ordAtT_pow`, `ordAtT_algebraMap`, `ordAtT_add_eq_of_le_succ` and the
  finite-sum rules `le_ordAtT_finset_sum` / `ordAtT_finset_sum_eq` — the valuation calculus on
  which the Frobenius/indicial analysis of a linear differential operator runs.
* The Frobenius cascade numerator in `Commons.Algebra.Polynomial`: `fallFact`, `dnum` (with
  `dnum_def`), `iterate_deriv_div_dnum` (`D^j (p/q) = dnum p q j / q^{j+1}` for any derivation `D`
  of `K(X)`), `fallFact_cast_ne_zero` and the cascade degree theorem
  **`dnum_natDegree_leadingCoeff`**
  (`natDegree (dnum p q j) = p.natDegree + 2j`,
  `leadingCoeff (dnum p q j) = (lc q)^j (N)_j (lc p)`, `natDegree q = 3`, `N = p.natDegree − 3`).
* The **Frobenius/indicial local theorems** (`Commons.FieldTheory.RatFunc`):
  **`frobenius_tie`** (the indicial theorem: if the residues `z^{e j} f^{(e j)} − (N)_{e j} f`
  have order `≥ N + 1` and the indicial value `σ = ∑_j (N)_{e j} B_j(α)` is nonzero, then
  `∑_j z^{e j} B_j · (d/dx)^{e j}` has order *exactly* `N` at `α`), `frobenius_order_ge` (the
  one-sided pole-order bound `ord_α (∑_j A_j f^{(e j)}) ≥ M`, with no indicial hypothesis),
  `ordAtT_iterate_deriv_ge` and `ordAtT_residual_ge` (the residual bound, i.e.
  `euler_cascade_dvd` read through `ordAtT`).  With these the whole local-exponent engine of
  `Submission/CDT/FrobeniusLocal.lean` exists in the commons for an arbitrary derivation `D`.
* The **symmetrization instantiation** (the paper's step 5 in the rational-function model):
  `Commons.RingTheory.RatFunc.exists_ratFuncDeriv` (the canonical `d/dX` as a `K`-derivation of
  `K(X)`), `Commons.FieldTheory.RatFunc.exists_sympSigma` (the Möbius involution `x ↦ x/(x−1)` as
  an order-two `ℚ`-algebra automorphism of `ℚ(X)`), `sympSigma_deriv_comp`
  (`D (σ f) = −(X−1)⁻² · σ (D f)`) and the capstone **`exists_symp_pushforward`**: for an
  involutive `σ` with `σ X = X/(X−1)` and `c = −(X−1)⁻²`, every nonzero `M` has a nonzero
  pushforward of order at most `deg M + deg (conjOp D σ c M)` annihilating `f + σ f` for every
  solution `f` of `opOf M` — the abstract form of `LL(G_A(y)) = 0`.
* `Commons.FieldTheory.RatFunc.instAlgebraOfPolynomial_eq_toRatAlgebra`: the two `ℚ`-algebra
  structures on `ℚ(X)` coincide (they are `Subsingleton`), which de-fuses the `RatFunc ℚ`
  instance diamond that otherwise blocks specialising a generic-`K` statement to `K = ℚ`.
-/

/-! ### SESSION 40 — the EXPLICIT C-side pushforward operator `LL` (reconnaissance only)

No change to the trust chain: the leaf `sorry`s are untouched and no new module is imported.
The session computed, verified and documented the **explicit order-four operator `LL`** of the
paper's §"Products of two logarithms" — the single remaining *formalizable* input of the C-side
step 5 (`Submission.cdt_theoremC_li`).  Everything is in `Scratch/lemma14/cside/` (scripts,
data `ll_data.json`, computed `LLdata.lean`, and a README with the full write-up).

* `LL = Σ_{i=0}^4 c_i(y)·∂_y^i` over `ℚ(a,b,y)` with (the paper's normalisation)
  `c_4 = (y-4)²y³·R₄(y)·R₁₀(y)`, `c_3 = (y-4)y²·Λ`, `c_3/c_4 = Λ := 3/(y-4) + 5/y +
  3R₄'/R₄ − R₁₀'/R₁₀`, and `c_0,c_1,c_2` of `y`-degrees 12, 16, 17 — exactly the paper's
  displayed `(coefficientsofL)`, including the scalar identity
  `c_4 = −128(a−b)⁶·(y−4)²y³R₄R₁₀` in the `y¹⁹`-monic normalisation.
* Two **independent** computations agree: (A) the annihilator of the power series
  `G_A(y) = P_A(x) + P_A(x/(x−1))` (kernel of the coefficient equations for operators of
  order ≤ 4; the interpolation of all 48 coefficient polynomials in `(a,b)`, total degree
  ≤ 12, validated at 11 points), and (B) the pushforward `D`-module
  `V = K[∂_x]/(M)`, `K = ℚ(a,b)(x)`, `∂_y ↦` left multiplication by `ρ∂_x`,
  `ρ = dx/dy = (x−1)²/(x(x−2))` — where `LL` is (up to scalar) the generator of the
  annihilator of the class of `1`.  All four ratios `c_i/c_4` of route (A) coincide exactly
  with those of route (B).
* **Trap recorded**: that action is *derivation-like* (`A·(fw) = f·(Aw) + (∂_y f)·w`), hence
  **not** `F`-linear, so the "matrices" `A^i` of the naive computation do **not** represent the
  action and the resulting characteristic polynomial is not the operator — an apparent
  "contradiction" that cost a long detour.  The correct object is the left ideal
  `{L ∈ F[∂_y] : L·1 = 0}` computed by *iterating* the action.
* Next formalization step (documented in the Scratch README): the certificate
  `Σ_i c_i(y)·A^i ∈ K[∂_x]·M` (an explicit division identity), the analogue of the A-side's
  `Submission/CDT/FinalLinear.lean` input; then the local/indicial analysis of `LL` and the
  final `10×10` determinant of Lemma `17functions`.
-/

/-! ### SESSION 41 — the C-side data chapter `LL` (runs)

`Submission.CDT.LLData` (namespace `Submission.CDT.LL`) turns the C-side computer-algebra
reconnaissance of SESSION 40 into checked mathematics.  It contains the paper's explicit
polynomials `R₄`, `R₁₀` (their displays), the log-derivative numerator `LambdaNum`, the
paper's `c₃ = y²(y-4)Λnum`, `c₄ = (y-4)²y³R₄R₁₀`, the quartic `Q₄` of `(ODE)`, and the
identities

* **`R4_symmetrisation`** — the paper's remark that `(1-x)⁴R₄(x + x/(x-1))` has
  `(a ± √(a²-1))(b ± √(b²-1))` as four of its eight roots, together with their `w`-images.
  Formally: `(X-1)⁴ R₄(X²/(X-1)) = Q₄(X) · Q₄^w(X)`, where `Q₄^w(X) = (X-1)⁴Q₄(X/(X-1))`.
  In particular the roots of `R₄(y)` are exactly the four singularities `y_{a^±,b^±}` of
  the pushforward `LL` — this is what pins the local/indicial analysis of `LL` to the
  singularities of the two Legendre equations.
* **`c3_mul_eq_c4_mul`** — the paper's `c₃/c₄ = 3/(y-4) + 5/y + 3R₄'/R₄ - R₁₀'/R₁₀`,
  cleared of denominators.  (This is the identity that makes the roots of `R₁₀` *non*-genuine
  singularities of `LL`.)
* `X2_pow3_dvd_c4`, `X2_sub4_sq_dvd_c4`, `X2_sq_dvd_c3`, together with the paper's shape
  `(y-4)²y³R₄R₁₀ ∣`-factorisation of `c₄`.

The computed tables of `c₀, c₁, c₂` (the paper's `R₁₂`, `R₁₆,ᴬ`, `y R₁₆,ᴮ`) are recorded in
**`Submission/CDT/LLOperator.lean`** (namespace `Submission.CDT.LLOp`, 1830 monomials,
source data `Scratch/lemma14/cside/ll_data.json`, regenerated by
`Scratch/lemma14/cside/gen_llop.py`), together with the shape fact `y ∣ c₂` needed by the
local analysis.  That module is **deliberately NOT imported here**: its tables take ≈ 9
minutes to elaborate, and `lake env lean Submission/CDT/LLOperator.lean` is the (green)
check.  The coefficient tables of `LL` and of the pushforward cofactor `Q` clear to
polynomials in `(a,b,X)` of `X`-degree ≈ 50 and `(a,b)`-degree ≈ 16 (≈ 10⁴ monomials per
coefficient identity), so both the *certificate* `Σᵢcᵢ(y(X))A^i = Q·M` and the *final* linear
algebra of Lemma `17functions` are size-blocked for a `ring`-style formalisation — they are
the largest open items of the C-side, together with the external Bost–Charles input.  The
full reconnaissance (two independent derivations of `c₀,c₁,c₂`, all three verification
routes) is in `Scratch/lemma14/cside/README.md`.

`Scratch/lemma14/cside/README.md` also carries the SESSION 41 note: the apparent
contradiction between `LL(G_A) = 0` and `Σᵢcᵢ(y(X))A^i ∈ (M)` is **not** a contradiction,
because the inference `Q·M(S) = 0 ⟹ M(S) = 0` is invalid — the cofactor `Q` of the LCLM
`LCLM(M, M^w) = QM = Q₂M^w` annihilates the non-zero function `M(P_A∘w)` since
`M^w(P_A∘w) = 0`.  Both facts were re-verified numerically at `(a,b) = (3,5)`.
-/

/-! ### SESSION 41 (continued) — new commons lemmas of the descent/pushforward layer

The fleet published, and these are now available in the shared commons (import the module and
use the full name):

* `Commons.RingTheory.PowerSeries.derivative_subst` — the chain rule for formal substitution,
  `(f ∘ g)' = (f' ∘ g)·g'`.  Mathlib had no `PowerSeries.subst_derivative` at all; this is the
  key input of every "descend along a substitution" argument.
* `Commons.RingTheory.PowerSeries.iterate_smul_derivative_subst` — the descent/pushforward
  transfer: if `ρ·g' = 1` then `(h ↦ ρ·h')ᵏ (f ∘ g) = f⁽ᵏ⁾ ∘ g`.  This is the formal-power-series
  form of "`∂_y` acts on the pullback of a function of `y` as `ρ ∂_X`", i.e. of
  `Φ(L)(G∘y) = (LG)∘y` for the pushforward `Φ`.
* `Commons.RingTheory.PowerSeries.subst_injective_of_ord_one` — `f ↦ f(g)` is injective when
  `g` has order one (the descent is injective).
* `Commons.FieldTheory.RatFunc.fixedField_sympSigma` — the **fixed field of the symmetrising
  involution**: for the `K`-algebra automorphism `σ` of `K(X)` with `σ X = X/(X-1)` and
  `σ∘σ = id`, every `σ`-fixed rational function is a rational function of `y = X²/(X-1)`.
  This is the algebraic form of the *descent* used in both CDT pushforward steps (the analogous
  statement for formal power series is `Commons.RingTheory.PowerSeries.comp_subst_of_invariant`).
* `Commons.RingTheory.Derivation.adjoint_of_firstOrder_system` — the **elimination of a
  first-order chain into a fourth-order equation**: given `D b₃ = g₃b₃ − b₂`, `D b₂ = g₂b₃ − b₁`,
  `D b₁ = g₁b₃ − b₀`, `D b₀ = g₀b₃ + R`, one has
  `Σ_{i≤3} (−1)ⁱ (gᵢ b₃)^{(i)} + b₃⁗ = −R`, i.e. `b₃` solves the fourth-order equation whose
  principal part is the formal adjoint of the *monic* operator `∂⁴ + g₃∂³ + g₂∂² + g₁∂ + g₀`.
  This is the algebraic input of the local/indicial analysis of both CDT systems (`(onceagain)`
  and the Theorem-A analogue), and it is exactly the step that converts the paper's system of
  four first-order equations into the statement "`Σ aᵢyⁱ = S₄₂/(y⁴R₁₀⁴)`" — see the SESSION 41
  notes in `Scratch/lemma14/cside/README.md`.
* `Commons.RingTheory.Polynomial.Q4_eval_prod_sqrt` — the four roots of the quartic `Q₄` of
  `(ODE)` are `(a ± √(a²−1))(b ± √(b²−1))`; combined with `R4_symmetrisation` this identifies
  the four `y_{a^±,b^±}` singularities of `LL` with the singularities of the two Legendre
  equations.
* `Commons.FieldTheory.RatFunc.ordAtT_iterate_deriv_mul_ge` — `ord_α(Dᵏ(γ·f)) ≥ ord_α γ + ord_α f − k`,
  the local estimate for the leading term of the eliminated fourth-order expression.

`Submission.CDT.LLData` additionally now contains the **residues of `Λ = c₃/c₄`**:
`X2_dvd_LambdaNum_sub_five`, `X2_sub4_dvd_LambdaNum_sub_three`,
`R4_dvd_LambdaNum_sub`, `R10_dvd_LambdaNum_add`, i.e. the residue is `5` at `y = 0`, `3` at
`y = 4`, `3` at each (simple) root of `R₄` and `−1` at each (simple) root of `R₁₀`.
These are the local data that feed the indicial analysis at each singularity of `LL`.
-/

/-! ### SESSION 41 (III) — the five indicial polynomials of the C-side system

`Scratch/lemma14/cside/{indicial.py,indicial2.py,indicial3.py}` compute, from the tables of
`c₀, c₁, c₂` (independently obtained, see `Submission/CDT/LLOperator.lean`) together with the
paper's `c₃, c₄`, the **indicial polynomial of the eliminated fourth-order equation at each
singularity of `LL`** and find that **all five agree exactly with the paper's display
`(onceagain)`**:

| `α` | `P_α(N)` | paper |
| --- | --- | --- |
| `0` | `¼(N-3)²(2N-5)²` | `-¼(3-N)²(5-2N)²` |
| `4` | `¼(N-2)(N-3)(2N-5)(2N-3)` | `-¼(2-N)(3-N)(5-2N)(3-2N)` |
| root `β` of `R₄` | `(N-1)(N-2)(N-3)²` | `-(1-N)(2-N)(3-N)²` |
| root `γ` of `R₁₀` | `(N-1)(N-2)(N-3)(N+1)` | `(1-N)(2-N)(3-N)(1+N)` |
| `∞` | `(N-5)(N-4)²(N-3)` | `-(5-N)(4-N)²(3-N)` |

At `α = 0` and `α = 4` these depend on `λ₁, λ₂`, the leading coefficients of `c₁/c₄`, `c₂/c₄`
(the constants `1/4`, `17/4` and `3/4`, `3`), so the match validates the computed tables.
Consequently the paper's five bounds `N₀ ≥ 0`, `N₄ ≥ 2`, `N_β ≥ 1`, `N_γ ≥ -1`, `N_∞ ≤ 5`
follow by comparing `ord_α(Σ_{i}(-1)ⁱ(γᵢb₃)^{(i)}) = ord_α(-R)` with `ord_α R`
(`ord₀ R ≥ -4`, `ord₄ R ≥ 0`, `ord_β R ≥ 0`, `ord_γ R ≥ 0`, `ord_∞ R ≥ -1`) and reading the
ordinary-derivative factor `(N+eᵢ)ᵢ` of the term `(γᵢb₃)^{(i)}` — the last ingredient being
available exactly in `Commons.RingTheory.Derivation.adjoint_of_firstOrder_system`.

The bound at `∞` gives `deg_y cᵢ = 12,16,17,18,19` for `i = 0,…,4`, so
`b₃ = (y-4)²R₄(y)Q(y)/R₁₀(y)` with `deg Q ≤ 9` (the paper's `(b3eqlog)`).  What is *not*
formalised is (a) the exactness of `ord_α` for the adjoint expression (the analogue of
`Commons.FieldTheory.RatFunc.frobenius_tie` for the eliminated form, whose `≥` half is
`Commons.FieldTheory.RatFunc.ordAtT_iterate_deriv_mul_ge`), and (b) the explicit local
coefficients `λ₁, λ₂` of `c₁/c₄`, `c₂/c₄` at `0` and `4` (small: only the `y⁰` and `y¹`
coefficients of `c₁, c₂` and the leading coefficient of `c₄` in each case).  The full
reconnaissance is in `Scratch/lemma14/cside/README.md` §11.
-/

/-! ### SESSION 41 (IV) — the indicial-exactness lemma, and the local data at `y = 0`

* `Commons.FieldTheory.RatFunc.ordAtT_adjoint_eq_of_indicial` — **the key missing piece of the
  local analysis on both sides**: for `D` the standard derivation of `K(X)`, `α : K`,
  `b ≠ 0` with `ord_α b = N` and `N`-leading coefficient `r ≠ 0`, and `γᵢ` with
  `ord_α γᵢ = eᵢ`, `eᵢ`-leading coefficient `λᵢ` (all encoded as second-order residual
  bounds), if `m ≤ eᵢ − i` for all `i ≤ 4` and the *indicial value*
  `Σ_{i : eᵢ−i=m} (−1)ⁱ λᵢ (N+eᵢ)ᵢ` is non-zero, then
  `ord_α (Σᵢ (−1)ⁱ Dⁱ(γᵢb)) = N + m`.  Together with
  `Commons.RingTheory.Derivation.adjoint_of_firstOrder_system` (the elimination of the
  first-order chain into the fourth-order equation) and
  `Commons.FieldTheory.RatFunc.ordAtT_iterate_deriv_mul_ge` (the `≥` half) this is *all* the
  general machinery the local/indicial analysis of the CDT systems needs.
* `Submission.CDT.LLData` now also records the **local data at the branch point `y = 0`**:
  `evalY0` (the substitution `y ↦ 0`), `evalY0_R4 : R₄(0) = 1`,
  `evalY0_R10 : R₁₀(0) = 4a²b²`, `evalY0_R4_mul_R10`.  With `Λnum(0) = −20R₄(0)R₁₀(0)`
  (all the other terms of `Λnum` carry a factor `y`) and `y³ ∣ c₄`, `y² ∣ c₃` these give the
  exponents `e = (−3,−3,−2,−1,0)` and the leading coefficients `λ = (·,1/4,17/4,5,1)` at
  `y = 0`, hence the indicial polynomial `¼(N−3)²(2N−5)²` and the bound `N₀ ≥ 0`
  (SESSION 41 §11 of `Scratch/lemma14/cside/README.md`).
-/

/-! ### SESSION 42 — the C-side local bounds `N_β ≥ 1` and `N_γ ≥ −1` (`Submission.CDT.CsideLocal`)

The local/indicial analysis of the C-side operator `LL` is now **proved**, for the two singularities
where no data from the computed coefficients `c₀, c₁, c₂` is needed.  The module
`Submission.CDT.CsideLocal` (in the import chain, zero `sorry`, ≈ 130 s to build) contains:

* **the local polynomial data at a simple root `β` of `R₄`**: `cden R4 R10 = (X−4)·X·R4·R10`,
  `cden_ne_zero`, `eval_cden`, `derivative_eval_cden`, and
  `rootMultiplicity_cden : ord_β(cden) = 1` (from `R₄(β)=0`, `R₄'(β)≠0`, `R₁₀(β)≠0`, `β∉{0,4}`);
  the residue numerator `residueNum R4 R10 Λnum β = Λnum·(X−β) − 3·cden R4 R10`, the derivative
  `derivative_residueNum`, and **`dvd_sq_X_sub_C_residueNum : (X−β)² ∣ residueNum`** — the algebraic
  content of the residue `+3` of `c₃/c₄` at `β`;
* the rearrangement `sub_div_identity` (`γ₃ − 3/(y−β)` over the common denominator) and
  **`residual_gamma3_at_root_of_R4 : ord_β(γ₃ − 3·(X−β)^{-1}) ≥ 0`**;
* **`local_bound_at_root_of_R4 : 1 ≤ ord_β b`** — the paper's `N_β ≥ 1`.  Given the eliminated
  equation `Σᵢ (−1)ⁱ Dⁱ(γᵢ b) = −R` with `γ₄ = 1`, `γ₃ = c₃/c₄` and the `γᵢ` (`i ≤ 2`) of the form
  `c/c₄` with `c` a polynomial, an inhomogeneity `R` with `ord_β R ≥ 0`, and `β` a simple root of
  `R₄` with `β ∉ {0,4}`, `R₁₀(β) ≠ 0`, the order of `b` at `β` is at least `1`.  The indicial
  polynomial at `β` is `(N−1)(N−2)(N−3)²`: with `e = (−1,−1,−1,−1,0)`, `m = −4` and the leading
  coefficients `λ₃ = 3`, `λ₄ = 1` (the residues of `Λnum/((y−4)yR₄R₁₀)`), a value `N ≤ 0` would force
  the indicial value `(N−1)(N−2)(N−3)²` to vanish, i.e. `N ∈ {1,2,3}` — contradiction;
* the mirror image at a simple root `γ` of `R₁₀` (`rootMultiplicity_cden_R10`, `residueNumG`,
  `dvd_sq_X_sub_C_residueNumG`, `add_div_identity`, `residual_gamma3_at_root_of_R10`) and
  **`local_bound_at_root_of_R10 : −1 ≤ ord_γ b`** (indicial polynomial `(N−1)(N−2)(N−3)(N+1)`,
  integer roots `−1,1,2,3`, so `N ≤ −2` is impossible);
* the auxiliary `ordAtT_div_cden_ge` / `ordAtT_div_cden_ge_R10` (`ord ≥ −1` for the coefficients
  `c/c₄` of the indices `i ≤ 2`);
* **the bridge to the paper's polynomials**: `spec a b : ℚ[a,b,y] → K[y]` (`a ↦ a`, `b ↦ b`,
  `y ↦ X`), `spec_X0/X1/X2`, **`spec_pderiv : spec (∂p/∂y) = (spec p)'`**, and the residue
  evaluations **`spec_LambdaNum_eval_at_root_of_R4`**
  (`Λnum(β) = 3(β−4)βR₄'(β)R₁₀(β)`) and `spec_LambdaNum_eval_at_root_of_R10`
  (`Λnum(γ) = −(γ−4)γR₄(γ)R₁₀'(γ)`), both obtained by specialising the divisibility lemmas
  `LLData.R4_dvd_LambdaNum_sub` / `LLData.R10_dvd_LambdaNum_add`.  The corollaries
  `local_bound_at_root_of_R4_spec` / `_R10_spec` are the two local bounds *for the paper's
  `R₄, R₁₀, Λnum`*.
* three new commons lemmas (proved by the fleet):
  `Commons.FieldTheory.RatFunc.ordAtT_adjoint_eq_of_indicial_le` (the indicial-exactness lemma with
  `ord_α γᵢ = eᵢ` relaxed to `eᵢ ≤ ord_α γᵢ` on the indices `eᵢ−i ≠ m`, and the leading-coefficient
  residual required only on `eᵢ−i = m` — this is what makes the `β`/`γ` cases need no `c₀,c₁,c₂`
  data), `Commons.FieldTheory.RatFunc.exists_leading_term` (every nonzero `b ∈ K(X)` has a leading
  term `r(X−α)^N` at `α`, `r ≠ 0`), and `Commons.Algebra.Polynomial.dvd_sq_X_sub_C_iff`
  (`(X−β)² ∣ p ↔ p(β) = p'(β) = 0`).

The remaining singularities (`α = 0`, `α = 4`, `α = ∞`) additionally need the `α`-adic leading
coefficients of `c₁, c₂` (and the degrees of `c₀..c₄`), which live in `Submission.CDT.LLOperator`
(deliberately outside the import chain because of its ≈ 9 min elaboration cost); they are recorded in
`Scratch/lemma14/cside/README.md` §11 together with the five indicial polynomials.

**SESSION 42 (II) — the local bounds at `α = 0` and `α = 4`.**  `Submission.CDT.CsideLocal` also now
contains `ordAtT_div_mul_ge` / `residual_at_zero` / `local_bound_at_zero` (the bound `N_0 ≥ 0`: the
data are `d(0) ≠ 0`, `4c₁(0) = d(0)`, `4c₂(0) = 17d(0)`, `4Λnum(0) = −5d(0)`, i.e. the leading
coefficients `λ = (·, 1/4, 17/4, 5, 1)`, and the indicial polynomial `¼(N−3)²(2N−5)²`, whose integer
root is only `3`), the general-alpha versions `ordAtT_div_pow_sub_ge` / `residual_at_alpha`, and
`local_bound_at_four` (the bound `N_4 ≥ 2`: the data are `dt(4) ≠ 0`, `4c₂(4) = 3dt(4)`,
`16Λnum(4) = 3dt(4)` with `c₄ = (X−4)²dt`, i.e. `λ = (·,·,3/4,3,1)`, and the indicial polynomial
`¼(2−N)(3−N)(5−2N)(3−2N)`, whose integer roots are `2,3`).  Together with the `β`/`γ` bounds of
SESSION 42 (I) this is **four of the five local bounds** of the C-side analysis; only `α = ∞`
remains (it needs an "order at infinity"/degree version of the indicial machinery and the degrees
`12, 16, 17, 18, 19` of `c₀…c₄` from `Submission.CDT.LLOperator`).

**SESSION 42 (III) — the valuation at `∞` and the precise plan for the fifth bound.**  The commons
gained the degree valuation of `K(X)` and its `min`-valuation form:
`Commons.FieldTheory.RatFunc.ordInfT` (`natDegree num − natDegree denom`, a *max*-valuation) with
`ordInfT_mul`, `ordInfT_add_ge`, `ordInfT_algebraMap`, `ordInfT_div`, `ordInfT_neg`, `ordInfT_inv`,
`ordInfT_pow`, `ordInfT_eq_top_iff`, `ordInfT_leading_term`, and
**`Commons.FieldTheory.RatFunc.ordDegT`** (`natDegree denom − natDegree num` `= −ordInfT`, a genuine
*min*-valuation with `ordDegT X⁻¹ = 1` and the one structural difference from the finite case:
`ordDegT (D x) = ordDegT x + 1`, i.e. the derivative *raises* the order at `∞`).  In flight at
hand-off: `ordDegT_leading_term` (the leading coefficient at `∞`) and
`ordDegT_adjoint_eq_of_indicial` — the indicial exactness at `∞` (mirror of
`ordAtT_adjoint_eq_of_indicial_le` with `linFactor α ↦ X⁻¹` and `eᵢ − i ↦ eᵢ + i`).  With those, the
fifth bound is: `eᵢ = deg c₄ − deg cᵢ = (7,3,2,1,0)`, `eᵢ + i = (7,4,4,4,4)`, `m = 4`,
`I = {1,2,3,4}`, `w(Σ) = N + 4` and `w(Σ) = w(R) ≥ −1` (an *upper* bound `d(R) ≤ 1` on the degree of
the inhomogeneity, unlike the finite points which need lower bounds), giving `N_∞ = d(b) ≤ 5`.
**Caveat recorded in `Scratch/lemma14/cside/README.md` §SESSION 42 (III): the `∞`-row of the §11
indicial table is not consistent with either convention's formula and must be re-derived by
re-running `indicial*.py` in the `w = −ordInfT` convention; the degrees `(12,16,17,18,19)` and the
combination `eᵢ + i` are the reliable part.**

**SESSION 42 (IV) — the fifth bound, `N_∞ ≤ 5`, and ALL FIVE LOCAL BOUNDS ARE NOW PROVED.**
`Submission.CDT.CsideInfty` (in the import chain, zero `sorry`) contains `ordDegT_neg` and
**`local_bound_at_infty`**: with the local data at `∞` — `ordDegT (g i) ≥ eᵢ` for
`e = ![7,3,2,1,0]`, `ordDegT (g i − λᵢ X^{−eᵢ}) ≥ eᵢ+1` for `λ = ![·,12,24,10,1]`, and
`ordDegT R ≥ −1` (i.e. `deg R ≤ 1`) — a solution `b` of `Σᵢ(−1)ⁱ Dⁱ(gᵢ b) = −R` satisfies
`ordDegT b ≥ −5`, i.e. **`ordInfT b ≤ 5`** (the paper's `N_∞ ≤ 5`).  The indicial value at `∞` is
`Σ_{i∈I}(−1)ⁱλᵢ∏_{j<i}(−(N+eᵢ+j)) = (N+3)(N+4)²(N+5)`, with `I = {1,2,3,4}` and integer roots
`−3,−4,−5` (machine-checked against `Scratch/lemma14/cside/indicial3.py`); this *corrects* the
`∞`-row of the §11 table, which used the finite-case sign of `eᵢ`.  The commons chapter built for
it: `ordInfT` (the degree valuation) with `ordInfT_mul/div/add_ge/add_le_max/algebraMap/neg/inv/pow/
eq_top_iff/leading_term/eq_coe_intDegree`, `intDegree_pow`, and `ordDegT` (`= −ordInfT`, the
min-valuation with `ordDegT (D x) = ordDegT x + 1`, uniformizer `X⁻¹`) with
`ordDegT_eq_neg_ordInfT/div/algebraMap/leading_term` and **`ordDegT_adjoint_eq_of_indicial`**
(the indicial exactness at `∞`).  **The five local bounds of the C-side local analysis
(`local_bound_at_root_of_R4`, `_root_of_R10`, `local_bound_at_zero`, `local_bound_at_four`,
`local_bound_at_infty`) are therefore all proved**, each taking its local coefficient data as an
explicit hypothesis; only feeding in the concrete numbers from `Submission.CDT.LLOperator.lean`
(and the `10 × 10` determinant and the Bost–Charles input downstream) remain.
-/

/-! ### SESSION 43 — THE CONCRETE C-SIDE DATA: THE FIVE LOCAL BOUNDS FOR THE ACTUAL OPERATOR `LL`

The five local/indicial bounds of SESSION 42 are stated with their local coefficient data as
explicit hypotheses.  SESSION 43 computes that data from the paper's operator and instantiates
the bounds, in three out-of-chain modules (the 1630-monomial tables of
`Submission.CDT.LLOperator` cost several minutes to elaborate, so these modules are **not**
imported here; check them with `lake build Submission.CDT.CsideData` etc.).

* **`Submission.CDT.CsideData`** (out of chain, zero `sorry`).  The evaluations at the two
  ramification points.  With `y0 = MvPolynomial.aeval ![X 0, X 1, 0]` and
  `y4 = MvPolynomial.aeval ![X 0, X 1, 4]` (the paper's `y = 0` and `y = 4`):
  `y0_ms`, `y4_ms` (the table evaluation lemmas), `y0_c1 : y0 c₁ = 16a²b²`,
  `y0_r16b : y0 (c₂/y) = 272a²b²` (with `X2_mul_r16b : y·(c₂/y) = c₂`), `y0_LambdaNum = −80a²b²`,
  `y4_c2 : y4 c₂ = 48·y4(R₄R₁₀)`, `y4_LambdaNum = 12·y4(R₄R₁₀)`, plus the bridges
  `eval_zero_spec`/`eval_four_spec` (`(spec a b p).eval 0 = aeval ![a,b,0] p`, and at `4`) and
  `aeval_y0_apply`/`aeval_y4_apply`.  The assembled consequences are
  **`local_bound_at_zero_concrete`** (`N₀ ≥ 0`, requiring only `a, b ≠ 0`) and
  **`local_bound_at_four_concrete`** (`N₄ ≥ 2`, requiring three explicit non-vanishing conditions
  on `a, b`), with the paper's `γᵢ = cᵢ/c₄` given by the vectors `gammaZero`, `gammaFour`.

* **`Submission.CDT.CsideTables`** (out of chain).  The tables of `LLOperator`/`LLData` re-encoded
  with **integer** coefficients (`c0ZL`, `c1ZL`, `c2ZL`, `R4ZL`, `R10ZL`) plus `msZ`.  This is the
  technical key to the `∞` bound: `DecidableEq (MvPolynomial σ R)` is *noncomputable*, so `decide`
  cannot check a table with coefficients in `ℚ[a,b]`; with integer coefficients the tables are
  `decide`-checkable and the identifications `cᵢ = msZ (ℤ-table)` are proved by `ring` after
  unfolding.

* **`Submission.CDT.CsideInftyData`** (out of chain, zero `sorry`).  The local data at `∞`:
  `natDegree_spec_msZ_le` (a `y`-degree bound from a `List.all` check on the table),
  `coeff_spec_msZ` (the `n`-th coefficient as a sum over the `y^n` layer), the degree and leading
  coefficient computations `c0_deg`, `c1_deg`, `c2_deg`, `R4_deg`, `R10_deg`, `c1_top`, `c2_top`,
  `R4_top`, `R10_top`, `LambdaNum_deg`, `LambdaNum_top` (giving `lc(R₄R₁₀)(4)`-style data and the
  degrees `12,16,17,18,19` of `c₀..c₄` with `lc(cᵢ)/lc(c₄) = (·,12,24,10,1)`), the residual bounds
  `c1_residual`, `c2_residual`, `c3_residual`, `c4_residual` (via
  `natDegree_sub_le_pred_of_coeff_eq`), and the capstone
  **`local_bound_at_infty_concrete`** (`N_∞ ≤ 5`, requiring `a ≠ b`), through the `ordDegT`
  helpers `le_ordDegT_div_algebraMap` and `ordDegT_div_sub_C_mul_zpow_le` and the vector
  `gammaInf = ![c₀/c₄, c₁/c₄, c₂/c₄, c₃/c₄, 1]`.

Two general lemmas found here were published to the commons:
`Commons.Data.List.sum_map_ite_eq_zero`, `Commons.Data.List.sum_map_eq_sum_map_filter`,
`Commons.Algebra.Polynomial.coeff_mul_X_pow_of_le`,
`Commons.Algebra.Polynomial.natDegree_sub_le_pred_of_coeff_eq`.
-/

/-! ### SESSION 44 — the C-side divisor bound (the paper's `(b3eqlog)`)

`Submission.CDT.CsideDivisor` (in the import chain, zero `sorry`) supplies the two ingredients that
turn the five local bounds of SESSION 42/43 into the paper's factorisation
`b₃ = ((y−4)²R₄/R₁₀)·Q`, `deg Q ≤ 9` (CDT arXiv:2408.15403, Lemma `17functions`, equation
`(b3eqlog)`), the C-side analogue of `Submission.CDT.DivisorBound.divisor_bound`:

* **`regular_bound`** — the bound at a *non-singular* point: if the coefficients `γᵢ` of the
  eliminated expression `Σᵢ (−1)ⁱ Dⁱ(γᵢ b)` are regular at `α` (`0 ≤ ordAtT α (γ i)`), `γ₄ = 1` and
  `Σᵢ (−1)ⁱ Dⁱ(γᵢ b) = −R` with `R` regular at `α`, then `0 ≤ ord_α b`.  This is what makes `R₁₀·b`
  a polynomial: the poles of a solution are supported on the singular points of the operator.
  It is a short corollary of the commons lemma
  `Commons.FieldTheory.RatFunc.ordAtT_adjoint_eq_of_regular` (the exact order `N − 4` at a regular
  point, indicial value `(N)₄ ≠ 0` for `N < 0`), which was published to the commons this session.
* `zero_le_ordAtT_div_of_eval_ne_zero` — a quotient `p/q` with `q` not vanishing at `α` is regular
  at `α`; this is how `γᵢ = cᵢ/cden` is checked at the points where `cden ≠ 0`.
* **`cside_divisor_bound`** — the assembly: given
  (i) `0 ≤ ord₀ b`, `2 ≤ ord₄ b`,
  (ii) `1 ≤ ord_β b` at every root `β` of `R₄` and `−1 ≤ ord_γ b` at every root `γ` of `R₁₀`,
  (iii) the generic bound `0 ≤ ord_α b` where `R₄` and `R₁₀` do not vanish,
  (iv) `ordInfT b ≤ 5` (`N_∞ ≤ 5`),
  (v) `R₄` squarefree, `R₄(4) ≠ 0`, `R₁₀(4) ≠ 0`, `R₄` and `R₁₀` with no common root, and the
  degrees `deg R₄ = 4`, `deg R₁₀ = 10`,
  there is `Q` with `Q.natDegree ≤ 9` and `(R₁₀ : K(X)) · b = ((y−4)²R₄ : K(X)) · Q`.
  The degree bound comes from `ordInfT b ≤ 5` via `RatFunc.intDegree`: `intDegree Q = 4 + intDegree b`.
* **`cside_divisor_bound_div`** — the same statement in the paper's own form
  `b = ((y−4)²R₄/R₁₀)·Q` with `deg Q ≤ 9`.
* **`cside_divisor_bound_of_isCoprime`** — the same bound with the hypotheses `hR4sq` and `hcop`
  replaced by the standard Bézout certificates `IsCoprime R₄ R₄'` (squarefreeness, via
  `Commons.Algebra.Polynomial.rootMultiplicity_le_one_of_isCoprime_derivative`) and
  `IsCoprime R₄ R₁₀` (no common root) — the paper's Lemma `(res)`.
* **`regular_bound_spec`** — the `spec`-form of `regular_bound` for the paper's own coefficients
  (`γᵢ = cᵢ/c₄` with `cden = (y−4)yR₄R₁₀`), i.e. the C-side companion of
  `Submission.CDT.CsideLocal.local_bound_at_root_of_R4_spec`; it produces the `hgen` hypothesis of
  `cside_divisor_bound` directly.
* **`adjoint_cleared`** — clearing denominators in the eliminated equation: if `b = p/q` and
  `Σᵢ (−1)ⁱ Dⁱ((cᵢ/c₄)·b) = S`, then
  `Σᵢ (−1)ⁱ · dnum (cᵢp) (c₄q) i · (c₄q)^{4−i} = (c₄q)^5 · S`,
  the bridge from the rational/analytic system `(onceagain)` to the polynomial linear algebra of the
  `10 × 10` determinant (the C-side analogue of `Submission.CDT.InfinityBound.POLYq_mul_X2`).

The commons lemmas it rests on / which it makes available for the rest of the project:
`Commons.FieldTheory.RatFunc.ordAtT_adjoint_eq_of_regular` (indicial exactness at a regular point),
`Commons.FieldTheory.RatFunc.zero_le_ordAtT_div_of_eval_ne_zero`,
`Commons.FieldTheory.RatFunc.exists_dvd_of_ordAt_bounds` (the general divisor bound, of which both
`Submission.CDT.DivisorBound.divisor_bound` and `cside_divisor_bound` are instances), and
`Commons.Algebra.Polynomial.dnum_add` / `dnum_C_mul` (linearity of the cascade numerator in its
first argument, i.e. the `K`-linearity of `Q ↦ Σᵢ Aᵢ·dnum (P₀Q) q i·q^{n−i}`).

*Where the C-side now stands.*  With the divisor bound the paper's step (1) is formalised.  The
remaining formalizable content of Lemma `17functions` is steps (2)–(3): substituting
`b₃ = (y−4)²R₄Q/R₁₀` into the last equation of `(onceagain)` gives
`Σ_{i=−4}^{1} aᵢy^i = S₄₂(y)/(y⁴R₁₀(y)⁴)` with `deg S₄₂ = 42`; for degree reasons
`a₁ = a₀ = a₋₁ = 0`; and then `R₁₀ | Ψ(Q)` for the cleared polynomial operator
`Ψ(Q) = Σᵢ(−1)ⁱ dnum(cᵢP₀Q)(c₄R₁₀) i (c₄R₁₀)^{4−i}` (a `10 × 10` linear system in
`q₀,…,q₉`), whose determinant is the explicit symmetric polynomial of the paper — non-vanishing for
the relevant `(a,b)` by Lemmas `(res)`/`(det)`.  The determinant/rank step is size-blocked
(see `Scratch/lemma14/cside/README.md`).
-/

/-! ### SESSION 45 — CONCENTRATION OF MEASURE FOR THE BOX DISCREPANCY
(`Submission.CDT.Discrepancy`, zero `sorry`)

The paper's §"Concentration of measure" proves, via the Erdős--Turán trigonometric inequality and
Hoeffding's bound, that the box discrepancy `D` of `n` independent uniform points of `[0,1)` has
sub-exponential tails: `vol{D ≥ ε} ≤ C e^{−c ε⁴ n}`.  This module formalises the *conclusion*
without the harmonic-analysis input, by a direct **grid argument**, and obtains the strictly
stronger exponent `ε²`:

* `nu` = Lebesgue measure on `[0,1)`, `muP n` = its `n`-fold product (the uniform probability
  measure on `[0,1)^n`), with `nu_Ico`, `nu_real_Ico`, `muP` a probability measure;
* `cnt t a b` = `#{i : t i ∈ [a,b)}` and `disc t` = the **box discrepancy**, the supremum over
  `0 ≤ a ≤ b ≤ 1` of `|(b−a) − cnt t a b/n|`;  `disc_le_one`;
* `dev t m k l` = the deviation of the empirical count on the grid interval `[k/m, l/m)`;
* `measure_dev_le` — **Hoeffding for a single grid interval**: the deviation of the count on
  `[k/m, l/m)` is sub-Gaussian, `≤ 2 exp(−n δ²/2)` (via the commons lemmas
  `Commons.Probability.RandomMatrix.abs_sum_tail`, `entry_subG`, i.e. the sub-Gaussian
  Chernoff bound for independent bounded random variables, and
  `MeasureTheory.integral_comp_eval` for the mean);
* `exists_grid_dev_of_disc_le` — **the grid approximation**: if `4 < m·ε` then any configuration
  with `disc t ≥ ε` has a grid interval `[k/m, l/m)` (`k,l ≤ m`) with deviation `≥ ε/2`
  (the interval achieving the discrepancy is squeezed between a grid interval containing it and
  one contained in it, according to the sign of the deviation);
* `measureReal_biUnion_finset_le` — the union bound for `μ.real`;
* **`disc_concentration`** — **the concentration estimate**
  `(muP n).real {t | ε ≤ disc t} ≤ min 1 (100·ε⁻²·exp(−n·ε²/8))`  for `n ≥ 1`, `ε > 0`.
  With the elementary `ε⁻² exp(−nε²/8) ≤ 100 e^{−nε⁴/100}` this yields the paper's shape
  `vol{D ≥ ε} ≤ C e^{−c ε⁴ n}`.  (For `ε > 1` the event is empty because `disc ≤ 1`.)

This is the *only* place in the paper where measure concentration enters; the module is
self-contained (Mathlib plus two commons probability lemmas) and belongs to the shared library
rather than to either of the two remaining leaves.

**`Submission.CDT.DiscrepancyFour`** (zero `sorry`) converts the sharp estimate into the paper's own
shape, with the exponent `ε⁴`: `log_100_ge_four` (`4 ≤ log 100`), `sq_mul_log_inv_le_one`
(`ε² log(1/ε) ≤ 1` for `ε > 0`), `log_100_mul_inv_sq`, and the theorem
**`disc_concentration_four`** : `(muP n).real {t | ε ≤ disc t} ≤ 100·exp(−n·ε⁴/100)`
(`n ≥ 1`, `ε > 0`).  The two cases of the split are `A := 100·ε⁻²·exp(−nε²/8) ≤ 1` (then the whole
`ε⁻²` factor is absorbed by the finer bound `(1 − 8ε²/100)log100 ≥ 2·(8ε²/100)log(1/ε)`) and
`1 ≤ A` (then `nε⁴ ≤ 12 log 100`, whence `exp(nε⁴/100) ≤ 100`).
-/

/-! ### SESSION 45 (II) — THE DENOMINATOR TYPES OF THE PURE FUNCTIONS `B_2, B_3, B_5, B_6`
(`Submission.CDT.PureDenom`, zero `sorry`)

Lemma `bdenominators` of the paper's §"Pure functions" gives the denominators of the seven power
series `B_i(y) ∈ ℚ⟦y⟧` (`[1..2n]` below denotes `Nat.lcmUpto (2n)`):

`B_2 = Σ 2y^n (n-2)!n!/(2n)!` (type `[1..2n]`), `B_3 = Σ y^n (n-1)!²/(2n)!` (type `[1..2n]·n`),
`B_4 = Sym⁻Li_2` (type `[1..2n]²`), `B_5 = Σ y^n (n-1)!²/((2n-1)!(2n-1))` (type `[1..2n](2n-1)`),
`B_6 = Σ y^n (n-1)!²/(n(2n)!)` (type `[1..2n]n²`), `B_7 = ∫B_4/y` (type `[1..2n]²n`).

The module formalises the four cases `i = 2,3,5,6` — the ones the paper proves "by direct
computation" from the explicit factorial formula — as the integrality statements
`∃ z : ℤ, lcmUpto (2n) · (type factor) · (coefficient) = z`:
`int_lcmUpto_mul_b2`, `int_lcmUpto_mul_n_mul_b3`, `int_lcmUpto_mul_two_n_sub_one_mul_b5`,
`int_lcmUpto_mul_n_sq_mul_b6`, together with the explicit coefficient functions `b2, b3, b5, b6`
and the elementary factorial algebra (`factorial_two_mul` : `(2n)! = (n!)²C(2n,n)`,
`factorial_succ_cast`, `factorial_two_mul_eq`, `b2_eq`, `n_mul_b3_eq`, `n_sq_mul_b6_eq`,
`two_n_sub_one_mul_b5_eq`).

The three arithmetic inputs are commons lemmas: `dvd_lcmUpto_mul_choose_two_mul_self`
(`n·C(2n,n) ∣ lcmUpto (2n)`), `dvd_lcmUpto_mul_choose_two_mul_sub_one`
(`n·C(2n-1,n-1) ∣ lcmUpto (2n)`) and `dvd_lcmUpto_fact_two_mul_sub_one_mul_fact_div`
(`lcmUpto (2n)·(n-2)!(n-1)!/(2n-1)! ∈ ℤ`), all in
`Commons.NumberTheory.Chebyshev`.  The cases `i = 4, 7` are derived in the paper from the
weight-zero modularity input (`etalecover`, Eichler integrals) and are NOT formalised here.

*The window-lcm asymptotic* (the paper's Lemma `lcm lemma`, part (1)) is **PROVED and published**
as `Commons.NumberTheory.Chebyshev.log_lcm_window_div_id_tendsto` (with the supporting commons
lemmas `tendsto_log_lcmUpto_div_id`, `log_lcm_window_erase_zero_sub_theta_sub_bad_le`,
`sum_log_primes_bad_eq`, `tendsto_theta_div_self`, `window_sum_telescope`,
`gamma_window_identity`, `eventually_natFloor_eq_of_tendsto_of_lt`, …).
NOTE: for `k = n` the window `[0,n]` contains `0`, so `Finset.lcm` collapses to `0`; the correct
formalisation takes the lcm of `(Finset.Icc (n-k) n).erase 0` (or assumes `k < n`).
The paper's Lemma `lcm-2` (the version with the prime cutoff `p > l`) is NOT yet formalised.
-/

/-! ### SESSION 45 (III) — HADAMARD'S DETERMINANT INEQUALITY, FEKETE'S TORUS BOUND, AND THE
VANISHING FILTRATION (shared commons)

Three further commons results, all classical and all missing from Mathlib, feeding the paper's
§"Equidistribution" (Lemma `Fekete`: `sup_{𝕋^d}|∏_{i<j}(z_i-z_j)| = d^{d/2}`) and §"Filtered
evaluation modules" (the vanishing filtration of the evaluation module):

* `Commons.LinearAlgebra.Matrix.det_norm_sq_le_prod_sum_norm_sq` — **Hadamard's determinant
  inequality**: `‖det A‖² ≤ ∏ i, ∑ j, ‖A i j‖²` for `A : Matrix n n ℂ`.  (Mathlib only had the
  weak bound `|det A| ≤ n!·x^n`.)  Mathlib's `Matrix.det_vandermonde` +
  `Matrix.posSemidef_conjTranspose_mul_self` give the route.
* `Commons.LinearAlgebra.Matrix.abs_vandermonde_prod_le` — **Fekete's bound**: for `‖z i‖ = 1`,
  `‖∏ i, ∏ j > i, (z j - z i)‖ ≤ √(d^d)` (the paper's Lemma `Fekete`, the `sup` being attained by
  the regular `d`-gon; the equality case is not needed here).
* `Commons.RingTheory.PowerSeries.ncard_vanishingOrders_eq_finrank` — the **vanishing filtration**:
  for a finite-dimensional `ℚ`-subspace `V ⊆ ℚ⟦X⟧`, the set of orders of the nonzero elements of
  `V` has cardinality `finrank ℚ V`; equivalently, the successive quotients of the filtration
  `W n = V ⊓ {X^n ∣ ·}` have `ℚ`-dimension `≤ 1` and their dimensions sum to `dim V`.  This is the
  paper's `r_D^{(n)} ∈ {0,1}`, `Σ_n r_D^{(n)} = dim E_D` of §"Filtered evaluation modules".

CAUTION: the commons lemma `Commons.NumberTheory.Chebyshev.dvd_lcmUpto_fact_two_mul_sub_one_div`
(requested early in the session) has a **vacuous** statement — it asserts
`lcmUpto (2n)·(2n-1)!/((n-2)!(n-1)!) ∈ ℤ`, but the second factor is an integer.  The correct
statement is the reciprocal one, `dvd_lcmUpto_fact_two_mul_sub_one_mul_fact_div`.  Do not use the
former for anything.

*NOT formalised* from the same sections: the Bilu-type damping bound
(`D(z) ≥ ε ⟹ |V(z)| < e^{−c(ε)d²}`, which rests on Bilu's equidistribution theorem / the
Bombieri--Gubler height argument) and the Erdős--Turán trigonometric discrepancy inequality
(the harmonic-analysis input of §"Concentration of measure"; the concentration estimate itself is
proved in `Submission.CDT.Discrepancy` *without* it).
-/



/-! ### SESSION 46 (I) — THE LOCATION OF THE SINGULARITIES OF `LL`
(`Submission.CDT.LocationSing`, zero `sorry`, in the import chain)

The paper's §"Location of the singularities" (Definition `yplus` and the paragraph after it): for
`ε < 10⁻⁶`, `m, n ≥ 1` with `m ≠ n` and `|m/n - 1| < ε`, the four singularities of the order-four
operator `LL` away from `0, 4, ∞` — the `y := x + x/(x-1) = x²/(x-1)` images of
`x = (a ± √(a²-1))(b ± √(b²-1))`, `a = 2m+1`, `b = 2n+1` — are all either inside the disc
`D(0, ε⁴/16)` or outside the disc `D(0, 1/(2ε))`.

`Submission.CDT.LocationSing` proves exactly this.  The key identities are
`sqP t = (√(t+1)+√t)² = a + √(a²-1)` and `sqM t = (√(t+1)-√t)² = (sqP t)⁻¹ = a - √(a²-1)` for
`a = 2t+1` (`t ≥ 0`); writing `P = max m n`, `Q = min m n`, `A = sqP P`, `B = sqM P`,
`C = sqP Q`, `D = sqM Q`, the four `x`-values are `A·C`, `A·D`, `B·C`, `B·D`, and with
`d = P - Q`, `d < P·ε` (which follows from `|m/n - 1| < ε` in *both* cases `m > n` and `n > m`):

* `sqP_mul_sqM`, `sqP_eq` (`sqP t = 2t+1+2√(t(t+1))`), `four_mul_add_one_le_sqP` (`4t+1 ≤ sqP t`),
  `sqP_le` (`sqP t ≤ 4t+2`), `sqP_lt_sqP` (strict monotonicity);
* **`sqP_sub_sqP_le`**: `sqP P - sqP Q ≤ 2(P-Q)(2 + 1/(2Q+1))`;
* the four local bounds, as abstract real lemmas — `ymap_large_large` (`|y(A·C)| ≥ A·C > 1/ε`),
  `ymap_large_small` (`|y(A/C)| = A²/(C(A-C)) > 1/ε` when `C(A-C) < εA²`),
  `ymap_small_small` (`|y(B·D)| ≤ 2(BD)² < ε⁴/16` when `BD < ε²/8`), and `ymap_small_large`
  (`|y(1/x)| = |y(x)|/x³ > 1/(2ε)` when `1 < x ≤ 1+3ε`);
* **`location_core`** (`P > Q ≥ 1`, `P - Q < P·ε`): `1/ε < |y(A·C)|`, `1/ε < |y(A·D)|`,
  `1/(2ε) < |y(B·C)|`, `|y(B·D)| ≤ ε⁴/16`;
* **`location_singularities`**: for all sign choices `s, t ∈ {±1}`,
  `|ymap (Xval m n s t)| ≤ ε⁴/16 ∨ 1/(2ε) < |ymap (Xval m n s t)|`.

The paper states the conclusion with `1/ε` in place of `1/(2ε)`.  **That stronger claim is false as
stated**: `|y(B·C)| = |y(η)|/η³` with `η = A/C ≈ 1 + d/n`, and `|y(η)| ≈ n/d ≈ 1/ε`; for
`ε = 10⁻⁶`, `n = 10¹⁴`, `m = n + 10⁸ - 1` one computes `|y(B·C)| ≈ 999999 < 1/ε`.  The correct
uniform statement is `1/(2ε)` (three of the four points are in fact `> 1/ε`, and the third displayed
estimate of the paper, `|y(ξ⁻¹)| > 16/ε²`, is recovered).  This is all that the contour argument
(Corollary `stacky overconvergence`) needs.
-/



/-! ### SESSION 46 (II) — THE PRIME-CUTOFF WINDOW PRODUCT AND THE ANALYTIC STEP OF LEMMA `lcm-2`
(`Submission.CDT.LcmGe`, zero `sorry`, in the import chain)

The paper's §"The cost of an integration", Lemma `lcm-2`: for `0 < γ₀ ≤ k/n, l/n ≤ 1`,
`log L^{≥ l}_{n,k}` — the logarithm of the product of the primes `p > l` having a multiple in the
window `[n-k, n]` — is asymptotic, *uniformly in `k, l`*, to
`k·(Σ_{h ≤ (n-k)/max(k,l)} 1/h) + (n/⌊(n + (l-k)⁺)/max(k,l)⌋ − l)⁺ + o(n)`.

`Submission.CDT.LcmGe` defines `Lge l n k` and proves:

* **`theta_nat_eq_sum_range`**, **`theta_sub_theta_eq`**: `θ(n) − θ(l)` is the sum of `log p` over
  the primes `l < p ≤ n`;
* **`log_Lge`**: the exact decomposition
  `log L^{≥l}_{n,k} = θ(n) − θ(l) − Σ_{a ≤ h} (θ((n-k-1)/a) − θ(max(n/(a+1), l)))`,
  `h = (n-k-1)/max(k,l)`, obtained by combining `theta_sub_theta_eq` with the commons lemma
  **`Commons.NumberTheory.Chebyshev.sum_log_primes_bad_eq_ge`** (requested and proved by the fleet:
  the cutoff version of the "bad primes lie in the gaps" identity `sum_log_primes_bad_eq`);
* **`bad_sum_model_error`** — **the analytic (PNT) step, uniform in `k, l`**: for every `ε > 0`,
  for all large `n` and all `k, l` with `γn ≤ k ≤ n`, `γn ≤ l ≤ n`, replacing every `θ(y)` by `y` in
  the last sum costs at most `εn`.  The mechanism: `h ≤ 1/γ` (so there are `O(1/γ)` terms) and each
  argument of `θ` is `≥ γn`, so `θ(y) − y = o(y)` (`theta_sub_id_isLittleO`) applies uniformly;
* **`lcm_ge_model`**: the model form of Lemma `lcm-2` (part 1),
  `|log L^{≥l}_{n,k} − (n − l − Σ_{a ≤ h}((n-k-1)/a − max(n/(a+1), l)))| ≤ εn` eventually and
  uniformly in `k,l` (for `0 < γ ≤ 1`).

* **`lcm_ge_harmonic`** — the *closed form* of the model (the telescoping identity
  `sum_Icc_one_div_add_one`: `Σ_{a≤h} 1/(a+1) = Σ_{a≤h}1/a - 1 + 1/(h+1)`, and the pointwise
  `max_eq_self_add_max_sub`): with `h = (n-k-1)/max(k,l)`, `H = Σ_{a≤h}1/a` and
  `C = Σ_{a≤h} max(l - n/(a+1), 0)`,
  `log L^{≥l}_{n,k} = (k+1)·H + n/(h+1) - l + C + o(n)`,
  uniformly in `k, l` with `γn ≤ k,l ≤ n` (`0 < γ ≤ 1`).  The paper's displayed value
  `k·Σ_{h ≤ (n-k)/max(k,l)} 1/h + (n/⌊(n+(l-k)⁺)/max(k,l)⌋ - l)⁺` agrees with it up to `O(log n)`
  (`C` has at most two nonzero terms), hence also `o(n)`; numerically verified for `n` up to `10⁵`
  and many `(k,l)` (both agree with the exact value to `o(n)`).
-/



/-! ### SESSION 46 (III) — THE TWO ELEMENTARY LEMMAS OF THE INTRODUCTION
(`Submission.CDT.BorelSimple`, zero `sorry`, in the import chain)

* **`irrational_of_mul_abs_sub_tendsto_zero`** — Lemma `simple` of the paper's §"Comparisons to the
  work of Apéry" (with the sharper hypothesis the authors note): if `β ∈ ℝ` has rational
  approximations `p n / q n ≠ β` (`q n > 0`) with `q n · |β - p n / q n| → 0`, then `β` is
  irrational.  Proof: if `β = r` were rational, `|r - p/q| = |r.num · q - p · r.den| / (r.den · q)`
  with an integer numerator that is nonzero, hence `≥ 1/(r.den · q)`, contradicting `→ 0`.

* **`int_coeff_eventually_zero_of_summable`** — Lemma `simpletwo` of the same section: an integer
  power series (`f : ℕ → ℤ`) converging at a point `z` with `‖z‖ > 1` is a polynomial.  (Sharper than
  the paper's "holomorphic on a disc of radius `> 1`": convergence at one such point suffices,
  because then `‖f n‖·‖z‖^n → 0`, so `‖f n‖ < 1`, and `f n ∈ ℤ` forces `f n = 0`.)
-/

/-! ### SESSION 47 — THE UNIFORM WINDOW-`lcm` ASYMPTOTIC (LEMMA `lcm lemma` (1), UNIFORM FORM)

(`Submission.CDT.LcmUniform`, zero `sorry`, in the import chain)

The paper's Lemma `lcm lemma` (1) is *uniform* in `γ`: for `γ₀ ∈ (0,1]` and every `ε > 0` there is
`N` such that for all `n ≥ N` and all `γ ∈ [γ₀, 1]`, with `k = ⌊γn⌋` and `L_{n,k} = lcm(n-k,…,n)`,

`|log L_{n,k}/n − (γ·Σ_{h ≤ ⌊1/γ⌋−1} 1/h + 1/⌊1/γ⌋)| ≤ ε`.

* **`Submission.CDT.LcmUniform.log_lcm_window_uniform`** — the statement above (the headline; the
  previous non-uniform version is the commons lemma
  `Commons.NumberTheory.Chebyshev.log_lcm_window_div_id_tendsto`).
* **`log_lcm_window_uniform_half`** — the range `γ ∈ [γ₀, 1/2]`, where the analysis is genuinely
  uniform:  the bad-prime decomposition
  `Commons.NumberTheory.Chebyshev.sum_log_primes_bad_eq` writes the correction as a sum of exactly
  `M = (n-1)/(k+1) − 1` gap terms, and `window_index_dichotomy` shows
  `M ∈ {⌊1/γ⌋−1, ⌊1/γ⌋−2}` as soon as `nγ² ≥ 1`; `window_F_bound` then compares the model
  `((k+1)/n)H_M + 1/(M+1)` with `γH_{⌊1/γ⌋−1} + 1/⌊1/γ⌋` with error `O(1/n)` (uniformly in `γ`),
  and the individual `θ`-values are all `≥ γ₀ n / C`, so the pointwise prime number theorem
  `Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_isLittleO` gives a uniform error `O(εn)`.
* **`log_lcm_window_uniform_ge_half`** — the range `γ ∈ [1/2, 1]` is elementary: `M = 0` (no bad
  primes), the value is `1` (`V_eq_one_of_half_le`), and only `θ(n) = n + o(n)` is needed.
* supporting lemmas: `sum_window_div_telescope` (the harmonic telescoping identity),
  `abs_sum_theta_sub_le` (a deviation lemma for sums of `θ`-errors), `hsum_le`,
  `sum_div_le_mul_sum_inv`, `sum_div_add_one_le`, `theta_rel_error`, `window_index_dichotomy`,
  `real_index_bound`, `V_eq_one_of_half_le`.

The general pieces are being republished to the shared commons (see the requests
`Analysis/Sum/sum_window_div_telescope`, `NumberTheory/Chebyshev/theta_rel_error`,
`NumberTheory/Chebyshev/real_index_bound`, `NumberTheory/Chebyshev/window_index_dichotomy`,
`NumberTheory/Chebyshev/V_eq_one_of_half_le`, `NumberTheory/Chebyshev/sum_Icc_inv_le_nat`).
-/

/-! ### SESSION 47 (II) — THE UNIFORM FORM OF LEMMA `lcm-2` AND LEMMA `lcm lemma` (2)

(`Submission.CDT.LcmGeUniform` and `Submission.CDT.LcmLe`, zero `sorry`, both in the import chain)

* **`Submission.CDT.LcmGeUniform`** makes session 46's Lemma `lcm-2` (part 1) uniform in the scale:
  * `bad_sum_model_error_uniform` — the prime-number-theorem error in the gap decomposition is
    `< εn` for all `k, l ≥ γ₀ n` (the number of gaps is `≤ 1/γ₀` and every argument of `θ` is
    `≥ γ₀ n`, so the pointwise relative PNT suffices);
  * `lcm_ge_model_uniform` — `log L^{≥l}_{n,k} = n − l − Σ_{a ≤ h}((n-k-1)/a − max(n/(a+1), l)) +
    O(εn)` uniformly in `k, l ∈ [γ₀n, n]`;
  * `lcm_ge_harmonic_uniform` — the closed form `(k+1)H + n/(h+1) − l + C + O(εn)`,
    `h = (n-k-1)/max(k,l)`.
* **`Submission.CDT.LcmLe`** — Lemma `lcm lemma` (2): for every `ε > 0`, eventually for all
  `0 ≤ k ≤ n`,
  `log L_{n,k}/n ≤ (Σ_{h ≤ n/k−1} 1/h)·(k/n) + 1/⌊n/k⌋ + ε`
  (`log_lcm_window_le_uniform`); the proof splits at a small constant scale `δ = 1/j`
  (`tendsto_harm_div` supplies the required `j`), using the monotonicity of the window `lcm`
  (`Finset.lcm_mono`) below the scale and `Submission.CDT.LcmUniform.log_lcm_window_uniform` above
  it.  The companion `tendsto_log_lcm_window_div` states the paper's qualitative assertion
  `k = o(n) ⟹ log L_{n,k} = o(n)` (equivalently `L_{n,k} = exp(o(n))`) directly, as a limit
  statement for a sequence `k : ℕ → ℕ` with `k n ≤ n` and `k n / n → 0`; its proof is the
  small-`k` half of the proof above with the scale `1/j` chosen once and for all.
-/

/-! ### SESSION 47 (III) — RIEMANN SUMS OF STEP FUNCTIONS

(`Submission.CDT.StepRiemann`, zero `sorry`, in the import chain)

The additional denominators coming from *integrating* the functions `f_i` in the paper's
"cost of an integration" are measured by the Riemann sums `(1/d)Σ_{j=1}^d G(mj/d)` of the model
function `G` of Lemma `lcm-2`, which is piecewise constant.  This module proves the general
convergence statement:

* `stepFun a c N` — the step function with breakpoints `a 0 < … < a N` and values `c 0, …, c (N-1)`;
* `filter_Icc_eq_Icc` — the integers `j ∈ [1,d]` with `α ≤ j < β` form
  `[max 1 ⌈α⌉, min d (⌈β⌉-1)]`;
* `card_filter_Icc_sub_close` — that count is within `2` of `β - α` (`0 ≤ α ≤ β ≤ d`);
* **`tendsto_riemannSum_stepFun`** — `(1/d)Σ_{j≤d} G(mj/d) → (1/m)Σ_i c_i(a(i+1) - a i)`, i.e. the
  Riemann sums converge to `(1/m)∫_0^m G`.

The remaining step of the paper's §"cost of an integration" is to identify the model function of
Lemma `lcm-2` with such a step function (its breakpoints are the finitely many points where
`⌊(t-1)/max(1,w)⌋` or `⌊(t+max(0,w-1))/max(1,w)⌋` change value) and to evaluate the resulting
finite sum against the paper's Definition `integrated lcm`.
-/


/-! ### SESSION 48 (I) — Lemma `lcm-2` (2): the uniform upper bound (`Submission.CDT.Lcm2Bound`, zero `sorry`)

`Submission.CDT.Lcm2Bound` completes the paper's Lemma `lcm-2` — the quantitative input of the
paper's §"The cost of an integration" — by proving the uniform upper bound

* **`log_Lge_le_uniform`** : for every `ε > 0`, eventually for all `n` and all `0 ≤ k, l ≤ n`,
  `log L^{≥ l}_{n,k} ≤ k·H_{h₀} + (n/⌊(n + (l-k)⁺)/max(k,l)⌋ - l)⁺ + εn` with `h₀ = ⌊(n-k)/max(k,l)⌋`
  and `H_m = Σ_{h ≤ m} 1/h` (the paper's display, uniformly in `k, l`).

Supporting material (all in the same module):

* `H`, `H_eq`, `H_succ`, `H_nonneg`, `H_le_log` — the harmonic sums, `H_m ≤ 1 + log m`;
* `add_div_eq` (`n/k = (n-k)/k + 1`), `hden_eq` (`(n + (l-k))/max(k,l) = (n-k)/max(k,l) + 1`),
  `h0_le_succ` (`N/M ≤ (N-1)/M + 1`), `mul_div_eq_of_div_eq`;
* `comparison`, `comparison_eq`, `comparison_succ`, `term_eq_zero`, `add_max_sub`, `add_max_neg` —
  the **floor/harmonic comparison**: the exact model
  `(k+1)H_h + n/(h+1) - l + Σ_{a≤h} max(l - n/(a+1)) 0` of the uniform Lemma `lcm-2` (1) is at most
  the paper's closed form `k·H_{h₀} + (n/(h₀+1) - l)⁺` plus `H_{h₀} = O(log n)`;
* `lcm_ne_zero`, `lcm_window_mono` — positivity and monotonicity of the window lcm;
* `Lge_dvd_lcm`, `one_le_Lge`, `log_Lge_le_log_lcm` — `L^{≥ l}_{n,k}` divides the window lcm, hence
  `log L^{≥ l}_{n,k} ≤ log L_{n,k}`;
* `log_lcm_window_uniform_at` (`|log L_{n,⌊n/J⌋}/n - (H(J-1)/J + 1/J)| ≤ η` eventually),
  `log_lcm_window_le_small` — the short-window case.

The proof is the paper's four-case argument (short `k`; large `l` via `θ(n) - θ(⌊(1-1/(2J))n⌋)`;
short `l` and long `k` via `lcm lemma` (2); the middle range via the uniform `lcm-2` (1) and the
comparison above), with the `J`-dependence of all errors made explicit.
-/

/-! ### SESSION 48 (II) — the paper's Definition `integrated lcm` (`Submission.CDT.IntegratedLcm`, zero `sorry`)

`Submission.CDT.IntegratedLcm` records the paper's §"The cost of an integration" quantitatively:

* `harmonicFun w t = Σ_{h ≤ ⌊(t-1)/max(1,w)⌋} 1/h` and
  `correctionFun w t = (t/⌊(t+max(0,w-1))/max(1,w)⌋ - w)⁺` — the two terms of the right-hand side
  of Lemma `lcm-2` (2) with `k/D = 1` and `l/D = w`;
* `modelFun w t` — the "cost density": `(t-w)⁺` for `t ≤ 1` (the window is everything) and
  `harmonicFun w t + correctionFun w t` for `t ≥ 1`;
* **`integratedLcm u v w`** — the paper's Definition `integrated lcm`
  (`∫_{min(u,1)}^1(t-w)⁺ + ∫_{max(u,1)}^v Σ ... + ∫_{max(u,1)}^v (...)^+`);
* `modelFun_nonneg`, `harmonicFun_nonneg`, `correctionFun_nonneg`, the integrability of the three
  pieces (from `Commons.MeasureTheory.IntervalIntegral.{integrableOn_sum_Icc_floor,
  integrableOn_div_floor}` and `Commons.Analysis.Floor.sum_Icc_floor_eq`);
* **`integratedLcm_zero_left`** : `I_0^v(w) = ∫_0^v modelFun w` for `1 ≤ v` — i.e. the paper's
  definition *is* the integral of the model function of Lemma `lcm-2` (2), and
  **`integratedLcm_zero_left_nonneg`** : `0 ≤ I_0^v(w)`.

Caveat (documented in the module): the analogue `I_u^v(w) = ∫_{min(u,1)}^v modelFun w` holds only
for `u ≤ 1`; for `u ≥ 1` the region `[1,u]` is dropped by the definition — it is exactly the region
where the paper estimates the primes `p ≤ ξD` *trivially* instead of by Lemma `lcm-2`.

The harmonic part of `I` is evaluated in closed form:
**`integral_harmonicFun`** : `∫_{1}^{v} Σ_{h ≤ ⌊(t-1)/B⌋} 1/h dt = Σ_{h ≤ ⌊(v-1)/B⌋} (1/h)·(v - max(1,1+hB))⁺`
(`B = max 1 w`), from `Commons.Analysis.Floor.integral_sum_Icc_floor`.
-/

/-! ### SESSION 48 (III) — the start of the multivariate vanishing filtration (`Submission.CDT.MvVanishing`, zero `sorry`)

The paper's §"Filtered evaluation modules" (Lemma `total jumps`, Corollary `jumps Cartesian`) is
about the *vanishing filtration* of a finite-dimensional `V ⊆ ℚ⟦x₁,…,x_d⟧` w.r.t. the degree-lex
order `≺` on exponents.  `Submission.CDT.MvVanishing` records the definitions and the basic API:

* `tdeg s = |s|`, `dk s = (|s|, s)` (the degree-lex *key*, in `Lex (ℕ × Lex (σ →₀ ℕ))`),
  `udk`, `dk_injective`, `dk_lt_iff`, `dk_le_iff`, `dk_lt_of_tdeg_lt`, `dk_lt_of_tdeg_lt_fst`;
* `degLevel N` — the finite set of exponent vectors of total degree `N` (from the commons lemma
  `Commons.RingTheory.MvPowerSeries.exists_finset_sum_eq`), `mem_degLevel_iff`;
* `minDeg f`, `minDeg_spec`, `minDeg_le`, `mem_degLevel_minDeg`;
* `leadLevel f`, **`leadExp f`** (the `≺`-minimal exponent of the support), `leadExp_mem`,
  `coeff_leadExp_ne_zero`, `tdeg_leadExp`, `leadExp_le`, `dk_udk_leadExp`,
  `leadExp_le_of_coeff_ne_zero`;
* `degStep V N` (all monomials of degree `≥ N`): `mem_degStep`, `degStep_le`, `degStep_zero`,
  `degStep_antitone`, `mem_degStep_iff_minDeg`;
* `lexStep V n` (all monomials `≻`-larger than the key `n`): `mem_lexStep`, `lexStep_le`,
  `lexStep_antitone`, `mem_lexStep_of_le_leadExp`, and the compatibility
  **`lexStep_le_degStep`**.

The proof of `#𝒱 = finrank` (the chain `lexStep V n₁ ⊋ … ⊋ lexStep V n_k ⊋ degStep V (N+1)`
telescoping the `finrank`) and of `jumps Cartesian` (both inclusions: the product construction and
the specialisation `ℚ⟦x,y⟧ → ℚ⟦x⟧`) is the task of the next session; the module's docstring records
the precise plan.
-/

/-! ### SESSION 49 (I) — the multivariate counting theorem (Lemma `total jumps`), `Submission.CDT.MvVanishingCount`, zero `sorry`

`Submission.CDT.MvVanishingCount` completes the paper's §"Filtered evaluation modules": for a
finite-dimensional `ℝ`-subspace `V ⊆ ℝ⟦x₁,…,x_d⟧` (an `MvPowerSeries`), the number of *leading
exponents* `𝒱 = {leadExp f : f ∈ V, f ≠ 0}` equals `finrank ℝ V`.

Contents:

* `lvlIx σ N`, `lvlFintype`, `lvlCoeff V N : ↥(degStep V N) →ₗ[ℝ] (lvlIx σ N → ℝ)`,
  `lvlCoeff_apply` — the degree-`N` coefficient vector, indexed by the exponent vectors of total
  degree `N` (a `Finset`-subtype with the *lexicographic* order inherited from `Lex (σ →₀ ℕ)`);
* `pivotSet V N` — the pivots of `(lvlCoeff V N).range`;
* `jumpFinset V N` (+ `mem_jumpFinset`, `mem_jumpFinset_dk`) — the `≺`-keys of the grade-`N` leading
  exponents;
* **`mem_pivotSet_iff`** — a grade-`N` exponent is a pivot of the coefficient space iff it is the
  leading exponent of an element of `V` (`jump_of_pivot`/`pivot_of_jump_aux`/`pivot_of_jump`);
* **`ncard_jumpFinset_eq_pivotSet`** — via `Set.ncard_congr` with the bijection `key ↦ udk key`;
* `finite_degStep`, **`exists_degStep_eq_bot`** — the degree filtration of a finite-dimensional
  subspace is separated;
* `kerEquiv` — the kernel of `lvlCoeff V N` is `degStep V (N+1)`;
* **`finrank_degStep_eq`** — rank-nullity: `finrank (degStep V N) = finrank (lvlCoeff V N).range +
  finrank (degStep V (N+1))`;
* **`card_jumpFinset_eq`** — the number of grade-`N` leading exponents is the drop
  `finrank (degStep V N) - finrank (degStep V (N+1))`;
* `sum_range_sub_antitone` — telescoping lemma for antitone `ℕ`-valued sequences;
* `jumpSet V`, `jumpSet_eq_biUnion`, **`ncard_jumpSet_eq_finrank`** — the paper's Lemma
  `total jumps`: `#𝒱 = finrank ℝ V` (the `N`-levels are disjoint since `tdeg ∘ udk` is determined
  by the key: `Finset.card_biUnion`).
-/

/-! ### SESSION 49 (II) — the paper's Lemma `commutation`, `Submission.CDT.MvVanishingCartesian`, zero `sorry`

Completes the paper's §"Filtered evaluation modules": for `V ⊆ ℝ⟦x_i⟧` and `W ⊆ ℝ⟦y_j⟧`, the
leading exponents of the product space `V ⊗ W = span{u(x)v(y)}` are exactly the pairs of leading
exponents of `V` and `W` (the paper's Lemma `commutation`; the paper's Corollary
`jumps Cartesian` iterates it to `d` factors on top of the evaluation-module formalism):

**`jumpSet_prodSpace`** : `jumpSet (prodSpace V W) = {dk (pairExp e f) | dk e ∈ jumpSet V,
dk f ∈ jumpSet W}`.

Contents:

* `pairExp`, `comapInl`, `comapInr`, `inlEmb`, `inrEmb`, `inlₗ_inj`, `inrₗ_inj`, `inlₗ_ne_inrₗ`,
  `inrₗ_ne_inlₗ`, `pairExp_apply_inl/inr`, `comapInl_apply`, `comapInr_apply`,
  `comapInl_pairExp`, `comapInr_pairExp`, `pairExp_comap`, `tdeg_eq_degree`, `pairExp_tdeg`;
* the order calculus `lex_pairExp_lt_iff` (from the commons
  `Commons.Data.Finsupp.lex_mapDomain_lexSum_lt_iff`), `dk_pairExp_lt_iff`, `dk_pairExp_le`,
  `dk_pairExp_lt_left`, `dk_pairExp_lt_right`;
* `renameInl`, `renameInr`, `genVW`, `prodSpace`, **`mem_prodSpace_iff`** (the product space is the
  set of finite sums of products, via `Finsupp.range_linearCombination`),
  **`coeff_prod`** (the coefficient formula `coeff μ (u(x)v(y)) = coeff (comapInl μ) u ·
  coeff (comapInr μ) v`, from the antidiagonal description of `coeff_mul`), `coeff_finsuppSum_gen`,
  `coeff_sum_prod`, `coeff_sum_gen`, `coeff_extract_sigma/tau/left/right`;
* **`jumpSet_subset_prodSpace`** (`𝒱(V)·𝒱(W) ⊆ 𝒱(V ⊗ W)`) and **`exists_pair_leadExp_sum`**
  (`𝒱(V ⊗ W) ⊆ 𝒱(V)·𝒱(W)`, the coefficient-extraction argument: from the leading exponent `μ` of a
  finite sum build `H ∈ V` and `H' ∈ W` with `coeff (comapInl μ) H = coeff μ F` and
  `coeff (comapInr μ) H' = coeff μ F`, then show their leading exponents project to `μ`).
-/

/-! ### SESSION 49 (III) — the Riemann-sum passage of the paper's §"The cost of an integration", `Submission.CDT.RiemannSum` and `Submission.CDT.ModelRiemann`, zero `sorry`

**(1) `Submission.CDT.RiemannSum`** — the analysis lemma:
**`tendsto_riemannSum_of_lipschitz_pieces`**: if `f : ℝ → ℝ` is bounded by `L` on `[0,m]` and
`L`-Lipschitz on each piece `[a i, a (i+1)]` (`i < N`, `a 0 = 0`, `a N ≥ m`), then
`(1/d)·Σ_{j=1}^{d} f(m·j/d) → (1/m)·∫_0^m f`.
Supporting: `continuousOn_of_lipschitz`, `intervalIntegrable_of_lipschitz`,
**`lipschitz_of_pieces_aux`** (the piecewise Lipschitz condition *chains* across the finitely many
breakpoints, giving a global Lipschitz bound), `abs_sub_le_abs_add`,
**`abs_riemannSum_sub_integral_le`** (the mesh estimate: the `j`-th rectangle differs from the
integral over `[(j-1)m/d, jm/d]` by at most `L(m/d)²`).
(The same statement was also requested as the commons lemma
`Commons.Analysis.RiemannSum.tendsto_riemannSum_of_lipschitz_pieces`; the proof here is independent.)

**(2) `Submission.CDT.ModelRiemann`** — the application to the model function of Lemma `lcm-2`
(`stepB w = max 1 w`, the grid `modelGrid w` with `modelGrid w (k+1) = 1 + k·B`,
`harmonicFun_eq_piece`, `correctionFun_eq_piece`, `modelFun_eq_piece`,
`modelFun_eq_grid_right`, `modelFun_eq_piece_closed`, `abs_modelFun_sub_le_first`,
`abs_modelFun_sub_le_piece`, `abs_modelFun_sub_le_grid`, `abs_modelFun_le`,
`modelGrid_eventually_ge`, `sum_nonneg_Icc`), culminating in
**`tendsto_riemannSum_modelFun`** and the paper-facing form
**`tendsto_riemannSum_modelFun_integratedLcm`**:
`(1/d)·Σ_{j=1}^{d} modelFun w (m·j/d) → integratedLcm 0 m w / m` for `1 ≤ m`
(the "horizontal integration" of the paper: the added denominator product is the exponential of
`(d·D/m)·(max_i e_i)·I_ξ^m(ξ)`).
-/


/-! ### SESSION 50 — THE DENOMINATOR RATE TERMS `τ♭` AND `τ♯` OF THE FINE HOLONOMY BOUND

`Submission.CDT.FineHolonomy` (zero `sorry`, in the import chain) formalises the two arithmetic
rate terms of Calegari–Dimitrov–Tang's Theorem `main:elementary form` (the paper's §"The fine
holonomy bound"), together with the paper's own Example `ex:li11`:

* the weighted average `tauFlat m r b = (1/m²)·Σ_{i≤m}(2i-1)·σ_i` of the row sums `σ_i = Σ_j b_{i,j}`
  and the paper's display `(taub)`: for an array whose columns have the paper's column shape
  (`0 = b₁ⱼ = ⋯ = b_{u_j,j} < b_{u_j+1,j} = ⋯ = b_{m,j}`),
  **`tauFlat_eq`**: `τ♭(b) = σ_m − (1/m²)·Σ_j u_j²·b_j` (with `σ_m = Σ_j b_{m,j}`),
  **`tauFlat_nonneg_le_rowSum`**: `τ♭ ∈ [0,σ_m]`, and
  **`tauFlat_eq_integral`**: the paper's display `(finitary rearrangement)`
  `τ♭(b) = Σ_i σ_i·∫_{(i-1)/m}^{i/m} 2t dt`.

* the additive term `tauSharp m esum emax = (2/m²)·inf_{ξ∈[0,m]}{ξ·Σe_i + (max e_i)·I_ξ^m(ξ)}`
  of Theorem `main:elementary form`, built on the paper's Definition `integrated lcm`
  (`Submission.CDT.IntegratedLcm`): `tauSharp_nonneg`, and, for the `[1,…,n][1,…,2n]`
  configuration of Example `ex:li11` (`m = 4`, `Σe_i = max e_i = 1`),
  **`integratedLcm_two_three`**: `I_ξ^4(ξ) = 7/2 - ξ` for every `ξ ∈ [2,3]` (the paper's
  "minimising interval"), and **`tauSharp_le_example`**: `τ♯ ≤ 7/16`.

**A correction of the paper.** Example `ex:li11` displays `τ♭(b) = 37/16`, `τ♯(e) = 7/16` and then
`τ(b;e) = 21/8`; but `37/16 + 7/16 = 11/4 = 2.75 ≠ 21/8 = 2.625`.  The value `21/8` is the one the
*same* example computes for the cruder array `b₀` (`τ(b₀) = (1·0 + 3·2 + 5·3 + 7·3)/16 = 21/8`).
We record the two correct values separately.
-/


/-! ### SESSION 51 — THE INCREASING REARRANGEMENT AND THE PAPER'S DISPLAY `(maxintegral)`

`Submission.CDT.Rearrangement` (zero `sorry`, in the import chain) formalises the paper's equation
`(maxintegral)` of §"Variants of the Nevanlinna growth characteristic": for a probability measure
`μ` and a bounded nonnegative measurable `f`,

`∫_0^1 2t·g*(t) dt = ∫_0^1 ∫_0^1 max(g(s), g(t)) ds dt`,

where `g*` is the *increasing rearrangement* (quantile function) of `g`.  Both sides are proved
equal to the "energy" `∫_0^∞ (1 - (1 - F(r))²) dr` of the complementary distribution function
`F(r) = μ {x | r < g x}`, i.e. the identity says that the expected maximum of two independent
copies depends only on the law of `g`.

Contents (namespace `Submission.CDT.Rearr`):

* the quantile function `rearr μ f t := sSup {y | ofReal (1-t) < μ {x | y < f x}}` with
  `rearr_mono`, and **`lt_rearr_iff`**: `r < g*(t) ↔ 1 - t < μ {f > r}` (the distribution
  characterisation of the rearrangement, proved by a continuity-from-below argument);
* `fstar` (the rearrangement of a real-valued `f`) and `distr` (`F(r) = μ {f > r}`), with
  `lt_fstar_iff`, `fstar_nonneg`, `fstar_le`, `distr_le_one`, `distr_antitone`;
* the weight measure `2t dt` on `(0,1]` (`weightMeasure`, with the density bridge
  `integral_weightMeasure` and `weightMeasure_real_lt_fstar`) and the Lebesgue/`toReal` bridge
  `toReal_lintegral_Ioc_ofReal`;
* **`integral_two_mul_fstar`**: `∫_0^1 2t·g* = ∫_0^∞ (1-(1-F)²)`;
* **`integral_integral_max`**: `∫∫ max(f s, f t) dμ dμ = ∫_0^∞ (1-(1-F)²)`;
* **`integral_two_mul_fstar_eq_integral_integral_max`**: the display `(maxintegral)`.

**A correction of the paper's convention.**  With the paper's literal definition
`g*(t) := inf_s { P(g > s) ≤ t }` the function is *decreasing* and the identity FAILS (for
`g = 1_A`, `P(A) = 1/2`: the left side is `1/4`, the right side `3/4`).  The standard quantile
function, which is increasing, is `g*(t) = inf { s : P(g > s) ≤ 1 - t }` — this is what we
implement (in the equivalent `sSup` form).
-/


/-! ### SESSION 52 — THE SYMMETRISATION OF DENOMINATOR TYPES (Lemma `etalecover`)

`Submission.CDT.EtaleCover` (zero `sorry`, in the import chain) formalises the *integrality* part of
the paper's Lemma `etalecover` — the input used for the denominator types of `B₄` and `B₇`.

With `y = x + x/(x−1) = x²/(x−1)`, the polynomials `P_n(y) := x^n + (x/(x−1))^n` are defined by
`symAux`/`symPoly` via the recurrence `P_0 = 2`, `P_1 = y`, `P_{n+2} = y·P_{n+1} − y·P_n`.  We prove

* `symPoly_coeff_int`: the coefficients of `P_n` are integers;
* `symPoly_coeff_eq_zero`: the `y`-support of `P_n` lies in the degree range `[⌈n/2⌉, n]`
  (stated as `2m < n ∨ n < m → (P_n).coeff m = 0`), hence `P_k` contributes to `y^n` only for
  `k ∈ [n, 2n]` (`symPoly_coeff_eq_zero_of_not_mem`);
* **`etalecover_integrality`**: if `A_n · lcmUpto (c·n) ∈ ℤ` for all `n`, then the symmetrised
  coefficients `B_n = Σ_{k} A_k·[y^n]P_k` satisfy `B_n · lcmUpto (2c·n) ∈ ℤ` (the paper's
  "`2F(y) = Σ b_n y^n/∏[1,…,2c_in]` with `b_n ∈ ℤ`"), the proof being the paper's: the coefficient
  index ranges over `k ∈ [n,2n]` and the `lcm`-windows are nested
  (`Commons.NumberTheory.Chebyshev.lcmUpto_dvd_of_le`).
-/

end Submission

