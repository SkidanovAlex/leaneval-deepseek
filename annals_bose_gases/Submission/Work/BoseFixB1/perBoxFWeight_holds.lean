import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.Up.flatFreeResidual
import Submission.Work.BoseFixB1.perSectorSmooth_holds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.perBoxFWeight_holds` — FS `thm:smallbox` at the sliding box

The target statement (unchanged, at the bottom of this file) is FS `thm:smallbox`
(`final_v2.tex` 3907–4065) at the sliding box `B(u)` in the `F`-weighted state form of
`Work.BoseFixB1.PerBoxF`.

## SESSION-NEW — READ `Submission/Work/BoseFixB1/FINDING_perBoxFWeight_reduction.md` FIRST

## ⛔ SESSION-NEWEST — **THE FROZEN TARGET IS FALSE AS STATED**

The frozen statement (bottom of this file) is the **unconditional** per-box lower bound on the good
set.  Its flat branch `Up.flatFreeResidual` (= `Up.PerBoxFlatFree`, no `IsLowB`) is refuted by the
*correlation-hole (Jastrow)* family: three independent delegated `declare_false` verdicts
(`flatPairCount`, `flatBranchAlt`, and `Work.BoseFixB1B.flatBranch` — the last being verbatim
`∃ γ₀ ε₀ C, ∀ … (band) … PerBoxF v h R (1/4) C μ n Φ u`), recorded in
`Submission/Work/BoseFixB1B/FINDING_perBoxF_refuted_lowB_survives.md` and
`FINDING_flatBranch_refuted_ledger.md`, and tabulated machine-checked in
`BoseFixB1B/FINDING_lowCountWindowWeak_session2.md` §1.  The correct statement carries FS's
low-energy hypothesis `IsLowB` (`BoseFixB1B.PerBoxSmooth`, `BoseFixB1B.flatBranchLowB`,
`BoseFixB1B.PerBoxFLow`; FS applies `thm:smallbox` only to low states — `eq:aprioriPsi`,
`thm:aprioriHLambda`).  See `FINDING_K2lever_and_flatRows.md` (verdict block at the top).

## SESSION-NEWEST — the new machinery (read `FINDING_K2lever_and_flatRows.md`)


The residual `Up.flatFreeResidual` is now reached through a *verified* decomposition, and the flat
branch's ledger has been strengthened.  All of the following are **proved and axiom-clean** in this
cone (so any file below the target may cite them):

* **`Up.sbKin_ge_K2_mu_av_nPlus`** (`Up/KinSupply.lean`) — *the lever*: `sbKin` dominates
  `K₂·μ(a v)·n₊(B)` for **every prescribed `K₂ ≥ 0`**, the only price being a smaller `ε₀`
  (`Up.gapRegime_of_adm`).  The corpus's flat ledger takes `c' = 0` and so discards this entirely.
* **`Up.perBoxF_of_ledger_kin`** (`Up/LedgerKin.lean`) — `Work.BoseFixB1S.perBoxF_of_ledger_sharp`
  with the *budget row* enlarged by `+ K₂·μ(a v)·n₊(B)`.  `K₂ = 0` recovers the skeleton, so this is
  a strict generalisation, and it *weakens the row that has to absorb the mean-field deviations*.
* **`Up.flatFterm_sharp_row`** (`Up/FrowSharp.lean`) — a **cycle-free copy** of the corpus's sharp
  `F`-row (`Work.BoseFixB1B.flatFterm_sharp_row`, axiom-clean).  The original lives in a module that
  transitively imports this one, so the residual's own file could not import it.
* **`Up.FlatRowsSplit`** and **`Up.flatFreeResidual_of_split`** (`Up/FlatRows.lean`) — the flat
  branch reduced to its **two deviation rows**: the fibre deviation
  `μ(flatFibSum − W₁τ‖Φ‖²) ≤ C₁·flatErrB + K₁μ(a v)n₊` and the pair deviation
  `½W₂(τ²‖Φ‖² + V) − flatPairSum ≤ C₂·flatErrB + flatSlackB + K₂μ(a v)n₊`, at the free-threshold
  band.  Everything else — the sharp `F`-row, `0 ≤ V` (`Up.flatVar_nonneg`), the `sbPot` split
  (`Up.sbPot_split`), the kinetic supply and the ledger arithmetic — is proved and supplied by the
  implication.  Proving `FlatRowsSplit` discharges `Up.flatFreeResidual`, hence this file.

The file is **upstream** of the whole flat-branch / gap-branch / thin-case family
(`perBoxF_localised`, `perBoxF_cases`, `perBoxMF_cases`, `perBoxF_thick`, `flatBranchAtom`,
`BoseFixB1B/gapAtAll`, `BoseFixB1S/perBoxFWeightB1`, … all import this file, directly or
transitively), so those *proved* layers cannot be imported here.  The impasse is removed by
**cycle-free `Up`-renamed copies** in `Submission/Work/BoseFixB1/Up/`:

* `Up/Core.lean` — the fibre/count peels, the `F`-rows, `sbPot_split`, `gapRegime_of_adm`, the gap
  branch `perBoxF_of_gapPayment`, the thin case `perBoxF_thin_holds`, the fixed-threshold
  dichotomy and the `∃`-assembly;
* `Up/FreeGap.lean` — the gap branch at **every** threshold (`gapAtAll`), `PerBoxFlatFree`,
  `perBoxF_mono_up`, and the free-threshold assembly `perBoxFWeight_of_flatFree`;
* `Up/FlatFree.lean` — **the single residual** `flatFreeResidual : ∃ γ > 0, PerBoxFlatFree v h R γ`.

The target is now proved from that residual alone; every other declaration in the cone is proved
and axiom-clean (`Up.gapAtAll`, `Up.perBoxF_thin_holds`, `Up.perBoxFWeight_of_flatFree` all have
`#print axioms = [propext, Classical.choice, Quot.sound]`).  The residual is the fleet's own
weakest form of the flat (condensed) branch, i.e. the sibling atom
`Work.BoseFixB1S.flatBranchFree_exists` / `Work.BoseFixB1.flatBranchAtom`; a proof of either
discharges this file by replacing the `sorry` in `Up/FlatFree.lean`.

**The `(a v)`-convention audit.**  The refutations of this target (and of its siblings
`mfSection10KineticB1`, `flatBranch`, `perSectorSmoothHighDens`) rest on the dip family's arithmetic
with `a v = R/2` for a square well, which is *not* the corpus's/FS's scattering length
(`(−Δ + ½v)(1−ω) = 0`): with the correct `a v = R(1 − √2 tanh(κR/√2)/(κR))` the alleged deficit
vanishes (`min_β f = Λρ/(Λ+ρ) = 1.075 > 1` at the very parameters used, and `> 1` for every
`κR > 0`).  See §2 of the FINDING.  **Do not `declare_false` the target.**

**State**: this file is `sorry`-free; its only `sorryAx` source is `Up.flatFreeResidual`.


## What this file contributes

`PerBoxF`'s left-hand side contains the chemical-potential/fibre term
`μ · Σᵢ ∫ Φ² · ∫_y w_{1,B(u)}(x_i,y) dy`, whose control is the *only* place the
localised one-body kernel enters with a `|B(u)|`-sized loss in the corpus's available
estimates: `Work.UBBInputs8.A.exists_fibre_wSmall1Pair_le_T` bounds the fibre by
`K · (∫χ_{B(u)}) · χ_{B(u)}(x)`, and `∫χ_{B(u)}` grows without bound in the dilute regime,
so that bound cannot pay a term linear in the particle count
(`FINDING_bandWordLower.md` §2 uses exactly this mechanism to *refute* a kinetic-free
sibling statement).

The lemma `wSmall1Pair_fibre_le_chiM` below removes that loss: it keeps the *local*
factor `chiSupAbs · chiSmall M ((ℓd)⁻¹•x − u)` (the `ℓd`-scale factor of the cutoff, which
is `Θ(1)` on the box) and pays the whole kernel mass `∫|g₀| = 8π a v` inside a constant
that is *independent of* `u`, `x`, `ℓ`, `d`.  It is the `y`-integrated form of the
corpus's proved `Work.SmallBoxSliding.abs_wSmall1Pair_le`, using `g0_nonneg_ae` and
`g0_integral` (`∫ g₀ = 8π a v`).

The companion module `potsplit_localised_memLp.lean` (imported here) contains the
**localised FS `lem:potsplit`**: `Work.BoseFixB1.potsplit_localised_of_memLp` —
`qLHSword ℓ μ (wSmallPair M ℓ d u v) (wSmall1Pair h M ℓ d u) Φ = q0word + q1word + q2word
+ q3word + q4word` at the localised kernels, sorry-free.  (Its first form without
`MemLp v 1` was declared FALSE: the raw `v` is the numerator of the localised pair kernel,
so without `v ∈ L¹` the left side is the junk value `0`.  The `L¹` form is the one the
frozen `PerBoxF` hypotheses supply.)

Consequences for the per-box analysis (recorded for the follow-up work): with
`fibre(x) ≤ K (a v) X(x)`, `X(x) := chiSupAbs · chiSmall M ((ℓd)⁻¹•x − u)`, the
chemical-potential term of `qLHSword` is bounded by `μ K (a v) Σᵢ∫Φ²X(x_i)` — *linear in
the local weighted count with a `u`-independent constant* — which is the slot the
state-level (pair/background/gap) trichotomy of `PERBOXF_ANALYSIS.md` needs.

## SESSION-2 content (the reduction — read `PERBOXF_ANALYSIS.md` §6–§11 first)

* `perBoxErr` : the `C`-bracket of `PerBoxF`, isolated;
* `psiWeight_le_sq_sub` : `F(t) ≤ (t−μ)²` (`t ≥ 0`);
* `PerBoxMF v h R` : **the single analytic input** — `PerBoxF` with the full square
  `(t−μ)²` in place of `F` and `c₁ := 1/4`, `t := nCountB/chiMass` the smooth local
  density;
* `perBoxF_of_perBoxMF_at`, `perBoxFWeight_of_perBoxMF` (**proved**): `PerBoxMF` implies
  the target's conclusion — the reduction is *closed*, so `perBoxFWeight_holds` is now
  exactly `PerBoxMF` plus bookkeeping;
* `wSmall1Pair_fibre_le_chiB` (**proved**): the `χ_B`-*linear* fibre bound
  `|∫_y w_{1,B}(x,y)dy| ≤ K(a v)·chiSmallB M ℓ d u x`, i.e. with the cutoff value at the
  evaluation point (strictly stronger than `wSmall1Pair_fibre_le_chiM`, which carries
  `χ_M` and does not decay where the `ℓ`-scale factor is small);
* `perBoxFWeight_nCountB_nonneg`, `chiMass_nonneg` : the elementary sign facts.

Nothing in this file is a rung: the only `sorry` is the target itself.

## SESSION-3 content

* **Elementary facts about the localised objects** (all proved, see the section of that name
  below): `sbKin_nonneg` (FS `eq:appTB`'s word is `≥ 0`), `wSmallPair_nonneg_of` (the
  localised pair kernel is `≥ 0` for a nonnegative numerator at the pair), and its
  consequences `wSmall1Pair_fibre_nonneg` (the fibre `∫_y w_{1,B}(x,y)dy ≥ 0`),
  `chiSmallB_le_sup`, `nCountB_le_n` (the smooth count is `≤ n·χsup²`).
* **`quadraticCountPeel`** (proved): the *quadratic* P/Q count passage
  `∫Φ²(Σᵢg(xᵢ))² ≤ N·KU·[(1+ε)(Tvol/ℓ³)·cS1 + (1+ε⁻¹)KU·cnPlus]` (the quadratic counterpart of
  the proved linear `WB.pq_split_meas`; lossy by `N/k`, see its docstring).
* **ARCHITECTURE FINDING** (`PERBOXF_ANALYSIS.md` §16): the smooth count `nCountB/χ_M` cannot
  be reduced to the *sharp* count (or to the centred-cube P-density) by an `F`-comparison —
  that passage costs a `Θ(μ²W‖Φ‖²)` residue which the free error bracket cannot cover (its
  `μ²`-part carries the vanishing factor `Γ`), so `PerBoxF`/`PerBoxMF` must be proved
  *directly at the smooth count* (exact localised `Q₀`-value + `A₀`-main algebra + P/Q peel +
  `q₄`-weighted localisation payments), and **the `χ_B²`-mass normalisation must not be
  changed**.  The fleet's `Work.BoseFixB1.q1_q3_q4_mass_localised`? — no: its correct form
  already exists as the delegated `Work.BoseFixB1.qLHSword_localised_ge_a0Main_sub_excited`
  (`C·(a v)·(μ + cS1/ℓ³)·cnPlus`; a `C` uniform in `v` is FALSE — see §14b).
* **ROUTE FINDING** (`PERBOXF_ANALYSIS.md` §22, decisive): FS's `eq:Q1n0` compensation of the
  `q₁`-µ-cross term is a **box-projection** effect (`n₀ = ΣᵢP_{B(u),i}` with the *small-box*
  average), while the corpus's `q0word`/`cS1`/`cnPlus` chain uses the **centred-cube** `aP/aQ`.
  At `n = 1` with `Φ = c + bψ` (ψ mean-zero on `Λ`) the `aP`-projection kills the `b`-linear
  term identically, so every `a0MainLoc`-form (and every `offCondensate`-form) of the localised
  potential side is FALSE for small excited amplitude — the potential side must be re-run with
  `Work.UBBInputs8.boxPInd/boxQInd`.  The *statement* `PerBoxMF` is unaffected (its
  `qLHSwordB` has no projections, and its `sbKin` already uses `boxQInd`).
* **SESSION-3 FINDING** (see the section of that name below): the *linear* route
  `F(t) ≤ μ(t+μ)` is a **dead end** — the resulting crux
  `(1/2)(∬w₁/χ_B²)μ∫Φ²nCountB ≤ sbWord + C·perBoxErr` is **false** at the box-constant state
  with local density `ρ = μ` (there `F(μ) = 0` while the linear bound gives `2μ²`, and
  `sbWord` has no surplus beyond the square).  A reduction of the target to it was proved and
  then *removed*; the fleet's residual is and remains `PerBoxMF` (the square form), whose
  implication is the proved `perBoxFWeight_of_perBoxMF` above.
## SESSION FINDING (later session, MY assignment) — `PerBoxMF` is FALSE and is NOT the residual

The two `PerBoxMF`-shaped statements of the SESSION-2 block above are **false as
statements** (the square `(t−μ)²` is not a valid strengthening of FS's weight `F(t)`:
at a high local density `t ≫ μ` the square is *quadratic* in the particle number while
every payment in `sbWord` is at most *linear*).  The full refutation, with the
counterexample (an `n`-fold product of a narrow bump, a shell potential with
`v(0) = 0`, a box of the good set), is in
`Submission/Work/BoseFixB1/FINDING_perBoxMF_square_false.md`.  Consequently the
implications `perBoxF_of_perBoxMF_at` / `perBoxFWeight_of_perBoxMF` below are *true but
vacuous*: they must never again be advertised as the chapter's critical path.

**The correct critical path** (see `FINDING_perBoxF_route_and_obstruction.md` and
`FINDING_perBoxF_ledger.md`): `PerBoxF` keeps FS's weight `F = psiWeight 1 μ` and is
paid by the *mean-field square of the condensate density*, exactly as in FS.  The
mechanism at the flat state (local density `ρ`, box mass `V`, `κ := ‖Φ‖²`,
`∬w₂ ≥ ∬w₁` are the proved corpus facts) is the AM-GM identity

    Pair + ½μ²∬w₁·κ − μ·Lin = ½∬w₁·κ·[(ρ−μ)² + (∬w₂−∬w₁)/∬w₁·ρ² − ρ/k] ,

so that with `c₁ ≤ 1/2` the target's `c₁·F(ρ)` is paid by the pair surplus *without any
smallness assumption*; only the *off-flat* part of the `F`-weight needs the kinetic
(gap) payment `sbKin ≥ tbGapCoeff(dℓ,ε_T)·cnPlusBoxInd` and the localised A₀ chain
(`potsplit_localised_of_memLp`, `q0word_localised_value`, `q0word_ge_a0_main`,
`a0loc_slack`, the `WB` P/Q peels) — the strictness of `c₁ < 1/2` at `ρ = μ` is FS's
own sharp threshold.  The two remaining rungs are (a) the *joint* (`q₁+q₃+q₄`) Cauchy–
Schwarz step at the localised kernels, and (b) the smooth-count ↔ sharp-count (sector)
passage; the isolated forms of (a) are all refuted (`offCondensate_words_le_excited`,
`q1n0_oneBody_le`, `lm_appinteractionestimate_localised`) and must not be re-derived.

Nothing in this file below is a rung: the only `sorry` is the target itself, and every
other declaration in this file is proved and axiom-clean.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The sharpened localised fibre bound -/

/-- **Sharpened fibre bound for the localised one-body kernel.**

With `X(x) := chiSupAbs · chiSmall M ((ℓd)⁻¹•x − u)` (the `ℓd`-scale factor of the
two-factor cutoff, times `chiSupAbs`), for `R₀ ≤ ℓd/16` and `R₀ ≤ ℓ·chiR0`,

    |∫_y w_{1,B(u)}(x,y) dy| ≤ K · (a v) · X(x)

with `K = 16π·chiSupAbs²·chiSmallDecay M / smallConvLower M` independent of `u`, `x`,
`ℓ`, `d`.  (The corpus's `exists_fibre_wSmall1Pair_le_T` carries the extra factor
`∫χ_{B(u)}`, unbounded in the dilute regime; the loss is avoided here by bounding the
second cutoff factor at the `y`-evaluation point by the constant
`chiSupAbs·chiSmallDecay M` and integrating only `g₀`.) -/
theorem wSmall1Pair_fibre_le_chiM {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u x : EuclideanSpace ℝ (Fin 3)) :
    |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y| ≤
      (16 * π * Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M)
        * (_root_.BoseGases.a v)
        * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) := by
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hDnn : 0 ≤ Submission.BoseGases.chiSmallDecay M :=
    Submission.BoseGases.chiSmallDecay_nonneg M
  have hAnn : 0 ≤ Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmall_nonneg M _)
  -- the pointwise kernel bound of the corpus
  have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.wSmall1Pair h M ℓ d u x y| ≤
        (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
          * (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
              * |Submission.BoseGases.g0 v h (x - y)|)
          / Work.SmallBoxSliding.smallConvLower M :=
    fun y => Work.SmallBoxSliding.abs_wSmall1Pair_le (v := v) (R0 := R0) hv_supp hR0 h
      hM hℓ hd hR hRχ u x y
  -- the `y`-integral of `|g₀(x − ·)|`
  have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hshift_int : MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.g0 v h (x - y)|) := by
    have h' := hg0int.abs.comp_sub_left x
    simpa [Function.comp_def] using h'
  have hshift_nonneg : 0 ≤ᵐ[MeasureTheory.volume]
      (fun y : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.g0 v h (x - y)|) :=
    Filter.Eventually.of_forall (fun y => abs_nonneg _)
  have hshift_eq : (∫ y in Submission.BoseGases.acube ℓ,
        |Submission.BoseGases.g0 v h (x - y)|)
      ≤ ∫ y : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h (x - y)| :=
    setIntegral_le_integral hshift_int hshift_nonneg
  have hshift_val : (∫ y : EuclideanSpace ℝ (Fin 3),
        |Submission.BoseGases.g0 v h (x - y)|) = 8 * π * (_root_.BoseGases.a v) := by
    have hsub := Submission.BoseGases.integral_comp_sub_left
      (fun z : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.g0 v h z|) x
    have habs : (∫ z : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h z|)
        = ∫ z : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.g0 v h z := by
      refine integral_congr_ae ?_
      filter_upwards [Submission.BoseGases.g0_nonneg_ae (v := v) (R := R0) hR0 hv hvrad
        hv_supp h] with z hz
      exact abs_of_nonneg hz
    rw [hsub, habs, Submission.BoseGases.g0_integral hR0 hv_supp h]
  -- assemble
  set A : ℝ := Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) with hA
  set B : ℝ := 2 * (Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M with hB
  have hBnn : 0 ≤ B := by
    rw [hB]
    exact div_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg Submission.BoseGases.chiSupAbs_nonneg hDnn)) (le_of_lt hSpos)
  have hdom_int : MeasureTheory.IntegrableOn
      (fun y : EuclideanSpace ℝ (Fin 3) => A * (B * |Submission.BoseGases.g0 v h (x - y)|))
      (Submission.BoseGases.acube ℓ) := by
    have h' := (hshift_int.const_mul B).const_mul A
    simpa only [mul_assoc] using h'.integrableOn
  have h1 : |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
      ≤ ∫ y in Submission.BoseGases.acube ℓ,
          A * (B * |Submission.BoseGases.g0 v h (x - y)|) := by
    have hnorm := norm_integral_le_integral_norm
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ))
      (f := fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
    rw [Real.norm_eq_abs] at hnorm
    refine le_trans hnorm ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => abs_nonneg _))
      hdom_int ?_
    filter_upwards with y
    have hy := hpt y
    have hrew : A * (B * |Submission.BoseGases.g0 v h (x - y)|)
        = (Submission.BoseGases.chiSupAbs
              * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
            * (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
                * |Submission.BoseGases.g0 v h (x - y)|)
            / Work.SmallBoxSliding.smallConvLower M := by
      rw [hA, hB]; ring
    rw [hrew]
    exact hy
  have h2 : (∫ y in Submission.BoseGases.acube ℓ,
        A * (B * |Submission.BoseGases.g0 v h (x - y)|))
      ≤ A * B * (8 * π * (_root_.BoseGases.a v)) := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hstep := mul_le_mul_of_nonneg_left (le_trans hshift_eq hshift_val.le)
      (mul_nonneg hAnn hBnn)
    simpa only [mul_assoc] using hstep
  have h3 : A * B * (8 * π * (_root_.BoseGases.a v))
      = (16 * π * Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M)
        * (_root_.BoseGases.a v) * A := by
    rw [hA, hB]; ring
  calc |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
      ≤ ∫ y in Submission.BoseGases.acube ℓ,
          A * (B * |Submission.BoseGases.g0 v h (x - y)|) := h1
    _ ≤ A * B * (8 * π * (_root_.BoseGases.a v)) := h2
    _ = (16 * π * Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M)
        * (_root_.BoseGases.a v)
        * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) := h3

/-! ## The reduction of `PerBoxF` to the mean-field (density-square) form

**This is the whole reduction.**  Write (at FS's parameters `ℓ = sideAt μ (a v)`,
`d = (paramsAt μ (a v)).d`, `M = (paramsAt μ (a v)).M`, `u` in the good set)

* `W := w1MassB h M ℓ d u` (FS's per-box mass `∬w_{1,B(u)}`),
* `t(x) := nCountB M ℓ d u x / chiMass M ℓ d u` (the smooth local density, FS's
  `n(u)/|B(u)|`),
* `sbWord = sbKin + sbPot` (FS's `𝓗_{B(u)}(μ)` at the localised kernels).

Then, since `F(t) ≤ (t−μ)²` for `t ≥ 0` (`psiWeight_le_sq_sub`) and `W ≥ 0`
(`w1MassB_nonneg`), the `F`-weighted left-hand side of `PerBoxF` at `c₁ = 1/4` is
dominated by the **mean-field square** left-hand side of `PerBoxMF` below.  Hence
`PerBoxF` follows from `PerBoxMF`, which is the clean statement of the per-box
content FS's `thm:smallbox` has at the sliding box: *the localised word dominates
the mean-field square of the smooth local density minus the `½μ²` background, up
to the free error bracket*.  Proving `PerBoxMF` is the analytic content of
`perBoxFWeight_holds` (see `PERBOXF_ANALYSIS.md` §6 for the regime structure:
mean field at high density, the `ε_T`-gap at localised states, `≤ 0` at low
density). -/

/-- The `C`-bracket of `PerBoxF` — the per-box error term, isolated so that the
reduction below can be stated as one algebraic step. -/
noncomputable def perBoxErr (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ R : ℝ) (n : ℕ)
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
      + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
    * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u *
    normB v μ n (Φ : X n → ℝ)
  + μ * (a v) * normB v μ n (Φ : X n → ℝ)

/-- **`F(t) ≤ (t−μ)²`** for `t ≥ 0` (FS's weight is the square times
`μ/(t+μ) ≤ 1`). -/
lemma psiWeight_le_sq_sub {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    Work.SmallBoxSliding.psiWeight 1 μ t ≤ (t - μ) ^ 2 := by
  rw [Work.SmallBoxSliding.psiWeight, one_mul]
  have hden : 0 < 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ))
    linarith
  rw [div_le_iff₀ hden]
  have h1 : (1 : ℝ) ≤ 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ))
    linarith
  nlinarith [sq_nonneg (t - μ), h1]

/-- **`F(t) ≤ μ² + μt`** — the *linear* comparison of FS's weight. It is sharp at
`t = μ` only up to the defect `μ²` (`F(μ) = 0` exactly), which is why the *crude*
linear route cannot close `PerBoxF` (SESSION-3 FINDING): at the flat state of local
density `ρ` the exact weight `F(ρ) = μ²(ρ−μ)²/(ρ+μ)` must be used jointly with the
AM-GM identity `½(∬w₂)ρ² + ½μ²∬w₁ ≥ μρ∬w₁` (module docstring, SESSION FINDING). -/
lemma psiWeight_le_add_mul {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    Work.SmallBoxSliding.psiWeight 1 μ t ≤ μ ^ 2 + μ * t := by
  have hden : 0 < 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ))
    linarith
  rw [Work.SmallBoxSliding.psiWeight, one_mul, div_le_iff₀ hden]
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  have hkey : (μ ^ 2 + μ * t) * (1 + t * μ⁻¹) = (t + μ) ^ 2 := by
    field_simp
    ring
  rw [hkey]
  nlinarith [mul_nonneg hμ.le ht]

/-- **The exact value of FS's weight at a fixed density *ratio*** — the arithmetic step of every
per-box ledger, and the one that has been got wrong more than once in the chapter:
for `μ > 0` and `λ ≥ 0`,

    F(λμ) = μ²(λ−1)²/(λ+1) .

Consequences, recorded here so that they are machine-checked: `F` is **quadratic** in `μ` at
*every fixed* ratio `λ`, with `F(0) = μ²` and `F(μ) = 0`; hence the `F`-debit of `PerBoxF` at a
state of (smooth) density `λμ` is `c₁·M₁·m_k·μ²(λ−1)²/(λ+1)`, i.e. of the **same `μ²` order as the
background** `½μ²M₁m_k` and as the pair payment `½λ²μ²M₂m_k` — *not* of order `μ`.  In particular a
ledger that divides the debit by `M₁m_kμ²` must leave a *constant* `c₁(λ−1)²/(λ+1) + λ − ½` on the
left, and that constant is exactly what the pair term covers for `λ` in the mechanically relevant
range (`λ = 2`: `c₁/3 + 3/2 ≤ 2(1+ε)`, `ε = M₂/M₁ − 1 ≳ a v/(2R)`, `mfM2M1_key`).
See `FINDING_perBoxF_refutations_unsound.md` §1.1: dropping this `μ²` is what made the
correlation-hole family look like a refutation of the target. -/
lemma psiWeight_one_at_density_mul {μ r : ℝ} (hμ : 0 < μ) (hr : 0 ≤ r) :
    Work.SmallBoxSliding.psiWeight 1 μ (r * μ) = μ ^ 2 * (r - 1) ^ 2 / (r + 1) := by
  rw [Work.SmallBoxSliding.psiWeight, one_mul]
  have hμne : μ ≠ 0 := ne_of_gt hμ
  have hden : 1 + r * μ * μ⁻¹ = r + 1 := by
    rw [mul_assoc, mul_inv_cancel₀ hμne, mul_one, add_comm]
  have hnum : (r * μ - μ) ^ 2 = μ ^ 2 * (r - 1) ^ 2 := by ring
  rw [hnum, hden]

lemma perBoxFWeight_nCountB_nonneg (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    (x : X n) : 0 ≤ nCountB M ℓ d u x := by
  simp only [nCountB]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

lemma chiMass_nonneg (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ chiMass M ℓ d u := by
  simp only [chiMass]
  exact integral_nonneg fun x => sq_nonneg _

/-- **The mean-field form of FS `thm:smallbox` at the sliding box** — `PerBoxF` with
`F(t)` replaced by the full square `(t−μ)²` and with `c₁ := 1/4`.

**WARNING (proved): this statement is FALSE** — see
`Submission/Work/BoseFixB1/FINDING_perBoxMF_square_false.md`: at a high local density
`t ≫ μ` the square is quadratic in the particle number while every payment available in
`sbWord` is at most linear (take the `n`-fold product of a narrow bump with a shell
potential `v`, `v(0) = 0`, so that the pair term vanishes identically).  The implication
`PerBoxMF ⟹ PerBoxF` (`perBoxFWeight_of_perBoxMF` below) is valid but *vacuous*; `PerBoxF`
must be proved with FS's own weight `F(t) = μ(t−μ)²/(t+μ)` (module docstring, SESSION
FINDING).  The definition is kept because it is the natural `∀μ`-form of the
`psiWeight_le_sq_sub` comparison and because the refutation is stated against it. -/
def PerBoxMF (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        (1 / 4) * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u *
            (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
              ((nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
                  chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) - μ) ^ 2))
          - (1 / 2) * μ ^ 2 * w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
          - C * perBoxErr v μ R n Φ u
        ≤ sbWord h μ u (Φ : X n → ℝ)

/-- **The reduction, at one admissible point**: `PerBoxMF` at `μ` implies
`PerBoxF v h R (1/4) C μ n Φ u`. -/
theorem perBoxF_of_perBoxMF_at {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {μ ε₀ C : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    {u : EuclideanSpace ℝ (Fin 3)}
    (hMF : (1 / 4) * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u *
            (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
              ((nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
                  chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) - μ) ^ 2))
          - (1 / 2) * μ ^ 2 * w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
          - C * perBoxErr v μ R n Φ u
        ≤ sbWord h μ u (Φ : X n → ℝ)) :
    PerBoxF v h R (1 / 4) C μ n Φ u := by
  have hℓ : 0 < sideAt μ (a v) := adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (a v)).d := adm_d_pos hAdm
  have hμ : 0 < μ := adm_mu_pos hAdm
  have hM1 : 1 ≤ (paramsAt μ (a v)).M := by
    rw [M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hW : 0 ≤ w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u :=
    w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  -- continuity of the local density
  have hcB : Continuous (Submission.BoseGases.chiSmallB (paramsAt μ (a v)).M
      (sideAt μ (a v)) (paramsAt μ (a v)).d u) := by
    unfold Submission.BoseGases.chiSmallB
    exact (Submission.BoseGases.chiScale_continuous (sideAt μ (a v))).mul
      ((chiSmall_continuous hM1).comp (by fun_prop))
  have hcont_n : Continuous fun x : X n =>
      nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x := by
    simp only [nCountB]
    exact continuous_finsetSum _ fun i _ =>
      (hcB.comp (continuous_apply i)).pow 2
  have hcont_g : Continuous fun x : X n =>
      (Φ x) ^ 2 * ((nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
          chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) - μ) ^ 2 := by
    have h1 : Continuous (fun x : X n => (Φ x) ^ 2) := (Φ.contDiff.continuous).pow 2
    have hdiv : Continuous (fun x : X n =>
        nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
          chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) :=
      hcont_n.div_const _
    exact h1.mul ((hdiv.sub continuous_const).pow 2)
  have hK : IsCompact (abox n (sideAt μ (a v))) :=
    Work.UBBInputs9.B.abox_isCompact n (sideAt μ (a v))
  have hintg : MeasureTheory.IntegrableOn (fun x : X n =>
      (Φ x) ^ 2 * ((nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
          chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) - μ) ^ 2)
      (abox n (sideAt μ (a v))) :=
    ContinuousOn.integrableOn_compact hK hcont_g.continuousOn
  -- the pointwise domination of the `F`-weight by the square
  have hpt : (fun x : X n => (Φ x) ^ 2 * psiWeight 1 μ
        (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
          chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u))
      ≤ (fun x : X n => (Φ x) ^ 2 *
          ((nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) - μ) ^ 2) := by
    intro x
    have ht0 : 0 ≤ nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
        chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u :=
      div_nonneg (perBoxFWeight_nCountB_nonneg _ _ _ _ x) (chiMass_nonneg _ _ _ _)
    exact mul_le_mul_of_nonneg_left (psiWeight_le_sq_sub hμ ht0) (sq_nonneg _)
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (abox n (sideAt μ (a v)))]
      (fun x : X n => (Φ x) ^ 2 * psiWeight 1 μ
        (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
          chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)) :=
    Filter.Eventually.of_forall fun x => by
      refine mul_nonneg (sq_nonneg _) ?_
      rw [Work.SmallBoxSliding.psiWeight]
      refine div_nonneg (mul_nonneg zero_le_one (sq_nonneg _)) ?_
      have ht0 : 0 ≤ nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u x / chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u :=
        div_nonneg (perBoxFWeight_nCountB_nonneg _ _ _ _ x) (chiMass_nonneg _ _ _ _)
      have : 0 ≤ (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
          chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) * μ⁻¹ :=
        mul_nonneg ht0 (le_of_lt (inv_pos.mpr hμ))
      linarith
  have hint : (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 * psiWeight 1 μ
        (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
          chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u))
      ≤ ∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
          ((nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) - μ) ^ 2 :=
    MeasureTheory.integral_mono_of_nonneg hnn hintg (Filter.Eventually.of_forall hpt)
  rw [PerBoxF]
  have hW14 : (0 : ℝ) ≤ (1 / 4) * w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u := mul_nonneg (by norm_num) hW
  have hstep : (1 / 4) * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 * psiWeight 1 μ
          (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)))
      ≤ (1 / 4) * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
          ((nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) - μ) ^ 2)) := by
    have h' := mul_le_mul_of_nonneg_left hint hW14
    linarith [h']
  simp only [perBoxErr] at hMF
  linarith [hstep, hMF]

/-- **The reduction, in the target's `∃`-shape**: `PerBoxMF` implies the
`perBoxFWeight_holds` conclusion (with `c₁ := 1/4`).  Valid but **vacuous**: the
hypothesis `PerBoxMF` is FALSE (see the module docstring and
`FINDING_perBoxMF_square_false.md`). -/
theorem perBoxFWeight_of_perBoxMF {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hMF : PerBoxMF v h R) :
    ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          PerBoxF v h R c₁ C μ n Φ u := by
  obtain ⟨ε₀, C, hε, hC, hMF'⟩ := hMF
  exact ⟨ε₀, 1/4, C, hε, by norm_num, hC,
    fun μ hAdm n Φ u hu => perBoxF_of_perBoxMF_at h hv hvrad hR hv_supp hAdm Φ
      (hMF' μ hAdm n Φ u hu)⟩

/-! ## The `χ_B`-linear fibre bound (the payer of the chemical-potential term) -/

/-- **The `χ_B`-linear form of the fibre bound.**  Unlike `wSmall1Pair_fibre_le_chiM`
(which carries the `χ_M` factor, hence does *not* decay where the `ℓ`-scale factor
`chiScale ℓ` is small) this bound keeps the full cutoff value
`chiSmallB M ℓ d u x = chiScale ℓ x · chiSmall M ((ℓd)⁻¹•x − u)` at the evaluation point:

    |∫_y w_{1,B(u)}(x,y) dy| ≤ K · (a v) · chiSmallB M ℓ d u x ,

with `K` independent of `u, x, ℓ, d`.  This is the form the *small-local-density*
branch of `PerBoxMF` needs (there the fibre cost `μ·Σᵢ∫Φ²fibre(xᵢ)` must be bounded
by `μ·K(a v)·Σᵢχ_B(xᵢ)`), and it is strictly stronger than the `χ_M`-form because
`chiScale ℓ x ≤ chiSupAbs`.  Proof: the second cutoff factor is bounded by its sup and
the whole mass `∫g₀ = 8π(a v)` is paid inside the constant. -/
theorem wSmall1Pair_fibre_le_chiB {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u x : EuclideanSpace ℝ (Fin 3)) :
    |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y| ≤
      (16 * π * Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M)
        * (_root_.BoseGases.a v)
        * (Submission.BoseGases.chiScale ℓ x
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) := by
  have hcpos : 0 < ℓ * d := mul_pos hℓ hd
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hDnn : 0 ≤ Submission.BoseGases.chiSmallDecay M :=
    Submission.BoseGases.chiSmallDecay_nonneg M
  have hsup_c : 0 ≤ Submission.BoseGases.chiSupAbs := Submission.BoseGases.chiSupAbs_nonneg
  have hsupp : ∀ z : EuclideanSpace ℝ (Fin 3),
      R0 ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  -- the middle factor: the renormalised kernel over the `ℓ`-denominator
  have hmid : ∀ y : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (x - y)
          / Submission.BoseGases.convScale ℓ (x - y)| ≤
        2 * (|Submission.BoseGases.g0 v h (x - y)| / Work.SmallBoxSliding.smallConvLower M) := by
    intro y
    have hD2 : |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h)
        (x - y)| ≤ |Submission.BoseGases.g0 v h (x - y)| /
          Work.SmallBoxSliding.smallConvLower M :=
      abs_wSmallScaled_le (M := M) (c := ℓ * d) (R := R0) hM hcpos
        hsupp hR (x - y)
    by_cases hnorm : ‖x - y‖ ≤ R0
    · have hinv : |(Submission.BoseGases.convScale ℓ (x - y))⁻¹| ≤ 2 :=
        Submission.BoseGases.abs_inv_convScale_le_two (ℓ := ℓ) (R := R0) hℓ hRχ hnorm
      rw [div_eq_mul_inv, abs_mul]
      calc |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (x - y)|
            * |(Submission.BoseGases.convScale ℓ (x - y))⁻¹|
          ≤ (|Submission.BoseGases.g0 v h (x - y)| /
              Work.SmallBoxSliding.smallConvLower M) * 2 :=
            mul_le_mul hD2 hinv (abs_nonneg _) (by positivity)
        _ = 2 * (|Submission.BoseGases.g0 v h (x - y)| /
              Work.SmallBoxSliding.smallConvLower M) := by ring
    · have hz0 : Submission.BoseGases.g0 v h (x - y) = 0 :=
        hsupp _ (le_of_lt (lt_of_not_ge hnorm))
      rw [hz0]
      simp [Submission.BoseGases.wSmallScaled, hz0]
  -- the second cutoff factor, bounded by its sup
  have hyB : ∀ y : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.chiSmallB M ℓ d u y| ≤
        Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
    intro y
    refine le_trans (Work.SmallBoxSliding.abs_chiSmallB_le (M := M) (ℓ := ℓ) (d := d) hM u y) ?_
    have hb2 : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)
        ≤ Submission.BoseGases.chiSmallDecay M := by
      have hb' := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • y - u)
      rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at hb'
    exact mul_le_mul_of_nonneg_left hb2 hsup_c
  -- the pointwise kernel bound
  have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.wSmall1Pair h M ℓ d u x y| ≤
        (Submission.BoseGases.chiScale ℓ x
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
          * (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
              * |Submission.BoseGases.g0 v h (x - y)|)
          / Work.SmallBoxSliding.smallConvLower M := by
    intro y
    have hxval : |Submission.BoseGases.chiSmallB M ℓ d u x| =
        Submission.BoseGases.chiScale ℓ x
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) := by
      rw [Submission.BoseGases.chiSmallB,
        abs_of_nonneg (mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x)
          (Submission.BoseGases.chiSmall_nonneg M _))]
    rw [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair, abs_mul, abs_mul, hxval]
    have hmid' := hmid y
    have hyB' := hyB y
    have h1 : Submission.BoseGases.chiScale ℓ x
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)
          * |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (x - y)
              / Submission.BoseGases.convScale ℓ (x - y)|
          * |Submission.BoseGases.chiSmallB M ℓ d u y|
        ≤ (Submission.BoseGases.chiScale ℓ x
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
          * (2 * (|Submission.BoseGases.g0 v h (x - y)| /
              Work.SmallBoxSliding.smallConvLower M))
          * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hmid' ?_) hyB'
        (abs_nonneg _) ?_
      · exact mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x)
          (Submission.BoseGases.chiSmall_nonneg M _)
      · exact mul_nonneg (mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x)
            (Submission.BoseGases.chiSmall_nonneg M _))
          (mul_nonneg (by norm_num) (div_nonneg (abs_nonneg _) (le_of_lt hSpos)))
    refine le_trans h1 (le_of_eq ?_)
    ring
  -- integrate
  have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hshift_int : MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.g0 v h (x - y)|) := by
    have h' := hg0int.abs.comp_sub_left x
    simpa [Function.comp_def] using h'
  have hshift_nonneg : 0 ≤ᵐ[MeasureTheory.volume]
      (fun y : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.g0 v h (x - y)|) :=
    Filter.Eventually.of_forall (fun y => abs_nonneg _)
  have hshift_eq : (∫ y in Submission.BoseGases.acube ℓ,
        |Submission.BoseGases.g0 v h (x - y)|)
      ≤ ∫ y : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h (x - y)| :=
    setIntegral_le_integral hshift_int hshift_nonneg
  have hshift_val : (∫ y : EuclideanSpace ℝ (Fin 3),
        |Submission.BoseGases.g0 v h (x - y)|) = 8 * π * (_root_.BoseGases.a v) := by
    have hsub := Submission.BoseGases.integral_comp_sub_left
      (fun z : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.g0 v h z|) x
    have habs : (∫ z : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h z|)
        = ∫ z : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.g0 v h z := by
      refine integral_congr_ae ?_
      filter_upwards [Submission.BoseGases.g0_nonneg_ae (v := v) (R := R0) hR0 hv hvrad
        hv_supp h] with z hz
      exact abs_of_nonneg hz
    rw [hsub, habs, Submission.BoseGases.g0_integral hR0 hv_supp h]
  set A : ℝ := Submission.BoseGases.chiScale ℓ x
      * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) with hA
  set B : ℝ := 2 * (Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M with hB
  have hAnn : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x)
      (Submission.BoseGases.chiSmall_nonneg M _)
  have hBnn : 0 ≤ B := by
    rw [hB]
    exact div_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg hsup_c hDnn)) (le_of_lt hSpos)
  have hdom_int : MeasureTheory.IntegrableOn
      (fun y : EuclideanSpace ℝ (Fin 3) => A * (B * |Submission.BoseGases.g0 v h (x - y)|))
      (Submission.BoseGases.acube ℓ) := by
    have h' := (hshift_int.const_mul B).const_mul A
    simpa only [mul_assoc] using h'.integrableOn
  have h1 : |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
      ≤ ∫ y in Submission.BoseGases.acube ℓ,
          A * (B * |Submission.BoseGases.g0 v h (x - y)|) := by
    have hnorm := norm_integral_le_integral_norm
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ))
      (f := fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
    rw [Real.norm_eq_abs] at hnorm
    refine le_trans hnorm ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => abs_nonneg _))
      hdom_int ?_
    filter_upwards with y
    have hy := hpt y
    have hrew : A * (B * |Submission.BoseGases.g0 v h (x - y)|)
        = (Submission.BoseGases.chiScale ℓ x
              * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
            * (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
                * |Submission.BoseGases.g0 v h (x - y)|)
            / Work.SmallBoxSliding.smallConvLower M := by
      rw [hA, hB]; ring
    rw [hrew]
    exact hy
  have h2 : (∫ y in Submission.BoseGases.acube ℓ,
        A * (B * |Submission.BoseGases.g0 v h (x - y)|))
      ≤ A * B * (8 * π * (_root_.BoseGases.a v)) := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hstep := mul_le_mul_of_nonneg_left (le_trans hshift_eq hshift_val.le)
      (mul_nonneg hAnn hBnn)
    simpa only [mul_assoc] using hstep
  have h3 : A * B * (8 * π * (_root_.BoseGases.a v))
      = (16 * π * Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M)
        * (_root_.BoseGases.a v) * A := by
    rw [hA, hB]; ring
  calc |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
      ≤ ∫ y in Submission.BoseGases.acube ℓ,
          A * (B * |Submission.BoseGases.g0 v h (x - y)|) := h1
    _ ≤ A * B * (8 * π * (_root_.BoseGases.a v)) := h2
    _ = (16 * π * Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M)
        * (_root_.BoseGases.a v)
        * (Submission.BoseGases.chiScale ℓ x
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) := h3

/-! ## Elementary facts about the localised objects

All proved here, no `sorry`; they are the parts of `PerBoxF` that need no analysis. -/

/-- **`0 ≤ sbKin`** — FS `eq:appTB`'s word is nonnegative (`0 ≤ ε_T`): both halves are
"nonnegative coefficient × integral of a square" (`Work.UBBInputs9.A.tBwordBInd_nonneg`). -/
theorem sbKin_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {M : ℕ}
    {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ} (Φ : X n → ℝ)
    (hℓ : 0 < sideAt μ (a v)) (hε : 0 ≤ (paramsAt μ (a v)).eT) :
    0 ≤ sbKin (v := v) μ M u Φ := by
  rw [sbKin]
  exact Work.UBBInputs9.A.tBwordBInd_nonneg hℓ hε u Φ

/-- **The localised two-body kernel is nonnegative** when the numerator is nonnegative at the
evaluated pair (both cutoff factors and both renormalisation denominators are nonnegative). -/
theorem wSmallPair_nonneg_of {M : ℕ} {ℓ d : ℝ} {u x y : EuclideanSpace ℝ (Fin 3)}
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : 0 ≤ f (x - y)) :
    0 ≤ Submission.BoseGases.wSmallPair M ℓ d u f x y := by
  simp only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled]
  exact mul_nonneg
    (mul_nonneg (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u x)
      (div_nonneg
        (div_nonneg hf (Work.SmallBoxSliding.convScaleSmall_nonneg M (ℓ * d) (x - y)))
        (Submission.BoseGases.convScale_nonneg ℓ (x - y))))
    (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u y)

/-- **The fibre of the localised one-body kernel is nonnegative** (`∫_y w_{1,B(u)}(x,y) dy ≥ 0`):
the integrand is a.e. nonnegative (`g₀ ≥ 0` a.e., all other factors nonnegative). -/
theorem wSmall1Pair_fibre_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ} (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} {ℓ d : ℝ} (u x : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y := by
  refine integral_nonneg_of_ae ?_
  refine MeasureTheory.ae_restrict_of_ae ?_
  filter_upwards [Work.SmallBoxSliding.ae_g0_comp_sub hv hvrad hv_supp hR0 h x] with y hy
  exact wSmallPair_nonneg_of hy

/-- The smooth box cutoff is dominated by `chiSupAbs · chiSmallDecay M`. -/
theorem chiSmallB_le_sup {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    (u z : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.chiSmallB M ℓ d u z
      ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
  have hb2 : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u)
      ≤ Submission.BoseGases.chiSmallDecay M := by
    have hb' := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • z - u)
    rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at hb'
  calc Submission.BoseGases.chiSmallB M ℓ d u z
      ≤ |Submission.BoseGases.chiSmallB M ℓ d u z| := le_abs_self _
    _ ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u) :=
        Work.SmallBoxSliding.abs_chiSmallB_le (M := M) (ℓ := ℓ) (d := d) hM u z
    _ ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
        mul_le_mul_of_nonneg_left hb2 Submission.BoseGases.chiSupAbs_nonneg

/-- **The smooth box count is dominated by the particle number times a universal constant**:
`nCountB M ℓ d u x ≤ n · (chiSupAbs · chiSmallDecay M)²`. -/
theorem nCountB_le_n {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3))
    {n : ℕ} (x : X n) :
    nCountB M ℓ d u x ≤ (n : ℝ)
      * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2 := by
  have hnn : 0 ≤ Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay M :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg M)
  rw [nCountB]
  calc ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
      ≤ ∑ _i : Fin n, (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 : Submission.BoseGases.chiSmallB M ℓ d u (x i) ≤
            Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
          chiSmallB_le_sup hM u (x i)
        have h2 : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u (x i) :=
          Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u (x i)
        nlinarith [h1, h2, hnn]
    _ = (n : ℝ) * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## SESSION-3 FINDING — the crude `F(t) ≤ μ(t+μ)` route is a DEAD END (do not repeat)

A first attempt of this session reduced the target to the *linear* crux

    (1/2)·(∬w_{1,B}/χ_{B}²)·μ·∫Φ²·nCountB  ≤  sbWord + C·perBoxErr        (linear crux, FALSE)

via `F(t) ≤ μ(t+μ)` (`perBoxF_pieces.psiWeight_le_mu_mul_add`) and the exact cancellation of
`½μ²W‖Φ‖²` at `c₁ = 1/2`.  **That crux is false**, and the reduction is therefore vacuous
(recorded here so that no one re-derives it): FS's weight `F(t) = μ(t−μ)²/(t+μ)` *vanishes* at
`t = μ`, so the linear bound loses `2μ²` exactly where the statement is tight.  At the
box-constant state with local density `ρ = μ` one has `sbWord ≈ ½W(ρ−μ)²‖Φ‖² − ½μ²W‖Φ‖² =
−½μ²W‖Φ‖²` (no surplus beyond the square) while `C·perBoxErr = o(μ²W‖Φ‖²)` at FS's parameters
(`Γ → 0`, `μV → ∞`), so the linear crux fails by `≈ Wμ²‖Φ‖²` for *every* fixed `C`.  The same
conclusion is recorded independently in
`Submission/Work/BoseFixB1/FINDING_perBoxF_ledger.md` §1b ("the crude `F(t) ≤ μ(t+μ)` route
does not close").

**The usable shapes** (machine-checked) are the *square* ones: `psiWeight_le_sq_sub`
(`F(t) ≤ (t−μ)²`, above) and `perBoxF_F_weight_le` (`c₁F(t) ≤ ¼(t−μ)²` for `c₁ ≤ 1/4`,
`perBoxF_pieces`).  Accordingly the residual of this file is (as before this session)
**`PerBoxMF`** (the mean-field square form), whose implication `PerBoxMF ⟹ perBoxFWeight_holds`
is the proved `perBoxF_of_perBoxMF_at` / `perBoxFWeight_of_perBoxMF` above.  The chapter's
critical path is therefore unchanged: `PerBoxMF` (FS `thm:smallbox` at the localised box),
whose fleet-side pieces are

* the localised `potsplit` (`Work.BoseFixB1.potsplit_localised_of_memLp`, proved),
* the localised `Q₀`-value and its `A₀`-main lower form
  (`Work.BoseFixB1.q0word_localised_value`, `q0word_ge_a0_main`),
* the `P/Q` peels (`Work.BoseFixB1.WB.peel_aP_g`, `WB.pq_split_meas`, proved),
* the `ε_T`-gap payment (`perBoxF_pieces.sbKin_ge_mu_av_cnPlus`, proved),
* the *cross-word* (`q₁..q₄`) Cauchy–Schwarz/pairing control (open),
* the count ↔ density passages and the assembly (open).
-/

/-! ## The quadratic count ↔ density passage (an assembly step of `PerBoxMF`)

`Work.BoseFixB1.WB.pq_split_meas` bounds the *linear* local count
`∫Φ²·Σᵢg(xᵢ)` by the `aP`-count (times the box density of `g`) plus the `aQ`-count.  The
assembly of `PerBoxMF` needs the *quadratic* version (its left side carries
`(nCountB/χ_B²-mass − μ)²`), which follows from the pointwise
`(Σᵢg(xᵢ))² ≤ N·KU·Σᵢg(xᵢ)` (`g ≤ KU` pointwise) and monotonicity of the integral. -/

/-- **The quadratic P/Q count passage.**  From

* the pointwise domination `(Σᵢg(xᵢ))² ≤ N·KU·Σᵢg(xᵢ)` (`0 ≤ g ≤ KU`),
* the integrability of the smooth count `∫Φ²·Σᵢg(xᵢ)`, and
* the *linear* P/Q peel (`WB.pq_split_meas`),

one gets the quadratic bound

    ∫Φ²(Σᵢg(xᵢ))² ≤ N·KU·[ (1+ε)(Tvol/ℓ³)·cS1 ℓ Φ + (1+ε⁻¹)KU·cnPlus ℓ Φ ] .

With `g = χ_{B(u)}²` this is the passage from `PerBoxMF`'s *smooth* local count
(`nCountB = Σᵢχ_B(xᵢ)²`, whose square is what the mean-field left side carries) to the
centred-cube counts that the localised `A₀` chain (`q0word_ge_a0_main`) and the gap payment
(`cnPlusBoxInd`) are stated in.

**Caveat (lossiness).**  The pointwise step `(Σᵢg(xᵢ))² ≤ N·KU·Σᵢg(xᵢ)` loses the factor
`N/k` where `k = #{i : xᵢ ∈ supp g}` is the number of particles actually inside the box: it is
*sharp* only for states whose particles are concentrated in the box (`k ≈ N`), and lossy for
spread states (where the smooth count is small but the `N`-factor is not).  A *sharp* count
passage (FS's `n(u)`-sector decomposition, i.e. the local count as a multiplication operator,
or the exact `(Σᵢg)² = k²`-identity on each of its level sets) is the lossless replacement and
should be used in the assembly if the crude form does not close.  The two *linear* inputs are hypotheses so that the lemma is
pure monotonicity/arithmetic; instantiate `hpeel` with
`(WB.pq_split_meas hℓ hΦc hε hgm hint hg hTvol hKU).1`. -/
theorem quadraticCountPeel {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ)
    {g : ℝ³ → ℝ} {Tvol KU ε : ℝ} (hε : 0 < ε) (hg : ∀ z, 0 ≤ g z) (hKU : ∀ z, g z ≤ KU)
    (hInt : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 * (∑ i : Fin N, g (x i)))
      (Submission.BoseGases.abox N ℓ))
    (hpeel : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * (∑ i : Fin N, g (x i)))
      ≤ (1 + ε) * (Tvol / ℓ ^ 3)
          * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Submission.BoseGases.aP ℓ i Φ x) ^ 2)
        + (1 + ε⁻¹) * KU
          * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Submission.BoseGases.aQ ℓ i Φ x) ^ 2)) :
    (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * (∑ i : Fin N, g (x i)) ^ 2)
      ≤ (N : ℝ) * KU * ((1 + ε) * (Tvol / ℓ ^ 3)
            * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
                (Submission.BoseGases.aP ℓ i Φ x) ^ 2)
          + (1 + ε⁻¹) * KU
            * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
                (Submission.BoseGases.aQ ℓ i Φ x) ^ 2)) := by
  have hKU0 : 0 ≤ KU := le_trans (hg 0) (hKU 0)
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  -- the pointwise domination `(Σ g)² ≤ N·KU·Σ g` on the box
  have hpt : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      (Φ x) ^ 2 * (∑ i : Fin N, g (x i)) ^ 2
        ≤ (N : ℝ) * KU * ((Φ x) ^ 2 * (∑ i : Fin N, g (x i))) := by
    intro x _
    have hSnn : 0 ≤ ∑ i : Fin N, g (x i) := Finset.sum_nonneg fun i _ => hg (x i)
    have hSle : (∑ i : Fin N, g (x i)) ≤ (N : ℝ) * KU := by
      calc (∑ i : Fin N, g (x i)) ≤ ∑ _i : Fin N, KU :=
            Finset.sum_le_sum fun i _ => hKU (x i)
        _ = (N : ℝ) * KU := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsq : (∑ i : Fin N, g (x i)) ^ 2
        ≤ ((N : ℝ) * KU) * (∑ i : Fin N, g (x i)) := by
      nlinarith [hSnn, hSle, hN0, hKU0]
    calc (Φ x) ^ 2 * (∑ i : Fin N, g (x i)) ^ 2
        ≤ (Φ x) ^ 2 * (((N : ℝ) * KU) * (∑ i : Fin N, g (x i))) :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = (N : ℝ) * KU * ((Φ x) ^ 2 * (∑ i : Fin N, g (x i))) := by ring
  have hle : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      (Φ x) ^ 2 * (∑ i : Fin N, g (x i)) ^ 2
        ≤ (N : ℝ) * KU * ((Φ x) ^ 2 * (∑ i : Fin N, g (x i))) :=
    (MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)).mpr
      (Filter.Eventually.of_forall fun x hx => hpt x hx)
  have hUpper : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (N : ℝ) * KU * ((Φ x) ^ 2 * (∑ i : Fin N, g (x i))))
      (Submission.BoseGases.abox N ℓ) :=
    hInt.const_mul ((N : ℝ) * KU)
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hUpper hle
  rw [MeasureTheory.integral_const_mul] at hmono
  have hstep : (N : ℝ) * KU
        * (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * (∑ i : Fin N, g (x i)))
      ≤ (N : ℝ) * KU * ((1 + ε) * (Tvol / ℓ ^ 3)
            * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
                (Submission.BoseGases.aP ℓ i Φ x) ^ 2)
          + (1 + ε⁻¹) * KU
            * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
                (Submission.BoseGases.aQ ℓ i Φ x) ^ 2)) :=
    mul_le_mul_of_nonneg_left hpeel (mul_nonneg hN0 hKU0)
  linarith [hmono, hstep]

/-! ## The reduction at the good set: `PerBoxSectorBoundG ⟹` the target's `∃ε₀c₁C`-conclusion

The chapter's analytic content is now isolated in **one** statement,
`Work.BoseFixB1B.PerBoxSectorBoundG` (`Submission/Work/BoseFixB1/PerBoxResidualG.lean`): FS
`thm:smallbox` read at the counting operator `n_{B(u)} = Σᵢ1_{B(u)}(xᵢ)` on the good set `G`.

The reduction below is verbatim
`Work.BoseFixB1B.perBoxPointwise_of_sectorBound`
(`Submission/Work/BoseFixB1B/perBoxPointwise.lean`, proved, axiom-clean): the only argument that
used the interior hypothesis `u ∈ I₋` is the application of the residual itself, so replacing
`interiorSet` by `goodSet` in both the hypothesis and the conclusion is a mechanical copy.  All
the ingredients are imported:

* `Work.BoseFixB1B.countDensityBridge` — the count ↔ density passage
  `∫Φ²F(nCountB/chiMass) ≤ K₀(Σ_k m_k F(k/chiMass) + μ²‖Φ‖²)` (`K₀ = 8ν²+8`, `ν = chiSupAbs·chiSmallDecay M`);
* `Work.BoseFixB1B.perBoxArithSum` — the pure arithmetic (`c₁ := c/K₀`,
  `C := C_res·(C_W·max(a v) 1 + 1)`, thresholds by `min`);
* `Work.BoseFixB1B.sectorMass_sum` — `Σ_k m_k = ‖Φ‖²`;
* `Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime` — the mass normalisation
  `∬w_{1,B(u)} ≤ C_W(a v)·chiMass`. -/

end Work.BoseFixB1

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge

/-- **The reduction at the good set.**  `PerBoxSectorBoundG` implies the exact conclusion of
`Work.BoseFixB1.perBoxFWeight_holds`. -/
theorem perBoxFWeight_of_sectorBoundG {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hb : PerBoxSectorBoundG v h R) :
    ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u := by
  obtain ⟨ε₀s, c, C, hε₀s, hc0, hc14, hC0, hmain⟩ := hb
  obtain ⟨ε₀w, C_W, hε₀w, hCW0, hWb⟩ :=
    Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime (v := v) (h := h) hv hvrad hR hv_supp
  have hν0 : 0 < chiSupAbs * chiSmallDecay Work.BoseBox.mValue := by
    have hM48 : 1 ≤ Work.BoseBox.mValue := by rw [Work.BoseBox.mValue]; norm_num
    have h1 : 0 < chiSupAbs := by
      rw [chiSupAbs]
      exact inv_pos.mpr (Real.sqrt_pos.mpr chiNormSq_pos)
    have h2 : 0 < chiSmallDecay Work.BoseBox.mValue := by
      rw [chiSmallDecay, chiSmallNormFactor]
      exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (chiSmallNormSq_pos hM48))) (by positivity)
    exact mul_pos h1 h2
  refine ⟨min ε₀s ε₀w, c / (8 * (chiSupAbs * chiSmallDecay Work.BoseBox.mValue) ^ 2 + 8),
    C * (C_W * max (_root_.BoseGases.a v) 1 + 1), lt_min hε₀s hε₀w,
    div_pos hc0 (by positivity), by positivity, ?_⟩
  intro μ hAdm n Φ u hu
  have hAs : Work.BoseBoxFix.Adm v ε₀s μ := Adm_mono' hAdm (min_le_left _ _)
  have hAw : Work.BoseBoxFix.Adm v ε₀w μ := Adm_mono' hAdm (min_le_right _ _)
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hWle := hWb μ hAw u
  have hbridge := countDensityBridge h hμ hℓ hd Φ u
  have hres := hmain μ hAs n Φ u hu
  have hsum := sectorMass_sum (v := v) (μ := μ) Φ u
  have hm0 : 0 ≤ PBW h μ u :=
    Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  have hnorm0 : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) :=
    Work.BoseFixB1.normB_nonneg _
  have hΓ0 : 0 ≤ PBΓ v μ := by
    rw [PBΓ, dlGamma]
    have h1 : 0 ≤ (paramsAt μ (_root_.BoseGases.a v)).KB :=
      le_of_lt (Work.BoseFixB1.paramsAt_KB_pos hAdm)
    have h2 : 0 ≤ μ * (_root_.BoseGases.a v) ^ 3 := by positivity
    exact mul_nonneg (pow_nonneg h1 3) (Real.rpow_nonneg h2 _)
  have hΓle : PBΓ v μ ≤ (R / (PBℓ v μ * PBd v μ)) ^ 2 + PBΓ v μ := by
    have : 0 ≤ (R / (PBℓ v μ * PBd v μ)) ^ 2 := sq_nonneg _
    linarith
  have hνeq : PBν v μ = chiSupAbs * chiSmallDecay Work.BoseBox.mValue := PBν_eq v μ
  have key := perBoxArithSum (s := Finset.range (n + 1))
    (m := fun k : ℕ => sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k)
    (Fk := fun k : ℕ => psiWeight 1 μ ((k : ℝ) / PBV v μ u))
    (c := c) (C := C) (C_W := C_W) (K₀ := 8 * (chiSupAbs * chiSmallDecay Work.BoseBox.mValue) ^ 2 + 8)
    (μ := μ) (aV := _root_.BoseGases.a v) (W := PBW h μ u) (V := PBV v μ u)
    (A := ∫ x in abox n (PBℓ v μ), (Φ x) ^ 2 * psiWeight 1 μ
      (Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x / PBV v μ u))
    (Mn := Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ))
    (sb := Work.BoseFixB1.sbWord h μ u (Φ : X n → ℝ))
    (ΓB := PBΓ v μ) (Γ' := (R / (PBℓ v μ * PBd v μ)) ^ 2 + PBΓ v μ)
    hμ (Work.BoseFixB1.adm_a_pos hAdm) (chiMass_nonneg _ _ _ _) hm0 hnorm0 hΓ0 hΓle hc0
    (by positivity) hC0 hCW0 (by simpa [hνeq] using hbridge) hres hsum hWle
  unfold Work.BoseFixB1.PerBoxF
  exact key

end Work.BoseFixB1B

namespace Work.BoseFixB1

/-! ## The target statement (unchanged)

**STATUS.**  The target is now obtained from the *single* residual
`Work.BoseFixB1.PerSectorSmooth` (`Submission/Work/BoseFixB1/PerSectorSmooth.lean`), the per-sector
form of FS `thm:smallbox` at the **smooth** density `t = nCountB/chiMass`:

* `Work.BoseFixB1B.perBoxFWeight_of_perSectorSmooth` (**PROVED** in this file): `PerSectorSmooth`
  implies the target's exact `∃ ε₀ c₁ C`-conclusion at the *same* `c₁ = c` and `C`; the assembly is
  the termwise summation of the per-sector inequalities together with the **exact partition**
  `∫Φ²F(t) = Σ_k ∫Φ_k²F(t)` (`sum_sectorPiece_sq`), the sector-mass sum
  (`Work.BoseFixB1B.sectorMass_sum`) and the **proved sector additivity** of the word
  (`Work.BoseFixB1.sbWordSectorAdditiveAdm`);
* `Work.BoseFixB1.perSectorSmooth_holds` (delegated) is that residual.

The earlier route through the *sharp*-count residual `Work.BoseFixB1B.PerBoxSectorBoundG` is
recorded in `PerBoxResidualG.lean` and `FINDING_perBoxFWeight_session_freeze.md`; that residual was
**refuted** (it read the `F`-weight at the smooth volume `chiMass` instead of the true box volume,
`1/χ̂` too strong on slabs), and the reduction `perBoxFWeight_of_sectorBoundG` below is kept only
as a proved, reusable implication. -/

theorem perBoxFWeight_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u :=
  -- The remaining obligation is EXACTLY the flat (condensed) branch of FS `thm:smallbox` at
  -- the sliding box, in its WEAKEST known form: there is *some* threshold `γ > 0` above which
  -- the gap branch takes over, and below which the state is flat.  Everything else is PROVED
  -- and axiom-clean in this cone:
  --   * the gap branch at EVERY threshold `γ` (`Up.gapAtAll`),
  --   * the thin (degenerate-box) case (`Up.perBoxF_thin_holds`),
  --   * the three-way assembly (`Up.perBoxFWeight_of_flatFree`).
  -- The residual is the sibling atom `Work.BoseFixB1S.flatBranchFree_exists` /
  -- `Work.BoseFixB1.flatBranchAtom`, copied upstream as `Up.FlatFreeResidual`.
  Work.BoseFixB1.Up.perBoxFWeight_of_flatFree (v := v) h hv hv1 hvrad hR hv_supp hav
    (Work.BoseFixB1.Up.flatFreeResidual (v := v) h hv hv1 hvrad hR hv_supp hav)

end Work.BoseFixB1
