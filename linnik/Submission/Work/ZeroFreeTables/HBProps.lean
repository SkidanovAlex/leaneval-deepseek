/-
# ZeroFreeTables — HBProps.lean

The paper's results of AREA 3 (Heath-Brown's zero-free region theorems and his
tables) as `Prop`s in the vocabulary of the frozen contract, i.e. the interface
that `Derive.lean` consumes to produce `ZeroFreeCert`.

Each `Prop` is exactly the paper's claim, with the existential `q₀` made explicit
and with the tables of `Tables.lean` read in the paper's sense: an entry
`(a, v)` of a table means *"if `λ₁ ≤ a` then the corresponding `λ` is `≥ v`"*.

**Hypotheses.**  The paper's `λ₁` is HB's §6 numbering, i.e. the minimum of `λ` over
the zeros of the *rectangle* (6.1), so every `Prop` whose proof uses that numbering
carries the minimality `IsMin1WideAt 10 χ₁ ρ₁` (`API.lean`: `IsMin1` together with
minimality over the strip `|Im| ≤ 10`, the predicate that the round-2 contract
`LinnikContract2` supplies) and *not* the frozen working-region minimality.  Only `XYLemma3_8` (an [X] statement, which needs no minimality at all) is stated
without the wider hypothesis; the assembly carries the frozen working-region
hypotheses in its own statements and derives `IsMin1Wide` at each use site from the
bridge `HBWideMin` (`API.lean`).
-/
import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.ZeroFreeTables.Defs
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.Tables

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-- The real-valued (coerced) version of a table of rational pairs. -/
def tableR (l : List (ℚ × ℚ)) : List (ℝ × ℝ) := l.map (fun p => ((p.1 : ℝ), (p.2 : ℝ)))

/-! ## The tables of the §15 range -/

/-- **HB Table 8** (p. 54): `λ₀` in the complex case (`χ₁` or `ρ₁` complex).
(The printed entry at `λ₁ = 0.66` is a typo — see `Tables.lean`; `hbTable8` carries
the corrected value `0.738`.  This `Prop` is *proved* below the engine, see
`Work.ZeroFreeTables.HBTable8_of_engine`.) -/
def HBTable8 : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
    ∀ p ∈ tableR hbTable8, lamOf q ρ₁ ≤ p.1 → Lam0Bound χ₁ ρ₁ p.2

/-- **HB Table 4** (p. 43): `λ₀` in the real case (`χ₁` and `ρ₁` real). -/
def HBTable4 : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
    ∀ p ∈ tableR hbTable4, lamOf q ρ₁ ≤ p.1 → Lam0Bound χ₁ ρ₁ p.2

/-- **HB Table 9** (p. 55) as used through Lemma 9.2: `λ_j` in the complex case,
for `χ_j` of order at least `3` (i.e. `χ_j ≠ χ₀, χ₁^{±1}, χ₂^{±1}`).

The hypothesis is `χ₁² ≠ 1`, i.e. `χ₁` complex: HB (p. 55) proves Lemma 9.2 only "if
`χ₁² ≠ χ₀`, `χ_j`, `χ̄_j`", i.e. "unless `χ₁` is real", so Table 9 is not claimed in the
real case (there the assembly uses HB Lemmas 8.8 and 9.4 instead, or the row is
vacuous by `XYLemma3_8`). -/
def HBTable9 : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 →
    ∀ p ∈ tableR hbTable9, lamOf q ρ₁ ≤ p.1 → Lam3Bound χ₁ p.2

/-- **HB Lemma 9.4** (p. 56): the bounds of Table 10 apply in *all* cases
(complex or real `χ₁`).  In particular `λ₂ ≥ 0.702`. -/
def HBLemma9_4 : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ →
    ∀ p ∈ tableR hbTable10, lamOf q ρ₁ ≤ p.1 → Lam2Bound χ₁ p.2

/-- **HB Table 7** (p. 47): `λ₂` in the real case (`χ₁` and `ρ₁` real). -/
def HBTable7 : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 → lamOf q ρ₁ < 696/1000 →
    ∀ p ∈ tableR hbTable7, lamOf q ρ₁ ≤ p.1 → Lam2Bound χ₁ p.2

/-- **ROUTE_LEAD §4.3**: HB Lemma 8.7 recomputed with `φ(χ₁) = 1/3` (the version
of Table 7 that does not need the small-order Burgess input). -/
def HBTable7phi3 : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
    ∀ p ∈ tableR hbTable7phi3, lamOf q ρ₁ ≤ p.1 → Lam2Bound χ₁ p.2

/-! ## The Deuring–Heilbronn range `λ₁ < 0.348` -/

/-- **HB Lemma 8.4** (p. 46): for `χ₁`, `ρ₁` real,
`λ₀ ≥ 2 log(1/λ₁)` for `λ₁ ≤ 0.2`, and `λ₀ ≥ max((3/2)log(1/λ₁), 1.294)` in general.

Stated in the paper's `ε`-form: HB proves `λ₀ ≥ (2 − ε) log(λ₁⁻¹)` for `q ≥ q(ε)`, and —
since `q₀` depends on `ε` — the `ε = 0` form `λ₀ ≥ 2 log(1/λ₁)` is *not* implied (a
colleague's criticism; HB Lemma 8.1 genuinely allows the loss).  The assembly only uses
the second conjunct, `λ₀ ≥ max((3/2) log(1/λ₁), 1.294)`, which is ε-free.

**Cap.**  HB's own §8 method (the smoothed explicit formula, whose admissible region is
`|Re s − 1| ≤ √(log log q)/log q`) proves this only for `λ₁` bounded below — his closing
remark to §8 — and his λ₁-uniform statement is **capped**: Theorem 4 (p. 4) gives
`λ₀ ≥ min{(2 − ε)log(1/λ₁), (1/3)log log log q}`.  The uncapped form stated here is the
*classical* Deuring–Heilbronn repulsion (Landau–Page with Graham's sieve / the log-free
zero-density estimate); the project records that input as `RepelResidual`
(`Submission/Work/LinnikAreas/dhRepelOtherChar.lean`).  It is what the frozen `Z5rep`
needs, and a prover should treat it as the deep input it is rather than expect it from
HB §8. -/
def HBLemma8_4 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 → lamS ≤ lamOf q ρ₁ →
    (lamOf q ρ₁ ≤ 2/10 → Lam0Bound χ₁ ρ₁ ((2 - ε) * Real.log (1 / lamOf q ρ₁))) ∧
    Lam0Bound χ₁ ρ₁ (max (3/2 * Real.log (1 / lamOf q ρ₁)) (1294/1000))

/-- **HB Lemma 8.8** (p. 47): for `χ₁`, `ρ₁` real and `λ₁ ≤ 1`,
`λ₂ ≥ (12/11 − ε) log(1/λ₁)` for `q ≥ q(ε)` and `λ₂ ≥ 0.745` for large `q`.

Stated in the paper's `ε`-form, for the same reason as `HBLemma8_4` (a colleague's
criticism): the `ε = 0` form `λ₂ ≥ (12/11)log(1/λ₁)` is not implied by the paper's
statement, since the threshold `q₀` depends on `ε`.  HB's §8 estimates are restricted to
zeros `ρ₂` in the rectangle (6.1) — his closing remark to §8 — and his λ₁-uniform
statement (Theorem 4) is **capped** at `(1/3)log log log q`; the uncapped λ₁-uniform form
stated here is again the *classical* Deuring–Heilbronn repulsion (the input the project
records as `RepelResidual`), which is what the frozen `Z5rep` needs.  The assembly uses
the log-conjunct with `ε = 1/100`.

**The hypothesis `lamOf q ρ₁ ≤ 1` is necessary** (a delegated prover refuted the form
without it): for `ε > 12/11` and `λ₁ > 1` the target `(12/11 − ε)·log(1/λ₁)` is
`(ε − 12/11)·log λ₁ > 0`, a bound growing in `λ₁`, while the hypotheses give only
`λ₂ ≥ λ₁` (`IsMin1WideAt 10`'s minimality); `λ₁ = 3`, `ε = 5` is a counterexample.  HB's
§8 tables cover `λ₁ ≤ 0.809`, so the restriction is harmless (the assembly only ever calls
it with `λ₁ < 0.348`). -/
def HBLemma8_8 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 → lamS ≤ lamOf q ρ₁ →
    lamOf q ρ₁ ≤ 1 →
    Lam2Bound χ₁ ((12/11 - ε) * Real.log (1 / lamOf q ρ₁)) ∧
      (lamOf q ρ₁ < 696/1000 → Lam2Bound χ₁ (745/1000))

/-- **HB §6/§8/§9, repeated-zero case.**  If `ρ₁` is a zero of `χ₁` of multiplicity
`≥ 2` (so that the "second zero" of `χ₁` coincides with `ρ₁`, and the tables'
`λ₀` is `λ₁` itself), then the same arguments give the tables' bounds for `λ₁`:
here, the universal bound `λ₁ ≥ 1.724` for `λ₁ ≤ 0.7` of HB Table 4.

In the repeated case the multiplicity sharpens the `P₃(1)`/`F(0)` terms, which is
why the inequality is not the `ρ₀ = ρ₁` instance of `HBLemma9_1`; the exact
repeated-case inequality of HB §6 (ε) is the remaining piece of the `P₃` engine.

**Route (added after a colleague's review).**  In the *real-real* case (`χ₁² = 1`,
`ρ₁.im = 0`) the claim is HB Table 4's entry `(0.7, 1.724)`: it is the multiplicity
conjunct of `Lam0Bound χ₁ ρ₁ (1724/1000)` for `λ₁ ≤ 0.7`, so it follows from
`HBTable4` alone (`hbRepZero_of_table4` in `ZeroFreeTables.HBRepZero_red`).  In the
remaining cases (`χ₁` complex, or `ρ₁` non-real) the sharper value is *not* available
from HB's §6 discussion — which treats the real-real case — but the weaker bound
`λ₁ ≥ 0.696` is: HB **Theorem 2** says that `∏_{χ mod q} L(s,χ)` has at most two zeros,
counted with multiplicity, in `σ ≥ 1 − 0.696/log q`, `|t| ≤ 1`, while a multiple zero
of a pair that is not real-real contributes at least *four* counted zeros there (`χ₁`
and `χ̄₁` each with multiplicity `≥ 2` when `χ₁` is complex; `ρ₁` and `ρ̄₁ ≠ ρ₁` each
with multiplicity `≥ 2` when `ρ₁` is non-real).  A prover should therefore either
restrict the statement to the real-real case, or derive the general form from that
Theorem-2 count. -/
def HBRepZero : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 → 2 ≤ zeroMult χ₁ ρ₁ →
    lamOf q ρ₁ ≤ 7/10 → 1724/1000 ≤ lamOf q ρ₁

/-- **The multiplicity conjunct outside the real-real case.**  If `(χ₁,ρ₁)` is *not* a
real-real pair and `ρ₁` is a zero of multiplicity at least two, then `λ₁ ≥ 0.696`.

This is the consequence of **HB Theorem 2** that the contract needs: HB's Theorem 2 says
that `∏_{χ mod q} L(s,χ)` has at most two zeros, counted according to multiplicity, in
`σ ≥ 1 − 0.696/log q`, `|t| ≤ 1`, while a multiple zero of a pair that is not real-real
contributes at least *four* counted zeros there — `χ₁` and `χ̄₁` each with multiplicity
`≥ 2` when `χ₁` is complex, and `ρ₁` and `ρ̄₁ ≠ ρ₁` each with multiplicity `≥ 2` when `ρ₁`
is non-real.  (In the excluded real-real case the sharper Table 4 entry `1.724` applies
instead; that is `HBRepZero`.)

The sharpness of `0.696` is not an accident: it is the last row of Table 8, the tangency
point of (9.13), and HB §15 uses `λ₀ ≥ 0.696` as the universal bound. -/
def HBRepZeroC : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) → 2 ≤ zeroMult χ₁ ρ₁ →
    lamOf q ρ₁ ≤ 7/10 → 696/1000 ≤ lamOf q ρ₁

/-- **HB Lemma 10.3**, conclusion form with the contract's margin `1/1000`:
for `q` large enough, every character outside two conjugate pairs has no zero
with `λ < 6/7 - 1/1000` in the working region. -/
def HB10_3_conclusion : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ → Lam3Bound χ₁ (6/7 - 1/1000)

/-! ## HB Theorem 1 (the `λ₁ < 0.348` region) and [X] Lemma 3.8 -/

/-- **The off-axis case of `ZeroFreeCert` (the round-2 assembly input).**

Round 2 numbers `λ₁` over the *wide* region `|Im| ≤ 50`, so the numbered zero `ρ₁` need not lie
in the working region `|Im| ≤ 1`.  The local engine of HB §§6–10 handles the on-axis case
(`|Im ρ₁| ≤ 1`, where the windows reach height `≤ 4 + δ` and the frozen Propositions of this
area apply); for the *off-axis* case the windows reach `4|γ₁| + δ`, beyond the local arguments,
and HB's tables are used at the §6 (rectangle) level instead.  The audit
(`ENGINE_AUDIT_LEAD.md` §4) records that case as TRUE by HB (Lemma 9.5 at the rectangle level for
`Z1`, the table Props plus fact (B) and Theorems 2(b)/3 at the rectangle level for `Z2`–`Z4`;
`Z5` is vacuous there once `Z1` holds) but *not* reachable by the local Propositions.  This
single `Prop` is that input: the five clauses of `ZeroFreeCert` for the off-axis pairs. -/
def HBOffAxis : Prop := ZeroFreeCertOffAxis

/-- **HB Theorem 1** (p. 3).  Below `0.348/log q` the function `∏_{χ mod q} L(s,χ)`
has at most one zero in `σ ≥ 1 - 0.348/log q`, `|t| ≤ 1`; such a zero is real,
simple, and belongs to a real non-principal character.

This is `Z1` of the contract. -/
def HBTheorem1 : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ → Z1 χ₁ ρ₁

/-- **[X] Lemma 3.8** (Xylouris, arXiv:0906.2749; the `ord χ₁ = 2` case of the
`λ₁`-estimates): if `χ₁` is real and `ρ₁` is not, then `λ₁ ≥ 0.628`.  HB's own
Lemma 9.5 gives only `0.518`, which is not enough for the assembly.

The minimality hypothesis is part of Xylouris's setting: the claim is about the
*exceptional* zero `λ₁` of a real character, so `(χ₁,ρ₁)` must be a zero of the working
region of maximal real part (a bare "`χ₁² = 1 ∧ ρ₁.im ≠ 0`" would be satisfied by
`χ₁ = 1`, `ρ₁ = 2 + i`, where `lamOf < 0`). -/
def XYLemma3_8 : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im ≠ 0 → 628/1000 ≤ lamOf q ρ₁

end Work.ZeroFreeTables
