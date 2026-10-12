import ChallengeDeps
import Submission.Work.BoseBoxFix.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.AprioriCount.Defs` — the vocabulary of the multiplicative count window

The target `Work.AprioriCount.cubeCountWindow` asks for the **multiplicative count window**

    n · ‖Φ‖² ≤ C · ℓ³ · ‖Φ‖²        (`ℓ = sideAt μ (a v)`)

on FS's low box states (`IsLowB`, FS `eq:aprioriPsi`).  This module carries the two objects the
*reduction* of that target to the classical Dyson-type mean-field bound uses, together with the
two elementary transfer statements that the reduction consumes.  Nothing here is analytic: the
only content is the χ-mass of a state and the two interfaces.

**The reduction** (see `FINDING_cubeCountWindow.md` and `cubeCountWindow.lean`):

* `chiCount ℓ Φ` — the χ-mass `∫_{abox} Φ² Σᵢ χ_ℓ(xᵢ)`; the chemical kernel
  `wLoc ℓ (g₀) 0 x y = χ(x/ℓ)·wScaled(x−y)·χ(y/ℓ)` carries `χ(x/ℓ)` in the particle's **own**
  coordinate, so the one-body mass `M₁` is controlled by `chiCount`;
* `ChiDysonBound v h R` — the **χ-weighted crude (Dyson-type) mean-field lower bound** on low box
  states: on `IsLowB` states, `kinFormB + pairPartB ≥ c·(a v)·(chiCount)²/(ℓ³·normB)`.  This is
  *strictly weaker* than the corpus's `(E)` (`kinFormB + pairPartB ≥ c·(a v)·n(n−1)ℓ^{-3}·normB`),
  which is machine-checked *equivalent* to the sharp count window; it is the honest missing input;
* `ChemMassLeChiMass v h R` — `M₁ ≤ K₀·chiCount` (elementary: the kernel factorises through
  `χ(x/ℓ)`);
* `FlatLeChi v h R` — the flat (box-constant) part is visible: `κ·Σᵢ∫(aP ℓ i Φ)² ≤ chiCount` for a
  fixed `κ > 0` (the window's volume fraction).

The corpus's *proved* budget (`Work.BoseFixB1B.boxFormB_budgetAlt`) and gap column
(`Work.BoseFixB1S.kinFormB_ge_gapColumn_boxState`, `b = 1/16`) together with
`ChiDysonBound + ChemMassLeChiMass + FlatLeChi` give the target, with a **fixed** constant `C`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.AprioriCount

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The χ-mass of a box state**: `∫_{abox n ℓ} Φ² · Σᵢ χ_ℓ(xᵢ)`, the configuration integral of
`|Φ|²` against the sum of the (ℓ-scaled, L²-normalised) localization functions `χ_ℓ`.

This is the quantity that the whole-box chemical kernel `wLoc ℓ (g₀) 0 x y` sees: that kernel
factorises as `χ_ℓ(x) · wScaled(x−y) · χ_ℓ(y)`, so a particle at `xᵢ` collects the chemical gain
`χ_ℓ(xᵢ)·(…)`.  In particular `M₁ ≤ K₀·chiCount` (`ChemMassLeChiMass`). -/
noncomputable def chiCount {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∫ x in Submission.BoseGases.abox n ℓ,
    (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i)

/-- **The χ-weighted crude (Dyson-type) mean-field lower bound for low box states.**  There are
`c > 0` and `ε₀ > 0` such that every `IsLowB` box state satisfies

    c · (a v) · (chiCount ℓ Φ)² ≤ (kinFormB + pairPartB) · ℓ³ · normB ,    `ℓ = sideAt μ (a v)`.

*Not* elementary: this is the classical mean-field bound in its χ-weighted form, whose proof must
pay the correlation ("close pairs") case by kinetic energy.  It is *strictly weaker* than the
corpus's `(E) = kinFormB + pairPartB ≥ c(a v)n(n−1)ℓ⁻³‖Φ‖²` (which uses the total count `n` and the
scalar coupling, and is machine-checked *equivalent* to FS's particle window), and it is *not*
refuted by the annulus/packed counterexample: that state has `wordB > 0`, hence fails `IsLowB`. -/
def ChiDysonBound (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ J : ℝ, Work.UBB.lhyC ≤ J →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n (Φ : Submission.BoseGases.X n → ℝ) →
            c * (_root_.BoseGases.a v)
                * (chiCount (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Φ : Submission.BoseGases.X n → ℝ)) ^ 2
              ≤ (Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
                    (Φ : Submission.BoseGases.X n → ℝ)
                  + Work.BoseKinLoc.pairPartB n v (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Φ : Submission.BoseGases.X n → ℝ))
                * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)

/-- **The one-body (chemical) mass is controlled by the χ-mass.**  The kernel
`wLoc ℓ (g₀ v h) 0 x y = χ_ℓ(x)·wScaled(x−y)·χ_ℓ(y)` carries `χ_ℓ` in the particle's own
coordinate, so with `K₀ = sup_x ∫_y |wScaled(x−y)|·χ_ℓ(y) dy` (finite at FS's parameters),

    M₁ = ∫_{abox} Φ² · Σᵢ ∫_y wLoc ℓ (g₀ v h) 0 (xᵢ) y dy ≤ K₀ · chiCount ℓ Φ .

The statement is restricted to `IsLowB` states (the same guard as `ChiDysonBound`): the
*unguarded* form is the elementary factorisation, but the finiteness of `K₀` uniformly in `μ` is
exactly where the corpus's regime hypothesis `R ≤ ℓ·chiR0` (`w1c_fibre_acube_abs_le`,
`exists_adm_chiR0_ge`) enters, so the honest interface carries the guard and the `ε₀`-triggered
regime. -/
def ChemMassLeChiMass (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ K₀ ε₀ : ℝ, 0 ≤ K₀ ∧ 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ J : ℝ, Work.UBB.lhyC ≤ J →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n (Φ : Submission.BoseGases.X n → ℝ) →
            (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (Φ x) ^ 2 *
                  ∑ i : Fin n, ∫ y : E3,
                    Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Submission.BoseGases.g0 v h) 0 (x i) y)
              ≤ K₀ * chiCount (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Φ : Submission.BoseGases.X n → ℝ)

/-- **The flat (box-constant) part is visible.**  With `S := Σᵢ ∫_{abox} (aP ℓ i Φ)²` the flat
count and `chiCount` the χ-mass, there is a fixed `κ > 0` with

    κ · S ≤ chiCount ℓ Φ .

A box-constant contribution to the wave function is spread over the whole cube, hence sees the
window: its χ-mass is the window's volume fraction `(∫χ)/|acube ℓ| > 0` times its flat mass.  The
statement is restricted to `IsLowB` states: the *unguarded* form is false (a state concentrated in
a cube corner has `chiCount = 0` while its flat (slice-mean) part is positive — the reviewers'
counterexample), and the guard is exactly what excludes it (`wordB = kinFormB ≥ 0` there). -/
def FlatLeChi (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ κ ε₀ : ℝ, 0 < κ ∧ 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ J : ℝ, Work.UBB.lhyC ≤ J →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n (Φ : Submission.BoseGases.X n → ℝ) →
            κ * (∑ i : Fin n,
                ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                  (Submission.BoseGases.aP (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) i
                    (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)
              ≤ chiCount (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Φ : Submission.BoseGases.X n → ℝ)

/-- **The trade-off budget for low box states** (`Work.BoseFixB1B.boxFormB_budgetAlt` with its two
`IntegrableOn` interfaces discharged for `BoxState`s).  `IsLowB` says

    wordB = boxFormB ≤ ℓ³·Theta (a v) J μ·‖Φ‖² = −4πμ²(a v)ℓ³(1 − J√(μ(a v)³))·‖Φ‖²

and the splitting `boxFormB = kinFormB + chemPartB + pairPartB` with
`chemPartB = −μ·M₁` (`M₁` the one-body mass of `ChemMassLeChiMass`) turns this into

    kinFormB + pairPartB + 4πμ²(a v)ℓ³(1 − J√(μ(a v)³))‖Φ‖² ≤ μ·M₁ .

This is the corpus's **proved** `boxFormB_budgetAlt`, restated without its two integrability
hypotheses (which hold for the smooth `BoxState`s of this chapter). -/
def BoxBudget (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ J : ℝ, Work.UBB.lhyC ≤ J →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n (Φ : Submission.BoseGases.X n → ℝ) →
            Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
                (Φ : Submission.BoseGases.X n → ℝ)
              + Work.BoseKinLoc.pairPartB n v (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Φ : Submission.BoseGases.X n → ℝ)
              + 4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v)
                  * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
                  * (1 - J * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3))
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              ≤ μ * (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                  (Φ x) ^ 2 *
                    ∑ i : Fin n, ∫ y : E3,
                      Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Submission.BoseGases.g0 v h) 0 (x i) y)

end Work.AprioriCount
