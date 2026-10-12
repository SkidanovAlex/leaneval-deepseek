import ChallengeDeps
import Submission.Work.BoseFixB1.AprioriPieces
import Submission.Work.BoseFixB1.BandSdefs
import Submission.Work.BoseFixR.PerBoxCrudeDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.thinShellBandCount` — the weak count bound on the bad band (statement)

**This is the one analytic residual of the node `Work.BoseFixB1B.thinShellCondensedBand`.**

On the bad band `bandSet ℓ d μ` the *proved* pointwise fibre bound
(`Work.BoseFixB1.qLHSwordB_ge_neg_bandS`, sorry-free) gives

    sbWord h μ u Φ ≥ − μ · bandK v h M · (bandS M ℓ d μ)² · n · ‖Φ‖²   (u ∈ bandSet ℓ d μ),

so the crude per-box bound `sbWord ≥ −C(μ²(a v)χ_M(u) + μ(a v))‖Φ‖²` follows as soon as

    n · bandK · bandS² ≤ C · (a v) · (μ · chiMass M ℓ d u + 1) .                       (★)

This module fixes (★) — *restricted to the states whose word is already negative* — as the
`Prop` `ThinShellBandCount`, the exact form the crude bound consumes.  (For `0 ≤ sbWord` the
crude bound is trivial, so the restriction loses nothing.)

The proof of `ThinShellBandCount` is delegated (path `BoseFixB1B/thinShellBandCountHeld`);
`Work.BoseFixB1B.thinShellCondensedBand` imports it and derives the target from it by the band
word bound above, a case split on the sign of `sbWord`, and `sbWord ≥ sbKin ≥ 0`.

## Why (★) is the honest residual, and why it is *much* weaker than FS's count window

* `n ≤ C μ ℓ³` (`Work.BoseFixB1B.lowCountBound`, FS `thm:aprioribounds`) implies (★) with an
  enormous margin: at `t = μ(a v)³ → 0` one has `μ ℓ³ ~ t^{-166/323}` and
  `bandS² ~ t^{14.67}`, so `μ ℓ³ bandK bandS² ≲ (a v) · μ(a v)^{1-o(1)} ≪ (a v)`: (★) asks for a
  count bound of size `~ t^{-14}` instead of FS's `~ t^{-0.5}`.
* (★) does **not** hold without the restriction `sbWord < 0`: for a potential `v` vanishing on
  `ball(0, √3 ℓ)` (`Work.BoseFixR.low_particle_bound.wordB_const_of_corner`) the constant state
  `Φ ≡ 1` is low at *arbitrary* `n` whenever `J√(μ(a v)³) ≥ 1`, and there `sbWord = sbKin ≥ 0`
  (both kernels of `sbPot` vanish), so the crude bound holds trivially and no count bound exists.
  The hypothesis `sbWord < 0` is exactly what removes that family, and it is free in the
  consumer, which already has `sbWord` on the right-hand side.
* The threshold `ε₀` is ours to choose; taking it below `1/J² ≤ 1/lhyC² ≈ 0.0432` removes the
  family above (it needs `J√(μ(a v)³) ≥ 1`).

## Ingredients a prover has (all sorry-free in the corpus)

* `Work.BoseFixB1.qLHSwordB_ge_neg_bandS` — the band fibre bound used above;
* `Work.BoseFixB1B.isLowB_chemBoundAlt` — a low state's flat one-body mass is
  `≥ 4πμ(a v)ℓ³(1 − J√(μ(a v)³))‖Φ‖²`;
* `Work.BoseFixB1B.boxFormB_budgetAlt` — the trade-off budget
  `kinFormB + pairPartB + 4πμ²(a v)ℓ³(1 − J√(μ(a v)³))‖Φ‖² ≤ μ·(flat one-body mass)`;
* `Work.BoseFixB1B.visCount_le_countAlt`, `Work.BoseFixB1.pairPartB_nonneg`,
  `Work.BoseFixB1.kinFormB_nonneg`, `Work.BoseFixR.SlabCountSplit`.

The content is the standard dichotomy: a state carrying many particles either has a large
pair (mean-field) energy — bounded by the budget against the chemical term — or must avoid the
coincidence set, which costs kinetic energy at the scale `1/R²`, far above `μ(a v)` in the
dilute regime.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix
  Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The weak count bound on the bad band, restricted to the negative-word states.** -/
def ThinShellBandCount (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (J : ℝ) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        ∀ u : E3,
          u ∈ Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) < 0 →
            (n : ℝ)
                * (Work.BoseFixB1.bandK v h
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    * Work.BoseFixB1.bandS
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ ^ 2)
              ≤ C * (_root_.BoseGases.a v)
                  * (μ * Work.SmallBoxSliding.chiMass
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u + 1)

end Work.BoseFixB1B
