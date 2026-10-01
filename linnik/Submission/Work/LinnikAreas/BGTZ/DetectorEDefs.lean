/-
# The corrected, non-vacuous BGTZ detector interface (`DetectorPropE`)

This file replaces the vacuous `Work.LinnikAreas.BGTZ.DetectorMainProp` of `BGTZSetup.lean`
(retired; see `Submission/Work/LinnikAreas/BGTZ/BGTZ_ROUTE_LEAD.md` §2.1 and
`BGTZ/NOTE_detector_interface_2026-09-28.md`).

## Why the old interface could not be used

`DetectorMainProp` used **one** existential constant `C` in two places: as the lower bound
`C·X ≤ R` on the sifting level, and as the lower bound `C·Y ≤ N` on the detection length, while the
*upper* bound on the sifting level was the fixed `R ≤ 2·sieveR = 512·X`.  For `C > 512` the window
for `R` is empty, so the whole implication holds vacuously and `DetectorMainProp` (proved with the
witness `C = 1000`, `BGTZArith.detectorMainProp_vacuous`) carries no detector information; and the
pinning `C ≤ 256` is *false*, because the same `C` would have to bound `N` from below, where the
`detJ` estimate needs a constant of size `3·10¹⁶`.

## The fix

Three independent quantities, and two changes of scale (see the route document for the proof):

* `CR ≥ 1` — the lower constant for `R`, chosen by the proof (the residue estimate needs
  `R ≥ max 1 (4·CS²)·X`, where `CS` is the existential constant of `SmoothedCoeffLower`);
* the *upper* bound on `R` is a multiple of the **same** constant, `R ≤ 2·CR·X`, so the window
  `[CR·X, 2·CR·X]` is never empty: `X ≥ (10𝓛)² ≥ 16641`, hence `⌈CR·X⌉₊` lies in it and is `≥ 200`;
* `CN > 0` — a **separate** constant for the lower bound on `N`, with no upper bound.

The `N`-scale is adapted to Graham's *trivial* critical-line bound
`‖G(1/2+iτ,χ)‖ ≤ R(1+log R)^9` (which is all we use, in place of the false BGTZ Lemma 4.3): hence
`(1-β₁)^{-6}` and `(1+log R)^{18}`.  The price `(1-β₁)^{-4}` in `N` costs only `0.04·log q`,
because `RepulsionGenC` is only used under `1/λ₁ < q^{1/100} log q`, i.e.
`(1-β₁)^{-1} < q^{1/100}(log q)²`.  The total exponent is `u = 8θ₀ + 6/100 = 2.14 < 11/5` and
`v = 4θ₀ = 1.04 < 11/10`, with `θ₀ = thA = 1/4 + 1/100` from the proved `UniformConvexity`.

The conclusion has exactly the shape of the old one, so the proved `DetectorChain` and the repulsion
arithmetic (`detector_step`, `phi_bound`, `caseB_bound`) consume it unchanged.
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.BGTZ.DetectorDefs

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section
namespace Work.LinnikAreas.BGTZ
open Work.LinnikContract

/-- The convexity exponent (`UniformConvexity : ∃ A, HypA A thA`). -/
abbrev thA : ℝ := 1 / 4 + 1 / 100

/-- Sifting-level scale `X = A² q^{2θ₀} e^{2(log q)^{3/4}} (1-β₁)^{-2}`  (`sieveR = 256·X`). -/
def sieveX (A : ℝ) (q : ℕ) (β₁ : ℝ) : ℝ :=
  A ^ 2 * (q : ℝ) ^ (2 * thA) * Real.exp (2 * (Real.log q) ^ (3 / 4 : ℝ))
    * (1 - β₁) ^ (-2 : ℝ)

/-- Detection-length scale for the trivial `G`-bound. -/
def detNE (A : ℝ) (q : ℕ) (β₁ T : ℝ) (R : ℕ) : ℝ :=
  A ^ 8 * (q : ℝ) ^ (8 * thA) * Real.exp (8 * (Real.log q) ^ (3 / 4 : ℝ)) * T ^ (4 * thA)
    * (1 - β₁) ^ (-6 : ℝ) * (1 + Real.log (R : ℝ)) ^ 18

/-- **The corrected (non-vacuous) BGTZ detector, Prop. 5.1 with Graham's trivial `G`-bound.** -/
def DetectorPropE : Prop :=
  ∃ CR : ℝ, 1 ≤ CR ∧ ∃ CN : ℝ, 0 < CN ∧
  ∀ (q : ℕ) [NeZero q], 400000 < q → ∀ (χ₁ : DirichletCharacter ℂ q),
    χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ∀ {β₁ : ℝ}, β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    1 - 1 / (10 * Real.log q) < β₁ →
    ∀ {A Cz : ℝ}, 1 ≤ A → HypA A thA → HypZeta Cz →
    ∀ {R : ℕ}, 200 ≤ R → CR * sieveX A q β₁ ≤ (R : ℝ) → (R : ℝ) ≤ 2 * CR * sieveX A q β₁ →
    ∀ {θw : ℕ → ℝ}, IsSieveWeight R θw →
    sieveGre χ₁ R θw 1 (1 : DirichletCharacter ℂ q)
        ≤ (q : ℝ) / (q.totient : ℝ) * (∑ n ∈ Finset.Icc 1 R, aCoeff χ₁ n / (n : ℝ))⁻¹ →
    ∀ (χ : DirichletCharacter ℂ q) (T : ℝ), 4 ≤ T → ∀ {ρ : ℂ},
      (DirichletCharacter.LFunction χ ρ = 0 ∨ DirichletCharacter.LFunction (χ * χ₁) ρ = 0) →
      3 / 4 ≤ ρ.re → 1 + |ρ.im| ≤ T →
    ∀ (N : ℕ), CN * detNE A q β₁ T R ≤ (N : ℝ) →
      ‖detector χ₁ χ N θw ρ‖
        ≤ ((2 - β₁) / (1 - ρ.re) + 1 / (ρ.re - 1 / 2)) * (1 - β₁) * ((N : ℝ) ^ (1 - ρ.re))

end Work.LinnikAreas.BGTZ
