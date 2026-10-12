import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.pairRung.boxWinModeRGen_one
import Submission.Work.BoseFixB1B.pairRung.fsKinPGenIntegrable
import Submission.Work.BoseFixB1B.pairRung.intKIntegrable
import Submission.Work.BoseFixB1B.pairRung.nuPairWNuBounds
import Submission.Work.BoseFixB1B.wMR_memLp_one_contDiff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.pairRung.chainInputs` — the per-`q` inputs of the `chainIntegralQdep` instantiation

This module supplies, in the general vocabulary of `chainIntegralQdep`, the algebraic and
integrability inputs of the chain at

* `𝒲 : E3 → ℝ` — the localised profile `wSmallScaled M (ℓ*d) (g0 v h) / convScale ℓ`,
* `χ : E3 → ℝ` — the window `chiSmallB M ℓ d u` (so that `wSmall1Pair`'s kernel is the product
  `χ x * 𝒲 (x - y) * χ y`; see `wSmall1Pair_kernel`),
* `𝒜 q = 1/((N+1)) * fsKinCoeff c ‖q‖ + 2K_s (a v)/V`,  `B q = pairW 𝒲 q / V`:

| lemma | chain hypothesis |
|---|---|
| `wSmall1Pair_kernel` | recognition of `wSmall1Pair` as the `χ χ 𝒲` product (for `hpair`) |
| `hBle_of` | `hBle : ∀ q, |B q| ≤ 𝒜 q`, from the sup bound `|pairW 𝒲| ≤ K (a v)` with `K ≤ 2K_s` |
| `hIntK_of` | `hIntK : Integrable (fun q => B q ^ 2 / 𝒜 q)`, from `intKIntegrable` |
| `hintP_of'`, `hintR_of'` | `hintP`, `hintR`, thin wrappers over `chainHints` in the exact shapes |
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1B.pairRung

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **`wSmall1Pair` *is* the `χ χ 𝒲` product.**  By definition
`wSmallPair M ℓ d u h x y = χ x * (wSmallScaled M (ℓd) h (x-y) / convScale ℓ (x-y)) * χ y` with
`χ = chiSmallB M ℓ d u`, so the kernel of `wSmall1Pair` is the one `boxPairIntGenC2'` consumes,
up to the reassociation `χ x * (𝒲 (x-y)) * χ y = χ x * χ y * 𝒲 (x-y)`. -/
theorem wSmall1Pair_kernel {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (ℓ d : ℝ) (u : E3) :
    Submission.BoseGases.wSmall1Pair h M ℓ d u
      = fun x y : E3 => Submission.BoseGases.chiSmallB M ℓ d u x *
          Submission.BoseGases.chiSmallB M ℓ d u y *
          (Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (x - y)
            / Submission.BoseGases.convScale ℓ (x - y)) := by
  funext x y
  rw [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair]
  ring

/-- **`hBle` of `chainIntegralQdep`.**  With the sup bound `|pairW 𝒲 q| ≤ K (a v)` and
`K ≤ 2K_s`, the coefficient `B q = pairW 𝒲 q / V` is dominated by
`𝒜 q = 1/((N+1))·fsKinCoeff c ‖q‖ + 2K_s(a v)/V` (the `fsKinCoeff` term being nonnegative). -/
theorem hBle_of {n : ℕ} {V Ks av c K : ℝ} {𝒲 : E3 → ℝ}
    (hV : 0 < V) (hav : 0 ≤ av) (hK : K ≤ 2 * Ks)
    (hsup : ∀ q : E3, |Submission.BoseGases.pairW 𝒲 q| ≤ K * av) (q : E3) :
    |Submission.BoseGases.pairW 𝒲 q / V|
      ≤ 1 / ((n : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / V := by
  have h1 : 0 ≤ 1 / ((n : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ :=
    mul_nonneg (by positivity) (Submission.BoseGases.fsKinCoeff_nonneg c ‖q‖)
  have h2 : |Submission.BoseGases.pairW 𝒲 q| / V ≤ 2 * Ks * av / V :=
    div_le_div_of_nonneg_right
      (le_trans (hsup q) (mul_le_mul_of_nonneg_right hK hav)) hV.le
  rw [abs_div, abs_of_pos hV]
  linarith

/-- **`hIntK` of `chainIntegralQdep`**, from `intKIntegrable`. -/
theorem hIntK_of {n : ℕ} {V Ks av c : ℝ} {𝒲 : E3 → ℝ}
    (hV : 0 < V) (hKs : 0 < Ks) (ha : 0 < av) (hc : 0 ≤ c)
    (hWint : MeasureTheory.Integrable 𝒲)
    (hfin : MeasureTheory.Integrable (fun q : E3 =>
        (Submission.BoseGases.pairW 𝒲 q) ^ 2 / ‖q‖ ^ 2)) :
    MeasureTheory.Integrable (fun q : E3 =>
      (Submission.BoseGases.pairW 𝒲 q / V) ^ 2 /
        (1 / ((n : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / V)) := by
  refine (intKIntegrable (N := n) (V := V) (Ks := Ks) (c := c) (a := av) (𝒲 := 𝒲)
    hV hKs ha hc hWint hfin).congr ?_
  filter_upwards with q
  ring

end Work.BoseFixB1B.pairRung
