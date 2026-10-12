import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.Work.SmallBoxSliding.Sliding
import Submission.Work.WCrossD2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Item 3 — the assembly of `(eq:apriorinn+)` from the sliding-localisation inputs

FS `thm:aprioriHLambda` step 3 completes the a-priori chain.  The two
numerical conjuncts of `APrioriSkeleton.apriori_nplus_window` are

  (i) the excited-count window `cnPlus ≤ C·μ·ℓ³·K_B³·K_ℓ²·(μa³)^{1/2}`;
  (ii) the particle window `|N̂/ℓ³ − μ| ≤ μ·C·K_B^{3/2}·K_ℓ·(μa³)^{1/4}`.

They follow from FOUR named inputs, of which the first two are what the
sliding-localisation segment (items 1–2) supplies and the last two are pure
numeric bookkeeping (`K_ℓ`, `C` are chosen by the consumer):

* `hE`      — the energy hypothesis FS `eq:aprioriPsi`,
              `⟨H_Λ(μ)⟩ ≤ −4πμ²aℓ³(1 − J(μa³)^{1/2})`;
* `hslide`  — the sliding-sum identity of item 1 *with the a-priori remainder
              split off* (`R_Ψ` + kinetic gap − background), i.e. FS step 2
              `⟨H_Λ(μ)⟩ ≥ R_Ψ + (b/2ℓ²)⟨n₊⟩ − 4πμ²aℓ³(1 + K_B³(μa³)^{1/2})`;
* `hwindow` — the Cauchy–Schwarz particle window of item 2
              (`Window.window_of_remainder` composed with the R_Ψ lower bound
              `Jensen.R_Psi_lower`), in the form
              `|N̂ − μℓ³| ≤ √om·√(R_Ψ/c₁)`;
* `hcnShape`, `hwinShape` — the arithmetic shapes of the two resulting
              quantities (the consumer picks `C`, `K_ℓ`).

Nothing here waits on SmallBoxA0: `hslide` is exactly the interface that the
SmallBoxA0 per-box bound (`SmallBoxDLBound.smallbox_dl_energy_bound`) plus
`Sliding.sliding_sum_identity` deliver.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases

/-- The excited-particle count is nonnegative (sum of `L²`-norms of projected
states). -/
lemma cnPlus_nonneg {N : ℕ} (ℓ : ℝ) {Φ : X N → ℝ} : 0 ≤ cnPlus ℓ Φ := by
  rw [cnPlus]
  exact Finset.sum_nonneg (fun i _ =>
    integral_nonneg (fun x => sq_nonneg _))

/-- **FS step 3 (the arithmetic core)**: the energy hypothesis `hE` and the
sliding-sum identity `hslide` (with the `R_Ψ`/kinetic split) give

    (b/2ℓ²)·cnPlus ≤ 4πμ²aℓ³(J + K_B³)(μa³)^{1/2} − R_Ψ ,  R_Ψ ≤ 4πμ²aℓ³(J+K_B³)(μa³)^{1/2} .

The first is eq:apriorinn+ (the excited-count window), the second is the
`R_Ψ`-upper bound that the Cauchy–Schwarz window consumes. -/
theorem cnPlus_and_R_le {N : ℕ} {ℓ μ b : ℝ} (hℓ : 0 < ℓ) (hb : 0 < b)
    {a R J K_B E : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R)
    {Φ : X N → ℝ} (hcn : 0 ≤ cnPlus ℓ Φ)
    (hE : E ≤ - 4 * π * μ ^ 2 * a * ℓ ^ 3 * (1 - J * (μ * a ^ 3) ^ (1 / 2 : ℝ)))
    (hslide : R + (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ
        - 4 * π * μ ^ 2 * a * ℓ ^ 3 * (1 + K_B ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ)) ≤ E) :
    (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ
        ≤ 4 * π * μ ^ 2 * a * ℓ ^ 3 * (J + K_B ^ 3) * (μ * a ^ 3) ^ (1 / 2 : ℝ) - R
      ∧ R ≤ 4 * π * μ ^ 2 * a * ℓ ^ 3 * (J + K_B ^ 3) * (μ * a ^ 3) ^ (1 / 2 : ℝ) := by
  have hmain : R + (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ
      ≤ 4 * π * μ ^ 2 * a * ℓ ^ 3 * (J + K_B ^ 3) * (μ * a ^ 3) ^ (1 / 2 : ℝ) := by
    nlinarith [hE, hslide]
  constructor
  · linarith
  · have hb2 : 0 < b / (2 * ℓ ^ 2) := by positivity
    nlinarith [hmain, mul_nonneg (le_of_lt hb2) hcn]

/-- **Item 3, the assembly in the shape of `apriori_nplus_window`**: the
excited-count and particle windows, from the energy hypothesis, the
sliding-sum identity (item 1), the Cauchy–Schwarz window (item 2) and the two
numeric-shape inputs.  This is exactly the pair of conjuncts the mega-statement
`APrioriBounds.aPriori_bounds_statement` consumes. -/
theorem apriori_nplus_window_assembly {N : ℕ} {ℓ μ b : ℝ} (hℓ : 0 < ℓ) (hμ : 0 < μ)
    (hb : 0 < b)
    {a R J K_B K_ℓ om c₁ C E : ℝ} (ha : 0 ≤ a) (hKB : 0 < K_B) (hKℓ : 0 < K_ℓ)
    (hJ : 0 ≤ J) (hR : 0 ≤ R) (hom : 0 ≤ om) (hc₁ : 0 < c₁) (hC : 0 ≤ C)
    {Φ : X N → ℝ}
    (hE : E ≤ - 4 * π * μ ^ 2 * a * ℓ ^ 3 * (1 - J * (μ * a ^ 3) ^ (1 / 2 : ℝ)))
    (hslide : R + (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ
        - 4 * π * μ ^ 2 * a * ℓ ^ 3 * (1 + K_B ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ)) ≤ E)
    (hwindow : |(N : ℝ) - μ * ℓ ^ 3| ≤ Real.sqrt om * Real.sqrt (R / c₁))
    (hcnShape : (2 * ℓ ^ 2 / b) * (4 * π * μ ^ 2 * a * ℓ ^ 3 * (J + K_B ^ 3)
          * (μ * a ^ 3) ^ (1 / 2 : ℝ))
        ≤ C * μ * ℓ ^ 3 * K_B ^ 3 * K_ℓ ^ 2 * (μ * a ^ 3) ^ (1 / 2 : ℝ))
    (hwinShape : Real.sqrt om
          * Real.sqrt (4 * π * μ ^ 2 * a * ℓ ^ 3 * (J + K_B ^ 3)
              * (μ * a ^ 3) ^ (1 / 2 : ℝ) / c₁) / ℓ ^ 3
        ≤ μ * C * K_B ^ (3 / 2 : ℝ) * K_ℓ * (μ * a ^ 3) ^ (1 / 4 : ℝ)) :
    cnPlus ℓ Φ ≤ C * μ * ℓ ^ 3 * K_B ^ 3 * K_ℓ ^ 2 * (μ * a ^ 3) ^ (1 / 2 : ℝ)
      ∧ |((N : ℝ) / ℓ ^ 3) - μ| ≤ μ * C * K_B ^ (3 / 2 : ℝ) * K_ℓ
          * (μ * a ^ 3) ^ (1 / 4 : ℝ) := by
  have hcn := cnPlus_nonneg ℓ (Φ := Φ)
  obtain ⟨h1, h2⟩ := cnPlus_and_R_le hℓ hb ha hR hcn hE hslide
  have hQ0 : 0 ≤ 4 * π * μ ^ 2 * a * ℓ ^ 3 * (J + K_B ^ 3) * (μ * a ^ 3) ^ (1 / 2 : ℝ) := by
    have : 0 ≤ (μ * a ^ 3) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
    positivity
  constructor
  · have hQdef : 0 ≤ 4 * π * μ ^ 2 * a * ℓ ^ 3 * (J + K_B ^ 3) * (μ * a ^ 3) ^ (1 / 2 : ℝ) := hQ0
    have h1Q : (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ
        ≤ 4 * π * μ ^ 2 * a * ℓ ^ 3 * (J + K_B ^ 3) * (μ * a ^ 3) ^ (1 / 2 : ℝ) := by
      linarith [h1, hR]
    have hb0 : 0 < 2 * ℓ ^ 2 / b := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1Q (le_of_lt hb0)
    have heq : (2 * ℓ ^ 2 / b) * ((b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ) = cnPlus ℓ Φ := by
      field_simp
    rw [heq] at h2
    exact le_trans h2 hcnShape
  · have hRle : R ≤ 4 * π * μ ^ 2 * a * ℓ ^ 3 * (J + K_B ^ 3) * (μ * a ^ 3) ^ (1 / 2 : ℝ) := h2
    have hsqrt : Real.sqrt (R / c₁)
        ≤ Real.sqrt (4 * π * μ ^ 2 * a * ℓ ^ 3 * (J + K_B ^ 3) * (μ * a ^ 3) ^ (1 / 2 : ℝ) / c₁) := by
      apply Real.sqrt_le_sqrt
      exact div_le_div_of_nonneg_right hRle (le_of_lt hc₁)
    have hstep : |(N : ℝ) - μ * ℓ ^ 3| ≤ Real.sqrt om
        * Real.sqrt (4 * π * μ ^ 2 * a * ℓ ^ 3 * (J + K_B ^ 3) * (μ * a ^ 3) ^ (1 / 2 : ℝ) / c₁) := by
      have h1' : Real.sqrt om * Real.sqrt (R / c₁)
          ≤ Real.sqrt om * Real.sqrt (4 * π * μ ^ 2 * a * ℓ ^ 3 * (J + K_B ^ 3)
              * (μ * a ^ 3) ^ (1 / 2 : ℝ) / c₁) :=
        mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg om)
      linarith [hwindow]
    have hℓ3 : 0 < ℓ ^ 3 := by positivity
    have habs : |((N : ℝ) / ℓ ^ 3) - μ| = |(N : ℝ) - μ * ℓ ^ 3| / ℓ ^ 3 := by
      have hdiv : ((N : ℝ) / ℓ ^ 3) - μ = ((N : ℝ) - μ * ℓ ^ 3) / ℓ ^ 3 := by
        field_simp
      rw [hdiv, abs_div, abs_of_pos hℓ3]
    calc |((N : ℝ) / ℓ ^ 3) - μ| = |(N : ℝ) - μ * ℓ ^ 3| / ℓ ^ 3 := habs
        _ ≤ (Real.sqrt om * Real.sqrt (4 * π * μ ^ 2 * a * ℓ ^ 3 * (J + K_B ^ 3)
              * (μ * a ^ 3) ^ (1 / 2 : ℝ) / c₁)) / ℓ ^ 3 :=
            div_le_div_of_nonneg_right hstep (le_of_lt hℓ3)
        _ ≤ μ * C * K_B ^ (3 / 2 : ℝ) * K_ℓ * (μ * a ^ 3) ^ (1 / 4 : ℝ) := hwinShape


/-! ## The kinetic gap constant `b = 1/18` (CLOSED)

The sliding-sum identity of item 1 carries `(b/2ℓ²)·cnPlus` with `b` the
sector kinetic gap.  In the corpus that gap is the CLOSED
`CentredGap.centredGap`, `cnPlus ℓ Φ ≤ 36ℓ²·kinWord N ℓ Φ`, i.e. the value of
`b` is `1/18`.  Equivalently, in the exact normalisation of
`Sliding.sliding_sum_identity`:

    (1/18)/(2ℓ²)·cnPlus ℓ Φ ≤ kinWord N ℓ Φ .

NOTE (why this does not by itself reduce `hslide`): the `(b/2ℓ²)cnPlus` term of
`eq:BSsliding2` is *produced inside* the localisation argument, from the
localised kinetic words `kinWordB` (the corpus kinetic energy distributed over
the sliding boxes); it is not an independent addend of the localisation
hypothesis.  The present lemma only records the numerical value of `b` so that
the two interfaces agree. -/

/-- The kinetic gap in the sliding-sum normalisation:
`(1/18)/(2ℓ²)·cnPlus ≤ kinWord` (since `cnPlus ≤ 36ℓ²·kinWord`,
`CentredGap.centredGap`). -/
theorem kinetic_gap_18 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) :
    (1 / 18 : ℝ) / (2 * ℓ ^ 2) * cnPlus ℓ Φ ≤ kinWord N ℓ Φ := by
  have h := centredGap hℓ hΦc
  have h1 : (1 / 18 : ℝ) / (2 * ℓ ^ 2) * cnPlus ℓ Φ = cnPlus ℓ Φ / (36 * ℓ ^ 2) := by
    field_simp
    ring
  rw [h1]
  calc cnPlus ℓ Φ / (36 * ℓ ^ 2)
      ≤ (36 * ℓ ^ 2 * kinWord N ℓ Φ) / (36 * ℓ ^ 2) :=
        div_le_div_of_nonneg_right h (by positivity)
    _ = kinWord N ℓ Φ := by field_simp

end Work.SmallBoxSliding
