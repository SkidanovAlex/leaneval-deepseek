import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.AprioriCount.Defs
import Submission.Work.AprioriCount.weighted_cauchy_schwarz
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.AprioriCount.chiSqMassBridge` — the χ-mass / χ²-mass Cauchy–Schwarz bridge

The node `Work.AprioriCount.ChiDysonBound` asks for the **χ-mass** `chiCount ℓ Φ` to be paid by
the box energy `kinFormB + pairPartB`:

    c·(a v)·(chiCount ℓ Φ)² ≤ (kinFormB + pairPartB)·ℓ³·normB .

Every *proved* row of the Dyson ledger (the sharp-weight `N`-body Dyson brick
`Work.AprioriCount.dysonSpreadRowBoxState`, the grid/annulus pair visibilities
`Work.AprioriCount.pairPartB_ge_grid` / `annulusClosePairs`) pays the **χ²-mass**

    chiSqMass ℓ Φ = ∫_{abox n ℓ} Φ² · Σᵢ χ_ℓ(xᵢ)² ,

i.e. the sum of **squares** of the window along the particles, and never the χ-mass directly.

The two quantities are related by configuration-level Cauchy–Schwarz,

    (Σᵢ χᵢ)² ≤ n · Σᵢ χᵢ²       (`Finset.sq_sum_le_card_mul_sum_sq`),

and the exact integrated form of that inequality is the bridge proved here:

    **(BRIDGE)**   (chiCount ℓ Φ)² ≤ (∫_{abox} Φ²) · n · chiSqMass ℓ Φ .

This is the *correct* form of the "χ-unbalance" step: the naive row `Σᵢχᵢ ≤ chiSup·Σᵢχᵢ²` of the
session-15/16 ledger (used to convert the pair/Dyson rows into a χ-*mass* bound) is **false** for a
window small compared with `1/chiSup`, whereas (BRIDGE) is true for every window and costs exactly a
factor `n`.  The factor `n` is the whole reason the node meets the corpus's count cap
(`Work.BoseFixB1S.LowStateCountCapB1`, `n ≲ μℓ³`): with (BRIDGE) the ledger reads

    c·a·n·chiSqMass ℓ Φ / ℓ³ ≤ kinFormB + pairPartB ,

i.e. the pair + Dyson rows pay the χ²-mass at the mean-field rate and the count `n` is the only
remaining length scale.

The proof is a two-line composition:
* `Work.AprioriCount.weighted_cauchy_schwarz` with `F = Φ²`, `G = Σᵢχ_ℓ(xᵢ)` gives
  `(chiCount)² ≤ (∫Φ²)·(∫Φ²(Σχ)²)`;
* `(Σχ)² ≤ n·Σχ²` pointwise, times `Φ² ≥ 0`, integrates to `∫Φ²(Σχ)² ≤ n·chiSqMass`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.AprioriCount

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The χ²-mass of a box state**: `∫_{abox n ℓ} Φ² · Σᵢ χ_ℓ(xᵢ)²`.

This is the quantity that the *proved* rows of the Dyson ledger pay (the sharp-weight Dyson brick
and the pair visibilities all carry `χ_ℓ(xᵢ)²` or a product `χ_ℓ(xᵢ)χ_ℓ(xⱼ)`), and it is related to
the node's `chiCount` by the Cauchy–Schwarz bridge `chiCount_sq_le_normB_mul_chiSqMass`. -/
noncomputable def chiSqMass {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∫ x in Submission.BoseGases.abox n ℓ,
    (Φ x) ^ 2 * ∑ i : Fin n, (Submission.BoseGases.chiScale ℓ (x i)) ^ 2

/-- `chiSqMass` is nonnegative for a continuous state. -/
theorem chiSqMass_nonneg {n : ℕ} {ℓ : ℝ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : Continuous Φ) : 0 ≤ chiSqMass ℓ Φ := by
  refine integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => ?_)
  exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- `chiSqMass` is dominated by `chiSup` times the χ-mass: `Σᵢχᵢ² ≤ chiSup·Σᵢχᵢ` pointwise. -/
theorem chiSqMass_le_chiSup_mul_chiCount {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    chiSqMass ℓ Φ ≤ Submission.BoseGases.chiSup * chiCount ℓ Φ := by
  have hsqcont : Continuous fun x : Submission.BoseGases.X n => (Φ x) ^ 2 := hΦ.pow 2
  have hcomp : IsCompact (Submission.BoseGases.abox n ℓ) :=
    Submission.BoseGases.abox_compact n hℓ
  have hpt : ∀ x : Submission.BoseGases.X n,
      (Φ x) ^ 2 * ∑ i : Fin n, (Submission.BoseGases.chiScale ℓ (x i)) ^ 2
        ≤ (Φ x) ^ 2 * (Submission.BoseGases.chiSup *
            ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i)) := by
    intro x
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    calc ∑ i : Fin n, (Submission.BoseGases.chiScale ℓ (x i)) ^ 2
        ≤ ∑ i : Fin n, Submission.BoseGases.chiSup *
            Submission.BoseGases.chiScale ℓ (x i) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hnn := Submission.BoseGases.chiScale_nonneg ℓ (x i)
          have hle := Submission.BoseGases.abs_chiScale_le_chiSup ℓ (x i)
          nlinarith [abs_le.mp hle, hnn]
      _ = Submission.BoseGases.chiSup * ∑ i : Fin n,
            Submission.BoseGases.chiScale ℓ (x i) := by rw [Finset.mul_sum]
  have h1 : Integrable (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ∑ i : Fin n, (Submission.BoseGases.chiScale ℓ (x i)) ^ 2)
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    ContinuousOn.integrableOn_compact hcomp (hsqcont.mul (continuous_finsetSum _ fun i _ =>
      ((Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply i)).pow 2)).continuousOn
  have h2 : Integrable (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * (Submission.BoseGases.chiSup *
        ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i)))
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    ContinuousOn.integrableOn_compact hcomp (hsqcont.mul (continuous_const.mul
      (continuous_finsetSum _ fun i _ =>
        (Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply i)))).continuousOn
  have hmono := integral_mono h1 h2 hpt
  have hrhs : (∫ x in Submission.BoseGases.abox n ℓ,
      (Φ x) ^ 2 * (Submission.BoseGases.chiSup *
        ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i)))
      = Submission.BoseGases.chiSup * chiCount ℓ Φ := by
    rw [chiCount]
    have hpt' : (fun x : Submission.BoseGases.X n =>
        (Φ x) ^ 2 * (Submission.BoseGases.chiSup * ∑ i : Fin n,
          Submission.BoseGases.chiScale ℓ (x i)))
        = fun x : Submission.BoseGases.X n => Submission.BoseGases.chiSup *
            ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i)) := by
      funext x; ring
    rw [hpt', integral_const_mul]
  show chiSqMass ℓ Φ ≤ Submission.BoseGases.chiSup * chiCount ℓ Φ
  rw [chiSqMass, ← hrhs]
  exact hmono

/-- **The bridge**: the χ-mass is controlled by the χ²-mass with the particle count `n`,

    (chiCount ℓ Φ)² ≤ (∫_{abox n ℓ} Φ²) · n · chiSqMass ℓ Φ .

Both factors on the right are nonnegative, and the inequality is sharp (a state with all `n` χ-masses
concentrated at distinct positions where `χ_ℓ ≈ 1` has `chiCount ≈ n`, `chiSqMass ≈ n`,
`∫Φ² = 1`). -/
theorem chiCount_sq_le_normB_mul_chiSqMass {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    (chiCount ℓ Φ) ^ 2
      ≤ (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) * (n : ℝ)
          * chiSqMass ℓ Φ := by
  set s : Set (Submission.BoseGases.X n) := Submission.BoseGases.abox n ℓ with hs
  set S : Submission.BoseGases.X n → ℝ :=
    fun x => ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i) with hS
  have hScont : Continuous S := by
    rw [hS]
    exact continuous_finsetSum _ fun i _ =>
      (Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply i)
  have hSnneg : ∀ x, 0 ≤ S x := fun x =>
    Finset.sum_nonneg fun i _ => Submission.BoseGases.chiScale_nonneg ℓ (x i)
  have hsqcont : Continuous fun x : Submission.BoseGases.X n => (Φ x) ^ 2 := hΦ.pow 2
  have hcomp : IsCompact s := by
    rw [hs]; exact Submission.BoseGases.abox_compact n hℓ
  have hFi : Integrable (fun x => (Φ x) ^ 2) (volume.restrict s) :=
    ContinuousOn.integrableOn_compact hcomp hsqcont.continuousOn
  have hFGi : Integrable (fun x => (Φ x) ^ 2 * S x) (volume.restrict s) :=
    ContinuousOn.integrableOn_compact hcomp (hsqcont.mul hScont).continuousOn
  have hFG2i : Integrable (fun x => (Φ x) ^ 2 * S x ^ 2) (volume.restrict s) :=
    ContinuousOn.integrableOn_compact hcomp (hsqcont.mul (hScont.pow 2)).continuousOn
  have hcs := weighted_cauchy_schwarz (μ := volume.restrict s)
    (F := fun x => (Φ x) ^ 2) (G := S)
    (Filter.Eventually.of_forall fun x => sq_nonneg _)
    (Filter.Eventually.of_forall hSnneg) hFi hFGi hFG2i
  -- the pointwise configuration-level Cauchy–Schwarz
  have hpt : ∀ x : Submission.BoseGases.X n,
      (Φ x) ^ 2 * S x ^ 2 ≤ (n : ℝ) * ((Φ x) ^ 2 * ∑ i : Fin n,
        (Submission.BoseGases.chiScale ℓ (x i)) ^ 2) := by
    intro x
    have hsq : S x ^ 2 ≤ (n : ℝ) * ∑ i : Fin n,
        (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 := by
      rw [hS]
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i : Fin n => Submission.BoseGases.chiScale ℓ (x i))
      simpa using h
    calc (Φ x) ^ 2 * S x ^ 2
        ≤ (Φ x) ^ 2 * ((n : ℝ) * ∑ i : Fin n,
            (Submission.BoseGases.chiScale ℓ (x i)) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = (n : ℝ) * ((Φ x) ^ 2 * ∑ i : Fin n,
            (Submission.BoseGases.chiScale ℓ (x i)) ^ 2) := by ring
  have hG2i : Integrable (fun x => (n : ℝ) * ((Φ x) ^ 2 * ∑ i : Fin n,
      (Submission.BoseGases.chiScale ℓ (x i)) ^ 2)) (volume.restrict s) := by
    refine Integrable.const_mul ?_ _
    refine ContinuousOn.integrableOn_compact hcomp ?_
    refine (hsqcont.mul ?_).continuousOn
    exact continuous_finsetSum _ fun i _ => ((Submission.BoseGases.chiScale_continuous ℓ).comp
      (continuous_apply i)).pow 2
  have hmono : ∫ x, (Φ x) ^ 2 * S x ^ 2 ∂(volume.restrict s)
      ≤ (n : ℝ) * chiSqMass ℓ Φ := by
    have h1 : ∫ x, (Φ x) ^ 2 * S x ^ 2 ∂(volume.restrict s)
        ≤ ∫ x, (n : ℝ) * ((Φ x) ^ 2 * ∑ i : Fin n,
            (Submission.BoseGases.chiScale ℓ (x i)) ^ 2) ∂(volume.restrict s) :=
      integral_mono hFG2i hG2i hpt
    rw [integral_const_mul] at h1
    rw [hs] at h1
    rw [chiSqMass]
    exact h1
  have hkey := hcs
  rw [hs] at hkey
  have hlhs : (∫ x in Submission.BoseGases.abox n ℓ,
      (Φ x) ^ 2 * S x) = chiCount ℓ Φ := by
    rw [chiCount, hS]
  have hI0 : 0 ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
  calc (chiCount ℓ Φ) ^ 2
      = (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * S x) ^ 2 := by rw [hlhs]
    _ ≤ (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
          * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * S x ^ 2) := hkey
    _ ≤ (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) * ((n : ℝ) * chiSqMass ℓ Φ) :=
        mul_le_mul_of_nonneg_left hmono hI0
    _ = (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) * (n : ℝ) * chiSqMass ℓ Φ := by
        ring

end Work.AprioriCount
