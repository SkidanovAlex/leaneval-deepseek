import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiRowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.muLine_abs_le`

The `μ`-line of the χ-sandwich is bounded by the sector counts:

    |muLine n ℓ w Φ| ≤ 2·K·√(cS1 ℓ Φ · cnPlus ℓ Φ)

whenever `|w| ≤ K` pointwise.  This is the elementary Cauchy–Schwarz estimate on the
`Q`-leg / `P`-leg pairing: with `uᵢ := aP ℓ i Φ`, `vᵢ := aQ ℓ i Φ`,

    |muLine| = 2·|Σᵢ ∫ vᵢ · w(xᵢ) · uᵢ|
            ≤ 2K·Σᵢ ∫|vᵢ||uᵢ|
            ≤ 2K·Σᵢ √(∫vᵢ²)·√(∫uᵢ²)
            ≤ 2K·√(Σᵢ∫vᵢ²)·√(Σᵢ∫uᵢ²) = 2K·√(cnPlus·cS1),

the last two steps being the integral Cauchy–Schwarz and the Cauchy–Schwarz inequality for
finsets using square roots.  No hypothesis on `w` beyond the pointwise bound is used, so in
particular `w` need not be measurable: whenever the integrand fails to be integrable the
Bochner integral vanishes and the estimate is trivial, while on the integrable part the
pointwise domination by the continuous `K·|vᵢ|·|uᵢ|` is applied via `integral_mono_of_nonneg`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

/-- Cauchy–Schwarz for the Bochner integral: `∫ f g ≤ √(∫f²)·√(∫g²)` for nonnegative
`f, g ∈ L²`. -/
private lemma integral_mul_le_sqrt_mul_sqrt {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ] {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfnn : 0 ≤ᵐ[μ] f) (hgnn : 0 ≤ᵐ[μ] g) :
    ∫ a, f a * g a ∂μ ≤ Real.sqrt (∫ a, f a ^ 2 ∂μ) * Real.sqrt (∫ a, g a ^ 2 ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2) hpq hfnn hgnn
    (by simpa using hf) (by simpa using hg)
  have hA : (∫ a, f a ^ (2 : ℝ) ∂μ) = ∫ a, f a ^ 2 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with a
    rw [Real.rpow_two]
  have hB : (∫ a, g a ^ (2 : ℝ) ∂μ) = ∫ a, g a ^ 2 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with a
    rw [Real.rpow_two]
  simpa only [hA, hB, ← Real.sqrt_eq_rpow] using h

theorem muLine_abs_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) {w : EuclideanSpace ℝ (Fin 3) → ℝ} {K : ℝ}
    (hw : ∀ x, |w x| ≤ K) (hK : 0 ≤ K) :
    |Work.BoseBoxFock.muLine n ℓ w Φ|
      ≤ 2 * K * Real.sqrt (Submission.BoseGases.cS1 ℓ Φ * Submission.BoseGases.cnPlus ℓ Φ) := by
  have : IsFiniteMeasure ((volume : Measure (X n)).restrict (abox n ℓ)) :=
    isFiniteMeasure_restrict.2 (ne_of_lt (abox_lt_top n ℓ hℓ.le))
  -- the per-slot Cauchy–Schwarz estimate
  have hterm : ∀ j : Fin n,
      |∫ x in abox n ℓ, (aQ ℓ j Φ x) * w (x j) * (aP ℓ j Φ x)|
        ≤ K * (Real.sqrt (∫ x in abox n ℓ, (aQ ℓ j Φ x) ^ 2)
             * Real.sqrt (∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2)) := by
    intro j
    have hqc : Continuous (fun x : X n => aQ ℓ j Φ x) := by
      simp only [aQ]
      exact hΦc.sub (aP_continuous hℓ j hΦc)
    have hpc : Continuous (fun x : X n => aP ℓ j Φ x) := aP_continuous hℓ j hΦc
    have hint : Integrable (fun x : X n => K * (|aQ ℓ j Φ x| * |aP ℓ j Φ x|))
        ((volume : Measure (X n)).restrict (abox n ℓ)) :=
      (integrableOn_abox_of_continuous hℓ
        (continuous_const.mul (hqc.abs.mul hpc.abs))).integrable
    have hle : (fun x : X n => |(aQ ℓ j Φ x) * w (x j) * (aP ℓ j Φ x)|)
        ≤ᵐ[(volume : Measure (X n)).restrict (abox n ℓ)]
        (fun x : X n => K * (|aQ ℓ j Φ x| * |aP ℓ j Φ x|)) := by
      filter_upwards with x
      rw [abs_mul, abs_mul]
      calc |aQ ℓ j Φ x| * |w (x j)| * |aP ℓ j Φ x|
          ≤ |aQ ℓ j Φ x| * K * |aP ℓ j Φ x| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hw (x j)) (abs_nonneg _)) (abs_nonneg _)
        _ = K * (|aQ ℓ j Φ x| * |aP ℓ j Φ x|) := by ring
    have hstep4 : (∫ x in abox n ℓ, |aQ ℓ j Φ x| * |aP ℓ j Φ x|)
        ≤ Real.sqrt (∫ x in abox n ℓ, (aQ ℓ j Φ x) ^ 2)
          * Real.sqrt (∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2) := by
      have hQ2 : MemLp (fun x : X n => |aQ ℓ j Φ x|) 2
          ((volume : Measure (X n)).restrict (abox n ℓ)) := by
        obtain ⟨C, hC⟩ := (abox_compact n hℓ).exists_bound_of_continuousOn hqc.continuousOn
        refine MemLp.of_bound (hqc.abs.aestronglyMeasurable) C ?_
        rw [ae_restrict_iff' (abox_measurable n ℓ)]
        filter_upwards with x hx
        simpa only [Real.norm_eq_abs, abs_abs] using hC x hx
      have hP2 : MemLp (fun x : X n => |aP ℓ j Φ x|) 2
          ((volume : Measure (X n)).restrict (abox n ℓ)) := by
        obtain ⟨C, hC⟩ := (abox_compact n hℓ).exists_bound_of_continuousOn hpc.continuousOn
        refine MemLp.of_bound (hpc.abs.aestronglyMeasurable) C ?_
        rw [ae_restrict_iff' (abox_measurable n ℓ)]
        filter_upwards with x hx
        simpa only [Real.norm_eq_abs, abs_abs] using hC x hx
      have hmain := integral_mul_le_sqrt_mul_sqrt hQ2 hP2
        (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (Filter.Eventually.of_forall fun x => abs_nonneg _)
      have hA : (∫ x in abox n ℓ, |aQ ℓ j Φ x| ^ 2)
          = ∫ x in abox n ℓ, (aQ ℓ j Φ x) ^ 2 := by
        refine integral_congr_ae ?_
        filter_upwards with x
        rw [sq_abs]
      have hB : (∫ x in abox n ℓ, |aP ℓ j Φ x| ^ 2)
          = ∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2 := by
        refine integral_congr_ae ?_
        filter_upwards with x
        rw [sq_abs]
      simpa only [hA, hB] using hmain
    calc |∫ x in abox n ℓ, (aQ ℓ j Φ x) * w (x j) * (aP ℓ j Φ x)|
        ≤ ∫ x in abox n ℓ, |(aQ ℓ j Φ x) * w (x j) * (aP ℓ j Φ x)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x in abox n ℓ, K * (|aQ ℓ j Φ x| * |aP ℓ j Φ x|) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _) hint hle
      _ = K * ∫ x in abox n ℓ, |aQ ℓ j Φ x| * |aP ℓ j Φ x| :=
          integral_const_mul K _
      _ ≤ K * (Real.sqrt (∫ x in abox n ℓ, (aQ ℓ j Φ x) ^ 2)
            * Real.sqrt (∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2)) :=
          mul_le_mul_of_nonneg_left hstep4 hK
  -- Cauchy–Schwarz for the sum over the slots
  have hsum1 : |∑ j : Fin n, ∫ x in abox n ℓ, (aQ ℓ j Φ x) * w (x j) * (aP ℓ j Φ x)|
      ≤ ∑ j : Fin n, |∫ x in abox n ℓ, (aQ ℓ j Φ x) * w (x j) * (aP ℓ j Φ x)| := by
    simpa using Finset.abs_sum_le_sum_abs (s := Finset.univ)
      (fun j : Fin n => ∫ x in abox n ℓ, (aQ ℓ j Φ x) * w (x j) * (aP ℓ j Φ x))
  have hsum2 : (∑ j : Fin n, |∫ x in abox n ℓ, (aQ ℓ j Φ x) * w (x j) * (aP ℓ j Φ x)|)
      ≤ ∑ j : Fin n, K * (Real.sqrt (∫ x in abox n ℓ, (aQ ℓ j Φ x) ^ 2)
            * Real.sqrt (∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2)) :=
    Finset.sum_le_sum (fun j _ => hterm j)
  have hsum3 : (∑ j : Fin n, K * (Real.sqrt (∫ x in abox n ℓ, (aQ ℓ j Φ x) ^ 2)
            * Real.sqrt (∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2)))
      = K * ∑ j : Fin n, (Real.sqrt (∫ x in abox n ℓ, (aQ ℓ j Φ x) ^ 2)
            * Real.sqrt (∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2)) := by
    rw [Finset.mul_sum]
  have hsum4 : (∑ j : Fin n, (Real.sqrt (∫ x in abox n ℓ, (aQ ℓ j Φ x) ^ 2)
            * Real.sqrt (∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2)))
      ≤ Real.sqrt (∑ j : Fin n, ∫ x in abox n ℓ, (aQ ℓ j Φ x) ^ 2)
        * Real.sqrt (∑ j : Fin n, ∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2) := by
    simpa using Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
      (f := fun j : Fin n => ∫ x in abox n ℓ, (aQ ℓ j Φ x) ^ 2)
      (g := fun j : Fin n => ∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2)
      (fun j => integral_nonneg (fun x => sq_nonneg _))
      (fun j => integral_nonneg (fun x => sq_nonneg _))
  have hcn : (∑ j : Fin n, ∫ x in abox n ℓ, (aQ ℓ j Φ x) ^ 2) = cnPlus ℓ Φ := rfl
  have hcS : (∑ j : Fin n, ∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2) = cS1 ℓ Φ := rfl
  have hfinal : |∑ j : Fin n, ∫ x in abox n ℓ, (aQ ℓ j Φ x) * w (x j) * (aP ℓ j Φ x)|
      ≤ K * (Real.sqrt (cnPlus ℓ Φ) * Real.sqrt (cS1 ℓ Φ)) := by
    calc |∑ j : Fin n, ∫ x in abox n ℓ, (aQ ℓ j Φ x) * w (x j) * (aP ℓ j Φ x)|
        ≤ ∑ j : Fin n, |∫ x in abox n ℓ, (aQ ℓ j Φ x) * w (x j) * (aP ℓ j Φ x)| := hsum1
      _ ≤ ∑ j : Fin n, K * (Real.sqrt (∫ x in abox n ℓ, (aQ ℓ j Φ x) ^ 2)
            * Real.sqrt (∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2)) := hsum2
      _ = K * ∑ j : Fin n, (Real.sqrt (∫ x in abox n ℓ, (aQ ℓ j Φ x) ^ 2)
            * Real.sqrt (∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2)) := hsum3
      _ ≤ K * (Real.sqrt (∑ j : Fin n, ∫ x in abox n ℓ, (aQ ℓ j Φ x) ^ 2)
            * Real.sqrt (∑ j : Fin n, ∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum4 hK
      _ = K * (Real.sqrt (cnPlus ℓ Φ) * Real.sqrt (cS1 ℓ Φ)) := by rw [hcn, hcS]
  have hcS1nn : 0 ≤ cS1 ℓ Φ := by
    rw [← hcS]
    exact Finset.sum_nonneg (fun j _ => integral_nonneg (fun x => sq_nonneg _))
  have hsq : Real.sqrt (cS1 ℓ Φ * cnPlus ℓ Φ)
      = Real.sqrt (cnPlus ℓ Φ) * Real.sqrt (cS1 ℓ Φ) := by
    rw [Real.sqrt_mul hcS1nn]
    ring
  have hF : muLine n ℓ w Φ
      = 2 * ∑ j : Fin n, ∫ x in abox n ℓ, (aQ ℓ j Φ x) * w (x j) * (aP ℓ j Φ x) := rfl
  rw [hF, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), hsq]
  linarith [hfinal]

end Work.BoseBoxFock
