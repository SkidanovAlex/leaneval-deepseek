import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Submission.Work.BoseFixR.LatGreen.LatGreenCellFourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.HeatPeriodFixedS` — the fixed-time cell identity

For `s > 0` the cell double integral of the periodisation `P = period W ℓ` against the bounded
kernel `heatPeriod s (ℓ⁻¹•(x−y)) − 1` equals the exponentially damped lattice row
`Σ_k [k ≠ 0] e^{−s‖vec k‖²}(chat W q_k)²` (`q_k = ℓ⁻¹ • vec k`).

This is the "bounded ε-cut" half of the cell-Parseval identity `LatGreenParsevalB`: it is the
pointwise-in-`s` identity that is integrated over `s ∈ (0,∞)` there.  The proof expands
`heatPeriod s u − 1` in its Poisson/θ series (`heatPeriod_sub_one_eq_tsum`, absolutely summable),
exchanges the (x,y)-integrals with the series (`integral_tsum` / Fubini on the product measure)
and applies the per-mode pairing `hcos` (proved in `LatGreenCellFourier.LatGreenCellPairing`).
-/

namespace Work.BoseFixR.LatGreen

open scoped Real BigOperators RealInnerProductSpace
open MeasureTheory

theorem HeatPeriodFixedS {ℓ : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W)
    (hper : ∀ x : EuclideanSpace ℝ (Fin 3),
      Summable (fun n : Fin 3 → ℤ => W (x - Work.BoseFixR.lat ℓ n)))
    (hcos : ∀ k : Fin 3 → ℤ,
      ∫ x in Work.BoseFixR.cell ℓ, ∫ y in Work.BoseFixR.cell ℓ,
          Work.BoseFixR.LatGreen.period W ℓ x * Work.BoseFixR.LatGreen.period W ℓ y
            * Real.cos (inner ℝ (qmom ℓ k) (x - y))
        = (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2)
    {s : ℝ} (hs : 0 < s) :
    ∫ x in Work.BoseFixR.cell ℓ, ∫ y in Work.BoseFixR.cell ℓ,
        Work.BoseFixR.LatGreen.period W ℓ x * Work.BoseFixR.LatGreen.period W ℓ y
          * (Work.BoseFixR.LatGreen.heatPeriod s (ℓ⁻¹ • (x - y)) - 1)
      = ∑' k : Fin 3 → ℤ, if k = 0 then 0 else
          Real.exp (-s * ‖Work.BoseB4.vec k‖ ^ 2)
            * (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2 := by
  set P : EuclideanSpace ℝ (Fin 3) → ℝ := Work.BoseFixR.LatGreen.period W ℓ with hP
  set μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)) :=
    MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ) with hμ
  set D : ℝ := ∑' k : {k : Fin 3 → ℤ // k ≠ 0},
    Real.exp (-s * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2) with hD
  have hDnn : 0 ≤ D := by
    rw [hD]; exact tsum_nonneg fun k => Real.exp_nonneg _
  have hPint : MeasureTheory.Integrable P μ := integrableOn_period hℓ hW hper
  have habs : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => |P p.1| * |P p.2|)
      (μ.prod μ) :=
    (hPint.norm.mul_prod hPint.norm).congr
      (Filter.Eventually.of_forall fun p => by simp [Real.norm_eq_abs])
  have hmeasp : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        P p.1 * P p.2 * (Work.BoseFixR.LatGreen.heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1))
      (μ.prod μ) := by
    refine (((hPint.aestronglyMeasurable.aemeasurable.comp_fst).mul
      (hPint.aestronglyMeasurable.aemeasurable.comp_snd)).mul ?_).aestronglyMeasurable
    exact (((measurable_heatPeriod s hs).comp
      (by fun_prop : Measurable fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ℓ⁻¹ • (p.1 - p.2))).sub measurable_const).aemeasurable
  have hsm : AEStronglyMeasurable
      (Function.uncurry (fun x y : EuclideanSpace ℝ (Fin 3) =>
        P x * P y * (Work.BoseFixR.LatGreen.heatPeriod s (ℓ⁻¹ • (x - y)) - 1))) (μ.prod μ) :=
    hmeasp
  have hbound : ∀ᵐ p ∂(μ.prod μ),
      ‖P p.1 * P p.2 * (Work.BoseFixR.LatGreen.heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1)‖
        ≤ D * (|P p.1| * |P p.2|) := by
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul, abs_mul, hD]
    calc |P p.1| * |P p.2| * |Work.BoseFixR.LatGreen.heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1|
        ≤ |P p.1| * |P p.2| * (∑' k : {k : Fin 3 → ℤ // k ≠ 0},
            Real.exp (-s * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (abs_heatPeriod_sub_one_le s hs (ℓ⁻¹ • (p.1 - p.2)))
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (∑' k : {k : Fin 3 → ℤ // k ≠ 0},
            Real.exp (-s * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2)) * (|P p.1| * |P p.2|) := by
          ring
  have hint : MeasureTheory.Integrable
      (Function.uncurry (fun x y : EuclideanSpace ℝ (Fin 3) =>
        P x * P y * (Work.BoseFixR.LatGreen.heatPeriod s (ℓ⁻¹ • (x - y)) - 1))) (μ.prod μ) :=
    (habs.const_mul D).mono' hsm hbound
  have hswap := MeasureTheory.integral_integral hint
  -- the pointwise series representation
  set F : {k : Fin 3 → ℤ // k ≠ 0} → EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun k p => P p.1 * P p.2 * (Real.exp (-s * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2)
      * Real.cos (inner ℝ (qmom ℓ (k : Fin 3 → ℤ)) (p.1 - p.2))) with hF
  have hpoint : ∀ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
      P p.1 * P p.2 * (Work.BoseFixR.LatGreen.heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1)
        = ∑' k, F k p := by
    intro p
    have h1 : Work.BoseFixR.LatGreen.heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1
        = ∑' k : {k : Fin 3 → ℤ // k ≠ 0},
            (Real.exp (-s * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2)
              * Real.cos (inner ℝ (qmom ℓ (k : Fin 3 → ℤ)) (p.1 - p.2))) := by
      rw [heatPeriod_sub_one_eq_tsum s hs (ℓ⁻¹ • (p.1 - p.2))]
      exact tsum_congr fun k => by rw [cos_qmom]
    rw [h1, ← tsum_mul_left]
  -- integrability of the summands, and summability of their norms
  have hFbdd : ∀ k : {k : Fin 3 → ℤ // k ≠ 0}, ∀ᵐ p ∂(μ.prod μ),
      ‖F k p‖ ≤ Real.exp (-s * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2) * (|P p.1| * |P p.2|) := by
    intro k
    filter_upwards with p
    rw [hF, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |P p.1| * |P p.2|
          * (Real.exp (-s * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2)
            * |Real.cos (inner ℝ (qmom ℓ (k : Fin 3 → ℤ)) (p.1 - p.2))|)
        ≤ |P p.1| * |P p.2| * (Real.exp (-s * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2) * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_nonneg _))
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = Real.exp (-s * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2) * (|P p.1| * |P p.2|) := by
          ring
  have hFint : ∀ k : {k : Fin 3 → ℤ // k ≠ 0}, MeasureTheory.Integrable (F k) (μ.prod μ) := by
    intro k
    have hsm' : AEStronglyMeasurable (F k) (μ.prod μ) := by
      rw [hF]
      refine ((((hPint.aestronglyMeasurable.aemeasurable.comp_fst).mul
        (hPint.aestronglyMeasurable.aemeasurable.comp_snd)).mul
        (measurable_const.mul ((by fun_prop : Measurable fun p :
            EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
            Real.cos (inner ℝ (qmom ℓ (k : Fin 3 → ℤ)) (p.1 - p.2))))).aemeasurable)).aestronglyMeasurable
    exact (habs.const_mul _).mono' hsm' (hFbdd k)
  have hFsum : Summable (fun k : {k : Fin 3 → ℤ // k ≠ 0} =>
      ∫ p, ‖F k p‖ ∂(μ.prod μ)) := by
    have hcoe : Summable (fun k : {k : Fin 3 → ℤ // k ≠ 0} =>
        Real.exp (-s * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2)) :=
      (summable_exp_neg_norm_vec_sq (t := s) hs).subtype _
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun p => norm_nonneg _)
      (fun k => ?_) (hcoe.mul_right (∫ p, |P p.1| * |P p.2| ∂(μ.prod μ)))
    calc ∫ p, ‖F k p‖ ∂(μ.prod μ)
        ≤ ∫ p, Real.exp (-s * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2) * (|P p.1| * |P p.2|)
            ∂(μ.prod μ) := integral_mono_ae (hFint k).norm (habs.const_mul _) (hFbdd k)
      _ = Real.exp (-s * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2)
            * ∫ p, |P p.1| * |P p.2| ∂(μ.prod μ) := integral_const_mul _ _
  have htsum := MeasureTheory.hasSum_integral_of_summable_integral_norm (μ := μ.prod μ) hFint hFsum
  -- the value of each summand integral
  have hval : ∀ k : {k : Fin 3 → ℤ // k ≠ 0},
      ∫ p, F k p ∂(μ.prod μ)
        = Real.exp (-s * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2)
            * (Work.BoseFixR.chat W (qmom ℓ (k : Fin 3 → ℤ))) ^ 2 := by
    intro k
    have hcosm : AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          P p.1 * P p.2 * Real.cos (inner ℝ (qmom ℓ (k : Fin 3 → ℤ)) (p.1 - p.2))) (μ.prod μ) := by
      refine (((hPint.aestronglyMeasurable.aemeasurable.comp_fst).mul
        (hPint.aestronglyMeasurable.aemeasurable.comp_snd)).mul
        (by fun_prop : Measurable fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Real.cos (inner ℝ (qmom ℓ (k : Fin 3 → ℤ)) (p.1 - p.2))).aemeasurable).aestronglyMeasurable
    have hprodint : MeasureTheory.Integrable
        (Function.uncurry (fun x y : EuclideanSpace ℝ (Fin 3) =>
          P x * P y * Real.cos (inner ℝ (qmom ℓ (k : Fin 3 → ℤ)) (x - y)))) (μ.prod μ) := by
      refine habs.mono' hcosm ?_
      filter_upwards with p
      have hp : Function.uncurry (fun x y : EuclideanSpace ℝ (Fin 3) =>
          P x * P y * Real.cos (inner ℝ (qmom ℓ (k : Fin 3 → ℤ)) (x - y))) p
          = P p.1 * P p.2 * Real.cos (inner ℝ (qmom ℓ (k : Fin 3 → ℤ)) (p.1 - p.2)) := rfl
      rw [hp, Real.norm_eq_abs, abs_mul, abs_mul]
      simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hpair : ∫ x, ∫ y, P x * P y * Real.cos (inner ℝ (qmom ℓ (k : Fin 3 → ℤ)) (x - y))
          ∂μ ∂μ = (Work.BoseFixR.chat W (qmom ℓ (k : Fin 3 → ℤ))) ^ 2 := by
      rw [hμ]
      exact hcos (k : Fin 3 → ℤ)
    rw [hF]
    rw [show (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          P p.1 * P p.2 * (Real.exp (-s * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2)
            * Real.cos (inner ℝ (qmom ℓ (k : Fin 3 → ℤ)) (p.1 - p.2))))
        = fun p => Real.exp (-s * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2)
            * (P p.1 * P p.2 * Real.cos (inner ℝ (qmom ℓ (k : Fin 3 → ℤ)) (p.1 - p.2))) from
      funext fun p => by ring]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [← MeasureTheory.integral_integral hprodint]
    exact hpair
  -- the subtype sum in `if`-form
  have hsub : (∑' k : ({k : Fin 3 → ℤ | k ≠ 0} : Set (Fin 3 → ℤ)),
        Real.exp (-s * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2)
          * (Work.BoseFixR.chat W (qmom ℓ (k : Fin 3 → ℤ))) ^ 2)
      = ∑' k : Fin 3 → ℤ, if k = 0 then 0 else
          Real.exp (-s * ‖Work.BoseB4.vec k‖ ^ 2)
            * (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2 := by
    rw [tsum_subtype (s := {k : Fin 3 → ℤ | k ≠ 0})
      (f := fun n : Fin 3 → ℤ => Real.exp (-s * ‖Work.BoseB4.vec n‖ ^ 2)
        * (Work.BoseFixR.chat W (qmom ℓ n)) ^ 2)]
    refine tsum_congr fun k => ?_
    by_cases hk : k = 0 <;> simp [Set.indicator, hk]
  calc ∫ x in Work.BoseFixR.cell ℓ, ∫ y in Work.BoseFixR.cell ℓ,
        Work.BoseFixR.LatGreen.period W ℓ x * Work.BoseFixR.LatGreen.period W ℓ y
          * (Work.BoseFixR.LatGreen.heatPeriod s (ℓ⁻¹ • (x - y)) - 1)
      = ∫ p, P p.1 * P p.2
          * (Work.BoseFixR.LatGreen.heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1) ∂(μ.prod μ) := hswap
    _ = ∫ p, ∑' k, F k p ∂(μ.prod μ) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑' k, ∫ p, F k p ∂(μ.prod μ) := htsum.tsum_eq.symm
    _ = ∑' k : {k : Fin 3 → ℤ // k ≠ 0},
          Real.exp (-s * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2)
            * (Work.BoseFixR.chat W (qmom ℓ (k : Fin 3 → ℤ))) ^ 2 := tsum_congr hval
    _ = ∑' k : Fin 3 → ℤ, if k = 0 then 0 else
          Real.exp (-s * ‖Work.BoseB4.vec k‖ ^ 2)
            * (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2 := hsub

end Work.BoseFixR.LatGreen
