import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixR.LatGreen.LatGreenParsevalBDefs
import Submission.Work.BoseFixR.LatGreen.chat_cellIntegral
import Submission.Work.BoseFixR.LatGreen.integrableOn_period
import Submission.Work.BoseFixR.LatGreen.period_even
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

open scoped Real BigOperators RealInnerProductSpace
open MeasureTheory

/-!
# `Work.BoseFixR.LatGreen.LatGreenCellFourier` — cell Fourier coefficients and the cosine pairing

The three cell-integral lemmas on which the `(B)`-carrying cell Parseval identity
`Work.BoseFixR.LatGreen.LatGreenParsevalB` rests, for the *torus* momenta
`q_k = qmom ℓ k = ℓ⁻¹ • vec k` (`vec k = 2πk`, so `⟨q_k, lat ℓ n⟩ = 2π(k·n)` drops out of the
periodisation):

* `LatGreenCellChat` — `chat W q_k = ∫_{cell ℓ} P(x)cos⟨q_k,x⟩dx` for the periodisation
  `P = period W ℓ`;
* `LatGreenCellSine` — `∫_{cell ℓ} P(x)sin⟨q_k,x⟩dx = 0` for an even charge `W` (this is the
  input that kills the sine cross terms; the identity is false without it);
* `LatGreenCellPairing` — `∬_{cell ℓ × cell ℓ} P(x)P(y)cos⟨q_k,x−y⟩ = (chat W q_k)²`.

The proofs are the cell-argument of `chat_cellIntegral` (tiling identity, phase drop,
`tsum`/integral exchange) together with the parity computation for the sine, and Fubini for
products of `L¹` functions for the pairing. -/

/-- The phase of a torus momentum against an `ℓ`-lattice vector is a multiple of `2π`. -/
lemma inner_qmom_lat {ℓ : ℝ} (hℓ : ℓ ≠ 0) (k n : Fin 3 → ℤ) :
    inner ℝ (qmom ℓ k) (Work.BoseFixR.lat ℓ n)
      = 2 * Real.pi * ((∑ i, k i * n i : ℤ) : ℝ) := by
  rw [qmom, Work.BoseFixR.lat_eq_smul, real_inner_smul_left, real_inner_smul_right,
    ← mul_assoc, inv_mul_cancel₀ hℓ, one_mul]
  exact Work.BoseFixR.inner_vec_lat1 k n

/-- The cosine of a torus momentum is invariant under the lattice `ℓℤ³`. -/
lemma cos_qmom_add_lat {ℓ : ℝ} (hℓ : ℓ ≠ 0) (k n : Fin 3 → ℤ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    Real.cos (inner ℝ (qmom ℓ k) (x + Work.BoseFixR.lat ℓ n))
      = Real.cos (inner ℝ (qmom ℓ k) x) := by
  rw [inner_add_right, inner_qmom_lat hℓ k n,
    show 2 * Real.pi * ((∑ i, k i * n i : ℤ) : ℝ)
        = ((∑ i, k i * n i : ℤ) : ℝ) * (2 * Real.pi) by ring]
  exact Real.cos_add_int_mul_two_pi _ _

theorem LatGreenCellChat {ℓ : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W)
    (hper : ∀ x : EuclideanSpace ℝ (Fin 3),
      Summable (fun n : Fin 3 → ℤ => W (x - Work.BoseFixR.lat ℓ n)))
    (k : Fin 3 → ℤ) :
    Work.BoseFixR.chat W (qmom ℓ k)
      = ∫ x in Work.BoseFixR.cell ℓ,
          Work.BoseFixR.LatGreen.period W ℓ x * Real.cos (inner ℝ (qmom ℓ k) x) := by
  set q : EuclideanSpace ℝ (Fin 3) := qmom ℓ k with hq
  rw [Work.BoseB7AK.W1low.chat_eq_integral_cos hW q]
  have hcosbdd : ∀ y : EuclideanSpace ℝ (Fin 3), ‖Real.cos (inner ℝ q y)‖ ≤ (1 : ℝ) := by
    intro y
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hfint : MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      W y * Real.cos (inner ℝ q y)) :=
    hW.mul_bdd (c := 1) (by fun_prop) (Filter.Eventually.of_forall hcosbdd)
  rw [Work.BoseFixR.tiling_integral hℓ (fun y => W y * Real.cos (inner ℝ q y)) hfint]
  have hstep2 : (∑' n : Fin 3 → ℤ, ∫ x in Work.BoseFixR.cell ℓ,
        W (x + Work.BoseFixR.lat ℓ n) * Real.cos (inner ℝ q (x + Work.BoseFixR.lat ℓ n)))
      = ∑' n : Fin 3 → ℤ, ∫ x in Work.BoseFixR.cell ℓ,
        W (x + Work.BoseFixR.lat ℓ n) * Real.cos (inner ℝ q x) :=
    tsum_congr fun n => by
      refine MeasureTheory.setIntegral_congr_fun
        (show MeasurableSet (Work.BoseFixR.cell ℓ) from Work.BoseFixR.measurableSet_boxL ℓ)
        (fun x _ => ?_)
      rw [hq, cos_qmom_add_lat (ne_of_gt hℓ) k n x]
  rw [hstep2]
  have hFint : ∀ n : Fin 3 → ℤ, MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin 3) =>
        W (x + Work.BoseFixR.lat ℓ n) * Real.cos (inner ℝ q x))
      (MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ)) := by
    intro n
    have h := ((hW.comp_add_right (Work.BoseFixR.lat ℓ n)).integrableOn
      (s := Work.BoseFixR.cell ℓ)).mul_bdd
      (c := 1) (by fun_prop) (Filter.Eventually.of_forall hcosbdd)
    simpa only using h
  have hB : Summable (fun n : Fin 3 → ℤ =>
      ∫ x : EuclideanSpace ℝ (Fin 3),
        ‖W (x + Work.BoseFixR.lat ℓ n) * Real.cos (inner ℝ q x)‖
        ∂(MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ))) := by
    refine Summable.of_nonneg_of_le (fun n => MeasureTheory.integral_nonneg fun x => norm_nonneg _)
      (fun n => ?_) (summable_setIntegral_abs_lat hℓ hW)
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x => norm_nonneg _)
      ((hW.abs.comp_add_right (Work.BoseFixR.lat ℓ n)).integrableOn
        (s := Work.BoseFixR.cell ℓ)) ?_
    filter_upwards with x
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _)
      (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  have hexch := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (μ := MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ)) hFint hB
  have hstep3 : (∑' n : Fin 3 → ℤ, ∫ x in Work.BoseFixR.cell ℓ,
        W (x + Work.BoseFixR.lat ℓ n) * Real.cos (inner ℝ q x))
      = ∫ x in Work.BoseFixR.cell ℓ, ∑' n : Fin 3 → ℤ,
        W (x + Work.BoseFixR.lat ℓ n) * Real.cos (inner ℝ q x) :=
    hexch.tsum_eq
  rw [hstep3]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  show (∑' n : Fin 3 → ℤ, W (x + Work.BoseFixR.lat ℓ n) * Real.cos (inner ℝ q x))
      = Work.BoseFixR.LatGreen.period W ℓ x * Real.cos (inner ℝ q x)
  rw [tsum_mul_right, Work.BoseFixR.LatGreen.period]
  congr 1
  exact tsum_lat_add_eq_tsum_lat_sub ℓ W x

end Work.BoseFixR.LatGreen

namespace Work.BoseFixR.LatGreen

/-- Negation preserves the closed cell. -/
lemma neg_mem_cell_iff {ℓ : ℝ} {x : EuclideanSpace ℝ (Fin 3)} :
    -x ∈ Work.BoseFixR.cell ℓ ↔ x ∈ Work.BoseFixR.cell ℓ := by
  constructor <;> intro h i
  · have := h i
    simpa using this
  · have := h i
    simpa using this

theorem LatGreenCellSine {ℓ : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W)
    (hWev : ∀ x : EuclideanSpace ℝ (Fin 3), W (-x) = W x)
    (hper : ∀ x : EuclideanSpace ℝ (Fin 3),
      Summable (fun n : Fin 3 → ℤ => W (x - Work.BoseFixR.lat ℓ n)))
    (k : Fin 3 → ℤ) :
    ∫ x in Work.BoseFixR.cell ℓ,
        Work.BoseFixR.LatGreen.period W ℓ x
          * Real.sin (inner ℝ (qmom ℓ k) x) = 0 := by
  set q : EuclideanSpace ℝ (Fin 3) := qmom ℓ k with hq
  set G : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun x => Work.BoseFixR.LatGreen.period W ℓ x * Real.sin (inner ℝ q x) with hG
  have hcellm : MeasurableSet (Work.BoseFixR.cell ℓ) := Work.BoseFixR.measurableSet_boxL ℓ
  have hpoint : ∀ x : EuclideanSpace ℝ (Fin 3),
      (Work.BoseFixR.cell ℓ).indicator G (-x) = -((Work.BoseFixR.cell ℓ).indicator G x) := by
    intro x
    by_cases hx : x ∈ Work.BoseFixR.cell ℓ
    · rw [Set.indicator_of_mem (neg_mem_cell_iff.mpr hx), Set.indicator_of_mem hx]
      simp only [hG]
      rw [period_even hWev ℓ x, inner_neg_right, Real.sin_neg]
      ring
    · rw [Set.indicator_of_notMem (fun h => hx (neg_mem_cell_iff.mp h)),
        Set.indicator_of_notMem hx, neg_zero]
  have hA : ∫ x, (Work.BoseFixR.cell ℓ).indicator G x
      = ∫ x, (Work.BoseFixR.cell ℓ).indicator G (-x) :=
    (MeasureTheory.integral_neg_eq_self (fun x => (Work.BoseFixR.cell ℓ).indicator G x)
      MeasureTheory.volume).symm
  have hB : ∫ x, (Work.BoseFixR.cell ℓ).indicator G (-x)
      = ∫ x, -((Work.BoseFixR.cell ℓ).indicator G x) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)
  have hC : ∫ x, -((Work.BoseFixR.cell ℓ).indicator G x)
      = -∫ x, (Work.BoseFixR.cell ℓ).indicator G x := MeasureTheory.integral_neg _
  rw [← MeasureTheory.integral_indicator hcellm (μ := MeasureTheory.volume) (f := G)]
  linarith

end Work.BoseFixR.LatGreen

namespace Work.BoseFixR.LatGreen

theorem LatGreenCellPairing {ℓ : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W)
    (hWev : ∀ x : EuclideanSpace ℝ (Fin 3), W (-x) = W x)
    (hper : ∀ x : EuclideanSpace ℝ (Fin 3),
      Summable (fun n : Fin 3 → ℤ => W (x - Work.BoseFixR.lat ℓ n)))
    (k : Fin 3 → ℤ) :
    ∫ x in Work.BoseFixR.cell ℓ, ∫ y in Work.BoseFixR.cell ℓ,
        Work.BoseFixR.LatGreen.period W ℓ x * Work.BoseFixR.LatGreen.period W ℓ y
          * Real.cos (inner ℝ (qmom ℓ k) (x - y))
      = (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2 := by
  set q : EuclideanSpace ℝ (Fin 3) := qmom ℓ k with hq
  set μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)) :=
    MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ) with hμ
  have hPi : MeasureTheory.Integrable (Work.BoseFixR.LatGreen.period W ℓ) μ :=
    integrableOn_period hℓ hW hper
  have hcosb : ∀ y : EuclideanSpace ℝ (Fin 3), ‖Real.cos (inner ℝ q y)‖ ≤ (1 : ℝ) := by
    intro y; rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hsinb : ∀ y : EuclideanSpace ℝ (Fin 3), ‖Real.sin (inner ℝ q y)‖ ≤ (1 : ℝ) := by
    intro y; rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have hIc : MeasureTheory.Integrable
      (fun y => Work.BoseFixR.LatGreen.period W ℓ y * Real.cos (inner ℝ q y)) μ :=
    hPi.mul_bdd (by fun_prop) (Filter.Eventually.of_forall hcosb)
  have hIs : MeasureTheory.Integrable
      (fun y => Work.BoseFixR.LatGreen.period W ℓ y * Real.sin (inner ℝ q y)) μ :=
    hPi.mul_bdd (by fun_prop) (Filter.Eventually.of_forall hsinb)
  have hchat : ∫ x, Work.BoseFixR.LatGreen.period W ℓ x * Real.cos (inner ℝ q x) ∂μ
      = Work.BoseFixR.chat W q := by
    rw [hμ]
    have hcell := LatGreenCellChat hℓ hW hper k
    rw [← hq] at hcell
    exact hcell.symm
  have hsin : ∫ x, Work.BoseFixR.LatGreen.period W ℓ x * Real.sin (inner ℝ q x) ∂μ = 0 := by
    rw [hμ]
    have hcell := LatGreenCellSine hℓ hW hWev hper k
    rw [← hq] at hcell
    exact hcell
  calc ∫ x in Work.BoseFixR.cell ℓ, ∫ y in Work.BoseFixR.cell ℓ,
        Work.BoseFixR.LatGreen.period W ℓ x * Work.BoseFixR.LatGreen.period W ℓ y
          * Real.cos (inner ℝ q (x - y))
      = ∫ x, ∫ y, ((Work.BoseFixR.LatGreen.period W ℓ x * Real.cos (inner ℝ q x))
            * (Work.BoseFixR.LatGreen.period W ℓ y * Real.cos (inner ℝ q y))
          + (Work.BoseFixR.LatGreen.period W ℓ x * Real.sin (inner ℝ q x))
            * (Work.BoseFixR.LatGreen.period W ℓ y * Real.sin (inner ℝ q y))) ∂μ ∂μ := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with x
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with y
        rw [inner_sub_right, Real.cos_sub]
        ring
    _ = ∫ x, ((Work.BoseFixR.LatGreen.period W ℓ x * Real.cos (inner ℝ q x))
            * (∫ y, Work.BoseFixR.LatGreen.period W ℓ y * Real.cos (inner ℝ q y) ∂μ)
          + (Work.BoseFixR.LatGreen.period W ℓ x * Real.sin (inner ℝ q x))
            * (∫ y, Work.BoseFixR.LatGreen.period W ℓ y * Real.sin (inner ℝ q y) ∂μ)) ∂μ := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with x
        rw [MeasureTheory.integral_add (hIc.const_mul _) (hIs.const_mul _),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ = (∫ x, Work.BoseFixR.LatGreen.period W ℓ x * Real.cos (inner ℝ q x) ∂μ)
          * (∫ y, Work.BoseFixR.LatGreen.period W ℓ y * Real.cos (inner ℝ q y) ∂μ)
        + (∫ x, Work.BoseFixR.LatGreen.period W ℓ x * Real.sin (inner ℝ q x) ∂μ)
          * (∫ y, Work.BoseFixR.LatGreen.period W ℓ y * Real.sin (inner ℝ q y) ∂μ) := by
        rw [MeasureTheory.integral_add (hIc.mul_const _) (hIs.mul_const _),
          MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const]
    _ = (Work.BoseFixR.chat W q) ^ 2 := by
        rw [hchat, hsin]
        ring

end Work.BoseFixR.LatGreen
