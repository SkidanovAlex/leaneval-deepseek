import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.SqrtKin.kinFT_weight2_integrable
import Submission.Work.BoseBoxFock.continuum_heatSubordination_v2
import Submission.Work.BoseBoxFock.lattice_heatSubordination
import Submission.Work.BoseBoxFock.moment_two_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PhiTaylorQuant` — the quantitative Taylor bound for the heat deficit

For `g` smooth with `tsupport g ⊆ ball 0 (ℓ/2)`, define (as in `heatSampling_smallT`)

* `Λ(t) = Σ_n ℓ⁻³ e^{−t‖k_n‖²}‖ĝ(k_n)‖²`  (lattice heat content),
* `R(t) = (2π)⁻³ ∫ e^{−t‖p‖²}‖ĝ(p)‖²`      (continuum heat content),
* `Φ(t) = 2R(t) + R0 − 3Λ(t)`.

The *published* lemma `heatSampling_smallT` proves `Φ(t) ≥ 0` under the smallness hypothesis
`3t·S4 ≤ 2·S2`.  This file banks the **quantitative** statement behind that proof, valid for
*every* `t > 0` and with no smallness hypothesis:

    Φ(t) ≥ t·S2 − (3/2)·t²·S4 ,   S2 = Σ_n ℓ⁻³‖k_n‖²‖ĝ(k_n)‖²,  S4 = Σ_n ℓ⁻³‖k_n‖⁴‖ĝ(k_n)‖².

Indeed `LT := R0 − Λ ≥ t S2 − (t²/2) S4` (lattice Taylor, `1 − e^{−y} ≥ y − y²/2`) while
`LR := R0 − R ≤ t S2` (continuum, `1 − e^{−y} ≤ y`), and `Φ = 3 LT − 2 LR`.

Consequence (positive part of the bound): `∫_0^{t₂} t^{−3/2}Φ(t) dt ≥ (4/3)·S2·√(2S2/(3S4))`
with `t₂ = 2S2/(3S4)`, i.e. `2√π (3S1 − 2R1) ≥ 1.0885·S2^{3/2}/√S4`.

**Status: this file is sorry-free and self-contained** (the two exponential Taylor lemmas are
`private` in `heatSampling_smallT`, so they are re-derived here).
-/

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators Real

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Elementary exponential bounds -/

private lemma exp_neg_le_one_sub_add_sq {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-y) ≤ 1 - y + y ^ 2 / 2 := by
  have h1 : (1 : ℝ) + y + y ^ 2 / 2 ≤ Real.exp y := Real.quadratic_le_exp_of_nonneg hy
  have hpos : (0 : ℝ) < 1 + y + y ^ 2 / 2 := by positivity
  have h2 : (Real.exp y)⁻¹ ≤ (1 + y + y ^ 2 / 2)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le hpos h1
  have h3 : (1 + y + y ^ 2 / 2)⁻¹ ≤ (1 - y + y ^ 2 / 2) := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    have h4 : (1 - y + y ^ 2 / 2) * (1 + y + y ^ 2 / 2) = 1 + (y ^ 2) ^ 2 / 4 := by ring
    nlinarith [sq_nonneg (y ^ 2)]
  rw [Real.exp_neg]
  linarith

lemma one_sub_exp_neg_ge {y : ℝ} (hy : 0 ≤ y) : y - y ^ 2 / 2 ≤ 1 - Real.exp (-y) := by
  have h := exp_neg_le_one_sub_add_sq hy
  linarith

lemma one_sub_exp_neg_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ 1 - Real.exp (-y) := by
  have h : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

lemma one_sub_exp_neg_le_self (y : ℝ) : 1 - Real.exp (-y) ≤ y := by
  have h := Real.one_sub_le_exp_neg y
  linarith

/-! ## 2. The two moment bounds -/

/-- Lattice side: `Σ aᵢ (t xᵢ − t²xᵢ²/2) ≤ Σ aᵢ (1 − e^{−t xᵢ})`. -/
lemma heatLossLattice_ge {ι : Type*} [Countable ι] {a x : ι → ℝ} {t : ℝ}
    (ha : ∀ i, 0 ≤ a i) (haS : Summable a) (hx : ∀ i, 0 ≤ x i)
    (hx2 : Summable (fun i => a i * x i)) (hx4 : Summable (fun i => a i * x i ^ 2))
    (ht : 0 < t) :
    t * (∑' i, a i * x i) - (t ^ 2 / 2) * (∑' i, a i * x i ^ 2)
      ≤ ∑' i, a i * (1 - Real.exp (-(t * x i))) := by
  have hpt : ∀ i, a i * (t * x i - (t * x i) ^ 2 / 2)
      ≤ a i * (1 - Real.exp (-(t * x i))) := fun i =>
    mul_le_mul_of_nonneg_left (one_sub_exp_neg_ge (mul_nonneg ht.le (hx i))) (ha i)
  have hgsum : Summable (fun i => a i * (t * x i - (t * x i) ^ 2 / 2)) := by
    have h1 : Summable (fun i => t * (a i * x i)) := hx2.mul_left t
    have h2 : Summable (fun i => t ^ 2 / 2 * (a i * x i ^ 2)) := hx4.mul_left _
    exact (h1.sub h2).congr (fun i => by ring)
  have hfsum : Summable (fun i => a i * (1 - Real.exp (-(t * x i)))) := by
    refine Summable.of_nonneg_of_le
      (fun i => mul_nonneg (ha i) (one_sub_exp_neg_nonneg (mul_nonneg ht.le (hx i))))
      (fun i => ?_) haS
    refine mul_le_of_le_one_right (ha i) ?_
    have := Real.exp_pos (-(t * x i)); linarith
  have hmain := Summable.tsum_le_tsum hpt hgsum hfsum
  have hval : (∑' i, a i * (t * x i - (t * x i) ^ 2 / 2))
      = t * (∑' i, a i * x i) - (t ^ 2 / 2) * (∑' i, a i * x i ^ 2) := by
    rw [show (∑' i, a i * (t * x i - (t * x i) ^ 2 / 2))
        = ∑' i, (t * (a i * x i) - t ^ 2 / 2 * (a i * x i ^ 2)) from
      tsum_congr (fun i => by ring)]
    rw [Summable.tsum_sub (hx2.mul_left t) (hx4.mul_left _),
      Summable.tsum_mul_left t hx2, Summable.tsum_mul_left (t ^ 2 / 2) hx4]
  rwa [hval] at hmain

/-- Continuum side: `∫ (1 − e^{−t‖p‖²}) f ≤ t ∫ ‖p‖² f` for `f ≥ 0`. -/
lemma heatLossContinuum_le {f : E3 → ℝ} (hf0 : ∀ p, 0 ≤ f p)
    (hint : Integrable (fun p => ‖p‖ ^ 2 * f p)) {t : ℝ} (ht : 0 < t) :
    ∫ p, (1 - Real.exp (-(t * ‖p‖ ^ 2))) * f p ≤ t * ∫ p, ‖p‖ ^ 2 * f p := by
  have hpt : ∀ p : E3, (1 - Real.exp (-(t * ‖p‖ ^ 2))) * f p ≤ t * (‖p‖ ^ 2 * f p) := by
    intro p
    have hb := one_sub_exp_neg_le_self (t * ‖p‖ ^ 2)
    calc (1 - Real.exp (-(t * ‖p‖ ^ 2))) * f p ≤ (t * ‖p‖ ^ 2) * f p :=
          mul_le_mul_of_nonneg_right hb (hf0 p)
      _ = t * (‖p‖ ^ 2 * f p) := by ring
  have hnn : ∀ p : E3, 0 ≤ (1 - Real.exp (-(t * ‖p‖ ^ 2))) * f p := fun p =>
    mul_nonneg (one_sub_exp_neg_nonneg (mul_nonneg ht.le (sq_nonneg _))) (hf0 p)
  have hmono := integral_mono_of_nonneg (μ := volume)
    (f := fun p : E3 => (1 - Real.exp (-(t * ‖p‖ ^ 2))) * f p)
    (g := fun p : E3 => t * (‖p‖ ^ 2 * f p))
    (Filter.Eventually.of_forall hnn) (hint.const_mul t) (Filter.Eventually.of_forall hpt)
  rwa [integral_const_mul] at hmono

/-! ## 3. The heat losses in the notation of the target -/

/-- The lattice heat content `Λ(t)`. -/
noncomputable def latHeat (ℓ t : ℝ) (g : E3 → ℂ) : ℝ :=
  ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))
    * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2

/-- The continuum heat content `R(t)`. -/
noncomputable def contHeat (g : E3 → ℂ) (t : ℝ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, Real.exp (-(t * ‖p‖ ^ 2))
    * ‖Submission.BoseGases.kinFT g p‖ ^ 2

/-- The lattice second moment `S2`. -/
noncomputable def latS2 (ℓ : ℝ) (g : E3 → ℂ) : ℝ :=
  ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ 2
    * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2

/-- The lattice fourth moment `S4`. -/
noncomputable def latS4 (ℓ : ℝ) (g : E3 → ℂ) : ℝ :=
  ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ 4
    * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2

/-- **The quantitative Taylor bound for the heat deficit.**

For `g` smooth with `tsupport g ⊆ ball 0 (ℓ/2)` and every `t > 0`:
`Φ(t) = 2R(t) + R0 − 3Λ(t) ≥ t·S2 − (3/2)·t²·S4`.

(Proof: `Φ = 3 LT − 2 LR` with `LT = R0 − Λ`, `LR = R0 − R`; `LT ≥ t S2 − (t²/2) S4` by the
lattice Taylor bound applied to `a n = (ℓ³)⁻¹‖ĝ(k_n)‖²`, `x n = ‖k_n‖²`; `LR ≤ t S2` by the
continuum bound applied to `F = ‖ĝ‖²` with `S2 = (2π)⁻³∫‖p‖²F` (the second-moment identity).) -/
theorem phi_taylor_quant {ℓ : ℝ} (hℓ : 0 < ℓ) {g : E3 → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ/2))
    {t : ℝ} (ht : 0 < t) :
    2 * contHeat g t + ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2)
        - 3 * latHeat ℓ t g
      ≥ t * latS2 ℓ g - (3 / 2) * t ^ 2 * latS4 ℓ g := by
  -- compact support of `g`
  have hgc : HasCompactSupport g := by
    rw [HasCompactSupport, Metric.isCompact_iff_isClosed_bounded]
    exact ⟨isClosed_tsupport g, Metric.isBounded_ball.subset hgsupp⟩
  -- notation
  set F : E3 → ℝ := fun p => ‖Submission.BoseGases.kinFT g p‖ ^ 2 with hF
  have hF0 : ∀ p, 0 ≤ F p := fun p => by rw [hF]; positivity
  set a : (Fin 3 → ℤ) → ℝ := fun n => (ℓ ^ 3)⁻¹ * F (kmomInt ℓ n) with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n => by rw [ha]; positivity
  have haS : Summable a := by
    refine (summable_lattice_kinFT_weight hℓ hg hgc 0).congr (fun n => ?_)
    rw [ha, hF]; ring
  set S2 : ℝ := ∑' n : Fin 3 → ℤ, a n * ‖kmomInt ℓ n‖ ^ 2 with hS2
  set S4 : ℝ := ∑' n : Fin 3 → ℤ, a n * ‖kmomInt ℓ n‖ ^ 4 with hS4
  set NN : ℝ := ∑' n : Fin 3 → ℤ, a n with hN
  set Λ : ℝ := ∑' n : Fin 3 → ℤ, a n * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2)) with hΛ
  set Rt : ℝ := ((2 * Real.pi) ^ 3)⁻¹ *
      ∫ p : E3, Real.exp (-(t * ‖p‖ ^ 2)) * F p with hRt
  have hFint : Integrable F := by
    simpa [hF] using SqrtKin.kinFT_sq_integrable (g := g) hg hgc
  have hw2int : Integrable (fun p : E3 => ‖p‖ ^ 2 * F p) := by
    simpa [hF] using SqrtKin.kinFT_weight2_integrable (g := g) hg hgc
  have hmom : S2 = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖p‖ ^ 2 * F p := by
    rw [hS2, show (∑' n : Fin 3 → ℤ, a n * ‖kmomInt ℓ n‖ ^ 2)
        = ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ 2
            * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 from
      tsum_congr (fun n => by rw [ha, hF]; ring)]
    simpa [hF] using moment_two_kinFT hℓ hg hgsupp
  have hsum2 : Summable (fun n : Fin 3 → ℤ => a n * ‖kmomInt ℓ n‖ ^ 2) := by
    refine (summable_lattice_kinFT_weight hℓ hg hgc 2).congr (fun n => ?_)
    rw [ha, hF]; ring
  have hsum4 : Summable (fun n : Fin 3 → ℤ => a n * ‖kmomInt ℓ n‖ ^ 4) := by
    refine (summable_lattice_kinFT_weight hℓ hg hgc 4).congr (fun n => ?_)
    rw [ha, hF]; ring
  have hheat : Summable (fun n : Fin 3 → ℤ => a n * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (ha0 n) (Real.exp_nonneg _))
      (fun n => ?_) haS
    refine mul_le_of_le_one_right (ha0 n) ?_
    rw [Real.exp_le_one_iff]; nlinarith [ht, sq_nonneg ‖kmomInt ℓ n‖]
  -- the two heat losses
  set LT : ℝ := ∑' n : Fin 3 → ℤ, a n * (1 - Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))) with hLT
  set LR : ℝ := ((2 * Real.pi) ^ 3)⁻¹ *
      ∫ p : E3, (1 - Real.exp (-(t * ‖p‖ ^ 2))) * F p with hLR
  have hLT_eq : LT = NN - Λ := by
    rw [hLT, hN, hΛ]
    rw [show (∑' n : Fin 3 → ℤ, a n * (1 - Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))))
        = ∑' n : Fin 3 → ℤ, (a n - a n * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))) from
      tsum_congr (fun n => by ring)]
    exact Summable.tsum_sub haS hheat
  have heFint : Integrable (fun p : E3 => Real.exp (-(t * ‖p‖ ^ 2)) * F p) := by
    refine hFint.mono' ?_ ?_
    · have hc : Continuous (fun p : E3 => -(t * ‖p‖ ^ 2)) :=
        (continuous_const.mul (continuous_norm.pow 2)).neg
      exact (Real.continuous_exp.comp hc).aestronglyMeasurable.mul hFint.aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (hF0 p))]
      refine mul_le_of_le_one_left (hF0 p) ?_
      rw [Real.exp_le_one_iff]; nlinarith [ht, sq_nonneg ‖p‖]
  have hint_eq : (∫ p : E3, (1 - Real.exp (-(t * ‖p‖ ^ 2))) * F p)
      = (∫ p : E3, F p) - ∫ p : E3, Real.exp (-(t * ‖p‖ ^ 2)) * F p := by
    rw [show (∫ p : E3, (1 - Real.exp (-(t * ‖p‖ ^ 2))) * F p)
        = ∫ p : E3, (F p - Real.exp (-(t * ‖p‖ ^ 2)) * F p) from
      integral_congr_ae (Filter.Eventually.of_forall (fun p => by ring))]
    exact integral_sub hFint heFint
  have hLR_eq : LR = ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, F p) - Rt := by
    rw [hLR, hRt, hint_eq, mul_sub]
  -- the two quantitative bounds
  have hT_ge : t * S2 - (t ^ 2 / 2) * S4 ≤ LT := by
    have hsum4sq : Summable (fun n : Fin 3 → ℤ => a n * (‖kmomInt ℓ n‖ ^ 2) ^ 2) :=
      hsum4.congr (fun n => by ring)
    have h := heatLossLattice_ge (a := a) (x := fun n : Fin 3 → ℤ => ‖kmomInt ℓ n‖ ^ 2)
      ha0 haS (fun n => by positivity) hsum2 hsum4sq ht
    have hS4sq : S4 = ∑' n : Fin 3 → ℤ, a n * (‖kmomInt ℓ n‖ ^ 2) ^ 2 := by
      rw [hS4]; exact tsum_congr (fun n => by ring)
    rw [← hS2, ← hS4sq] at h
    rw [hLT]
    exact h
  have hLR_le : LR ≤ t * S2 := by
    rw [hLR]
    have h := heatLossContinuum_le hF0 hw2int ht
    have hc : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
    calc ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, (1 - Real.exp (-(t * ‖p‖ ^ 2))) * F p)
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * (t * ∫ p : E3, ‖p‖ ^ 2 * F p) :=
          mul_le_mul_of_nonneg_left h hc
      _ = t * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖p‖ ^ 2 * F p) := by ring
      _ = t * S2 := by rw [← hmom]
  -- combine the two quantitative bounds
  have hfine : t * S2 - (3 / 2) * t ^ 2 * S4 ≤ 3 * LT - 2 * LR := by
    nlinarith [hT_ge, hLR_le]
  -- the frame identity: the total lattice mass is the total continuum mass
  have hframe : NN = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, F p := by
    rw [hN, hF]
    simpa using frame_lattice_ball (ℓ := ℓ) hℓ hg hgc
      (hgsupp.trans (ball_subset_corpusBox_boxL hℓ))
  -- `3 LT − 2 LR = 2 Rt + (2π)⁻³∫F − 3 Λ`
  have hcomb : 3 * LT - 2 * LR
      = 2 * Rt + ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, F p) - 3 * Λ := by
    rw [hLT_eq, hLR_eq]
    linarith [hframe]
  -- rewrite the goal in local notation
  have hgoal1 : latHeat ℓ t g = Λ := by
    simp only [latHeat, hΛ]
    apply tsum_congr; intro n
    simp only [ha, hF]; ring
  have hgoal2 : latS2 ℓ g = S2 := by
    simp only [latS2, hS2]
    apply tsum_congr; intro n
    simp only [ha, hF]; ring
  have hgoal3 : latS4 ℓ g = S4 := by
    simp only [latS4, hS4]
    apply tsum_congr; intro n
    simp only [ha, hF]; ring
  have hgoal4 : contHeat g t = Rt := by
    simp only [contHeat, hRt, hF]
  have hgoal5 : ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      = ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, F p) := by
    simp only [hF]
  rw [hgoal1, hgoal2, hgoal3, hgoal4, hgoal5, ← hcomb]
  exact hfine

end Work.BoseBoxFock
