import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseRowsL.LatticeCoulomb.cellOddMoments
import Submission.Work.BoseRowsL.LatticeCoulomb.cosCellAverage
import Submission.Work.BoseRowsL.LatticeCoulomb.latticeInvFourSum
import Submission.Work.BoseRowsL.LatticeCoulomb.taylorRemainderNorm
import Submission.Work.BoseRowsL.LatticeCoulomb.ucellNormSqIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.latticeCellExpand`

The **cell expansion** of the lattice Coulomb kernel: the comparison of the lattice sum
`Σ_{n∈T} cos(2π⟪n,z⟫)/‖n‖²` with the corresponding sum of *cell integrals*
`Σ_{n∈T} ∫_{q ∈ ucell n} cos(2π⟪q,z⟫)/‖q‖² dq`, up to the exact linearisation.  Writing
`σ z = ∫_{ucell 0} cos(2π⟪q,z⟫) dq` and `sigBullet z = ∫_{ucell 0} sin(2π⟪q,z⟫) • q dq`, the
second-order Taylor expansion of `q ↦ cos(2π⟪q,z⟫)/‖q‖²` on the unit cell centred at `n` reads

  `∫_{ucell n} cos(2π⟪q,z⟫)/‖q‖² = σ z·cos(2π⟪n,z⟫)/‖n‖² + 2·sin(2π⟪n,z⟫)·⟪n,sigBullet z⟫/‖n‖⁴
     + Eₙ`,

with `|Eₙ| ≤ 25/‖nvec n‖⁴` (`perCell_of`, from `taylorRemainderNorm`, `cellOddMoments` and
`∫_{ucell 0} ‖w‖²dw = 1/4` = `ucellNormSqIntegral`).  Summing over `n ∈ T` and using the
convergence `Σ_{n≠0} ‖nvec n‖⁻⁴ ≤ 300` (`latticeInvFourSum`) gives the stated bound `10000`
(the true value of the remainder is at most `25·16.53 ≈ 413`; the constants are deliberately
very loose).

Sums of this shape are exactly the "absolutely summable `‖n‖⁻⁴` corrections" produced by the cell
method in `FINDING_latticeKernel.md` §3d.
-/

noncomputable section
open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

/-! ### Toolbox for the cell expansion -/

private lemma isFiniteMeasure_ucell_zero : IsFiniteMeasure (volume.restrict (ucell 0)) :=
  ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, volume_ucell 0]
      exact ENNReal.one_lt_top⟩

private lemma integrableOn_ucell_zero {f : E3 → ℝ}
    (hmeas : AEStronglyMeasurable f (volume.restrict (ucell 0))) {C : ℝ}
    (hC : ∀ w ∈ ucell 0, ‖f w‖ ≤ C) : Integrable f (volume.restrict (ucell 0)) := by
  haveI := isFiniteMeasure_ucell_zero
  refine Integrable.of_bound hmeas C ?_
  filter_upwards [self_mem_ae_restrict (ucell_measurableSet 0)] with w hw
  exact hC w hw

/-- Translation of a set integral from the cell at `n` to the cell at the origin. -/
private lemma setIntegral_ucell_shift (n : Fin 3 → ℤ) (F : E3 → ℝ) :
    ∫ q in ucell n, F q = ∫ w in ucell 0, F (nvec n + w) := by
  have hmp : MeasurePreserving (fun w : E3 => nvec n + w) volume volume :=
    measurePreserving_add_left volume (nvec n)
  have hemb : MeasurableEmbedding (fun w : E3 => nvec n + w) :=
    (Homeomorph.addLeft (nvec n)).measurableEmbedding
  have h := hmp.setIntegral_preimage_emb hemb F (ucell n)
  have hpre : (fun w : E3 => nvec n + w) ⁻¹' (ucell n) = ucell 0 := by
    ext w
    simp only [Set.mem_preimage, ucell, Set.mem_setOf_eq]
    constructor <;> intro h i <;> · have := h i; simpa using this
  rw [hpre] at h
  exact h.symm

private lemma norm_le_ucell_zero {w : E3} (hw : w ∈ ucell 0) : ‖w‖ ≤ 9 / 10 := by
  have h2 : ‖w‖ ^ 2 ≤ (3 : ℝ) / 4 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i : Fin 3, ‖w.ofLp i‖ ^ 2 ≤ ∑ _i : Fin 3, ((1 / 2 : ℝ)) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hi : |w.ofLp i| ≤ 1 / 2 := by
            have h := hw i
            simp only [ucell, Set.mem_setOf_eq] at h
            simpa using h
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hi 2
      _ = 3 / 4 := by rw [Fin.sum_univ_three]; norm_num
  nlinarith [norm_nonneg w]

private lemma norm_nvec_ge_one {n : Fin 3 → ℤ} (hn : n ≠ 0) : 1 ≤ ‖nvec n‖ := by
  have h1 : ∃ i : Fin 3, n i ≠ 0 := by
    by_contra h
    exact hn (funext (fun i => not_not.mp (not_exists.mp h i)))
  obtain ⟨i, hi⟩ := h1
  have hcast : ((n i : ℤ) : ℝ) ^ 2 = ‖(nvec n).ofLp i‖ ^ 2 := by
    rw [nvec_apply, Real.norm_eq_abs, sq_abs]
  have h2 : (1 : ℝ) ≤ ((n i : ℤ) : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ n i ^ 2 := by
      have h3 : 1 ≤ |n i| := Int.one_le_abs hi
      nlinarith [h3, abs_nonneg (n i), sq_abs (n i)]
    exact_mod_cast this
  have h3 : ((n i : ℤ) : ℝ) ^ 2 ≤ ‖nvec n‖ ^ 2 := by
    rw [hcast, EuclideanSpace.norm_sq_eq]
    exact Finset.single_le_sum (f := fun j : Fin 3 => ‖(nvec n).ofLp j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
  nlinarith [norm_nonneg (nvec n), h2, h3]

/-- The one-dimensional `b`-cosine and `b`-sine of the origin cell. -/
private lemma int_cos_b (z : E3) :
    ∫ w in ucell 0, Real.cos (2 * Real.pi * inner ℝ w z) = sigma z := rfl

private lemma int_sin_b (z : E3) :
    ∫ w in ucell 0, Real.sin (2 * Real.pi * inner ℝ w z) = 0 := (cellOddMoments z).1

private lemma integrable_cos_b (z : E3) :
    Integrable (fun w : E3 => Real.cos (2 * Real.pi * inner ℝ w z))
      (volume.restrict (ucell 0)) := by
  refine integrableOn_ucell_zero (C := 1) ?_ ?_
  · exact (by fun_prop : Continuous
      (fun w : E3 => Real.cos (2 * Real.pi * inner ℝ w z))).continuousOn.aestronglyMeasurable
      (ucell_measurableSet 0)
  · intro w _
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _

private lemma integrable_sin_b (z : E3) :
    Integrable (fun w : E3 => Real.sin (2 * Real.pi * inner ℝ w z))
      (volume.restrict (ucell 0)) := by
  refine integrableOn_ucell_zero (C := 1) ?_ ?_
  · exact (by fun_prop : Continuous
      (fun w : E3 => Real.sin (2 * Real.pi * inner ℝ w z))).continuousOn.aestronglyMeasurable
      (ucell_measurableSet 0)
  · intro w _
    rw [Real.norm_eq_abs]
    exact Real.abs_sin_le_one _

private lemma integrable_cos_b_mul_inner (b z : E3) :
    Integrable (fun w : E3 => Real.cos (2 * Real.pi * inner ℝ w z) * inner ℝ b w)
      (volume.restrict (ucell 0)) := by
  refine integrableOn_ucell_zero (C := ‖b‖) ?_ ?_
  · exact (by fun_prop : Continuous
      (fun w : E3 => Real.cos (2 * Real.pi * inner ℝ w z) * inner ℝ b w)).continuousOn.aestronglyMeasurable
      (ucell_measurableSet 0)
  · intro w hw
    rw [Real.norm_eq_abs, abs_mul]
    calc |Real.cos (2 * Real.pi * inner ℝ w z)| * |inner ℝ b w| ≤ 1 * |inner ℝ b w| :=
          mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = |inner ℝ b w| := one_mul _
      _ ≤ ‖b‖ * ‖w‖ := abs_real_inner_le_norm b w
      _ ≤ ‖b‖ * 1 := by
          exact mul_le_mul_of_nonneg_left (by linarith [norm_le_ucell_zero hw]) (norm_nonneg b)
      _ = ‖b‖ := mul_one _

private lemma integrable_sin_b_mul_inner (b z : E3) :
    Integrable (fun w : E3 => Real.sin (2 * Real.pi * inner ℝ w z) * inner ℝ b w)
      (volume.restrict (ucell 0)) := by
  refine integrableOn_ucell_zero (C := ‖b‖) ?_ ?_
  · exact (by fun_prop : Continuous
      (fun w : E3 => Real.sin (2 * Real.pi * inner ℝ w z) * inner ℝ b w)).continuousOn.aestronglyMeasurable
      (ucell_measurableSet 0)
  · intro w hw
    rw [Real.norm_eq_abs, abs_mul]
    calc |Real.sin (2 * Real.pi * inner ℝ w z)| * |inner ℝ b w| ≤ 1 * |inner ℝ b w| :=
          mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
      _ = |inner ℝ b w| := one_mul _
      _ ≤ ‖b‖ * ‖w‖ := abs_real_inner_le_norm b w
      _ ≤ ‖b‖ * 1 := by
          exact mul_le_mul_of_nonneg_left (by linarith [norm_le_ucell_zero hw]) (norm_nonneg b)
      _ = ‖b‖ := mul_one _

private lemma integrable_smul_w (z : E3) :
    Integrable (fun w : E3 => (Real.sin (2 * Real.pi * inner ℝ w z)) • w)
      (volume.restrict (ucell 0)) := by
  haveI := isFiniteMeasure_ucell_zero
  refine Integrable.of_bound ?_ (9 / 10) ?_
  · exact (by fun_prop : Continuous
      (fun w : E3 => (Real.sin (2 * Real.pi * inner ℝ w z)) • w)).continuousOn.aestronglyMeasurable
      (ucell_measurableSet 0)
  · filter_upwards [self_mem_ae_restrict (ucell_measurableSet 0)] with w hw
    rw [norm_smul, Real.norm_eq_abs]
    calc |Real.sin (2 * Real.pi * inner ℝ w z)| * ‖w‖ ≤ 1 * ‖w‖ :=
          mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (norm_nonneg w)
      _ = ‖w‖ := one_mul _
      _ ≤ 9 / 10 := norm_le_ucell_zero hw

private lemma int_cos_b_mul_inner (b z : E3) :
    ∫ w in ucell 0, Real.cos (2 * Real.pi * inner ℝ w z) * inner ℝ b w = 0 := by
  haveI := isFiniteMeasure_ucell_zero
  have hint : Integrable (fun w : E3 => (Real.cos (2 * Real.pi * inner ℝ w z)) • w)
      (volume.restrict (ucell 0)) := by
    refine Integrable.of_bound ?_ (9 / 10) ?_
    · exact (by fun_prop : Continuous
        (fun w : E3 => (Real.cos (2 * Real.pi * inner ℝ w z)) • w)).continuousOn.aestronglyMeasurable
        (ucell_measurableSet 0)
    · filter_upwards [self_mem_ae_restrict (ucell_measurableSet 0)] with w hw
      rw [norm_smul, Real.norm_eq_abs]
      calc |Real.cos (2 * Real.pi * inner ℝ w z)| * ‖w‖ ≤ 1 * ‖w‖ :=
            mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg w)
        _ = ‖w‖ := one_mul _
        _ ≤ 9 / 10 := norm_le_ucell_zero hw
  have h := ContinuousLinearMap.integral_comp_comm (innerSL ℝ b) hint
  have h1 : (∫ w in ucell 0, (innerSL ℝ b) ((Real.cos (2 * Real.pi * inner ℝ w z)) • w))
      = ∫ w in ucell 0, Real.cos (2 * Real.pi * inner ℝ w z) * inner ℝ b w :=
    integral_congr_ae (Filter.Eventually.of_forall fun w => by
      simp [innerSL, inner_smul_right])
  have h2 : (∫ w in ucell 0, Real.cos (2 * Real.pi * inner ℝ w z) * inner ℝ b w)
      = inner ℝ b (∫ w in ucell 0, (Real.cos (2 * Real.pi * inner ℝ w z)) • w) := by
    rw [← h1, h]
    simp [innerSL]
  have hzero : (∫ w in ucell 0, (Real.cos (2 * Real.pi * inner ℝ w z)) • w) = 0 :=
    (cellOddMoments z).2
  rw [h2, hzero, inner_zero_right]

private lemma int_sin_b_mul_inner (b z : E3) :
    ∫ w in ucell 0, Real.sin (2 * Real.pi * inner ℝ w z) * inner ℝ b w
      = inner ℝ b (sigBullet z) := by
  have h := ContinuousLinearMap.integral_comp_comm (innerSL ℝ b) (integrable_smul_w z)
  have h1 : (∫ w in ucell 0, (innerSL ℝ b) ((Real.sin (2 * Real.pi * inner ℝ w z)) • w))
      = ∫ w in ucell 0, Real.sin (2 * Real.pi * inner ℝ w z) * inner ℝ b w :=
    integral_congr_ae (Filter.Eventually.of_forall fun w => by
      simp [innerSL, inner_smul_right])
  have h2 : (∫ w in ucell 0, Real.sin (2 * Real.pi * inner ℝ w z) * inner ℝ b w)
      = inner ℝ b (∫ w in ucell 0, (Real.sin (2 * Real.pi * inner ℝ w z)) • w) := by
    rw [← h1, h]
    simp [innerSL]
  have hsb : (∫ w in ucell 0, (Real.sin (2 * Real.pi * inner ℝ w z)) • w) = sigBullet z := rfl
  rw [h2, hsb]


set_option autoImplicit false

private def lceA (n : Fin 3 → ℤ) (z : E3) (w : E3) : ℝ :=
  (Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2)
    * Real.cos (2 * Real.pi * inner ℝ w z)

private def lceB (n : Fin 3 → ℤ) (z : E3) (w : E3) : ℝ :=
  (Real.sin (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2)
    * Real.sin (2 * Real.pi * inner ℝ w z)

private def lceC (n : Fin 3 → ℤ) (z : E3) (w : E3) : ℝ :=
  (2 * Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 4)
    * (Real.cos (2 * Real.pi * inner ℝ w z) * inner ℝ (nvec n) w)

private def lceD (n : Fin 3 → ℤ) (z : E3) (w : E3) : ℝ :=
  (2 * Real.sin (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 4)
    * (Real.sin (2 * Real.pi * inner ℝ w z) * inner ℝ (nvec n) w)

private def lceLin (n : Fin 3 → ℤ) (z : E3) : E3 → ℝ :=
  fun w => (lceA n z w - lceB n z w) + (lceD n z w - lceC n z w)

private def lceR (n : Fin 3 → ℤ) : E3 → ℝ :=
  fun w => 1 / ‖nvec n + w‖ ^ 2 - 1 / ‖nvec n‖ ^ 2 + 2 * inner ℝ (nvec n) w / ‖nvec n‖ ^ 4

private lemma norm_sq_le_ucell_zero {w : E3} (hw : w ∈ ucell 0) : ‖w‖ ^ 2 ≤ (3 : ℝ) / 4 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc ∑ i : Fin 3, ‖w.ofLp i‖ ^ 2 ≤ ∑ _i : Fin 3, ((1 / 2 : ℝ)) ^ 2 := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hi : |w.ofLp i| ≤ 1 / 2 := by
          have h := hw i
          simp only [ucell, Set.mem_setOf_eq] at h
          simpa using h
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hi 2
    _ = 3 / 4 := by rw [Fin.sum_univ_three]; norm_num

private lemma integrable_normSq : Integrable (fun w : E3 => ‖w‖ ^ 2) (volume.restrict (ucell 0)) := by
  refine integrableOn_ucell_zero (C := 3 / 4) ?_ ?_
  · exact (by fun_prop : Continuous (fun w : E3 => ‖w‖ ^ 2)).continuousOn.aestronglyMeasurable
      (ucell_measurableSet 0)
  · intro w hw
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    exact norm_sq_le_ucell_zero hw

private lemma norm_add_ge_one_tenth {b w : E3} (hb : 1 ≤ ‖b‖) (hw : ‖w‖ ≤ 9 / 10) :
    1 / 10 ≤ ‖b + w‖ := by
  have h := norm_sub_le (b + w) w
  simp only [add_sub_cancel_right] at h
  linarith

private lemma integrable_lceA (n : Fin 3 → ℤ) (z : E3) :
    Integrable (lceA n z) (volume.restrict (ucell 0)) := by
  have h := (integrable_cos_b z).const_mul
    (Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2)
  exact h

private lemma integrable_lceB (n : Fin 3 → ℤ) (z : E3) :
    Integrable (lceB n z) (volume.restrict (ucell 0)) := by
  have h := (integrable_sin_b z).const_mul
    (Real.sin (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2)
  exact h

private lemma integrable_lceC (n : Fin 3 → ℤ) (z : E3) :
    Integrable (lceC n z) (volume.restrict (ucell 0)) := by
  have h := (integrable_cos_b_mul_inner (nvec n) z).const_mul
    (2 * Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 4)
  exact h

private lemma integrable_lceD (n : Fin 3 → ℤ) (z : E3) :
    Integrable (lceD n z) (volume.restrict (ucell 0)) := by
  have h := (integrable_sin_b_mul_inner (nvec n) z).const_mul
    (2 * Real.sin (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 4)
  exact h

private lemma integrable_lceLin (n : Fin 3 → ℤ) (z : E3) :
    Integrable (lceLin n z) (volume.restrict (ucell 0)) := by
  have h := ((integrable_lceA n z).sub (integrable_lceB n z)).add
    ((integrable_lceD n z).sub (integrable_lceC n z))
  exact h

private lemma integrable_cosR (n : Fin 3 → ℤ) (z : E3) (hn : n ≠ 0) :
    Integrable (fun w : E3 => Real.cos (2 * Real.pi * inner ℝ (nvec n + w) z) * lceR n w)
      (volume.restrict (ucell 0)) := by
  have hb : 1 ≤ ‖nvec n‖ := norm_nvec_ge_one hn
  have hK : 0 < ‖nvec n‖ := lt_of_lt_of_le zero_lt_one hb
  refine integrableOn_ucell_zero (C := 75 / ‖nvec n‖ ^ 4) ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    simp only [lceR]
    fun_prop
  · intro w hw
    have hmem : ∀ i : Fin 3, |(nvec n + w).ofLp i - (nvec n).ofLp i| ≤ 1 / 2 := by
      intro i
      have h := hw i
      simp only [ucell, Set.mem_setOf_eq] at h
      simpa using h
    have hwbox : ∀ i : Fin 3, |w.ofLp i| ≤ 1 / 2 := by
      intro i
      have h := hmem i
      simpa using h
    have hR := taylorRemainderNorm (b := nvec n) (w := w) hb hwbox
    have hReq : lceR n w
        = 1 / ‖nvec n + w‖ ^ 2 - 1 / ‖nvec n‖ ^ 2 + 2 * inner ℝ (nvec n) w / ‖nvec n‖ ^ 4 :=
      rfl
    rw [Real.norm_eq_abs, abs_mul]
    have hcos : |Real.cos (2 * Real.pi * inner ℝ (nvec n + w) z)| ≤ 1 :=
      Real.abs_cos_le_one _
    have hRn : |lceR n w| ≤ 100 * ‖w‖ ^ 2 / ‖nvec n‖ ^ 4 := by
      rw [hReq]; exact hR
    have hw3 : ‖w‖ ^ 2 ≤ 3 / 4 := norm_sq_le_ucell_zero hw
    have hK4 : 0 < ‖nvec n‖ ^ 4 := by positivity
    calc |Real.cos (2 * Real.pi * inner ℝ (nvec n + w) z)| * |lceR n w|
        ≤ 1 * (100 * ‖w‖ ^ 2 / ‖nvec n‖ ^ 4) :=
          mul_le_mul hcos hRn (abs_nonneg _) (by norm_num)
      _ = 100 * ‖w‖ ^ 2 / ‖nvec n‖ ^ 4 := one_mul _
      _ ≤ 100 * (3 / 4) / ‖nvec n‖ ^ 4 := by
          apply div_le_div_of_nonneg_right _ hK4.le
          nlinarith [norm_nonneg w]
      _ = 75 / ‖nvec n‖ ^ 4 := by ring

private lemma lce_pointwise (n : Fin 3 → ℤ) (z w : E3) (hn : n ≠ 0) (hw : w ∈ ucell 0) :
    Real.cos (2 * Real.pi * inner ℝ (nvec n + w) z) / ‖nvec n + w‖ ^ 2
      = lceLin n z w + Real.cos (2 * Real.pi * inner ℝ (nvec n + w) z) * lceR n w := by
  have hb : 1 ≤ ‖nvec n‖ := norm_nvec_ge_one hn
  have hK : ‖nvec n‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hb)
  have hKw : ‖nvec n + w‖ ≠ 0 := by
    have h1 := norm_add_ge_one_tenth hb (norm_le_ucell_zero hw)
    intro h; rw [h] at h1; norm_num at h1
  rw [inner_add_left, mul_add, Real.cos_add]
  simp only [lceLin, lceA, lceB, lceC, lceD, lceR]
  field_simp
  ring

private lemma lceLin_integral (n : Fin 3 → ℤ) (z : E3) :
    (∫ w in ucell 0, lceLin n z w)
      = sigma z * (Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2)
        + Real.sin (2 * Real.pi * inner ℝ (nvec n) z) * (inner ℝ (nvec n) (sigBullet z))
          * (2 / ‖nvec n‖ ^ 4) := by
  have hA := integrable_lceA n z
  have hB := integrable_lceB n z
  have hC := integrable_lceC n z
  have hD := integrable_lceD n z
  have eA : (∫ w in ucell 0, lceA n z w)
      = (Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2) * sigma z := by
    simp only [lceA]
    rw [integral_const_mul, int_cos_b]
  have eB : (∫ w in ucell 0, lceB n z w) = 0 := by
    simp only [lceB]
    rw [integral_const_mul, int_sin_b, mul_zero]
  have eC : (∫ w in ucell 0, lceC n z w) = 0 := by
    simp only [lceC]
    rw [integral_const_mul, int_cos_b_mul_inner, mul_zero]
  have eD : (∫ w in ucell 0, lceD n z w)
      = (2 * Real.sin (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 4)
        * inner ℝ (nvec n) (sigBullet z) := by
    simp only [lceD]
    rw [integral_const_mul, int_sin_b_mul_inner]
  have hAB : (∫ w in ucell 0, (lceA n z w - lceB n z w))
      = (∫ w in ucell 0, lceA n z w) - (∫ w in ucell 0, lceB n z w) :=
    integral_sub hA hB
  have hDC : (∫ w in ucell 0, (lceD n z w - lceC n z w))
      = (∫ w in ucell 0, lceD n z w) - (∫ w in ucell 0, lceC n z w) :=
    integral_sub hD hC
  have hsum : (∫ w in ucell 0, lceLin n z w)
      = (∫ w in ucell 0, (lceA n z w - lceB n z w))
        + (∫ w in ucell 0, (lceD n z w - lceC n z w)) := by
    simp only [lceLin]
    exact integral_add (hA.sub hB) (hD.sub hC)
  rw [hsum, hAB, hDC, eA, eB, eC, eD]
  ring

private lemma lce_expand (n : Fin 3 → ℤ) (z : E3) (hn : n ≠ 0) :
    (∫ w in ucell 0, Real.cos (2 * Real.pi * inner ℝ (nvec n + w) z) / ‖nvec n + w‖ ^ 2)
      = (∫ w in ucell 0, lceLin n z w)
        + ∫ w in ucell 0, Real.cos (2 * Real.pi * inner ℝ (nvec n + w) z) * lceR n w := by
  have hae : (fun w : E3 => Real.cos (2 * Real.pi * inner ℝ (nvec n + w) z) / ‖nvec n + w‖ ^ 2)
      =ᵐ[volume.restrict (ucell 0)]
      fun w => lceLin n z w + Real.cos (2 * Real.pi * inner ℝ (nvec n + w) z) * lceR n w := by
    filter_upwards [self_mem_ae_restrict (ucell_measurableSet 0)] with w hw
    exact lce_pointwise n z w hn hw
  rw [integral_congr_ae hae, integral_add (integrable_lceLin n z) (integrable_cosR n z hn)]

theorem perCell_of (hns : ∫ w in ucell 0, ‖w‖ ^ 2 ≤ 1 / 4) (n : Fin 3 → ℤ) (hn : n ≠ 0)
    (z : E3) :
    |(∫ q in ucell n, Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2)
      - (sigma z * (Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2)
         + Real.sin (2 * Real.pi * inner ℝ (nvec n) z) * (inner ℝ (nvec n) (sigBullet z))
           * (2 / ‖nvec n‖ ^ 4))|
    ≤ 25 / ‖nvec n‖ ^ 4 := by
  have hb : 1 ≤ ‖nvec n‖ := norm_nvec_ge_one hn
  have hK : 0 < ‖nvec n‖ := lt_of_lt_of_le zero_lt_one hb
  rw [setIntegral_ucell_shift n (fun q => Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2)]
  have hkey : (∫ w in ucell 0, Real.cos (2 * Real.pi * inner ℝ (nvec n + w) z) / ‖nvec n + w‖ ^ 2)
      = (sigma z * (Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2)
         + Real.sin (2 * Real.pi * inner ℝ (nvec n) z) * (inner ℝ (nvec n) (sigBullet z))
           * (2 / ‖nvec n‖ ^ 4))
        + ∫ w in ucell 0, Real.cos (2 * Real.pi * inner ℝ (nvec n + w) z) * lceR n w := by
    rw [lce_expand n z hn, lceLin_integral n z]
  rw [hkey, add_sub_cancel_left]
  -- bound the remainder
  have hInt1 : Integrable
      (fun w : E3 => |Real.cos (2 * Real.pi * inner ℝ (nvec n + w) z) * lceR n w|)
      (volume.restrict (ucell 0)) := (integrable_cosR n z hn).abs
  have hInt2 : Integrable (fun w : E3 => (100 / ‖nvec n‖ ^ 4) * ‖w‖ ^ 2)
      (volume.restrict (ucell 0)) := (integrable_normSq).const_mul _
  have hInt3 : Integrable (fun w : E3 => ‖w‖ ^ 2) (volume.restrict (ucell 0)) :=
    integrable_normSq
  calc |∫ w in ucell 0, Real.cos (2 * Real.pi * inner ℝ (nvec n + w) z) * lceR n w|
      ≤ ∫ w in ucell 0, |Real.cos (2 * Real.pi * inner ℝ (nvec n + w) z) * lceR n w| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ w in ucell 0, (100 / ‖nvec n‖ ^ 4) * ‖w‖ ^ 2 := by
        refine integral_mono_ae hInt1 hInt2 ?_
        filter_upwards [self_mem_ae_restrict (ucell_measurableSet 0)] with w hw
        have hmem : ∀ i : Fin 3, |(nvec n + w).ofLp i - (nvec n).ofLp i| ≤ 1 / 2 := by
          intro i
          have h := hw i
          simp only [ucell, Set.mem_setOf_eq] at h
          simpa using h
        have hwbox : ∀ i : Fin 3, |w.ofLp i| ≤ 1 / 2 := by
          intro i
          have h := hmem i
          simpa using h
        have hR := taylorRemainderNorm (b := nvec n) (w := w) hb hwbox
        have hRn : |lceR n w| ≤ 100 * ‖w‖ ^ 2 / ‖nvec n‖ ^ 4 := by rw [lceR]; exact hR
        rw [abs_mul]
        calc |Real.cos (2 * Real.pi * inner ℝ (nvec n + w) z)| * |lceR n w|
            ≤ 1 * (100 * ‖w‖ ^ 2 / ‖nvec n‖ ^ 4) :=
              mul_le_mul (Real.abs_cos_le_one _) hRn (abs_nonneg _) (by norm_num)
          _ = 100 * ‖w‖ ^ 2 / ‖nvec n‖ ^ 4 := one_mul _
          _ = (100 / ‖nvec n‖ ^ 4) * ‖w‖ ^ 2 := by ring
    _ = (100 / ‖nvec n‖ ^ 4) * ∫ w in ucell 0, ‖w‖ ^ 2 := by
        rw [integral_const_mul]
    _ ≤ (100 / ‖nvec n‖ ^ 4) * (1 / 4) := by
        apply mul_le_mul_of_nonneg_left hns (by positivity)
    _ = 25 / ‖nvec n‖ ^ 4 := by ring_nf


set_option autoImplicit false

private def lcf (z : E3) (n : Fin 3 → ℤ) : ℝ :=
  Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2

private def lcg (z : E3) (n : Fin 3 → ℤ) : ℝ :=
  ∫ q in ucell n, Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2

private def lch (z : E3) (n : Fin 3 → ℤ) : ℝ :=
  Real.sin (2 * Real.pi * inner ℝ (nvec n) z) * (inner ℝ (nvec n) (sigBullet z))
    * (-2 / ‖nvec n‖ ^ 4)

theorem latticeCellExpand_of
    (hns : ∫ w in ucell 0, ‖w‖ ^ 2 ≤ 1 / 4)
    (T : Finset (Fin 3 → ℤ)) (z : E3) (h1 : ∀ n ∈ T, n ≠ 0)
    (hT : ∑ n ∈ T, 1 / ‖nvec n‖ ^ 4 ≤ 400) :
    |(∑ n ∈ T, (Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2
          - ∫ q in ucell n, Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2))
      - ((1 - sigma z) * (∑ n ∈ T, Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2)
        + ∑ n ∈ T, Real.sin (2 * Real.pi * inner ℝ (nvec n) z)
            * (inner ℝ (nvec n) (sigBullet z)) * (-2 / ‖nvec n‖ ^ 4))|
    ≤ 10000 := by
  have hcell : ∀ n ∈ T, |lcg z n - (sigma z * lcf z n - lch z n)| ≤ 25 / ‖nvec n‖ ^ 4 := by
    intro n hn
    have h := perCell_of hns n (h1 n hn) z
    have key : sigma z * lcf z n - lch z n
        = sigma z * (Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2)
          + Real.sin (2 * Real.pi * inner ℝ (nvec n) z) * (inner ℝ (nvec n) (sigBullet z))
            * (2 / ‖nvec n‖ ^ 4) := by
      simp only [lcf, lch]
      ring
    have keyg : lcg z n = ∫ q in ucell n, Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2 := rfl
    rw [keyg, key]
    exact h
  have hsumE : |∑ n ∈ T, (lcg z n - (sigma z * lcf z n - lch z n))|
      ≤ ∑ n ∈ T, 25 / ‖nvec n‖ ^ 4 :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hcell)
  have hbound : ∑ n ∈ T, 25 / ‖nvec n‖ ^ 4 ≤ 10000 := by
    calc ∑ n ∈ T, 25 / ‖nvec n‖ ^ 4 = 25 * ∑ n ∈ T, 1 / ‖nvec n‖ ^ 4 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun n _ => by ring)
      _ ≤ 25 * 400 := by linarith
      _ = 10000 := by norm_num
  have key2 : (∑ n ∈ T, (lcf z n - lcg z n))
        - ((1 - sigma z) * (∑ n ∈ T, lcf z n) + ∑ n ∈ T, lch z n)
      = -∑ n ∈ T, (lcg z n - (sigma z * lcf z n - lch z n)) := by
    have e1 : (∑ n ∈ T, (lcf z n - lcg z n))
        = (∑ n ∈ T, lcf z n) - ∑ n ∈ T, lcg z n := Finset.sum_sub_distrib _ _
    have e2 : (∑ n ∈ T, (lcg z n - (sigma z * lcf z n - lch z n)))
        = (∑ n ∈ T, lcg z n) - (sigma z * (∑ n ∈ T, lcf z n) - ∑ n ∈ T, lch z n) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [e1, e2]
    ring
  have hgoal : |(∑ n ∈ T, (lcf z n - lcg z n))
        - ((1 - sigma z) * (∑ n ∈ T, lcf z n) + ∑ n ∈ T, lch z n)|
      = |∑ n ∈ T, (lcg z n - (sigma z * lcf z n - lch z n))| := by
    rw [key2, abs_neg]
  rw [show |(∑ n ∈ T, (Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2
          - ∫ q in ucell n, Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2))
      - ((1 - sigma z) * (∑ n ∈ T, Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2)
        + ∑ n ∈ T, Real.sin (2 * Real.pi * inner ℝ (nvec n) z)
            * (inner ℝ (nvec n) (sigBullet z)) * (-2 / ‖nvec n‖ ^ 4))|
      = |∑ n ∈ T, (lcg z n - (sigma z * lcf z n - lch z n))| from hgoal]
  exact hsumE.trans hbound


theorem latticeCellExpand (T : Finset (Fin 3 → ℤ)) (z : E3) (h1 : ∀ n ∈ T, n ≠ 0) :
    |(∑ n ∈ T, (Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2
          - ∫ q in ucell n, Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2))
      - ((1 - sigma z) * (∑ n ∈ T, Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2)
        + ∑ n ∈ T, Real.sin (2 * Real.pi * inner ℝ (nvec n) z)
            * (inner ℝ (nvec n) (sigBullet z)) * (-2 / ‖nvec n‖ ^ 4))|
    ≤ 10000 := by
  refine latticeCellExpand_of (le_of_eq ucellNormSqIntegral) T z h1 ?_
  exact le_trans (latticeInvFourSum T h1) (by norm_num)

end Work.BoseRowsL.LatticeCoulomb
