import Mathlib
import Submission.Commons.MeasureTheory.Integral.simplex_integral_scaled
import Submission.Commons.Analysis.Integral.volume_orthant_slab_card

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Commons.MeasureTheory.Integral

noncomputable section

private lemma measurableSet_simplex_body (k : ℕ) (c : ℝ) :
    MeasurableSet {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c} := by
  have h : {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c}
      = (⋂ i, {t : Fin k → ℝ | 0 ≤ t i}) ∩ {t : Fin k → ℝ | ∑ i, t i ≤ c} := by
    ext t; simp [Set.mem_iInter]
  rw [h]
  exact (MeasurableSet.iInter fun i =>
      measurableSet_le measurable_const (measurable_pi_apply i)).inter
    (measurableSet_le (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)) measurable_const)

private lemma volume_simplex_body_lt_top (k : ℕ) (c : ℝ) :
    (volume : Measure (Fin k → ℝ)) {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c} < ∞ := by
  calc (volume : Measure (Fin k → ℝ)) {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c}
      ≤ (volume : Measure (Fin k → ℝ)) (Set.pi Set.univ (fun _ : Fin k => Icc (0:ℝ) c)) := by
        refine measure_mono ?_
        intro t ht
        simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
        intro i
        exact ⟨ht.1 i, le_trans (Finset.single_le_sum (fun j _ => ht.1 j) (Finset.mem_univ i)) ht.2⟩
    _ = ∏ _ : Fin k, (volume : Measure ℝ) (Icc (0:ℝ) c) := volume_pi_pi _
    _ < ∞ := ENNReal.prod_lt_top (fun i _ => by
        rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)

private lemma integrableOn_simplex_monomial {k : ℕ} {c : ℝ} (hc : 0 ≤ c) (a : ℕ)
    (b : Fin k → ℕ) :
    IntegrableOn (fun t : Fin k → ℝ => (c - ∑ i, t i)^a * ∏ i, (t i)^(b i))
      {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c} volume := by
  have hSmeas := measurableSet_simplex_body k c
  have hvol := volume_simplex_body_lt_top k c
  refine IntegrableOn.of_bound hvol ?_ (c ^ (a + ∑ i, b i)) ?_
  · exact ((by fun_prop : Continuous
      (fun t : Fin k → ℝ => (c - ∑ i, t i)^a * ∏ i, (t i)^(b i)))).aestronglyMeasurable.restrict
  · rw [ae_restrict_iff' hSmeas]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    obtain ⟨h0, hsum⟩ := ht
    have hsi : 0 ≤ ∑ i, t i := Finset.sum_nonneg (fun i _ => h0 i)
    have hti : ∀ i, t i ≤ c := fun i =>
      le_trans (Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)) hsum
    have hca : 0 ≤ c - ∑ i, t i := by linarith
    have hcs : c - ∑ i, t i ≤ c := by linarith
    have hprod_nonneg : 0 ≤ ∏ i, (t i)^(b i) :=
      Finset.prod_nonneg (fun i _ => pow_nonneg (h0 i) _)
    have hnn : 0 ≤ (c - ∑ i, t i)^a * ∏ i, (t i)^(b i) :=
      mul_nonneg (pow_nonneg hca _) hprod_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc (c - ∑ i, t i)^a * ∏ i, (t i)^(b i)
        ≤ c^a * ∏ i, c^(b i) :=
          mul_le_mul (pow_le_pow_left₀ hca hcs a)
            (Finset.prod_le_prod₀ (fun i _ => pow_nonneg (h0 i) _)
              (fun i _ => pow_le_pow_left₀ (h0 i) (hti i) _))
            hprod_nonneg (pow_nonneg hc a)
      _ = c^a * c^(∑ i, b i) := by rw [Finset.prod_pow_eq_pow_sum]
      _ = c^(a + ∑ i, b i) := by rw [← pow_add]

private lemma pow_sub_eq_sum (c d : ℝ) (A : ℕ) (x : ℝ) :
    (d - x) ^ A =
      ∑ j ∈ Finset.range (A + 1), (A.choose j : ℝ) * (d - c) ^ j * (c - x) ^ (A - j) := by
  rw [show d - x = (d - c) + (c - x) by ring, add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  ring


theorem simplex_integral_shifted {k : ℕ} (c d : ℝ) (hc : 0 < c) (A : ℕ) (b : Fin k → ℕ) :
    ∫ t : Fin k → ℝ in {t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c},
        (d - ∑ i, t i) ^ A * ∏ i, (t i) ^ (b i)
      = ∑ j ∈ Finset.range (A + 1),
          ((A.choose j : ℕ) : ℝ) * (d - c) ^ j *
            (c ^ (k + (A - j) + ∑ i, b i) *
              ((((A - j).factorial * ∏ i, (b i).factorial : ℕ)) : ℝ) /
                ((((A - j) + ∑ i, b i + k).factorial : ℕ) : ℝ)) := by
  classical
  have hSmeas : MeasurableSet {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c} :=
    measurableSet_simplex_body k c
  have hpoint : ∀ t : Fin k → ℝ, (d - ∑ i, t i) ^ A * ∏ i, (t i) ^ (b i)
      = ∑ j ∈ Finset.range (A + 1), ((A.choose j : ℝ) * (d - c) ^ j) *
          ((c - ∑ i, t i) ^ (A - j) * ∏ i, (t i) ^ (b i)) := by
    intro t
    rw [pow_sub_eq_sum c d A (∑ i, t i)]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [setIntegral_congr_fun hSmeas (fun t _ => hpoint t)]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [MeasureTheory.integral_const_mul]
    rw [simplex_integral_scaled c hc (A - j) b]
  · intro j hj
    exact (integrableOn_simplex_monomial hc.le (A - j) b).const_mul _

end

end Commons.MeasureTheory.Integral
