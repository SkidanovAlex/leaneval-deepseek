import Mathlib
import Submission.Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg
import Submission.Commons.Analysis.DirichletPolynomial.dual_integral_mean_value_finset
import Submission.Commons.Analysis.DirichletPolynomial.integral_normsq_cpow_expansion
import Submission.Commons.NumberTheory.DirichletPolynomial.normSq_sum_cpow_expansion
import Submission.Commons.Analysis.Metric.separated_pairs_count_bound_finset
import Submission.Commons.NumberTheory.DirichletPolynomial.aliasing_exp_sum_both

namespace Commons.NumberTheory.DirichletPolynomial

open Finset Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false

noncomputable def Zsum (N : ℕ) (δ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ (Complex.I * (δ : ℂ))

noncomputable def Isum (N : ℕ) (δ : ℝ) : ℂ :=
  ∫ x in (N : ℝ)..(2 * (N : ℝ)), (x : ℂ) ^ (Complex.I * (δ : ℂ))

noncomputable def Ealias (N : ℕ) (δ : ℝ) : ℂ := Zsum N δ - Isum N δ


lemma conj_cpow_I_neg (x : ℝ) (hx : 0 ≤ x) (a : ℝ) :
    (starRingEnd ℂ) ((x : ℂ) ^ (Complex.I * (a : ℂ))) = (x : ℂ) ^ (-(Complex.I * (a : ℂ))) := by
  rw [Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg hx (Complex.I * (a : ℂ))]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

lemma Zsum_neg (N : ℕ) (δ : ℝ) : Zsum N (-δ) = (starRingEnd ℂ) (Zsum N δ) := by
  rw [Zsum, Zsum, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Complex.ofReal_natCast n]
  simp only [Complex.ofReal_neg, mul_neg]
  exact (conj_cpow_I_neg (n : ℝ) (Nat.cast_nonneg n) δ).symm

lemma Isum_neg (N : ℕ) (δ : ℝ) : Isum N (-δ) = (starRingEnd ℂ) (Isum N δ) := by
  have hle : (N:ℝ) ≤ 2 * (N:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  rw [Isum, Isum, intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle]
  have hcongr : (∫ x in Set.Ioc (N:ℝ) (2 * (N:ℝ)), (x:ℂ)^(Complex.I*(Complex.ofReal (-δ))))
      = ∫ x in Set.Ioc (N:ℝ) (2 * (N:ℝ)), (starRingEnd ℂ) ((x:ℂ)^(Complex.I*(δ:ℂ))) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg N) hx.1)
    simp only [Complex.ofReal_neg, mul_neg]
    exact (conj_cpow_I_neg x hx0 δ).symm
  rw [hcongr, integral_conj]

lemma Ealias_neg (N : ℕ) (δ : ℝ) : Ealias N (-δ) = (starRingEnd ℂ) (Ealias N δ) := by
  rw [Ealias, Ealias, Zsum_neg, Isum_neg, map_sub]

lemma norm_Ealias_neg (N : ℕ) (δ : ℝ) : ‖Ealias N (-δ)‖ = ‖Ealias N δ‖ := by
  rw [Ealias_neg, norm_conj]



/-- Both aliasing estimates, uniform in the sign of `δ`. -/
lemma Ealias_bounds :
    ∃ C : ℝ, 0 < C ∧
      (∀ (N : ℕ), 1 ≤ N → ∀ δ : ℝ, |δ| ≤ (N : ℝ) →
        ‖Ealias N δ‖ ≤ C * (1 + |δ| / (N : ℝ))) ∧
      (∀ (N : ℕ), 1 ≤ N → ∀ δ : ℝ, (N : ℝ) ≤ |δ| →
        ‖Ealias N δ‖ ≤ C * Real.sqrt |δ|) := by
  obtain ⟨C, hC, hsmall, hlarge⟩ := aliasing_exp_sum_both
  refine ⟨C, hC, ?_, ?_⟩
  · intro N hN δ hδ
    exact hsmall N hN δ hδ
  · intro N hN δ hδ
    by_cases h0 : 0 ≤ δ
    · rw [abs_of_nonneg h0] at hδ ⊢
      exact hlarge N hN δ hδ
    · rw [abs_of_neg (lt_of_not_ge h0)] at hδ ⊢
      have h := hlarge N hN (-δ) hδ
      rw [← norm_Ealias_neg N δ]
      simpa only [Ealias, Zsum, Isum] using h

/-- `f * (if p then A else B) ≤ (if p then f*A else 0) + (if p then 0 else f*B)`. -/
private lemma ite_mul_le_add (p : Prop) [Decidable p] (f A B : ℝ) :
    f * (if p then A else B) ≤ (if p then f * A else 0) + (if p then 0 else f * B) := by
  by_cases h : p <;> simp [h]

private lemma sum_sum_ite_mul_const {ι : Type} (S : Finset ι) (p : ι → ι → Prop)
    [DecidableRel p] (f : ι → ι → ℝ) (A : ℝ) :
    (∑ i ∈ S, ∑ j ∈ S, (if p i j then f i j * A else 0))
      = A * ∑ i ∈ S, ∑ j ∈ S, (if p i j then f i j else 0) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : p i j <;> simp [h, mul_comm]

private lemma sum_sum_ite_not_mul_const {ι : Type} (S : Finset ι) (p : ι → ι → Prop)
    [DecidableRel p] (f : ι → ι → ℝ) (A : ℝ) :
    (∑ i ∈ S, ∑ j ∈ S, (if p i j then 0 else f i j * A))
      = A * ∑ i ∈ S, ∑ j ∈ S, (if p i j then 0 else f i j) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : p i j <;> simp [h, mul_comm]

private lemma sum_norm_sq_le_card {ι : Type} (S : Finset ι) (c : ι → ℂ) :
    (∑ i ∈ S, ‖c i‖) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, ‖c i‖ ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ : ι => (1 : ℝ)) (fun i => ‖c i‖)
  have h1 : (∑ i ∈ S, (1 : ℝ) * ‖c i‖) = ∑ i ∈ S, ‖c i‖ := by simp
  have h2 : (∑ _i ∈ S, (1 : ℝ) ^ 2) = (S.card : ℝ) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [h1, h2] at h
  exact h

/-- The "aliasing part" of the Halász double sum is bounded by the two aliasing estimates
and the pair-counting bound. -/
lemma Ealias_pair_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} (S : Finset ι) (N : ℕ), 1 ≤ N →
      ∀ (t : ι → ℝ) (c : ι → ℂ) (L : ℝ), 0 ≤ L →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ S, ∀ j ∈ S, |t i - t j| ≤ L) →
      ‖∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j * Ealias N (t j - t i)‖
        ≤ C * ((N : ℝ) + (S.card : ℝ) * Real.sqrt L) * ∑ i ∈ S, ‖c i‖ ^ 2 := by
  obtain ⟨C2, hC2, hsmall, hlarge⟩ := Ealias_bounds
  refine ⟨7 * C2, by positivity, ?_⟩
  intro ι S N hN t c L hL hsep hLt
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := hNpos.le
  have hCn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg S.card
  have hS0 : (0 : ℝ) ≤ ∑ i ∈ S, ‖c i‖ ^ 2 := by positivity
  set A : ℝ := 2 * C2 with hA
  set B : ℝ := C2 * Real.sqrt L with hB
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hpt : ∀ i ∈ S, ∀ j ∈ S,
      ‖Ealias N (t j - t i)‖ ≤ if |t j - t i| ≤ (N : ℝ) then A else B := by
    intro i hi j hj
    by_cases hc : |t j - t i| ≤ (N : ℝ)
    · rw [if_pos hc]
      have h1 := hsmall N hN (t j - t i) hc
      have hdiv : |t j - t i| / (N : ℝ) ≤ 1 := by
        rw [div_le_one hNpos]; exact hc
      have h2 : 1 + |t j - t i| / (N : ℝ) ≤ 2 := by linarith
      have h3 := mul_le_mul_of_nonneg_left h2 hC2.le
      rw [hA]
      linarith
    · rw [if_neg hc]
      have hge : (N : ℝ) ≤ |t j - t i| := le_of_lt (lt_of_not_ge hc)
      have h1 := hlarge N hN (t j - t i) hge
      have hle : |t j - t i| ≤ L := by
        rw [abs_sub_comm (t j) (t i)]; exact hLt i hi j hj
      have h2 : Real.sqrt |t j - t i| ≤ Real.sqrt L := Real.sqrt_le_sqrt hle
      have h3 : C2 * Real.sqrt |t j - t i| ≤ C2 * Real.sqrt L :=
        mul_le_mul_of_nonneg_left h2 hC2.le
      rw [hB]
      linarith
  have hclose : (∑ i ∈ S, ∑ j ∈ S,
        (if |t j - t i| ≤ (N : ℝ) then ‖c i‖ * ‖c j‖ else 0))
      ≤ (2 * (N : ℝ) + 1) * ∑ i ∈ S, ‖c i‖ ^ 2 := by
    have h := Commons.Analysis.Metric.separated_pairs_count_bound_finset S t hsep N c
    have heq : (∑ i ∈ S, ∑ j ∈ S,
          (if |t j - t i| ≤ (N : ℝ) then ‖c i‖ * ‖c j‖ else 0))
        = (∑ i ∈ S, ∑ j ∈ S,
          (if |t i - t j| ≤ (N : ℝ) then ‖c i‖ * ‖c j‖ else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [abs_sub_comm (t j) (t i)]
    rw [heq]
    exact h
  have hfar : (∑ i ∈ S, ∑ j ∈ S,
        (if |t j - t i| ≤ (N : ℝ) then 0 else ‖c i‖ * ‖c j‖))
      ≤ (S.card : ℝ) * ∑ i ∈ S, ‖c i‖ ^ 2 := by
    calc (∑ i ∈ S, ∑ j ∈ S, (if |t j - t i| ≤ (N : ℝ) then 0 else ‖c i‖ * ‖c j‖))
        ≤ ∑ i ∈ S, ∑ j ∈ S, ‖c i‖ * ‖c j‖ := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          by_cases h : |t j - t i| ≤ (N : ℝ)
          · simp only [h, if_true]
            exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
          · simp only [h, if_false]; exact le_rfl
      _ = (∑ i ∈ S, ‖c i‖) * (∑ j ∈ S, ‖c j‖) := by rw [Finset.sum_mul_sum]
      _ = (∑ i ∈ S, ‖c i‖) ^ 2 := by ring
      _ ≤ (S.card : ℝ) * ∑ i ∈ S, ‖c i‖ ^ 2 := sum_norm_sq_le_card S c
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h2N : (2 * (N : ℝ) + 1) ≤ 3 * (N : ℝ) := by linarith
  have hsplit : (∑ i ∈ S, ∑ j ∈ S, ‖c i‖ * ‖c j‖ * (if |t j - t i| ≤ (N : ℝ) then A else B))
      ≤ A * (∑ i ∈ S, ∑ j ∈ S, (if |t j - t i| ≤ (N : ℝ) then ‖c i‖ * ‖c j‖ else 0))
        + B * (∑ i ∈ S, ∑ j ∈ S, (if |t j - t i| ≤ (N : ℝ) then 0 else ‖c i‖ * ‖c j‖)) := by
    have hstep : (∑ i ∈ S, ∑ j ∈ S, ‖c i‖ * ‖c j‖ * (if |t j - t i| ≤ (N : ℝ) then A else B))
        ≤ ∑ i ∈ S, ∑ j ∈ S,
          ((if |t j - t i| ≤ (N : ℝ) then ‖c i‖ * ‖c j‖ * A else 0)
            + (if |t j - t i| ≤ (N : ℝ) then 0 else ‖c i‖ * ‖c j‖ * B)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact ite_mul_le_add _ _ _ _
    calc (∑ i ∈ S, ∑ j ∈ S, ‖c i‖ * ‖c j‖ * (if |t j - t i| ≤ (N : ℝ) then A else B))
        ≤ ∑ i ∈ S, ∑ j ∈ S,
          ((if |t j - t i| ≤ (N : ℝ) then ‖c i‖ * ‖c j‖ * A else 0)
            + (if |t j - t i| ≤ (N : ℝ) then 0 else ‖c i‖ * ‖c j‖ * B)) := hstep
      _ = (∑ i ∈ S, ∑ j ∈ S, (if |t j - t i| ≤ (N : ℝ) then ‖c i‖ * ‖c j‖ * A else 0))
          + (∑ i ∈ S, ∑ j ∈ S, (if |t j - t i| ≤ (N : ℝ) then 0 else ‖c i‖ * ‖c j‖ * B)) := by
          rw [show (∑ i ∈ S, ∑ j ∈ S,
                ((if |t j - t i| ≤ (N : ℝ) then ‖c i‖ * ‖c j‖ * A else 0)
                  + (if |t j - t i| ≤ (N : ℝ) then 0 else ‖c i‖ * ‖c j‖ * B)))
              = ∑ i ∈ S, ((∑ j ∈ S, (if |t j - t i| ≤ (N : ℝ) then ‖c i‖ * ‖c j‖ * A else 0))
                  + (∑ j ∈ S, (if |t j - t i| ≤ (N : ℝ) then 0 else ‖c i‖ * ‖c j‖ * B))) from by
              apply Finset.sum_congr rfl; intro i hi; rw [Finset.sum_add_distrib]]
          rw [Finset.sum_add_distrib]
      _ = A * (∑ i ∈ S, ∑ j ∈ S, (if |t j - t i| ≤ (N : ℝ) then ‖c i‖ * ‖c j‖ else 0))
          + B * (∑ i ∈ S, ∑ j ∈ S, (if |t j - t i| ≤ (N : ℝ) then 0 else ‖c i‖ * ‖c j‖)) := by
          rw [sum_sum_ite_mul_const S (fun i j => |t j - t i| ≤ (N : ℝ))
                (fun i j => ‖c i‖ * ‖c j‖) A,
              sum_sum_ite_not_mul_const S (fun i j => |t j - t i| ≤ (N : ℝ))
                (fun i j => ‖c i‖ * ‖c j‖) B]
  have hfin : A * ((2 * (N : ℝ) + 1) * ∑ i ∈ S, ‖c i‖ ^ 2)
      + B * ((S.card : ℝ) * ∑ i ∈ S, ‖c i‖ ^ 2)
      ≤ 7 * C2 * ((N : ℝ) + (S.card : ℝ) * Real.sqrt L) * ∑ i ∈ S, ‖c i‖ ^ 2 := by
    have hA2 : A * ((2 * (N : ℝ) + 1) * ∑ i ∈ S, ‖c i‖ ^ 2)
        ≤ (6 * C2 * (N : ℝ)) * ∑ i ∈ S, ‖c i‖ ^ 2 := by
      have hAA : A * (2 * (N : ℝ) + 1) ≤ 6 * C2 * (N : ℝ) := by
        rw [hA]; nlinarith [h2N, hC2.le]
      calc A * ((2 * (N : ℝ) + 1) * ∑ i ∈ S, ‖c i‖ ^ 2)
          = (A * (2 * (N : ℝ) + 1)) * ∑ i ∈ S, ‖c i‖ ^ 2 := by ring
        _ ≤ (6 * C2 * (N : ℝ)) * ∑ i ∈ S, ‖c i‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hAA hS0
    have hB2 : B * ((S.card : ℝ) * ∑ i ∈ S, ‖c i‖ ^ 2)
        = (C2 * Real.sqrt L * (S.card : ℝ)) * ∑ i ∈ S, ‖c i‖ ^ 2 := by
      rw [hB]; ring
    calc A * ((2 * (N : ℝ) + 1) * ∑ i ∈ S, ‖c i‖ ^ 2)
          + B * ((S.card : ℝ) * ∑ i ∈ S, ‖c i‖ ^ 2)
        ≤ (6 * C2 * (N : ℝ)) * ∑ i ∈ S, ‖c i‖ ^ 2
          + (C2 * Real.sqrt L * (S.card : ℝ)) * ∑ i ∈ S, ‖c i‖ ^ 2 :=
          add_le_add hA2 (le_of_eq hB2)
      _ = (6 * C2 * (N : ℝ) + C2 * Real.sqrt L * (S.card : ℝ)) * ∑ i ∈ S, ‖c i‖ ^ 2 := by
          ring
      _ ≤ (7 * C2 * ((N : ℝ) + (S.card : ℝ) * Real.sqrt L)) * ∑ i ∈ S, ‖c i‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hS0
          have hsL : (0 : ℝ) ≤ Real.sqrt L := Real.sqrt_nonneg L
          nlinarith [hC2.le, hNnonneg, hCn, hsL]
  calc ‖∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j * Ealias N (t j - t i)‖
      ≤ ∑ i ∈ S, ∑ j ∈ S, ‖c i‖ * ‖c j‖ * (if |t j - t i| ≤ (N : ℝ) then A else B) := by
        calc ‖∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j * Ealias N (t j - t i)‖
            ≤ ∑ i ∈ S, ‖∑ j ∈ S, (starRingEnd ℂ) (c i) * c j * Ealias N (t j - t i)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ i ∈ S, ∑ j ∈ S, ‖(starRingEnd ℂ) (c i) * c j * Ealias N (t j - t i)‖ := by
              apply Finset.sum_le_sum
              intro i hi
              exact norm_sum_le _ _
          _ = ∑ i ∈ S, ∑ j ∈ S, ‖c i‖ * ‖c j‖ * ‖Ealias N (t j - t i)‖ := by
              simp
          _ ≤ ∑ i ∈ S, ∑ j ∈ S, ‖c i‖ * ‖c j‖ * (if |t j - t i| ≤ (N : ℝ) then A else B) := by
              apply Finset.sum_le_sum
              intro i hi
              apply Finset.sum_le_sum
              intro j hj
              exact mul_le_mul_of_nonneg_left (hpt i hi j hj) (by positivity)
    _ ≤ A * (∑ i ∈ S, ∑ j ∈ S, (if |t j - t i| ≤ (N : ℝ) then ‖c i‖ * ‖c j‖ else 0))
        + B * (∑ i ∈ S, ∑ j ∈ S, (if |t j - t i| ≤ (N : ℝ) then 0 else ‖c i‖ * ‖c j‖)) := hsplit
    _ ≤ A * ((2 * (N : ℝ) + 1) * ∑ i ∈ S, ‖c i‖ ^ 2)
        + B * ((S.card : ℝ) * ∑ i ∈ S, ‖c i‖ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hclose hA0) (mul_le_mul_of_nonneg_left hfar hB0)
    _ ≤ 7 * C2 * ((N : ℝ) + (S.card : ℝ) * Real.sqrt L) * ∑ i ∈ S, ‖c i‖ ^ 2 := hfin

private lemma sum_sum_add_distrib {ι : Type} (S : Finset ι) (f g : ι → ι → ℂ) :
    (∑ i ∈ S, ∑ j ∈ S, (f i j + g i j))
      = (∑ i ∈ S, ∑ j ∈ S, f i j) + (∑ i ∈ S, ∑ j ∈ S, g i j) := by
  rw [show (∑ i ∈ S, ∑ j ∈ S, (f i j + g i j))
      = ∑ i ∈ S, ((∑ j ∈ S, f i j) + (∑ j ∈ S, g i j)) from by
        apply Finset.sum_congr rfl; intro i hi; rw [Finset.sum_add_distrib]]
  rw [Finset.sum_add_distrib]

/-- Log-free Halász inequality: for `1`-separated frequencies `t i` with pairwise distances
at most `L`, the mean square of `∑_i c_i n^{I t_i}` over `n ∈ [N,2N]` is at most
`C (N + R √L) ∑_i ‖c_i‖²`. -/
theorem halasz_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} (S : Finset ι) (N : ℕ), 1 ≤ N →
      ∀ (t : ι → ℝ) (c : ι → ℂ) (L : ℝ), 0 ≤ L →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ S, ∀ j ∈ S, |t i - t j| ≤ L) →
      ∑ n ∈ Finset.Icc N (2 * N), ‖∑ i ∈ S, c i * (n : ℂ) ^ (Complex.I * (t i : ℂ))‖ ^ 2
        ≤ C * ((N : ℝ) + (S.card : ℝ) * Real.sqrt L) * ∑ i ∈ S, ‖c i‖ ^ 2 := by
  obtain ⟨C1, hC1, hInt⟩ := Commons.Analysis.DirichletPolynomial.dual_integral_mean_value_finset
  obtain ⟨Ce, hCe, hE⟩ := Ealias_pair_bound
  refine ⟨C1 + Ce + 1, by linarith, ?_⟩
  intro ι S N hN t c L hL hsep hLt
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hle : (N : ℝ) ≤ 2 * (N : ℝ) := by linarith [hNpos]
  have hS0 : (0 : ℝ) ≤ ∑ i ∈ S, ‖c i‖ ^ 2 := by positivity
  rw [normSq_sum_cpow_expansion S N hN t c]
  have hZ : (∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j * Zsum N (t j - t i))
      = (∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j * Isum N (t j - t i))
        + (∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j * Ealias N (t j - t i)) := by
    rw [show (∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j * Zsum N (t j - t i))
        = ∑ i ∈ S, ∑ j ∈ S, ((starRingEnd ℂ) (c i) * c j * Isum N (t j - t i)
            + (starRingEnd ℂ) (c i) * c j * Ealias N (t j - t i)) from by
          apply Finset.sum_congr rfl; intro i hi
          apply Finset.sum_congr rfl; intro j hj
          rw [Ealias]; ring]
    exact sum_sum_add_distrib S _ _
  have hI : (∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j * Isum N (t j - t i)).re
      = ∫ x in (N : ℝ)..(2 * (N : ℝ)),
          ‖∑ i ∈ S, c i * (x : ℂ) ^ (Complex.I * (t i : ℂ))‖ ^ 2 := by
    have h := Commons.Analysis.DirichletPolynomial.integral_normsq_cpow_expansion S (N : ℝ) (2 * (N : ℝ)) hNpos hle t c
    simp only [Isum]
    rw [← h, intervalIntegral.integral_ofReal, Complex.ofReal_re]
  have hIntb : (∫ x in (N : ℝ)..(2 * (N : ℝ)),
        ‖∑ i ∈ S, c i * (x : ℂ) ^ (Complex.I * (t i : ℂ))‖ ^ 2)
      ≤ C1 * (N : ℝ) * ∑ i ∈ S, ‖c i‖ ^ 2 := by
    have h := hInt N hN S t c hsep
    have hnn : (0 : ℝ) ≤ ∫ x in (N : ℝ)..(2 * (N : ℝ)),
        ‖∑ i ∈ S, c i * (x : ℂ) ^ (Complex.I * (t i : ℂ))‖ ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hle (fun x => by positivity)
    rwa [Real.norm_eq_abs, abs_of_nonneg hnn] at h
  have hEb := hE S N hN t c L hL hsep hLt
  have hfin : C1 * (N : ℝ) * ∑ i ∈ S, ‖c i‖ ^ 2
      + Ce * ((N : ℝ) + (S.card : ℝ) * Real.sqrt L) * ∑ i ∈ S, ‖c i‖ ^ 2
      ≤ (C1 + Ce + 1) * ((N : ℝ) + (S.card : ℝ) * Real.sqrt L) * ∑ i ∈ S, ‖c i‖ ^ 2 := by
    have hcn : (0 : ℝ) ≤ (S.card : ℝ) * Real.sqrt L := by positivity
    have hNB : (N : ℝ) ≤ (N : ℝ) + (S.card : ℝ) * Real.sqrt L := by linarith
    have hB0 : (0 : ℝ) ≤ (N : ℝ) + (S.card : ℝ) * Real.sqrt L := by linarith [hNpos]
    calc C1 * (N : ℝ) * ∑ i ∈ S, ‖c i‖ ^ 2
          + Ce * ((N : ℝ) + (S.card : ℝ) * Real.sqrt L) * ∑ i ∈ S, ‖c i‖ ^ 2
        ≤ C1 * ((N : ℝ) + (S.card : ℝ) * Real.sqrt L) * ∑ i ∈ S, ‖c i‖ ^ 2
          + Ce * ((N : ℝ) + (S.card : ℝ) * Real.sqrt L) * ∑ i ∈ S, ‖c i‖ ^ 2 :=
          add_le_add (by
            apply mul_le_mul_of_nonneg_right _ hS0
            exact mul_le_mul_of_nonneg_left hNB hC1.le) le_rfl
      _ = (C1 + Ce) * ((N : ℝ) + (S.card : ℝ) * Real.sqrt L) * ∑ i ∈ S, ‖c i‖ ^ 2 := by ring
      _ ≤ (C1 + Ce + 1) * ((N : ℝ) + (S.card : ℝ) * Real.sqrt L) * ∑ i ∈ S, ‖c i‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hS0
          apply mul_le_mul_of_nonneg_right _ hB0
          linarith
  calc (∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j * Zsum N (t j - t i)).re
      = (∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j * Isum N (t j - t i)).re
        + (∑ i ∈ S, ∑ j ∈ S,
            (starRingEnd ℂ) (c i) * c j * Ealias N (t j - t i)).re := by
        rw [hZ, Complex.add_re]
    _ = (∫ x in (N : ℝ)..(2 * (N : ℝ)),
            ‖∑ i ∈ S, c i * (x : ℂ) ^ (Complex.I * (t i : ℂ))‖ ^ 2)
        + (∑ i ∈ S, ∑ j ∈ S,
            (starRingEnd ℂ) (c i) * c j * Ealias N (t j - t i)).re := by rw [hI]
    _ ≤ C1 * (N : ℝ) * ∑ i ∈ S, ‖c i‖ ^ 2
        + ‖∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j * Ealias N (t j - t i)‖ :=
        add_le_add hIntb (Complex.re_le_norm _)
    _ ≤ C1 * (N : ℝ) * ∑ i ∈ S, ‖c i‖ ^ 2
        + Ce * ((N : ℝ) + (S.card : ℝ) * Real.sqrt L) * ∑ i ∈ S, ‖c i‖ ^ 2 :=
        add_le_add le_rfl hEb
    _ ≤ (C1 + Ce + 1) * ((N : ℝ) + (S.card : ℝ) * Real.sqrt L) * ∑ i ∈ S, ‖c i‖ ^ 2 := hfin

/-- In one window of length `L₀ = V⁴/(16 C² N²)`, the number of large values is `≤ 4 C N²/V²`. -/
lemma group_card_le {ι : Type} (J : Finset ι) (N : ℕ) (hN : 1 ≤ N) (V L₀ Chl : ℝ)
    (hChl : 0 < Chl) (hV : 0 < V) (b : ℕ → ℂ) (hb : ∀ n, ‖b n‖ ≤ 1) (t : ι → ℝ)
    (hJlt : ∀ i ∈ J, ∀ j ∈ J, |t i - t j| ≤ L₀)
    (hHL : ∀ (c : ι → ℂ) (L : ℝ), 0 ≤ L → (∀ i ∈ J, ∀ j ∈ J, |t i - t j| ≤ L) →
      ∑ n ∈ Finset.Icc N (2 * N), ‖∑ i ∈ J, c i * (n : ℂ) ^ (Complex.I * (t i : ℂ))‖ ^ 2
        ≤ Chl * ((N : ℝ) + (J.card : ℝ) * Real.sqrt L) * ∑ i ∈ J, ‖c i‖ ^ 2)
    (hval : ∀ r ∈ J, V ≤ ‖∑ n ∈ Finset.Icc N (2 * N),
      b n * (n : ℂ) ^ (Complex.I * (t r : ℂ))‖)
    (hL0 : L₀ = V ^ 4 / (16 * Chl ^ 2 * (N : ℝ) ^ 2)) :
    (J.card : ℝ) ≤ 4 * Chl * (N : ℝ) ^ 2 / V ^ 2 := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hL0pos : 0 < L₀ := by rw [hL0]; positivity
  by_cases hJ0 : J.card = 0
  · have : (J.card : ℝ) = 0 := by simp [hJ0]
    rw [this]
    positivity
  have hJpos : (0 : ℝ) < (J.card : ℝ) := by
    have : 0 < J.card := Nat.pos_of_ne_zero hJ0
    exact_mod_cast this
  set D : ι → ℂ := fun r => ∑ n ∈ Finset.Icc N (2 * N),
    b n * (n : ℂ) ^ (Complex.I * (t r : ℂ)) with hD
  set c : ι → ℂ := fun r => (starRingEnd ℂ) (D r) / ((‖D r‖ : ℝ) : ℂ) with hc
  have hcn : ∀ r ∈ J, ‖c r‖ = 1 := by
    intro r hr
    have hVr : (0 : ℝ) < ‖D r‖ := lt_of_lt_of_le hV (hval r hr)
    have hnorm : ‖((‖D r‖ : ℝ) : ℂ)‖ = ‖D r‖ := by
      rw [norm_ofReal_complex, abs_of_nonneg (norm_nonneg _)]
    simp only [hc]
    rw [norm_div, norm_conj, hnorm]
    exact div_self (ne_of_gt hVr)
  have hkey : ((∑ r ∈ J, ‖D r‖ : ℝ) : ℂ)
      = ∑ n ∈ Finset.Icc N (2 * N), b n * ∑ r ∈ J, c r * (n : ℂ) ^ (Complex.I * (t r : ℂ)) := by
    have h1 : ∀ r ∈ J, ‖D r‖ = D r * c r := by
      intro r hr
      have hVr : (0 : ℝ) < ‖D r‖ := lt_of_lt_of_le hV (hval r hr)
      have hmc : D r * (starRingEnd ℂ) (D r) = ((‖D r‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hdc : D r * c r = D r * (starRingEnd ℂ) (D r) / ((‖D r‖ : ℝ) : ℂ) := by
        simp only [hc]; ring
      rw [hdc, hmc, ← Complex.ofReal_div, Complex.ofReal_inj]
      rw [eq_div_iff (ne_of_gt hVr)]
      ring
    calc ((∑ r ∈ J, ‖D r‖ : ℝ) : ℂ) = ∑ r ∈ J, D r * c r := by
          push_cast
          exact Finset.sum_congr rfl h1
      _ = ∑ r ∈ J, (∑ n ∈ Finset.Icc N (2 * N),
            b n * (n : ℂ) ^ (Complex.I * (t r : ℂ))) * c r := by
          apply Finset.sum_congr rfl; intro r hr; simp only [hD]
      _ = ∑ r ∈ J, ∑ n ∈ Finset.Icc N (2 * N),
            (b n * (n : ℂ) ^ (Complex.I * (t r : ℂ))) * c r := by
          apply Finset.sum_congr rfl; intro r hr; rw [Finset.sum_mul]
      _ = ∑ n ∈ Finset.Icc N (2 * N), ∑ r ∈ J,
            (b n * (n : ℂ) ^ (Complex.I * (t r : ℂ))) * c r := Finset.sum_comm
      _ = ∑ n ∈ Finset.Icc N (2 * N), b n * ∑ r ∈ J,
            c r * (n : ℂ) ^ (Complex.I * (t r : ℂ)) := by
          apply Finset.sum_congr rfl; intro n hn
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro r hr
          ring
  set w : ℕ → ℂ := fun n => ∑ r ∈ J, c r * (n : ℂ) ^ (Complex.I * (t r : ℂ)) with hw
  have hCS : (∑ r ∈ J, ‖D r‖) ^ 2
      ≤ (∑ n ∈ Finset.Icc N (2 * N), ‖b n‖ ^ 2)
        * (∑ n ∈ Finset.Icc N (2 * N), ‖w n‖ ^ 2) := by
    have hkey2 : ((∑ r ∈ J, ‖D r‖ : ℝ) : ℂ)
        = ∑ n ∈ Finset.Icc N (2 * N), b n * w n := by
      rw [hkey, hw]
    have hnorm : ‖∑ n ∈ Finset.Icc N (2 * N), b n * w n‖ = ∑ r ∈ J, ‖D r‖ := by
      rw [← hkey2, norm_ofReal_complex, abs_of_nonneg (by positivity)]
    rw [← hnorm]
    calc ‖∑ n ∈ Finset.Icc N (2 * N), b n * w n‖ ^ 2
        ≤ (∑ n ∈ Finset.Icc N (2 * N), ‖b n‖ * ‖w n‖) ^ 2 := by
          apply pow_le_pow_left₀ (norm_nonneg _)
          calc ‖∑ n ∈ Finset.Icc N (2 * N), b n * w n‖
              ≤ ∑ n ∈ Finset.Icc N (2 * N), ‖b n * w n‖ := norm_sum_le _ _
            _ = ∑ n ∈ Finset.Icc N (2 * N), ‖b n‖ * ‖w n‖ := by simp
      _ ≤ (∑ n ∈ Finset.Icc N (2 * N), ‖b n‖ ^ 2)
          * (∑ n ∈ Finset.Icc N (2 * N), ‖w n‖ ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hb2 : (∑ n ∈ Finset.Icc N (2 * N), ‖b n‖ ^ 2) ≤ 2 * (N : ℝ) := by
    have h1 : (∑ n ∈ Finset.Icc N (2 * N), ‖b n‖ ^ 2)
        ≤ ∑ n ∈ Finset.Icc N (2 * N), (1 : ℝ) := by
      apply Finset.sum_le_sum; intro n hn
      exact pow_le_one₀ (norm_nonneg _) (hb n)
    have h2 : (∑ _n ∈ Finset.Icc N (2 * N), (1 : ℝ)) = ((N + 1 : ℕ) : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 1
      rw [Nat.card_Icc]
      omega
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    calc (∑ n ∈ Finset.Icc N (2 * N), ‖b n‖ ^ 2)
        ≤ ∑ n ∈ Finset.Icc N (2 * N), (1 : ℝ) := h1
      _ = ((N + 1 : ℕ) : ℝ) := h2
      _ ≤ 2 * (N : ℝ) := by push_cast; linarith
  have hwbound : (∑ n ∈ Finset.Icc N (2 * N), ‖w n‖ ^ 2)
      ≤ Chl * ((N : ℝ) + (J.card : ℝ) * Real.sqrt L₀) * (J.card : ℝ) := by
    have h := hHL c L₀ hL0pos.le hJlt
    have hcsum : (∑ i ∈ J, ‖c i‖ ^ 2) = (J.card : ℝ) := by
      rw [show (∑ i ∈ J, ‖c i‖ ^ 2) = ∑ _i ∈ J, (1 : ℝ) from by
            apply Finset.sum_congr rfl; intro i hi; rw [hcn i hi]; norm_num]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcsum] at h
    simpa only [hw] using h
  have hmain : ((J.card : ℝ) * V) ^ 2
      ≤ 2 * (N : ℝ) * (Chl * ((N : ℝ) + (J.card : ℝ) * Real.sqrt L₀) * (J.card : ℝ)) := by
    calc ((J.card : ℝ) * V) ^ 2 ≤ (∑ r ∈ J, ‖D r‖) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity)
          have hconst : ((J.card : ℝ) * V) = ∑ _r ∈ J, V := by
            rw [Finset.sum_const, nsmul_eq_mul]
          rw [hconst]
          apply Finset.sum_le_sum; intro r hr
          exact hval r hr
      _ ≤ (∑ n ∈ Finset.Icc N (2 * N), ‖b n‖ ^ 2)
          * (∑ n ∈ Finset.Icc N (2 * N), ‖w n‖ ^ 2) := hCS
      _ ≤ 2 * (N : ℝ) * (Chl * ((N : ℝ) + (J.card : ℝ) * Real.sqrt L₀) * (J.card : ℝ)) :=
          mul_le_mul hb2 hwbound (by positivity) (by positivity)
  have hsqrt : Real.sqrt L₀ = V ^ 2 / (4 * Chl * (N : ℝ)) := by
    have hnonneg : (0 : ℝ) ≤ V ^ 2 / (4 * Chl * (N : ℝ)) := by positivity
    have hsq : L₀ = (V ^ 2 / (4 * Chl * (N : ℝ))) ^ 2 := by
      rw [hL0]; field_simp; ring
    rw [hsq, Real.sqrt_sq hnonneg]
  rw [hsqrt] at hmain
  have hexp : 2 * (N : ℝ) * (Chl * ((N : ℝ) + (J.card : ℝ) * (V ^ 2 / (4 * Chl * (N : ℝ))))
        * (J.card : ℝ)) = 2 * Chl * (N : ℝ) ^ 2 * (J.card : ℝ) + ((J.card : ℝ) * V) ^ 2 / 2 := by
    field_simp
    ring
  rw [hexp] at hmain
  have hf2 : ((J.card : ℝ) * V) ^ 2 / 2 ≤ 2 * Chl * (N : ℝ) ^ 2 * (J.card : ℝ) := by
    linarith [hmain]
  have h4 : (J.card : ℝ) * V ^ 2 / 2 ≤ 2 * Chl * (N : ℝ) ^ 2 := by
    have h2 : (J.card : ℝ) * ((J.card : ℝ) * V ^ 2 / 2)
        ≤ (J.card : ℝ) * (2 * Chl * (N : ℝ) ^ 2) := by
      nlinarith [hf2]
    exact le_of_mul_le_mul_left h2 hJpos
  have h5 : (J.card : ℝ) * V ^ 2 ≤ 4 * Chl * (N : ℝ) ^ 2 := by linarith
  rw [le_div_iff₀ (pow_pos hV 2)]
  linarith

open Finset Complex
open scoped ComplexConjugate BigOperators

/-- Classical (log-free, absolute constant) large-values estimate of Halász–Huxley type
for Dirichlet polynomials of length N with 1-bounded coefficients at 1-separated points
of [0,T]: R ≪ N^2 V^-2 + T N^4 V^-6, which beats the plain mean-value bound
N^2 V^-2 + T N V^-2 exactly when V ≥ N^(3/4).

This is classical Analytic Number Theory (Montgomery's large values method building on
Halász; see Ivić, "The Riemann Zeta-Function", ch. 8-9, or Montgomery "Topics in
multiplicative number theory", large values estimate).  The point is that it holds with
an ABSOLUTE constant (no powers of N or T on the right).  Auxiliary tools available in
the commons: the log-free Montgomery–Vaughan mean value bounds
(Commons.NumberTheory.DirichletPolynomial.mv_mean_value_logfree and relatives), the
sampled/large-sieve block bounds (Commons.NumberTheory.DirichletPolynomial.*), the
Montgomery–Vaughan Hilbert inequality
(Commons.LinearAlgebra.Matrix.mv_hilbert_separated) and
Commons.Analysis.Metric.one_separated_points_card_le. -/
theorem large_values_halasz_huxley :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (V T : ℝ) (R : ℕ) (t : Fin R → ℝ) (b : ℕ → ℂ),
        1 ≤ N → 0 < V → 1 ≤ T → (∀ n, ‖b n‖ ≤ 1) →
        (N : ℝ) ^ (3 / 4 : ℝ) ≤ V →
        (∀ i, t i ∈ Set.Icc 0 T) →
        (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
        (∀ r, V ≤ ‖∑ n ∈ Finset.Icc N (2 * N), b n * (n : ℂ) ^ (I * (t r : ℂ))‖) →
        (R : ℝ) ≤ C * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ) + T * (N : ℝ) ^ 4 * V ^ (-6 : ℤ)) := by
  obtain ⟨Chl, hChl, hHL⟩ := halasz_bound
  refine ⟨4 * Chl + 64 * Chl ^ 3, by positivity, ?_⟩
  intro N V T R t b hN hV hT hb _hVge htI htsep hval
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT
  set L₀ : ℝ := V ^ 4 / (16 * Chl ^ 2 * (N : ℝ) ^ 2) with hL₀def
  have hL₀pos : 0 < L₀ := by rw [hL₀def]; positivity
  set f : Fin R → ℕ := fun r => Nat.floor (t r / L₀) with hf
  set M : ℕ := Nat.floor (T / L₀) + 1 with hM
  have hMapsTo : Set.MapsTo f ↑(Finset.univ : Finset (Fin R)) ↑(Finset.range M) := by
    intro r _
    simp only [Finset.mem_coe, Finset.mem_range]
    have hr0 : 0 ≤ t r / L₀ := div_nonneg (htI r).1 hL₀pos.le
    have h2 : t r / L₀ ≤ T / L₀ := div_le_div_of_nonneg_right (htI r).2 hL₀pos.le
    have h3 : T / L₀ < (Nat.floor (T / L₀) : ℝ) + 1 := Nat.lt_floor_add_one _
    have h4 : t r / L₀ < (M : ℝ) := by rw [hM]; push_cast; linarith
    show Nat.floor (t r / L₀) < M
    exact (Nat.floor_lt hr0).mpr h4
  have hfib : (R : ℝ) = ∑ k ∈ Finset.range M,
      (((Finset.univ : Finset (Fin R)).filter (fun r => f r = k)).card : ℝ) := by
    have h1 : ((Finset.univ : Finset (Fin R)).card : ℝ)
        = ∑ k ∈ Finset.range M,
          (((Finset.univ : Finset (Fin R)).filter (fun r => f r = k)).card : ℝ) := by
      rw [Finset.card_eq_sum_card_fiberwise hMapsTo, Nat.cast_sum]
    have h2 : ((Finset.univ : Finset (Fin R)).card : ℝ) = (R : ℝ) := by
      rw [Finset.card_univ, Fintype.card_fin]
    rw [← h2]; exact h1
  have hgrp : ∀ k ∈ Finset.range M,
      (((Finset.univ : Finset (Fin R)).filter (fun r => f r = k)).card : ℝ)
        ≤ 4 * Chl * (N : ℝ) ^ 2 / V ^ 2 := by
    intro k hk
    set J : Finset (Fin R) := (Finset.univ.filter (fun r => f r = k)) with hJ
    have hJlt : ∀ i ∈ J, ∀ j ∈ J, |t i - t j| ≤ L₀ := by
      intro i hi j hj
      rw [hJ] at hi hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      have hi0 : 0 ≤ t i / L₀ := div_nonneg (htI i).1 hL₀pos.le
      have hj0 : 0 ≤ t j / L₀ := div_nonneg (htI j).1 hL₀pos.le
      have h1 : (k : ℝ) ≤ t i / L₀ := by rw [← hi, hf]; exact Nat.floor_le hi0
      have h2 : t j / L₀ < (k : ℝ) + 1 := by rw [← hj, hf]; exact Nat.lt_floor_add_one _
      have h3 : (k : ℝ) ≤ t j / L₀ := by rw [← hj, hf]; exact Nat.floor_le hj0
      have h4 : t i / L₀ < (k : ℝ) + 1 := by rw [← hi, hf]; exact Nat.lt_floor_add_one _
      rw [abs_le]
      constructor
      · have h5 : (-1 : ℝ) < (t i - t j) / L₀ := by rw [sub_div]; linarith
        rw [lt_div_iff₀ hL₀pos] at h5
        linarith
      · have h5 : (-1 : ℝ) < (t j - t i) / L₀ := by rw [sub_div]; linarith
        rw [lt_div_iff₀ hL₀pos] at h5
        linarith
    exact group_card_le J N hN V L₀ Chl hChl hV b hb t hJlt
      (fun c L hL' hLt' =>
        hHL (S := J) N hN t c L hL' (fun i hi j hj hij => htsep i j hij) hLt')
      (fun r hr => hval r) (by rw [hL₀def])
  have hRbound : (R : ℝ) ≤ (M : ℝ) * (4 * Chl * (N : ℝ) ^ 2 / V ^ 2) := by
    calc (R : ℝ) = ∑ k ∈ Finset.range M,
          (((Finset.univ : Finset (Fin R)).filter (fun r => f r = k)).card : ℝ) := hfib
      _ ≤ ∑ _k ∈ Finset.range M, (4 * Chl * (N : ℝ) ^ 2 / V ^ 2) := Finset.sum_le_sum hgrp
      _ = (M : ℝ) * (4 * Chl * (N : ℝ) ^ 2 / V ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  have hMbound : (M : ℝ) ≤ T / L₀ + 1 := by
    have h0 : (0 : ℝ) ≤ T / L₀ := div_nonneg hT0 hL₀pos.le
    have := Nat.floor_le h0
    rw [hM]; push_cast; linarith
  have hR2 : (R : ℝ) ≤ (T / L₀ + 1) * (4 * Chl * (N : ℝ) ^ 2 / V ^ 2) :=
    hRbound.trans (mul_le_mul_of_nonneg_right hMbound (by positivity))
  have hkey : (T / L₀ + 1) * (4 * Chl * (N : ℝ) ^ 2 / V ^ 2)
      = 4 * Chl * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ))
        + 64 * Chl ^ 3 * (T * (N : ℝ) ^ 4 * V ^ (-6 : ℤ)) := by
    have hV2 : V ^ (-2 : ℤ) = (V ^ 2)⁻¹ := by rw [zpow_neg, zpow_ofNat]
    have hV6 : V ^ (-6 : ℤ) = (V ^ 6)⁻¹ := by rw [zpow_neg, zpow_ofNat]
    rw [hV2, hV6, hL₀def]
    field_simp
    ring
  rw [hkey] at hR2
  have hfin : 4 * Chl * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ))
      + 64 * Chl ^ 3 * (T * (N : ℝ) ^ 4 * V ^ (-6 : ℤ))
      ≤ (4 * Chl + 64 * Chl ^ 3)
        * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ) + T * (N : ℝ) ^ 4 * V ^ (-6 : ℤ)) := by
    have h1 : (0 : ℝ) ≤ (N : ℝ) ^ 2 * V ^ (-2 : ℤ) := by positivity
    have h2 : (0 : ℝ) ≤ T * (N : ℝ) ^ 4 * V ^ (-6 : ℤ) := by positivity
    have h3 : 4 * Chl * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ))
        ≤ (4 * Chl) * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ) + T * (N : ℝ) ^ 4 * V ^ (-6 : ℤ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 4 * Chl)
      linarith
    have h4 : 64 * Chl ^ 3 * (T * (N : ℝ) ^ 4 * V ^ (-6 : ℤ))
        ≤ (64 * Chl ^ 3) * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ) + T * (N : ℝ) ^ 4 * V ^ (-6 : ℤ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 64 * Chl ^ 3)
      linarith
    calc 4 * Chl * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ))
          + 64 * Chl ^ 3 * (T * (N : ℝ) ^ 4 * V ^ (-6 : ℤ))
        ≤ (4 * Chl) * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ) + T * (N : ℝ) ^ 4 * V ^ (-6 : ℤ))
          + (64 * Chl ^ 3) * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ)
              + T * (N : ℝ) ^ 4 * V ^ (-6 : ℤ)) := add_le_add h3 h4
      _ = (4 * Chl + 64 * Chl ^ 3)
          * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ) + T * (N : ℝ) ^ 4 * V ^ (-6 : ℤ)) := by ring
  linarith [hR2, hfin]

end Commons.NumberTheory.DirichletPolynomial
