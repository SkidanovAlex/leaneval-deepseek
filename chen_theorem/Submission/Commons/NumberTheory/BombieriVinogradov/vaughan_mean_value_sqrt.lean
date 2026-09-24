import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.vonMangoldt_eq_lambda_decomp_pos
import Submission.Commons.NumberTheory.BombieriVinogradov.vaughan_lambda3_reindex
import Submission.Commons.NumberTheory.BombieriVinogradov.vaughan_mean_value_param
import Submission.Commons.NumberTheory.BombieriVinogradov.vaughan_type1_lambda2_estimate
import Submission.Commons.NumberTheory.BombieriVinogradov.vaughan_type1_lambda3_estimate
import Submission.Commons.NumberTheory.BombieriVinogradov.vaughan_type2_lambda3_estimate
import Submission.Commons.NumberTheory.BombieriVinogradov.vaughan_type2_lambda4_estimate

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators

set_option maxHeartbeats 4000000

noncomputable def primF (q : ℕ) : Finset (DirichletCharacter ℂ q) :=
  @Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive) (Classical.decPred _) Finset.univ

noncomputable def blockSum (x Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ ∈ primF q,
      ‖∑ n ∈ Finset.range (x+1),
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖

noncomputable def mvtL1 (T n : ℕ) : ℝ := if n ≤ T then (ArithmeticFunction.vonMangoldt n : ℝ) else 0

noncomputable def mvtL2 (T n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ T),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ)

noncomputable def mvtL3 (T n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ T),
    ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ T),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (ArithmeticFunction.vonMangoldt e : ℝ)

noncomputable def mvtL4 (T n : ℕ) : ℝ :=
  ∑ m ∈ n.divisors.filter (fun m => T < m ∧ T < n / m),
    (ArithmeticFunction.vonMangoldt m : ℝ) *
      ∑ d ∈ (n / m).divisors.filter (fun d => d ≤ T), ((ArithmeticFunction.moebius d : ℤ) : ℝ)

lemma vonMangoldt_eq_mvt (T n : ℕ) (hT : 1 ≤ T) :
    (ArithmeticFunction.vonMangoldt n : ℝ)
      = mvtL1 T n + mvtL2 T n - mvtL3 T n - mvtL4 T n := by
  rw [Commons.NumberTheory.ArithmeticFunction.vonMangoldt_eq_lambda_decomp_pos n T hT]
  unfold mvtL1 mvtL2 mvtL3 mvtL4
  ring

lemma sum_vonMangoldt_eq_blocks (x T q : ℕ) (hT : 1 ≤ T) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (∑ n ∈ Finset.range (x+1), ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q))
      = (∑ n ∈ Finset.range (x+1), ((mvtL1 T n : ℝ) : ℂ) * χ (n : ZMod q))
        + (∑ n ∈ Finset.range (x+1), ((mvtL2 T n : ℝ) : ℂ) * χ (n : ZMod q))
        - (∑ n ∈ Finset.range (x+1), ((mvtL3 T n : ℝ) : ℂ) * χ (n : ZMod q))
        - (∑ n ∈ Finset.range (x+1), ((mvtL4 T n : ℝ) : ℂ) * χ (n : ZMod q)) := by
  have h : ∀ n, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)
      = ((mvtL1 T n : ℝ) : ℂ) * χ (n : ZMod q) + ((mvtL2 T n : ℝ) : ℂ) * χ (n : ZMod q)
        - ((mvtL3 T n : ℝ) : ℂ) * χ (n : ZMod q) - ((mvtL4 T n : ℝ) : ℂ) * χ (n : ZMod q) := by
    intro n
    rw [vonMangoldt_eq_mvt T n hT]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun n _ => h n)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]

lemma norm_sum_vonMangoldt_le_blocks (x T q : ℕ) (hT : 1 ≤ T) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ‖∑ n ∈ Finset.range (x+1), ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖
      ≤ ‖∑ n ∈ Finset.range (x+1), ((mvtL1 T n : ℝ) : ℂ) * χ (n : ZMod q)‖
        + ‖∑ n ∈ Finset.range (x+1), ((mvtL2 T n : ℝ) : ℂ) * χ (n : ZMod q)‖
        + ‖∑ n ∈ Finset.range (x+1), ((mvtL3 T n : ℝ) : ℂ) * χ (n : ZMod q)‖
        + ‖∑ n ∈ Finset.range (x+1), ((mvtL4 T n : ℝ) : ℂ) * χ (n : ZMod q)‖ := by
  rw [sum_vonMangoldt_eq_blocks x T q hT χ]
  set A := (∑ n ∈ Finset.range (x+1), ((mvtL1 T n : ℝ) : ℂ) * χ (n : ZMod q)) with hA
  set B := (∑ n ∈ Finset.range (x+1), ((mvtL2 T n : ℝ) : ℂ) * χ (n : ZMod q)) with hB
  set Cc := (∑ n ∈ Finset.range (x+1), ((mvtL3 T n : ℝ) : ℂ) * χ (n : ZMod q)) with hC
  set D := (∑ n ∈ Finset.range (x+1), ((mvtL4 T n : ℝ) : ℂ) * χ (n : ZMod q)) with hD
  calc ‖A + B - Cc - D‖ ≤ ‖A + B - Cc‖ + ‖D‖ := norm_sub_le _ _
    _ ≤ (‖A + B‖ + ‖Cc‖) + ‖D‖ := by refine add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ ((‖A‖ + ‖B‖) + ‖Cc‖) + ‖D‖ := by
        refine add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ = ‖A‖ + ‖B‖ + ‖Cc‖ + ‖D‖ := by ring

lemma div_totient_nonneg (q : ℕ) : (0:ℝ) ≤ (q:ℝ)/(q.totient:ℝ) :=
  div_nonneg (Nat.cast_nonneg q) (Nat.cast_nonneg _)

lemma norm_chi_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ‖χ (n : ZMod q)‖ ≤ 1 :=
  DirichletCharacter.norm_le_one χ _

lemma log_cast_add_one_nonneg (T : ℕ) : 0 ≤ Real.log ((T:ℝ) + 1) := by
  apply Real.log_nonneg
  have hT : (0:ℝ) ≤ (T:ℝ) := Nat.cast_nonneg T
  linarith

lemma mvtL1_nonneg (T n : ℕ) : 0 ≤ mvtL1 T n := by
  rw [mvtL1]; split_ifs <;> simp

lemma mvtL1_le (T n : ℕ) : mvtL1 T n ≤ Real.log ((T:ℝ) + 1) := by
  rw [mvtL1]
  split_ifs with h
  · have hlog : Real.log (n:ℝ) ≤ Real.log ((T:ℝ)+1) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; rw [Nat.cast_zero, Real.log_zero]; exact log_cast_add_one_nonneg T
      · refine Real.log_le_log (by positivity) ?_
        have : n ≤ T + 1 := by omega
        exact_mod_cast this
    exact le_trans (ArithmeticFunction.vonMangoldt_le_log) hlog
  · exact log_cast_add_one_nonneg T

lemma sum_mvtL1_eq (x T : ℕ) (hTx : T ≤ x) :
    (∑ n ∈ Finset.range (x+1), mvtL1 T n) = ∑ n ∈ Finset.range (T+1), mvtL1 T n := by
  have hsub : Finset.range (T+1) ⊆ Finset.range (x+1) := fun n hn => by
    rw [Finset.mem_range] at hn ⊢
    exact Nat.lt_of_lt_of_le hn (Nat.succ_le_succ hTx)
  have hzero : ∀ n ∈ Finset.range (x+1), n ∉ Finset.range (T+1) → mvtL1 T n = 0 := by
    intro n _ hnt
    rw [Finset.mem_range] at hnt
    rw [mvtL1]; exact if_neg (by omega)
  exact (Finset.sum_subset hsub hzero).symm

lemma sum_mvtL1_le (x T : ℕ) (hTx : T ≤ x) :
    (∑ n ∈ Finset.range (x+1), mvtL1 T n) ≤ ((T:ℝ)+1) * Real.log ((T:ℝ)+1) := by
  rw [sum_mvtL1_eq x T hTx]
  calc (∑ n ∈ Finset.range (T+1), mvtL1 T n)
      ≤ ∑ _n ∈ Finset.range (T+1), Real.log ((T:ℝ)+1) :=
        Finset.sum_le_sum (fun n _ => mvtL1_le T n)
    _ = ((T:ℝ)+1) * Real.log ((T:ℝ)+1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

lemma sum_range_eq_sum_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (x : ℕ) (h0 : f 0 = 0) :
    (∑ n ∈ Finset.range (x+1), f n) = ∑ n ∈ Finset.Icc 1 x, f n := by
  rw [show Finset.range (x+1) = insert 0 (Finset.Icc 1 x) by
        ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega]
  rw [Finset.sum_insert (by simp [Finset.mem_Icc]), h0, zero_add]

lemma le_sSup_image_Icc (g : ℕ → ℝ) (x : ℕ) (hx : 1 ≤ x) :
    g x ≤ sSup (g '' Set.Icc 1 x) := by
  apply le_csSup
  · exact Set.Finite.bddAbove (Set.Finite.image g (Set.finite_Icc 1 x))
  · exact ⟨x, Set.mem_Icc.mpr ⟨hx, le_rfl⟩, rfl⟩

lemma block1_bound (x Q T : ℕ) (hTx : T ≤ x) :
    (∑ q ∈ Finset.Icc 1 Q, ((q:ℝ)/(q.totient:ℝ)) *
        ∑ χ ∈ primF q,
          ‖∑ n ∈ Finset.range (x+1), ((mvtL1 T n : ℝ) : ℂ) * χ (n : ZMod q)‖)
      ≤ ((T:ℝ)+1) * Real.log ((T:ℝ)+1) * (Q:ℝ)^2 := by
  have hinner : ∀ q ∈ Finset.Icc 1 Q,
      ((q:ℝ)/(q.totient:ℝ)) *
        ∑ χ ∈ primF q,
          ‖∑ n ∈ Finset.range (x+1), ((mvtL1 T n : ℝ) : ℂ) * χ (n : ZMod q)‖
        ≤ ((q:ℝ)/(q.totient:ℝ)) * ((q.totient:ℝ) * (((T:ℝ)+1) * Real.log ((T:ℝ)+1))) := by
    intro q hq
    haveI : NeZero q := ⟨by rw [Finset.mem_Icc] at hq; omega⟩
    refine mul_le_mul_of_nonneg_left ?_ (div_totient_nonneg q)
    have hterm : ∀ χ ∈ primF q,
        ‖∑ n ∈ Finset.range (x+1), ((mvtL1 T n : ℝ) : ℂ) * χ (n : ZMod q)‖
          ≤ ((T:ℝ)+1) * Real.log ((T:ℝ)+1) := by
      intro χ _
      refine le_trans (norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun n _ => ?_)) (sum_mvtL1_le x T hTx)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mvtL1_nonneg T n)]
      calc mvtL1 T n * ‖χ (n : ZMod q)‖ ≤ mvtL1 T n * 1 :=
            mul_le_mul_of_nonneg_left (norm_chi_le_one χ n) (mvtL1_nonneg T n)
        _ = mvtL1 T n := by ring
    calc (∑ χ ∈ primF q,
            ‖∑ n ∈ Finset.range (x+1), ((mvtL1 T n : ℝ) : ℂ) * χ (n : ZMod q)‖)
        ≤ ∑ _χ ∈ primF q, ((T:ℝ)+1) * Real.log ((T:ℝ)+1) := Finset.sum_le_sum hterm
      _ = ((primF q).card : ℝ) * (((T:ℝ)+1) * Real.log ((T:ℝ)+1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((q.totient:ℝ)) * (((T:ℝ)+1) * Real.log ((T:ℝ)+1)) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by positivity) (log_cast_add_one_nonneg T))
          have hc := card_primitive_le_totient q
          exact_mod_cast hc
  refine le_trans (Finset.sum_le_sum hinner) ?_
  have hsumq : (∑ q ∈ Finset.Icc 1 Q, ((q:ℝ)/(q.totient:ℝ)) * ((q.totient:ℝ) *
        (((T:ℝ)+1)*Real.log ((T:ℝ)+1))))
      = (∑ q ∈ Finset.Icc 1 Q, (q:ℝ)) * (((T:ℝ)+1)*Real.log ((T:ℝ)+1)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    have hq0 : (q:ℝ) ≠ 0 := by
      have : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      positivity
    have hφ : (q.totient:ℝ) ≠ 0 := by
      have h := Nat.totient_pos.mpr (by rw [Finset.mem_Icc] at hq; omega : 0 < q)
      positivity
    field_simp
  rw [hsumq]
  have hQsum : (∑ q ∈ Finset.Icc 1 Q, (q:ℝ)) ≤ (Q:ℝ)^2 := by
    calc (∑ q ∈ Finset.Icc 1 Q, (q:ℝ)) ≤ ∑ _q ∈ Finset.Icc 1 Q, (Q:ℝ) :=
          Finset.sum_le_sum (fun q hq => by exact_mod_cast (Finset.mem_Icc.mp hq).2)
      _ = (Q:ℝ)^2 := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  calc (∑ q ∈ Finset.Icc 1 Q, (q:ℝ)) * (((T:ℝ)+1)*Real.log ((T:ℝ)+1))
      ≤ (Q:ℝ)^2 * (((T:ℝ)+1)*Real.log ((T:ℝ)+1)) :=
        mul_le_mul_of_nonneg_right hQsum
          (mul_nonneg (add_nonneg (show (0:ℝ) ≤ (T:ℝ) from Nat.cast_nonneg T) zero_le_one) (log_cast_add_one_nonneg T))
    _ = ((T:ℝ)+1)*Real.log ((T:ℝ)+1) * (Q:ℝ)^2 := by ring

lemma block2_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x Q T : ℕ, 2 ≤ x → 2 ≤ Q → 1 ≤ T → T ≤ x →
      (∑ q ∈ Finset.Icc 1 Q, ((q:ℝ)/(q.totient:ℝ)) *
        ∑ χ ∈ primF q,
          ‖∑ n ∈ Finset.range (x+1), ((mvtL2 T n : ℝ) : ℂ) * χ (n : ZMod q)‖)
      ≤ C * ((x : ℝ) + (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ))
          * (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ 3 := by
  obtain ⟨C, hC, hb⟩ := vaughan_type1_lambda2_estimate
  refine ⟨C, hC, ?_⟩
  intro x Q T hx hQ hT hTx
  refine le_trans (Finset.sum_le_sum (fun q hq => ?_)) (hb x Q T hx hQ hT hTx)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ hχ => ?_)) (div_totient_nonneg q)
  haveI : NeZero q := ⟨by rw [Finset.mem_Icc] at hq; omega⟩
  have hzero : ((mvtL2 T 0 : ℝ) : ℂ) * χ ((0:ℕ) : ZMod q) = 0 := by
    have : mvtL2 T 0 = 0 := by rw [mvtL2, Nat.divisors_zero]; simp
    rw [this]; simp
  rw [sum_range_eq_sum_Icc (fun n => ((mvtL2 T n : ℝ) : ℂ) * χ (n : ZMod q)) x hzero]
  exact le_sSup_image_Icc (fun y => ‖∑ n ∈ Finset.Icc 1 y,
    ((mvtL2 T n : ℝ) : ℂ) * χ (n : ZMod q)‖) x (by omega)

lemma mvtL3_cast (T n : ℕ) :
    ((mvtL3 T n : ℝ) : ℂ)
      = ∑ d ∈ n.divisors.filter (fun d => d ≤ T),
          ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ T),
            ((ArithmeticFunction.moebius d : ℤ) : ℂ) * ((ArithmeticFunction.vonMangoldt e : ℝ) : ℂ) := by
  rw [mvtL3]; push_cast; ring

lemma block3_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ x Q T : ℕ, 2 ≤ x → 2 ≤ Q → 1 ≤ T → T ≤ x →
      (∑ q ∈ Finset.Icc 1 Q, ((q:ℝ)/(q.totient:ℝ)) *
        ∑ χ ∈ primF q,
          ‖∑ n ∈ Finset.range (x+1), ((mvtL3 T n : ℝ) : ℂ) * χ (n : ZMod q)‖)
      ≤ C * ((x : ℝ) + (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ))
            * (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ 3
        + D * ((x : ℝ) + (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ)
                + (Q : ℝ) * (x : ℝ) * ((T : ℝ) ^ (1 / 2 : ℝ))⁻¹
                + (Q : ℝ) ^ 2 * (x : ℝ) ^ (1 / 2 : ℝ))
            * (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ 5 := by
  obtain ⟨C, hC, hb3⟩ := vaughan_type1_lambda3_estimate
  obtain ⟨D, hD, hb4⟩ := vaughan_type2_lambda3_estimate
  refine ⟨C, D, hC, hD, ?_⟩
  intro x Q T hx hQ hT hTx
  have hT2 : T ≤ T^2 := by nlinarith [hT]
  have hper : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      ‖∑ n ∈ Finset.range (x+1), ((mvtL3 T n : ℝ) : ℂ) * χ (n : ZMod q)‖
      ≤ sSup ((fun y : ℕ => ‖∑ t ∈ Finset.Icc 1 T,
            (∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
              ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
                ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ))
            * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))‖) '' Set.Icc 1 x)
        + sSup ((fun y : ℕ => ‖∑ t ∈ Finset.Icc (T+1) (T^2),
            (∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
              ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
                ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ))
            * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))‖) '' Set.Icc 1 x) := by
    intro q _ χ
    have hzero : ((mvtL3 T 0 : ℝ) : ℂ) * χ ((0:ℕ) : ZMod q) = 0 := by
      have : mvtL3 T 0 = 0 := by rw [mvtL3, Nat.divisors_zero]; simp
      rw [this]; simp
    rw [sum_range_eq_sum_Icc (fun n => ((mvtL3 T n : ℝ) : ℂ) * χ (n : ZMod q)) x hzero]
    have hcast : (∑ n ∈ Finset.Icc 1 x, ((mvtL3 T n : ℝ) : ℂ) * χ (n : ZMod q))
        = ∑ n ∈ Finset.Icc 1 x,
            (∑ d ∈ n.divisors.filter (fun d => d ≤ T),
              ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ T),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
                  ((ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)) * χ (n : ZMod q) := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [mvtL3_cast]
    rw [hcast, vaughan_lambda3_reindex T x q hT χ]
    have hunion : Finset.Icc 1 (T^2) = Finset.Icc 1 T ∪ Finset.Icc (T+1) (T^2) := by
      ext t
      simp only [Finset.mem_Icc, Finset.mem_union]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases h : t ≤ T
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr ⟨by omega, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, le_trans h2 hT2⟩
        · exact ⟨by omega, h2⟩
    have hdisj : Disjoint (Finset.Icc 1 T) (Finset.Icc (T+1) (T^2)) :=
      Finset.disjoint_left.mpr (fun t ht ht' => by
        rw [Finset.mem_Icc] at ht ht'; omega)
    rw [hunion, Finset.sum_union hdisj]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · exact le_sSup_image_Icc (fun y => ‖∑ t ∈ Finset.Icc 1 T,
        (∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
          ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
            ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ))
        * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))‖) x (by omega)
    · exact le_sSup_image_Icc (fun y => ‖∑ t ∈ Finset.Icc (T+1) (T^2),
        (∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
          ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
            ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ))
        * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))‖) x (by omega)
  set F1 : ℝ := (∑ q ∈ Finset.Icc 1 Q, ((q:ℝ)/(q.totient:ℝ)) *
          ∑ χ ∈ primF q,
            sSup ((fun y : ℕ => ‖∑ t ∈ Finset.Icc 1 T,
              (∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
                ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
                  ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ))
              * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))‖) '' Set.Icc 1 x)) with hF1
  set F2 : ℝ := (∑ q ∈ Finset.Icc 1 Q, ((q:ℝ)/(q.totient:ℝ)) *
          ∑ χ ∈ primF q,
            sSup ((fun y : ℕ => ‖∑ t ∈ Finset.Icc (T+1) (T^2),
              (∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
                ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
                  ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ))
              * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))‖) '' Set.Icc 1 x)) with hF2
  have main : (∑ q ∈ Finset.Icc 1 Q, ((q:ℝ)/(q.totient:ℝ)) *
        ∑ χ ∈ primF q,
          ‖∑ n ∈ Finset.range (x+1), ((mvtL3 T n : ℝ) : ℂ) * χ (n : ZMod q)‖) ≤ F1 + F2 := by
    rw [hF1, hF2, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun q hq => ?_)
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (div_totient_nonneg q)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun χ hχ => ?_)
    haveI : NeZero q := ⟨by rw [Finset.mem_Icc] at hq; omega⟩
    exact hper q χ
  rw [hF1, hF2] at main
  exact le_trans main (add_le_add (hb3 x Q T hx hQ hT hTx) (hb4 x Q T hx hQ hT hTx))

lemma block4_bound : ∃ C : ℝ, 0 < C ∧ ∀ x Q T : ℕ, 2 ≤ x → 2 ≤ Q → 1 ≤ T → T ≤ x →
      (∑ q ∈ Finset.Icc 1 Q, ((q:ℝ)/(q.totient:ℝ)) *
        ∑ χ ∈ primF q,
          ‖∑ n ∈ Finset.range (x+1), ((mvtL4 T n : ℝ) : ℂ) * χ (n : ZMod q)‖)
      ≤ C * ((x : ℝ) + (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ)
              + (Q : ℝ) * (x : ℝ) * ((T : ℝ) ^ (1 / 2 : ℝ))⁻¹
              + (Q : ℝ) ^ 2 * (x : ℝ) ^ (1 / 2 : ℝ))
          * (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ 5 := by
  obtain ⟨C, hC, hb⟩ := vaughan_type2_lambda4_estimate
  refine ⟨C, hC, ?_⟩
  intro x Q T hx hQ hT hTx
  refine le_trans (Finset.sum_le_sum (fun q hq => ?_)) (hb x Q T hx hQ hT hTx)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ hχ => ?_)) (div_totient_nonneg q)
  haveI : NeZero q := ⟨by rw [Finset.mem_Icc] at hq; omega⟩
  have hzero : ((mvtL4 T 0 : ℝ) : ℂ) * χ ((0:ℕ) : ZMod q) = 0 := by
    have : mvtL4 T 0 = 0 := by rw [mvtL4, Nat.divisors_zero]; simp
    rw [this]; simp
  rw [sum_range_eq_sum_Icc (fun n => ((mvtL4 T n : ℝ) : ℂ) * χ (n : ZMod q)) x hzero]
  have hcast : (∑ n ∈ Finset.Icc 1 x, ((mvtL4 T n : ℝ) : ℂ) * χ (n : ZMod q))
      = ∑ n ∈ Finset.Icc 1 x,
          (∑ m ∈ n.divisors.filter (fun m => T < m ∧ T < n / m),
            ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
              (∑ d ∈ (n / m).divisors.filter (fun d => d ≤ T),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ))) * χ (n : ZMod q) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [mvtL4]; push_cast; ring
  rw [hcast]
  exact le_sSup_image_Icc (fun y => ‖∑ n ∈ Finset.Icc 1 y,
    (∑ m ∈ n.divisors.filter (fun m => T < m ∧ T < n / m),
      ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
        (∑ d ∈ (n / m).divisors.filter (fun d => d ≤ T),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ))) * χ (n : ZMod q)‖) x (by omega)

lemma vonMangoldt_range_le (x : ℕ) (hx : 1 ≤ x) :
    (∑ n ∈ Finset.range (x+1), (ArithmeticFunction.vonMangoldt n : ℝ)) ≤ (x:ℝ)*Real.log (x:ℝ) := by
  rw [sum_range_eq_sum_Icc (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) x
        (ArithmeticFunction.vonMangoldt.map_zero)]
  calc (∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.vonMangoldt n : ℝ))
      ≤ ∑ _n ∈ Finset.Icc 1 x, Real.log (x:ℝ) :=
        Finset.sum_le_sum (fun n hn => ?_)
    _ = (x:ℝ)*Real.log (x:ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  · have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnx : n ≤ x := (Finset.mem_Icc.mp hn).2
    refine le_trans ArithmeticFunction.vonMangoldt_le_log ?_
    refine Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) ?_
    exact_mod_cast hnx

lemma blockSum_le_crude (x Q : ℕ) (hx : 1 ≤ x) :
    blockSum x Q ≤ ((x:ℝ)*Real.log (x:ℝ)) * (Q:ℝ)^2 := by
  unfold blockSum
  have hper : ∀ q ∈ Finset.Icc 1 Q,
      ((q:ℝ)/(q.totient:ℝ)) * ∑ χ ∈ primF q,
          ‖∑ n ∈ Finset.range (x+1), ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖
      ≤ (q:ℝ) * ((x:ℝ)*Real.log (x:ℝ)) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    haveI : NeZero q := ⟨by omega⟩
    have hterm : ∀ χ ∈ primF q,
        ‖∑ n ∈ Finset.range (x+1), ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖
          ≤ (x:ℝ)*Real.log (x:ℝ) := by
      intro χ _
      refine le_trans (norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun n _ => ?_)) (vonMangoldt_range_le x hx)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]
      calc ArithmeticFunction.vonMangoldt n * ‖χ (n : ZMod q)‖
          ≤ ArithmeticFunction.vonMangoldt n * 1 :=
            mul_le_mul_of_nonneg_left (norm_chi_le_one χ n)
              (ArithmeticFunction.vonMangoldt_nonneg (n := n))
        _ = ArithmeticFunction.vonMangoldt n := by ring
    calc ((q:ℝ)/(q.totient:ℝ)) * ∑ χ ∈ primF q,
            ‖∑ n ∈ Finset.range (x+1), ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖
        ≤ ((q:ℝ)/(q.totient:ℝ)) * ∑ _χ ∈ primF q, (x:ℝ)*Real.log (x:ℝ) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (div_totient_nonneg q)
      _ = ((q:ℝ)/(q.totient:ℝ)) * (((primF q).card : ℝ) * ((x:ℝ)*Real.log (x:ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((q:ℝ)/(q.totient:ℝ)) * ((q.totient:ℝ) * ((x:ℝ)*Real.log (x:ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (div_totient_nonneg q)
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Nat.cast_nonneg x) (Real.log_nonneg (by exact_mod_cast hx)))
          have hc := card_primitive_le_totient q
          exact_mod_cast hc
      _ = (q:ℝ) * ((x:ℝ)*Real.log (x:ℝ)) := by
          have hφ : (q.totient:ℝ) ≠ 0 := by
            have h := Nat.totient_pos.mpr (by omega : 0 < q)
            positivity
          field_simp
  calc (∑ q ∈ Finset.Icc 1 Q, ((q:ℝ)/(q.totient:ℝ)) * ∑ χ ∈ primF q,
          ‖∑ n ∈ Finset.range (x+1), ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖)
      ≤ ∑ q ∈ Finset.Icc 1 Q, (q:ℝ) * ((x:ℝ)*Real.log (x:ℝ)) := Finset.sum_le_sum hper
    _ = (∑ q ∈ Finset.Icc 1 Q, (q:ℝ)) * ((x:ℝ)*Real.log (x:ℝ)) := by rw [Finset.sum_mul]
    _ ≤ (Q:ℝ)^2 * ((x:ℝ)*Real.log (x:ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Nat.cast_nonneg x) (Real.log_nonneg (by exact_mod_cast hx)))
        calc (∑ q ∈ Finset.Icc 1 Q, (q:ℝ)) ≤ ∑ _q ∈ Finset.Icc 1 Q, (Q:ℝ) :=
              Finset.sum_le_sum (fun q hq => by exact_mod_cast (Finset.mem_Icc.mp hq).2)
          _ = (Q:ℝ)^2 := by
              rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
    _ = ((x:ℝ)*Real.log (x:ℝ)) * (Q:ℝ)^2 := by ring

lemma rpow_half_third {x : ℝ} (hx : 0 < x) :
    x^(1/2:ℝ) * x^(1/3:ℝ) = x^(5/6:ℝ) := by
  rw [← Real.rpow_add hx]; norm_num

lemma rpow_half_twothird {x : ℝ} (hx : 0 < x) :
    x^(1/2:ℝ) * x^(2/3:ℝ) = x^(7/6:ℝ) := by
  rw [← Real.rpow_add hx]; norm_num

lemma rpow_five_half {Q : ℝ} (hQ : 0 < Q) : Q^(5/2:ℝ) = Q * Q^(3/2:ℝ) := by
  rw [show (5/2:ℝ) = 1 + 3/2 by norm_num, Real.rpow_add hQ, Real.rpow_one]

lemma rpow_three_half {Q : ℝ} (hQ : 0 < Q) : Q^(3/2:ℝ) = Q * Q^(1/2:ℝ) := by
  rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hQ, Real.rpow_one]

lemma pow_sixth_eq {x : ℝ} (hx : 0 < x) : (x^(1/6:ℝ))^2 = x^(1/3:ℝ) := by
  rw [sq, ← Real.rpow_add hx]; norm_num

lemma pow_third_eq {x : ℝ} (hx : 0 < x) : (x^(1/3:ℝ))^2 = x^(2/3:ℝ) := by
  rw [sq, ← Real.rpow_add hx]; norm_num

lemma div_sixth_sq {x : ℝ} (hx : 0 < x) : (x^(1/6:ℝ)/2)^2 = x^(1/3:ℝ)/4 := by
  rw [div_pow, pow_sixth_eq hx]; norm_num

lemma sqrt_lower_of_third {x T : ℝ} (hx : 0 < x) (hT : x^(1/3:ℝ)/4 ≤ T) :
    x^(1/6:ℝ)/2 ≤ Real.sqrt T := by
  have hxp : (0:ℝ) < x^(1/3:ℝ)/4 := by positivity
  have hTnn : (0:ℝ) ≤ T := le_trans (le_of_lt hxp) hT
  rw [Real.le_sqrt (by positivity) hTnn, div_sixth_sq hx]
  exact hT

lemma inv_sqrt_le_of_third {x T : ℝ} (hx : 0 < x) (hT : x^(1/3:ℝ)/4 ≤ T) :
    (Real.sqrt T)⁻¹ ≤ 2 * (x^(1/6:ℝ))⁻¹ := by
  have hxp : (0:ℝ) < x^(1/3:ℝ)/4 := by positivity
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le hxp hT
  have hy : (0:ℝ) < x^(1/6:ℝ)/2 := by positivity
  have hTspos : (0:ℝ) < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  have hle := sqrt_lower_of_third hx hT
  have h1 : (Real.sqrt T)⁻¹ ≤ (x^(1/6:ℝ)/2)⁻¹ := (inv_le_inv₀ hTspos hy).mpr hle
  rwa [inv_div] at h1

lemma sqrt_lower_of_twothird {x Q T : ℝ} (hx : 0 < x) (hQ : 0 < Q)
    (hT : x^(2/3:ℝ)/(2*Q) ≤ T) :
    x^(1/3:ℝ)/(2*Real.sqrt Q) ≤ Real.sqrt T := by
  have hQpos : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hy : (0:ℝ) < x^(1/3:ℝ)/(2*Real.sqrt Q) := by positivity
  have hTnn : (0:ℝ) ≤ T := by
    have : (0:ℝ) < x^(2/3:ℝ)/(2*Q) := by positivity
    linarith
  rw [Real.le_sqrt (le_of_lt hy) hTnn]
  have hsq : (x^(1/3:ℝ)/(2*Real.sqrt Q))^2 = x^(2/3:ℝ)/(4*Q) := by
    rw [div_pow, mul_pow, pow_third_eq hx, Real.sq_sqrt (le_of_lt hQ)]; ring_nf
  rw [hsq, div_le_iff₀ (by positivity : (0:ℝ) < 4*Q)]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*Q)] at hT
  nlinarith [hT]

lemma inv_sqrt_le_of_twothird {x Q T : ℝ} (hx : 0 < x) (hQ : 0 < Q)
    (hT : x^(2/3:ℝ)/(2*Q) ≤ T) :
    (Real.sqrt T)⁻¹ ≤ 2 * Real.sqrt Q * (x^(1/3:ℝ))⁻¹ := by
  have hy : (0:ℝ) < x^(1/3:ℝ)/(2*Real.sqrt Q) := by positivity
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le (by positivity : (0:ℝ) < x^(2/3:ℝ)/(2*Q)) hT
  have hTspos : (0:ℝ) < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  have hle := sqrt_lower_of_twothird hx hQ hT
  have h1 : (Real.sqrt T)⁻¹ ≤ (x^(1/3:ℝ)/(2*Real.sqrt Q))⁻¹ := (inv_le_inv₀ hTspos hy).mpr hle
  rw [inv_div, div_eq_mul_inv] at h1
  exact h1

lemma rpow_mul_inv_sixth {x : ℝ} (hx : 0 < x) : x * (x^(1/6:ℝ))⁻¹ = x^(5/6:ℝ) := by
  rw [show (5/6:ℝ) = 1 - 1/6 by norm_num, Real.rpow_sub hx, Real.rpow_one]
  exact div_eq_mul_inv x (x^(1/6:ℝ))

lemma rpow_mul_inv_third {x : ℝ} (hx : 0 < x) : x * (x^(1/3:ℝ))⁻¹ = x^(2/3:ℝ) := by
  rw [show (2/3:ℝ) = 1 - 1/3 by norm_num, Real.rpow_sub hx, Real.rpow_one]
  exact div_eq_mul_inv x (x^(1/3:ℝ))

lemma rpow_third_add_third {x : ℝ} (hx : 0 < x) :
    (x:ℝ)^(1/3:ℝ) * (x:ℝ)^(1/3:ℝ) = (x:ℝ)^(2/3:ℝ) := by
  rw [← Real.rpow_add hx]; norm_num

lemma rpow_twothird_eq {x : ℝ} (hx : 0 < x) :
    (x:ℝ)^(7/6:ℝ) = (x:ℝ)^(2/3:ℝ) * (x:ℝ)^(1/2:ℝ) := by
  rw [← Real.rpow_add hx]; norm_num

lemma rpow_id5 (Q x : ℝ) (hx : 0 < x) : Q*x^(1/2:ℝ)*x^(1/3:ℝ) = x^(5/6:ℝ)*Q := by
  rw [mul_assoc, rpow_half_third hx]; ring

lemma rpow_id7 (Q x : ℝ) (hx : 0 < x) (hQ : 0 < Q) :
    Q*x^(1/2:ℝ)*(x^(2/3:ℝ)/Q) = x^(7/6:ℝ) := by
  rw [show Q*x^(1/2:ℝ)*(x^(2/3:ℝ)/Q) = x^(1/2:ℝ)*x^(2/3:ℝ) by field_simp,
    rpow_half_twothird hx]

lemma rpow_id5b (Q x : ℝ) (hx : 0 < x) : Q*x*(2*(x^(1/6:ℝ))⁻¹) = 2*(x^(5/6:ℝ)*Q) := by
  rw [show Q*x*(2*(x^(1/6:ℝ))⁻¹) = 2*(Q*(x*(x^(1/6:ℝ))⁻¹)) by ring, rpow_mul_inv_sixth hx]
  ring

lemma rpow_id23 (Q x : ℝ) (hx : 0 < x) (hQ : 0 < Q) :
    Q*x*(2*Real.sqrt Q*(x^(1/3:ℝ))⁻¹) = 2*(x^(2/3:ℝ)*Q^(3/2:ℝ)) := by
  rw [show Q*x*(2*Real.sqrt Q*(x^(1/3:ℝ))⁻¹)
        = 2*((x*(x^(1/3:ℝ))⁻¹)*(Q*Real.sqrt Q)) by ring,
    rpow_mul_inv_third hx, Real.sqrt_eq_rpow, ← rpow_three_half hQ]

theorem vaughan_mean_value_sqrt :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ x Q : ℕ, 4 ≤ x → 1 ≤ Q → Q ^ 2 ≤ x →
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive) (Classical.decPred _) Finset.univ),
          ‖∑ n ∈ Finset.range (x + 1),
            (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q))‖)
      ≤ C * ((x : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)
              + (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ)
              + (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ))
          * (Real.log ((x : ℝ) + 2)) ^ K := by
  obtain ⟨C2, hC2, hb2⟩ := block2_bound
  obtain ⟨C3, C4, hC3, hC4, hb34⟩ := block3_bound
  obtain ⟨C5, hC5, hb5⟩ := block4_bound
  refine ⟨1000 * (C2 + C3 + C4 + C5 + 1), 20, by positivity, by norm_num, ?_⟩
  intro x Q hx4 hQ1 hQx
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hxpos : (0:ℝ) < (x:ℝ) := by linarith
  have hQ0 : (0:ℝ) < (Q:ℝ) := by exact_mod_cast (by omega : 0 < Q)
  have hQnn : (0:ℝ) ≤ (Q:ℝ) := le_of_lt hQ0
  have hQxn : (Q:ℝ)^2 ≤ (x:ℝ) := by exact_mod_cast hQx
  set W : ℝ := (x:ℝ) + (Q:ℝ)^2*Real.sqrt (x:ℝ) + (x:ℝ)^(5/6:ℝ)*(Q:ℝ)
      + (x:ℝ)^(2/3:ℝ)*(Q:ℝ)^(3/2:ℝ) with hW
  set L : ℝ := Real.log ((x:ℝ)+2) with hL
  have hL20cast : L ^ (20:ℝ) = L^20 := Real.rpow_natCast L 20
  rw [hL20cast]
  change blockSum x Q ≤ 1000 * (C2 + C3 + C4 + C5 + 1) * W * L^20
  have hWx : (x:ℝ) ≤ W := by
    rw [hW]; nlinarith [Real.sq_sqrt (le_of_lt hxpos), Real.sqrt_nonneg (x:ℝ),
      Real.rpow_nonneg (le_of_lt hxpos) (5/6:ℝ), Real.rpow_nonneg (le_of_lt hxpos) (2/3:ℝ),
      Real.rpow_nonneg hQnn (3/2:ℝ)]
  have hWQ2 : (Q:ℝ)^2*Real.sqrt (x:ℝ) ≤ W := by
    rw [hW]; nlinarith [Real.rpow_nonneg (le_of_lt hxpos) (5/6:ℝ),
      Real.rpow_nonneg (le_of_lt hxpos) (2/3:ℝ), Real.rpow_nonneg hQnn (3/2:ℝ),
      Real.sqrt_nonneg (x:ℝ)]
  have hWc : (x:ℝ)^(5/6:ℝ)*(Q:ℝ) ≤ W := by
    rw [hW]; nlinarith [Real.sq_sqrt (le_of_lt hxpos), Real.sqrt_nonneg (x:ℝ),
      Real.rpow_nonneg (le_of_lt hxpos) (2/3:ℝ), Real.rpow_nonneg hQnn (3/2:ℝ)]
  have hWd : (x:ℝ)^(2/3:ℝ)*(Q:ℝ)^(3/2:ℝ) ≤ W := by
    rw [hW]; nlinarith [Real.sq_sqrt (le_of_lt hxpos), Real.sqrt_nonneg (x:ℝ),
      Real.rpow_nonneg (le_of_lt hxpos) (5/6:ℝ)]
  have hWnn : (0:ℝ) ≤ W := le_trans (le_of_lt hxpos) hWx
  have hL1 : (1:ℝ) ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    linarith [Real.exp_one_lt_three, hx4]
  have hLnn : (0:ℝ) ≤ L := le_trans (by norm_num) hL1
  have hL20nn : (0:ℝ) ≤ L^20 := pow_nonneg hLnn 20
  rcases eq_or_lt_of_le hQ1 with hQ1' | hQ2
  · subst hQ1'
    have hcrude : blockSum x 1 ≤ (x:ℝ)*Real.log (x:ℝ) := by
      have h := blockSum_le_crude x 1 (by omega)
      simpa using h
    have hlogx : Real.log (x:ℝ) ≤ L := by
      rw [hL]; exact Real.log_le_log hxpos (by linarith)
    refine le_trans hcrude ?_
    calc (x:ℝ)*Real.log (x:ℝ)
        ≤ (x:ℝ)*L := mul_le_mul_of_nonneg_left hlogx (le_of_lt hxpos)
      _ ≤ (x:ℝ)*L^20 := mul_le_mul_of_nonneg_left
          (by simpa using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ 20)) (le_of_lt hxpos)
      _ ≤ W*L^20 := mul_le_mul_of_nonneg_right hWx hL20nn
      _ ≤ 1000 * (C2 + C3 + C4 + C5 + 1) * W * L^20 := by
          have hC1 : (1:ℝ) ≤ 1000 * (C2 + C3 + C4 + C5 + 1) := by linarith
          have hnn : (0:ℝ) ≤ W*L^20 := mul_nonneg hWnn hL20nn
          have h := mul_le_mul_of_nonneg_right hC1 hnn
          rw [one_mul] at h
          have hassoc : (1000 * (C2 + C3 + C4 + C5 + 1))*(W*L^20)
              = 1000 * (C2 + C3 + C4 + C5 + 1) * W * L^20 := by ring
          linarith [h, hassoc]
  · rcases lt_or_ge x 64 with hxlt | hx64
    · -- 4 ≤ x < 64
      have hcrude : blockSum x Q ≤ (x:ℝ)*Real.log (x:ℝ) * (Q:ℝ)^2 := blockSum_le_crude x Q (by omega)
      have hxle : (x:ℝ) ≤ 64 := by exact_mod_cast (by omega : x ≤ 64)
      have hlogx : Real.log (x:ℝ) ≤ L := by
        rw [hL]; exact Real.log_le_log hxpos (by linarith)
      have hlogxnn : (0:ℝ) ≤ Real.log (x:ℝ) := Real.log_nonneg hx1
      have h2 : (x:ℝ)*Real.log (x:ℝ) ≤ 64*L := by
        calc (x:ℝ)*Real.log (x:ℝ) ≤ 64*Real.log (x:ℝ) :=
              mul_le_mul_of_nonneg_right hxle hlogxnn
          _ ≤ 64*L := mul_le_mul_of_nonneg_left hlogx (by norm_num)
      refine le_trans hcrude ?_
      calc (x:ℝ)*Real.log (x:ℝ)*(Q:ℝ)^2
          ≤ (x:ℝ)*Real.log (x:ℝ)*(x:ℝ) :=
            mul_le_mul_of_nonneg_left hQxn (mul_nonneg (le_of_lt hxpos) hlogxnn)
        _ = (x:ℝ)*((x:ℝ)*Real.log (x:ℝ)) := by ring
        _ ≤ (x:ℝ)*(64*L) := mul_le_mul_of_nonneg_left h2 (le_of_lt hxpos)
        _ = 64*((x:ℝ)*L) := by ring
        _ ≤ 64*((x:ℝ)*L^20) := mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (by simpa using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ 20))
                (le_of_lt hxpos)) (by norm_num)
        _ ≤ 64*(W*L^20) := mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hWx hL20nn) (by norm_num)
        _ ≤ 1000 * (C2 + C3 + C4 + C5 + 1) * W * L^20 := by
            have hC64 : (64:ℝ) ≤ 1000 * (C2 + C3 + C4 + C5 + 1) := by linarith
            have hnn : (0:ℝ) ≤ W*L^20 := mul_nonneg hWnn hL20nn
            have h := mul_le_mul_of_nonneg_right hC64 hnn
            have hassoc : (1000 * (C2 + C3 + C4 + C5 + 1))*(W*L^20)
                = 1000 * (C2 + C3 + C4 + C5 + 1) * W * L^20 := by ring
            linarith [h, hassoc]
    · obtain ⟨T, hT1, hT13, hTQ, hTmin, hTx⟩ := vaughan_mean_value_param x Q hx64 hQ2 hQx
      have hTx' : T ≤ x := by exact_mod_cast hTx
      have hT1r : (1:ℝ) ≤ (T:ℝ) := by exact_mod_cast hT1
      have hTnn : (0:ℝ) ≤ (T:ℝ) := le_trans (by norm_num) hT1r
      have hTpos : (0:ℝ) < (T:ℝ) := lt_of_lt_of_le (by norm_num) hT1r
      have hx4r : (4:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx4
      have hQ2r : (2:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ2
      have hx1' : (1:ℝ) < (x:ℝ) := by linarith
      set L1 : ℝ := Real.log ((x:ℝ)*(Q:ℝ)+2) with hL1def
      have hblocks : blockSum x Q ≤
          (∑ q ∈ Finset.Icc 1 Q, ((q:ℝ)/(q.totient:ℝ)) * ∑ χ ∈ primF q,
              ‖∑ n ∈ Finset.range (x+1), ((mvtL1 T n : ℝ) : ℂ) * χ (n : ZMod q)‖)
          + (∑ q ∈ Finset.Icc 1 Q, ((q:ℝ)/(q.totient:ℝ)) * ∑ χ ∈ primF q,
              ‖∑ n ∈ Finset.range (x+1), ((mvtL2 T n : ℝ) : ℂ) * χ (n : ZMod q)‖)
          + (∑ q ∈ Finset.Icc 1 Q, ((q:ℝ)/(q.totient:ℝ)) * ∑ χ ∈ primF q,
              ‖∑ n ∈ Finset.range (x+1), ((mvtL3 T n : ℝ) : ℂ) * χ (n : ZMod q)‖)
          + (∑ q ∈ Finset.Icc 1 Q, ((q:ℝ)/(q.totient:ℝ)) * ∑ χ ∈ primF q,
              ‖∑ n ∈ Finset.range (x+1), ((mvtL4 T n : ℝ) : ℂ) * χ (n : ZMod q)‖) := by
        unfold blockSum
        have step1 : (∑ q ∈ Finset.Icc 1 Q, ((q:ℝ)/(q.totient:ℝ)) * ∑ χ ∈ primF q,
              ‖∑ n ∈ Finset.range (x+1), ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖)
            ≤ ∑ q ∈ Finset.Icc 1 Q, ((q:ℝ)/(q.totient:ℝ)) * ∑ χ ∈ primF q,
                (‖∑ n ∈ Finset.range (x+1), ((mvtL1 T n : ℝ) : ℂ) * χ (n : ZMod q)‖
                 + ‖∑ n ∈ Finset.range (x+1), ((mvtL2 T n : ℝ) : ℂ) * χ (n : ZMod q)‖
                 + ‖∑ n ∈ Finset.range (x+1), ((mvtL3 T n : ℝ) : ℂ) * χ (n : ZMod q)‖
                 + ‖∑ n ∈ Finset.range (x+1), ((mvtL4 T n : ℝ) : ℂ) * χ (n : ZMod q)‖) := by
          refine Finset.sum_le_sum (fun q hq => ?_)
          refine mul_le_mul_of_nonneg_left ?_ (div_totient_nonneg q)
          refine Finset.sum_le_sum (fun χ hχ => ?_)
          haveI : NeZero q := ⟨by rw [Finset.mem_Icc] at hq; omega⟩
          exact norm_sum_vonMangoldt_le_blocks x T q hT1 χ
        have step2 : (∑ q ∈ Finset.Icc 1 Q, ((q:ℝ)/(q.totient:ℝ)) * ∑ χ ∈ primF q,
                (‖∑ n ∈ Finset.range (x+1), ((mvtL1 T n : ℝ) : ℂ) * χ (n : ZMod q)‖
                 + ‖∑ n ∈ Finset.range (x+1), ((mvtL2 T n : ℝ) : ℂ) * χ (n : ZMod q)‖
                 + ‖∑ n ∈ Finset.range (x+1), ((mvtL3 T n : ℝ) : ℂ) * χ (n : ZMod q)‖
                 + ‖∑ n ∈ Finset.range (x+1), ((mvtL4 T n : ℝ) : ℂ) * χ (n : ZMod q)‖))
            = (∑ q ∈ Finset.Icc 1 Q, ((q:ℝ)/(q.totient:ℝ)) * ∑ χ ∈ primF q,
                ‖∑ n ∈ Finset.range (x+1), ((mvtL1 T n : ℝ) : ℂ) * χ (n : ZMod q)‖)
              + (∑ q ∈ Finset.Icc 1 Q, ((q:ℝ)/(q.totient:ℝ)) * ∑ χ ∈ primF q,
                ‖∑ n ∈ Finset.range (x+1), ((mvtL2 T n : ℝ) : ℂ) * χ (n : ZMod q)‖)
              + (∑ q ∈ Finset.Icc 1 Q, ((q:ℝ)/(q.totient:ℝ)) * ∑ χ ∈ primF q,
                ‖∑ n ∈ Finset.range (x+1), ((mvtL3 T n : ℝ) : ℂ) * χ (n : ZMod q)‖)
              + (∑ q ∈ Finset.Icc 1 Q, ((q:ℝ)/(q.totient:ℝ)) * ∑ χ ∈ primF q,
                ‖∑ n ∈ Finset.range (x+1), ((mvtL4 T n : ℝ) : ℂ) * χ (n : ZMod q)‖) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun q _ => ?_)
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
            mul_add, mul_add, mul_add]
        rw [step2] at step1
        exact step1
      have hB1 := block1_bound x Q T hTx'
      have hB2 := hb2 x Q T (by omega) hQ2 hT1 hTx'
      have hB34 := hb34 x Q T (by omega) hQ2 hT1 hTx'
      have hB4 := hb5 x Q T (by omega) hQ2 hT1 hTx'
      rw [← hL1def] at hB2 hB34 hB4
      have hsum := le_trans hblocks (add_le_add (add_le_add (add_le_add hB1 hB2) hB34) hB4)
      have hL1_1 : (1:ℝ) ≤ L1 := by
        rw [hL1def, Real.le_log_iff_exp_le (by positivity)]
        have : (8:ℝ) ≤ (x:ℝ)*(Q:ℝ)+2 := by nlinarith [hx4r, hQ2r]
        linarith [Real.exp_one_lt_three, this]
      have hL1nn : (0:ℝ) ≤ L1 := le_trans (by norm_num) hL1_1
      have hL1_35 : L1^3 ≤ L1^5 := by
        calc L1^3 = L1^3 * 1 := by ring
          _ ≤ L1^3 * L1^2 := mul_le_mul_of_nonneg_left
              (by simpa using one_le_pow₀ hL1_1 (n := 2)) (pow_nonneg hL1nn 3)
          _ = L1^5 := by ring
      have hL1_le2L : L1 ≤ 2*L := by
        rw [hL1def, hL]
        have hQle : (Q:ℝ) ≤ Real.sqrt (x:ℝ) :=
          (Real.le_sqrt hQnn (le_of_lt hxpos)).mpr hQxn
        have hbound : (x:ℝ)*(Q:ℝ)+2 ≤ ((x:ℝ)+2)^2 := by
          have hxx : (x:ℝ)*Real.sqrt (x:ℝ) ≤ (x:ℝ)^2 := by
            nlinarith [Real.sq_sqrt (le_of_lt hxpos), Real.sqrt_nonneg (x:ℝ), hx1]
          nlinarith [hQle, Real.sq_sqrt (le_of_lt hxpos), Real.sqrt_nonneg (x:ℝ), hxx, hxpos]
        calc Real.log ((x:ℝ)*(Q:ℝ)+2) ≤ Real.log (((x:ℝ)+2)^2) :=
              Real.log_le_log (by positivity) hbound
          _ = 2*Real.log ((x:ℝ)+2) := by rw [Real.log_pow]; push_cast; ring
      have hL15 : L1^5 ≤ 32*L^5 := by
        calc L1^5 ≤ (2*L)^5 := pow_le_pow_left₀ hL1nn hL1_le2L 5
          _ = 32*L^5 := by ring
      have hb1le : ((T:ℝ)+1)*Real.log ((T:ℝ)+1)*(Q:ℝ)^2 ≤ 2*L*W := by
        have hlogT : Real.log ((T:ℝ)+1) ≤ L := by
          rw [hL]
          refine Real.log_le_log (by positivity) ?_
          linarith [hTx]
        have hTQ2 : (T:ℝ)*(Q:ℝ)^2 ≤ W := by
          have h2 : (x:ℝ)^(1/3:ℝ) ≤ (x:ℝ)^(1/2:ℝ) :=
            (Real.rpow_le_rpow_left_iff hx1').mpr (by norm_num)
          have e : (x:ℝ)^(1/2:ℝ)*(Q:ℝ)^2 = (Q:ℝ)^2*Real.sqrt (x:ℝ) := by
            rw [Real.sqrt_eq_rpow]; ring
          calc (T:ℝ)*(Q:ℝ)^2 ≤ (x:ℝ)^(1/3:ℝ)*(Q:ℝ)^2 :=
                mul_le_mul_of_nonneg_right hT13 (by positivity)
            _ ≤ (x:ℝ)^(1/2:ℝ)*(Q:ℝ)^2 := mul_le_mul_of_nonneg_right h2 (by positivity)
            _ = (Q:ℝ)^2*Real.sqrt (x:ℝ) := e
            _ ≤ W := hWQ2
        have hlogTnn : (0:ℝ) ≤ Real.log ((T:ℝ)+1) := Real.log_nonneg (by linarith [hTnn])
        have hstep : ((T:ℝ)+1)*Real.log ((T:ℝ)+1) ≤ (2*(T:ℝ))*L :=
          mul_le_mul (by linarith : (T:ℝ)+1 ≤ 2*(T:ℝ)) hlogT hlogTnn (by positivity)
        calc ((T:ℝ)+1)*Real.log ((T:ℝ)+1)*(Q:ℝ)^2
            ≤ ((2*(T:ℝ))*L)*(Q:ℝ)^2 := mul_le_mul_of_nonneg_right hstep (by positivity)
          _ = 2*L*((T:ℝ)*(Q:ℝ)^2) := by ring
          _ ≤ 2*L*W := mul_le_mul_of_nonneg_left hTQ2 (by positivity)
      have hWQ2' : (Q:ℝ)^2*(x:ℝ)^(1/2:ℝ) ≤ W := by rw [← Real.sqrt_eq_rpow]; exact hWQ2
      have hA : (x:ℝ)+(T:ℝ)*(Q:ℝ)^(5/2:ℝ) ≤ 2*W := by
        have h1 : (T:ℝ)*(Q:ℝ)^(5/2:ℝ) ≤ W := by
          have e : (T:ℝ)*(Q:ℝ)^(5/2:ℝ) = (T:ℝ)*(Q:ℝ)*(Q:ℝ)^(3/2:ℝ) := by
            rw [rpow_five_half hQ0]; ring
          rw [e]
          calc (T:ℝ)*(Q:ℝ)*(Q:ℝ)^(3/2:ℝ) ≤ (x:ℝ)^(2/3:ℝ)*(Q:ℝ)^(3/2:ℝ) :=
                mul_le_mul_of_nonneg_right hTQ (Real.rpow_nonneg hQnn _)
            _ ≤ W := hWd
        linarith [hWx, h1]
      have hB : (x:ℝ)+(Q:ℝ)*(x:ℝ)^(1/2:ℝ)*(T:ℝ)+(Q:ℝ)*(x:ℝ)*((T:ℝ)^(1/2:ℝ))⁻¹
            +(Q:ℝ)^2*(x:ℝ)^(1/2:ℝ) ≤ 5*W := by
        have hqpos12 : (0:ℝ) ≤ (x:ℝ)^(1/2:ℝ) := Real.rpow_nonneg (le_of_lt hxpos) _
        have hterm1 : (Q:ℝ)*(x:ℝ)^(1/2:ℝ)*(T:ℝ) ≤ W := by
          by_cases hQA : (Q:ℝ) ≤ (x:ℝ)^(1/3:ℝ)
          · calc (Q:ℝ)*(x:ℝ)^(1/2:ℝ)*(T:ℝ)
                ≤ (Q:ℝ)*(x:ℝ)^(1/2:ℝ)*((x:ℝ)^(1/3:ℝ)) :=
                  mul_le_mul_of_nonneg_left hT13 (mul_nonneg hQnn hqpos12)
              _ = (x:ℝ)^(5/6:ℝ)*(Q:ℝ) := rpow_id5 (Q:ℝ) (x:ℝ) hxpos
              _ ≤ W := hWc
          · have hQB : (x:ℝ)^(1/3:ℝ) < (Q:ℝ) := lt_of_not_ge hQA
            have hTle : (T:ℝ) ≤ (x:ℝ)^(2/3:ℝ)/(Q:ℝ) := (le_div_iff₀ hQ0).mpr hTQ
            calc (Q:ℝ)*(x:ℝ)^(1/2:ℝ)*(T:ℝ)
                ≤ (Q:ℝ)*(x:ℝ)^(1/2:ℝ)*((x:ℝ)^(2/3:ℝ)/(Q:ℝ)) :=
                  mul_le_mul_of_nonneg_left hTle (mul_nonneg hQnn hqpos12)
              _ = (x:ℝ)^(7/6:ℝ) := rpow_id7 (Q:ℝ) (x:ℝ) hxpos hQ0
              _ ≤ (Q:ℝ)^2*(x:ℝ)^(1/2:ℝ) := by
                  have hQ23 : (x:ℝ)^(2/3:ℝ) ≤ (Q:ℝ)^2 := by
                    calc (x:ℝ)^(2/3:ℝ) = (x:ℝ)^(1/3:ℝ)*(x:ℝ)^(1/3:ℝ) := (rpow_third_add_third hxpos).symm
                      _ ≤ (Q:ℝ)*(Q:ℝ) := by
                            nlinarith [le_of_lt hQB, Real.rpow_nonneg (le_of_lt hxpos) (1/3:ℝ), hQnn]
                      _ = (Q:ℝ)^2 := by ring
                  calc (x:ℝ)^(7/6:ℝ) = (x:ℝ)^(2/3:ℝ)*(x:ℝ)^(1/2:ℝ) := rpow_twothird_eq hxpos
                    _ ≤ (Q:ℝ)^2*(x:ℝ)^(1/2:ℝ) :=
                        mul_le_mul_of_nonneg_right hQ23 (Real.rpow_nonneg (le_of_lt hxpos) _)
              _ ≤ W := hWQ2'
        have hterm2 : (Q:ℝ)*(x:ℝ)*((T:ℝ)^(1/2:ℝ))⁻¹ ≤ 2*W := by
          rw [← Real.sqrt_eq_rpow]
          by_cases hQA : (Q:ℝ) ≤ (x:ℝ)^(1/3:ℝ)
          · have hx23divQ : (x:ℝ)^(1/3:ℝ) ≤ (x:ℝ)^(2/3:ℝ)/(Q:ℝ) := by
              rw [le_div_iff₀ hQ0]
              rw [show (x:ℝ)^(2/3:ℝ) = (x:ℝ)^(1/3:ℝ)*(x:ℝ)^(1/3:ℝ) from (rpow_third_add_third hxpos).symm]
              exact mul_le_mul_of_nonneg_left hQA (Real.rpow_nonneg (le_of_lt hxpos) _)
            have hTlow : (x:ℝ)^(1/3:ℝ)/4 ≤ (T:ℝ) := by
              have hmin : (x:ℝ)^(1/3:ℝ) ≤ 2*(T:ℝ) := by
                rw [min_eq_left hx23divQ] at hTmin; exact hTmin
              linarith
            have hsqrt := inv_sqrt_le_of_third hxpos hTlow
            calc (Q:ℝ)*(x:ℝ)*(Real.sqrt (T:ℝ))⁻¹
                ≤ (Q:ℝ)*(x:ℝ)*(2*((x:ℝ)^(1/6:ℝ))⁻¹) :=
                  mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hQnn (le_of_lt hxpos))
              _ = 2*((x:ℝ)^(5/6:ℝ)*(Q:ℝ)) := rpow_id5b (Q:ℝ) (x:ℝ) hxpos
              _ ≤ 2*W := mul_le_mul_of_nonneg_left hWc (by norm_num)
          · have hQB : (x:ℝ)^(1/3:ℝ) < (Q:ℝ) := lt_of_not_ge hQA
            have hx23divQ : (x:ℝ)^(2/3:ℝ)/(Q:ℝ) ≤ (x:ℝ)^(1/3:ℝ) := by
              rw [div_le_iff₀ hQ0]
              rw [show (x:ℝ)^(2/3:ℝ) = (x:ℝ)^(1/3:ℝ)*(x:ℝ)^(1/3:ℝ) from (rpow_third_add_third hxpos).symm]
              exact mul_le_mul_of_nonneg_left (le_of_lt hQB) (Real.rpow_nonneg (le_of_lt hxpos) _)
            have hTlow : (x:ℝ)^(2/3:ℝ)/(2*Q:ℝ) ≤ (T:ℝ) := by
              have hmin : (x:ℝ)^(2/3:ℝ)/(Q:ℝ) ≤ 2*(T:ℝ) := by
                rw [min_eq_right hx23divQ] at hTmin; exact hTmin
              rw [div_le_iff₀ hQ0] at hmin
              rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*Q)]
              nlinarith [hmin]
            have hsqrt := inv_sqrt_le_of_twothird hxpos hQ0 hTlow
            calc (Q:ℝ)*(x:ℝ)*(Real.sqrt (T:ℝ))⁻¹
                ≤ (Q:ℝ)*(x:ℝ)*(2*Real.sqrt (Q:ℝ)*((x:ℝ)^(1/3:ℝ))⁻¹) :=
                  mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hQnn (le_of_lt hxpos))
              _ = 2*((x:ℝ)^(2/3:ℝ)*(Q:ℝ)^(3/2:ℝ)) := rpow_id23 (Q:ℝ) (x:ℝ) hxpos hQ0
              _ ≤ 2*W := mul_le_mul_of_nonneg_left hWd (by norm_num)
        have s1 : (x:ℝ)+(Q:ℝ)*(x:ℝ)^(1/2:ℝ)*(T:ℝ)+(Q:ℝ)*(x:ℝ)*((T:ℝ)^(1/2:ℝ))⁻¹
            +(Q:ℝ)^2*(x:ℝ)^(1/2:ℝ) ≤ W + W + 2*W + W := by
          nlinarith [hWx, hWQ2', hterm1, hterm2]
        linarith [s1]
      have hC2nn : (0:ℝ) ≤ C2 := le_of_lt hC2
      have hC3nn : (0:ℝ) ≤ C3 := le_of_lt hC3
      have hC4nn : (0:ℝ) ≤ C4 := le_of_lt hC4
      have hC5nn : (0:ℝ) ≤ C5 := le_of_lt hC5
      have ht1 : C2*((x:ℝ)+(T:ℝ)*(Q:ℝ)^(5/2:ℝ))*L1^3 ≤ C2*(2*W)*L1^5 := by
        calc C2*((x:ℝ)+(T:ℝ)*(Q:ℝ)^(5/2:ℝ))*L1^3
            = (C2*((x:ℝ)+(T:ℝ)*(Q:ℝ)^(5/2:ℝ)))*L1^3 := by ring
          _ ≤ (C2*(2*W))*L1^3 := by
              refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hL1nn 3)
              exact mul_le_mul_of_nonneg_left hA hC2nn
          _ ≤ (C2*(2*W))*L1^5 := mul_le_mul_of_nonneg_left hL1_35 (by positivity)
          _ = C2*(2*W)*L1^5 := by ring
      have ht2 : C3*((x:ℝ)+(T:ℝ)*(Q:ℝ)^(5/2:ℝ))*L1^3 ≤ C3*(2*W)*L1^5 := by
        calc C3*((x:ℝ)+(T:ℝ)*(Q:ℝ)^(5/2:ℝ))*L1^3
            = (C3*((x:ℝ)+(T:ℝ)*(Q:ℝ)^(5/2:ℝ)))*L1^3 := by ring
          _ ≤ (C3*(2*W))*L1^3 := by
              refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hL1nn 3)
              exact mul_le_mul_of_nonneg_left hA hC3nn
          _ ≤ (C3*(2*W))*L1^5 := mul_le_mul_of_nonneg_left hL1_35 (by positivity)
          _ = C3*(2*W)*L1^5 := by ring
      have ht3 : C4*((x:ℝ)+(Q:ℝ)*(x:ℝ)^(1/2:ℝ)*(T:ℝ)+(Q:ℝ)*(x:ℝ)*((T:ℝ)^(1/2:ℝ))⁻¹
            +(Q:ℝ)^2*(x:ℝ)^(1/2:ℝ))*L1^5 ≤ C4*(5*W)*L1^5 := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hL1nn 5)
        exact mul_le_mul_of_nonneg_left hB hC4nn
      have ht4 : C5*((x:ℝ)+(Q:ℝ)*(x:ℝ)^(1/2:ℝ)*(T:ℝ)+(Q:ℝ)*(x:ℝ)*((T:ℝ)^(1/2:ℝ))⁻¹
            +(Q:ℝ)^2*(x:ℝ)^(1/2:ℝ))*L1^5 ≤ C5*(5*W)*L1^5 := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hL1nn 5)
        exact mul_le_mul_of_nonneg_left hB hC5nn
      have hcomb : ((T:ℝ)+1)*Real.log ((T:ℝ)+1)*(Q:ℝ)^2
          + C2*((x:ℝ)+(T:ℝ)*(Q:ℝ)^(5/2:ℝ))*L1^3
          + (C3*((x:ℝ)+(T:ℝ)*(Q:ℝ)^(5/2:ℝ))*L1^3
             + C4*((x:ℝ)+(Q:ℝ)*(x:ℝ)^(1/2:ℝ)*(T:ℝ)+(Q:ℝ)*(x:ℝ)*((T:ℝ)^(1/2:ℝ))⁻¹
                   +(Q:ℝ)^2*(x:ℝ)^(1/2:ℝ))*L1^5)
          + C5*((x:ℝ)+(Q:ℝ)*(x:ℝ)^(1/2:ℝ)*(T:ℝ)+(Q:ℝ)*(x:ℝ)*((T:ℝ)^(1/2:ℝ))⁻¹
                +(Q:ℝ)^2*(x:ℝ)^(1/2:ℝ))*L1^5
          ≤ 2*L*W + (2*(C2+C3) + 5*(C4+C5))*W*L1^5 := by
        nlinarith [hb1le, ht1, ht2, ht3, ht4, hL1nn, hWnn, hC2nn, hC3nn, hC4nn, hC5nn,
          pow_nonneg hL1nn 5, pow_nonneg hL1nn 3]
      have hfin : 2*L*W + (2*(C2+C3) + 5*(C4+C5))*W*L1^5
          ≤ 1000 * (C2 + C3 + C4 + C5 + 1) * W * L^20 := by
        have hLpow : L^5 ≤ L^20 := by simpa using pow_le_pow_right₀ hL1 (by norm_num : 5 ≤ 20)
        have hLp : L ≤ L^20 := by simpa using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ 20)
        have hcoefnn : (0:ℝ) ≤ 2*(C2+C3) + 5*(C4+C5) := by nlinarith [hC2nn, hC3nn, hC4nn, hC5nn]
        have h1 : 2*L*W ≤ 2*W*L^20 := by nlinarith [hLp, hWnn, hLnn]
        have h2 : (2*(C2+C3) + 5*(C4+C5))*W*L1^5 ≤ (2*(C2+C3) + 5*(C4+C5))*W*(32*L^5) := by
          calc (2*(C2+C3) + 5*(C4+C5))*W*L1^5 = (2*(C2+C3) + 5*(C4+C5))*(W*L1^5) := by ring
            _ ≤ (2*(C2+C3) + 5*(C4+C5))*(W*(32*L^5)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL15 hWnn) hcoefnn
            _ = (2*(C2+C3) + 5*(C4+C5))*W*(32*L^5) := by ring
        have h3 : (2*(C2+C3) + 5*(C4+C5))*W*(32*L^5)
            ≤ 32*(2*(C2+C3) + 5*(C4+C5))*W*L^20 := by
          calc (2*(C2+C3) + 5*(C4+C5))*W*(32*L^5)
              = 32*((2*(C2+C3) + 5*(C4+C5))*(W*L^5)) := by ring
            _ ≤ 32*((2*(C2+C3) + 5*(C4+C5))*(W*L^20)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLpow hWnn) hcoefnn)
                  (by norm_num)
            _ = 32*(2*(C2+C3) + 5*(C4+C5))*W*L^20 := by ring
        have e : 2*L*W + (2*(C2+C3) + 5*(C4+C5))*W*L1^5
            ≤ 2*W*L^20 + 32*(2*(C2+C3) + 5*(C4+C5))*W*L^20 := by linarith [h1, h2, h3]
        have e2 : 2*W*L^20 + 32*(2*(C2+C3) + 5*(C4+C5))*W*L^20
            = (2 + 32*(2*(C2+C3) + 5*(C4+C5)))*W*L^20 := by ring
        have e3 : (2 + 32*(2*(C2+C3) + 5*(C4+C5)))*W*L^20
            ≤ 1000*(C2+C3+C4+C5+1)*W*L^20 := by
          refine mul_le_mul_of_nonneg_right ?_ (by nlinarith [hWnn, hL20nn, hLnn])
          nlinarith [hC2nn, hC3nn, hC4nn, hC5nn]
        linarith [e, e2, e3]
      exact le_trans hsum (le_trans hcomb hfin)

end Commons.NumberTheory.BombieriVinogradov
