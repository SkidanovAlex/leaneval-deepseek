import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.supf_le_of_decay
import Submission.Work.GM.Affine.comb_sum_le

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

private lemma antitoneOn_min_div_pow {A B : ℝ} (hB : 0 ≤ B) {j : ℕ} :
    AntitoneOn (fun x : ℝ => min A (B / x ^ j)) (Set.Ici (1:ℝ)) := by
  intro x hx y hy hxy
  rw [Set.mem_Ici] at hx hy
  exact min_le_min le_rfl
    (div_le_div_of_nonneg_left hB (by positivity) (pow_le_pow_left₀ (by linarith) hxy j))

private lemma integrableOn_min_div_pow {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {j : ℕ}
    (hj : 2 ≤ j) :
    IntegrableOn (fun x : ℝ => min A (B / x ^ j)) (Set.Ioi (1:ℝ)) := by
  have hmaj : IntegrableOn (fun x : ℝ => B / x ^ j) (Set.Ioi (1:ℝ)) := by
    have hj2 : 1 < j := by omega
    have hjr : -(j:ℝ) < -1 := by
      have h2 : (1:ℝ) < (j:ℝ) := by exact_mod_cast hj2
      linarith
    have h1 : IntegrableOn (fun x : ℝ => B * x ^ (-(j:ℝ))) (Set.Ioi (1:ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt hjr (by norm_num)).const_mul B
    refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : 0 ≤ x := by have h := Set.mem_Ioi.mp hx; linarith
    show B * x ^ (-(j:ℝ)) = B / x ^ j
    rw [Real.rpow_neg hx0, Real.rpow_natCast, div_eq_mul_inv]
  refine hmaj.mono' ((measurable_const.min (measurable_const.div (measurable_id.pow_const j))).aestronglyMeasurable)
    ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := by have h := Set.mem_Ioi.mp hx; linarith
  have hnn : 0 ≤ min A (B / x ^ j) := le_min hA (div_nonneg hB (pow_nonneg hx0 j))
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact min_le_right _ _

private lemma rpow_neg_div_key (K : ℝ) (j : ℕ) :
    -(K ^ ((-(j:ℝ)) + 1)) / ((-(j:ℝ)) + 1) = K ^ (1 - (j:ℝ)) / ((j:ℝ) - 1) := by
  have h6 : (-(j:ℝ)) + 1 = 1 - (j:ℝ) := by ring
  rw [h6]
  have h1 : (1:ℝ) - (j:ℝ) = -((j:ℝ) - 1) := by ring
  rw [h1, neg_div, div_neg, neg_neg]

private lemma setIntegral_min_div_pow_le {A B K : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {j : ℕ}
    (hj : 2 ≤ j) (hK : 1 ≤ K) (hAK : A * K ^ j = B) :
    ∫ x in Set.Ioi (1:ℝ), min A (B / x ^ j) ≤ A * (K - 1) + A * K / ((j:ℝ) - 1) := by
  have hInt : IntegrableOn (fun x : ℝ => min A (B / x ^ j)) (Set.Ioi (1:ℝ)) :=
    integrableOn_min_div_pow hA hB hj
  have hIoc : IntegrableOn (fun x : ℝ => min A (B / x ^ j)) (Set.Ioc (1:ℝ) K) :=
    hInt.mono_set Set.Ioc_subset_Ioi_self
  have hIoi : IntegrableOn (fun x : ℝ => min A (B / x ^ j)) (Set.Ioi K) :=
    hInt.mono_set (Set.Ioi_subset_Ioi hK)
  have hdisj : Disjoint (Set.Ioc (1:ℝ) K) (Set.Ioi K) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have h1 : x ≤ K := (Set.mem_Ioc.mp hx).2
    have h2 : K < x := Set.mem_Ioi.mp hx'
    linarith
  have hunion : Set.Ioc (1:ℝ) K ∪ Set.Ioi K = Set.Ioi (1:ℝ) := by
    ext x; simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨ha, hb⟩ | hc)
      · linarith
      · linarith
    · intro h
      by_cases hx : x ≤ K
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr (not_le.mp hx)
  have hsplit : ∫ x in Set.Ioi (1:ℝ), min A (B / x ^ j)
      = (∫ x in Set.Ioc (1:ℝ) K, min A (B / x ^ j))
        + ∫ x in Set.Ioi K, min A (B / x ^ j) := by
    rw [← hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hIoc hIoi]
  have h1 : ∫ x in Set.Ioc (1:ℝ) K, min A (B / x ^ j) ≤ A * (K - 1) := by
    have h2 : ∫ x in Set.Ioc (1:ℝ) K, min A (B / x ^ j) ≤ ∫ x in Set.Ioc (1:ℝ) K, A := by
      refine MeasureTheory.integral_mono_of_nonneg
        (f := fun x : ℝ => min A (B / x ^ j)) (g := fun _ : ℝ => A) ?_ ?_ ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        have hx1 : 1 < x := (Set.mem_Ioc.mp hx).1
        exact le_min hA (div_nonneg hB (pow_nonneg (by linarith) j))
      · exact MeasureTheory.integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top.ne)
      · filter_upwards with x using min_le_left _ _
    rw [MeasureTheory.setIntegral_const, Measure.real_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul] at h2
    linarith [h2]
  have h3 : ∫ x in Set.Ioi K, min A (B / x ^ j) ≤ A * K / ((j:ℝ) - 1) := by
    have h4 : ∫ x in Set.Ioi K, min A (B / x ^ j) ≤ ∫ x in Set.Ioi K, B / x ^ j := by
      refine MeasureTheory.integral_mono_of_nonneg
        (f := fun x : ℝ => min A (B / x ^ j)) (g := fun x : ℝ => B / x ^ j) ?_ ?_ ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : 0 ≤ x := by have h := Set.mem_Ioi.mp hx; linarith
        exact le_min hA (div_nonneg hB (pow_nonneg hx0 j))
      · have hj2 : 1 < j := by omega
        have hjr : -(j:ℝ) < -1 := by
          have h2 : (1:ℝ) < (j:ℝ) := by exact_mod_cast hj2
          linarith
        have hbase : IntegrableOn (fun x : ℝ => B * x ^ (-(j:ℝ))) (Set.Ioi K) :=
          (integrableOn_Ioi_rpow_of_lt hjr (lt_of_lt_of_le zero_lt_one hK)).const_mul B
        refine hbase.congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : 0 ≤ x := by have h := Set.mem_Ioi.mp hx; linarith
        show B * x ^ (-(j:ℝ)) = B / x ^ j
        rw [Real.rpow_neg hx0, Real.rpow_natCast, div_eq_mul_inv]
      · filter_upwards with x using min_le_right _ _
    have h5 : ∫ x in Set.Ioi K, (B / x ^ j) = B * K ^ (1 - (j:ℝ)) / ((j:ℝ) - 1) := by
      have hae : (fun x : ℝ => B / x ^ j) =ᵐ[volume.restrict (Set.Ioi K)]
          (fun x => B * x ^ (-(j:ℝ))) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : 0 ≤ x := by have h := Set.mem_Ioi.mp hx; linarith
        show B / x ^ j = B * x ^ (-(j:ℝ))
        rw [Real.rpow_neg hx0, Real.rpow_natCast, div_eq_mul_inv]
      have hj2 : 1 < j := by omega
      have hjr : -(j:ℝ) < -1 := by
        have h2 : (1:ℝ) < (j:ℝ) := by exact_mod_cast hj2
        linarith
      rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul,
        integral_Ioi_rpow_of_lt hjr (lt_of_lt_of_le zero_lt_one hK), rpow_neg_div_key K j]
      ring
    have h7 : B * K ^ (1 - (j:ℝ)) / ((j:ℝ) - 1) = A * K / ((j:ℝ) - 1) := by
      congr 1
      rw [← hAK, mul_assoc, ← Real.rpow_natCast K j, ← Real.rpow_add (by linarith : (0:ℝ) < K),
        show ((j:ℝ) + (1 - (j:ℝ))) = 1 by ring, Real.rpow_one]
    rw [h5, h7] at h4
    exact h4
  rw [hsplit]
  linarith [h1, h3]

private lemma tsum_nat_succ_inv_sq_le_two : (∑' n : ℕ, (1:ℝ)/(((n:ℝ)+1)^2)) ≤ 2 := by
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) (fun N => ?_)
  have hle : ∀ i ∈ Finset.range N,
      (1:ℝ)/(((i:ℝ)+1)^2) ≤ 2/((i:ℝ)+1) - 2/((i:ℝ)+2) := by
    intro i _
    have h' : 2/((i:ℝ)+1) - 2/((i:ℝ)+2) = 2/(((i:ℝ)+1)*((i:ℝ)+2)) := by
      field_simp
      ring
    rw [h']
    have h : (0:ℝ) ≤ 2/(((i:ℝ)+1)*((i:ℝ)+2)) - 1/(((i:ℝ)+1)^2) := by
      have heq : 2/(((i:ℝ)+1)*((i:ℝ)+2)) - 1/(((i:ℝ)+1)^2)
          = (i:ℝ)/(((i:ℝ)+1)^2 * ((i:ℝ)+2)) := by
        field_simp
        ring
      rw [heq]; positivity
    linarith
  calc ∑ i ∈ Finset.range N, (1:ℝ)/(((i:ℝ)+1)^2)
      ≤ ∑ i ∈ Finset.range N, (2/((i:ℝ)+1) - 2/((i:ℝ)+2)) := Finset.sum_le_sum hle
    _ = ∑ i ∈ Finset.range N,
          ((fun k : ℕ => 2/((k:ℝ)+1)) i - (fun k : ℕ => 2/((k:ℝ)+1)) (i+1)) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Nat.cast_add, Nat.cast_one]
        ring
    _ = 2/(((0:ℕ):ℝ)+1) - 2/((N:ℝ)+1) := Finset.sum_range_sub' (fun k : ℕ => 2/((k:ℝ)+1)) N
    _ ≤ 2 := by
        have h : (0:ℝ) ≤ 2/((N:ℝ)+1) := by positivity
        norm_num
        linarith

private theorem min_sum_half_aux {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {j : ℕ} (hj : 2 ≤ j) :
    (∑' n : ℕ, min A (B / ((n : ℝ) + 1) ^ j)) ≤ 2 * A ^ (1 - 1 / (j : ℝ)) * B ^ (1 / (j : ℝ)) := by
  have hsumm_cmp : Summable (fun n : ℕ => B / ((n:ℝ)+1)^j) := by
    have h1 : Summable fun n : ℕ => (1:ℝ)/((n:ℝ)^j) :=
      (Real.summable_one_div_nat_pow (p:=j)).mpr (by omega)
    have h2 : Summable fun n : ℕ => (1:ℝ)/(((n+1:ℕ):ℝ)^j) := (summable_nat_add_iff 1).mpr h1
    have h3 : Summable fun n : ℕ => B * ((1:ℝ)/(((n+1:ℕ):ℝ)^j)) := h2.mul_left B
    refine h3.congr (fun n => ?_)
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have hj0 : (0:ℝ) < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hexp_pos : (0:ℝ) < 1 - 1/(j:ℝ) := by
    have h : (1:ℝ)/(j:ℝ) < 1 := by
      rw [div_lt_one hj0]
      exact_mod_cast (by omega : 1 < j)
    linarith
  by_cases hA0 : A = 0
  · subst hA0
    have hz : (fun n : ℕ => min 0 (B / ((n:ℝ)+1)^j)) = fun _ => (0:ℝ) := by
      funext n
      exact min_eq_left (div_nonneg hB (pow_nonneg (by positivity) j))
    rw [hz, tsum_zero, Real.zero_rpow (ne_of_gt hexp_pos)]
    simp
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    by_cases hBA : B ≤ A
    · have hmin : ∀ n : ℕ, min A (B / ((n:ℝ)+1)^j) = B / ((n:ℝ)+1)^j := by
        intro n
        refine min_eq_right ?_
        have h1 : (1:ℝ) ≤ ((n:ℝ)+1)^j := one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
        calc B / ((n:ℝ)+1)^j ≤ B / (1:ℝ) := div_le_div_of_nonneg_left hB zero_lt_one h1
          _ = B := div_one B
          _ ≤ A := hBA
      have hsum_ub : (∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^j) ≤ 2 := by
        have h1 : (∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^2) ≤ 2 := tsum_nat_succ_inv_sq_le_two
        have hs2 : Summable fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^2 := by
          have h := (summable_nat_add_iff (f := fun n : ℕ => (1:ℝ)/((n:ℝ)^2)) 1).mpr
            ((Real.summable_one_div_nat_pow (p:=2)).mpr (by norm_num))
          simpa [Nat.cast_add, Nat.cast_one] using h
        have hsj : Summable fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^j := by
          have h := (summable_nat_add_iff (f := fun n : ℕ => (1:ℝ)/((n:ℝ)^j)) 1).mpr
            ((Real.summable_one_div_nat_pow (p:=j)).mpr (by omega))
          simpa [Nat.cast_add, Nat.cast_one] using h
        refine le_trans (Summable.tsum_le_tsum (fun n => ?_) hsj hs2) h1
        refine div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
          (by positivity : (0:ℝ) < ((n:ℝ)+1)^2) ?_
        exact pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) hj
      have hB_le : B ≤ A ^ (1 - 1/(j:ℝ)) * B ^ (1/(j:ℝ)) := by
        by_cases hB0 : B = 0
        · rw [hB0, Real.zero_rpow (ne_of_gt (div_pos zero_lt_one hj0))]
          simp
        · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
          have h1 : B ^ (1 - 1/(j:ℝ)) ≤ A ^ (1 - 1/(j:ℝ)) :=
            Real.rpow_le_rpow hB hBA (le_of_lt hexp_pos)
          have h2 : B ^ (1 - 1/(j:ℝ)) * B ^ (1/(j:ℝ)) = B := by
            rw [← Real.rpow_add hBpos, sub_add_cancel, Real.rpow_one]
          calc B = B ^ (1 - 1/(j:ℝ)) * B ^ (1/(j:ℝ)) := h2.symm
            _ ≤ A ^ (1 - 1/(j:ℝ)) * B ^ (1/(j:ℝ)) :=
                mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hB _)
      have heq : (∑' n : ℕ, min A (B / ((n:ℝ)+1)^j)) = B * ∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^j := by
        rw [← tsum_mul_left]
        refine tsum_congr (fun n => ?_)
        rw [hmin n]
        ring
      calc (∑' n : ℕ, min A (B / ((n:ℝ)+1)^j)) = B * ∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^j := heq
        _ ≤ B * 2 := mul_le_mul_of_nonneg_left hsum_ub hB
        _ = 2 * B := by ring
        _ ≤ 2 * (A ^ (1 - 1/(j:ℝ)) * B ^ (1/(j:ℝ))) := by linarith [hB_le]
        _ = 2 * A ^ (1 - 1/(j:ℝ)) * B ^ (1/(j:ℝ)) := by ring
    · rw [not_le] at hBA
      set K : ℝ := (B / A) ^ (1 / (j:ℝ)) with hKdef
      have hKpos : 0 < K := by
        rw [hKdef]; exact Real.rpow_pos_of_pos (div_pos (lt_trans hApos hBA) hApos) _
      have hK1 : 1 < K := by
        rw [hKdef]
        have hb : 1 < B / A := (one_lt_div hApos).mpr hBA
        calc (1:ℝ) = 1 ^ (1/(j:ℝ)) := (Real.one_rpow _).symm
          _ < (B/A) ^ (1/(j:ℝ)) := Real.rpow_lt_rpow (by norm_num) hb (by positivity)
      have hAK : A * K ^ j = B := by
        rw [hKdef, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ B/A),
          show (1/(j:ℝ)) * (j:ℝ) = 1 by field_simp, Real.rpow_one]
        field_simp
      have hAK' : A * K = A ^ (1 - 1/(j:ℝ)) * B ^ (1/(j:ℝ)) := by
        have h1 : A / A ^ (1/(j:ℝ)) = A ^ (1 - 1/(j:ℝ)) := by
          rw [eq_comm, Real.rpow_sub hApos, Real.rpow_one]
        calc A * K = A * (B/A) ^ (1/(j:ℝ)) := by rw [hKdef]
          _ = A * (B ^ (1/(j:ℝ)) / A ^ (1/(j:ℝ))) := by rw [Real.div_rpow hB (le_of_lt hApos)]
          _ = B ^ (1/(j:ℝ)) * (A / A ^ (1/(j:ℝ))) := by ring
          _ = B ^ (1/(j:ℝ)) * A ^ (1 - 1/(j:ℝ)) := by rw [h1]
          _ = A ^ (1 - 1/(j:ℝ)) * B ^ (1/(j:ℝ)) := by ring
      have hsumm : Summable (fun n : ℕ => min A (B / (((n):ℝ) + 1)^j)) := by
        refine Summable.of_nonneg_of_le
          (fun n => le_min hA (div_nonneg hB (pow_nonneg (by positivity) j)))
          (fun n => min_le_right _ _) hsumm_cmp
      have htail : (∑' n : ℕ, min A (B / ((n:ℝ)+2)^j)) ≤ ∫ x in Set.Ioi (1:ℝ), min A (B / x ^ j) := by
        have h := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => min A (B / x ^ j)) 1
          (by simpa only [Nat.cast_one] using antitoneOn_min_div_pow (A := A) (j := j) hB)
          (by simpa only [Nat.cast_one] using integrableOn_min_div_pow hA hB hj)
          (fun t ht => le_min hA (div_nonneg hB (by
            have h' : (1:ℝ) < t := by simpa only [Nat.cast_one] using Set.mem_Ioi.mp ht
            exact pow_nonneg (by linarith) j)))
        have heq : (∑' n : ℕ, min A (B / ((n:ℝ)+2)^j))
            = ∑' n : ℕ, min A (B / ((↑(n+1+1) : ℝ))^j) := by
          refine tsum_congr (fun n => ?_)
          push_cast
          ring_nf
        rw [heq]
        simpa only [Nat.cast_one] using h
      have hsplit : (∑' n : ℕ, min A (B / ((n:ℝ)+1)^j))
          = min A B + ∑' n : ℕ, min A (B / ((n:ℝ)+2)^j) := by
        have h := Summable.tsum_eq_zero_add hsumm
        rw [h]
        congr 1
        · norm_num
        · refine tsum_congr (fun n => ?_)
          push_cast
          ring_nf
      have hminAB : min A B = A := min_eq_left (le_of_lt hBA)
      calc (∑' n : ℕ, min A (B / ((n:ℝ)+1)^j))
          = min A B + ∑' n : ℕ, min A (B / ((n:ℝ)+2)^j) := hsplit
        _ ≤ A + (A * (K - 1) + A * K / ((j:ℝ) - 1)) := by
            rw [hminAB]
            exact add_le_add le_rfl
              (le_trans htail (setIntegral_min_div_pow_le hA hB hj (le_of_lt hK1) hAK))
        _ ≤ 2 * K * A := by
            have hj1 : (1:ℝ) ≤ (j:ℝ) - 1 := by
              have h2 : (2:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
              linarith
            have hAKnn : 0 ≤ A * K := mul_nonneg hA (le_of_lt hKpos)
            have hdiv : A * K / ((j:ℝ) - 1) ≤ A * K := by
              rw [div_le_iff₀ (by linarith : (0:ℝ) < (j:ℝ) - 1)]
              nlinarith [hAKnn]
            nlinarith [hdiv]
        _ = 2 * A ^ (1 - 1/(j:ℝ)) * B ^ (1/(j:ℝ)) := by
            rw [show (2:ℝ) * K * A = 2 * (A * K) by ring, hAK']
            ring

private theorem min_sum_int_aux {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {j : ℕ} (hj : 2 ≤ j) :
    (∑' k : ℤ, min A (B / |(k : ℝ)| ^ j)) ≤ 4 * A ^ (1 - 1 / (j : ℝ)) * B ^ (1 / (j : ℝ)) := by
  have hcast : ∀ n : ℕ, |(((n : ℕ) : ℤ) : ℝ)| = (n : ℝ) := by
    intro n
    rw [Int.cast_natCast]
    exact abs_of_nonneg (Nat.cast_nonneg n)
  set f : ℤ → ℝ := fun k => min A (B / |(k:ℝ)|^j) with hfdef
  have hsumm_nat : Summable fun n : ℕ => f ↑n := by
    have h1 : Summable fun n : ℕ => B / ((n:ℝ)^j) := by
      have h := (Real.summable_one_div_nat_pow (p:=j)).mpr (by omega : 1 < j)
      refine (h.mul_left B).congr (fun n => ?_)
      ring
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) h1
    · rw [hfdef]; simp only
      exact le_min hA (div_nonneg hB (pow_nonneg (abs_nonneg _) j))
    · rw [hfdef]; simp only
      rw [hcast n]
      exact min_le_right _ _
  have hsumm_neg : Summable fun n : ℕ => f (-(↑n + 1)) := by
    have h1 : Summable fun n : ℕ => B / (((n:ℝ)+1)^j) := by
      have h := (Real.summable_one_div_nat_pow (p:=j)).mpr (by omega : 1 < j)
      have h2 := (summable_nat_add_iff 1).mpr h
      refine (h2.mul_left B).congr (fun n => ?_)
      rw [Nat.cast_add, Nat.cast_one]; ring
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) h1
    · rw [hfdef]; simp only
      exact le_min hA (div_nonneg hB (pow_nonneg (abs_nonneg _) j))
    · rw [hfdef]; simp only
      have hc : |((-(↑n + 1) : ℤ) : ℝ)| = (n:ℝ)+1 := by
        rw [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, abs_neg]
        exact abs_of_pos (by positivity)
      rw [hc]
      exact min_le_right _ _
  have hdecomp := tsum_of_nat_of_neg_add_one hsumm_nat hsumm_neg
  have hnat_eq : (∑' n : ℕ, f ↑n) = ∑' n : ℕ, min A (B / ((n:ℝ)+1)^j) := by
    rw [hsumm_nat.tsum_eq_zero_add]
    have h0 : f ((0:ℕ):ℤ) = 0 := by
      rw [hfdef]
      simp only
      have hz : ((((0:ℕ):ℤ):ℝ)) = 0 := by simp
      rw [hz, abs_zero, zero_pow (by omega : j ≠ 0), div_zero]
      exact min_eq_right hA
    rw [h0, zero_add]
    refine tsum_congr (fun n => ?_)
    rw [hfdef]
    simp only
    have hb : |((((n+1 : ℕ)) : ℤ) : ℝ)| = ((n:ℝ)+1) := by
      rw [Int.cast_natCast, Nat.cast_add, Nat.cast_one]
      exact abs_of_nonneg (by positivity)
    rw [hb]
  have hneg_eq : (∑' n : ℕ, f (-(↑n + 1))) = ∑' n : ℕ, min A (B / ((n:ℝ)+1)^j) := by
    refine tsum_congr (fun n => ?_)
    rw [hfdef]
    simp only
    have hb : |(((-(↑n + 1) : ℤ) : ℝ))| = (n:ℝ)+1 := by
      rw [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, abs_neg]
      exact abs_of_pos (by positivity)
    rw [hb]
  rw [hdecomp, hnat_eq, hneg_eq]
  have h := min_sum_half_aux hA hB hj
  linarith

private lemma fhat_zero_eq_integral' (f : ℝ → ℝ) : Fhat f 0 = (((∫ u : ℝ, f u) : ℝ) : ℂ) := by
  have h1 : Fhat f 0 = ∫ v : ℝ, (f v : ℂ) := by
    simp only [Fhat]
    rw [Real.fourier_eq]
    congr 1
    funext v
    simp
  rw [h1]
  exact integral_ofReal

/-- **GM §9 (sharp aliasing bound).**  Interpolating between the trivial bound
`‖Fhat f ξ‖ ≤ ∫f` and the Fourier-decay hypothesis `DecayHyp` (with exponent `j`), and summing
the resulting `min` over the lattice, bounds the aliasing mass `Σ_k ‖Fhat f (k m)‖` by
`∫f + 4 (∫f)^{1-1/j} (c j ε T^ε (T/m)^j supf f)^{1/j}`. -/
theorem aliasing_sharp {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hnn : ∀ u, 0 ≤ f u) (hcs : HasCompactSupport f) (hdec : DecayHyp c T f)
    {j : ℕ} (hj : 3 ≤ j) {ε : ℝ} (hε : 0 < ε) :
    ∀ m : ℝ, 0 < m → aliasing f m ≤ (∫ u, f u) +
        4 * (∫ u, f u) ^ (1 - 1/(j:ℝ)) * (c j ε * T ^ ε * (T/m) ^ j * supf f) ^ (1/(j:ℝ)) := by
  set_option linter.unusedVariables false in
  intro m hm
  set A : ℝ := ∫ u, f u with hA
  set B : ℝ := c j ε * T ^ ε * (T/m)^j * supf f with hB
  have hAnn : 0 ≤ A := by rw [hA]; exact integral_nonneg hnn
  have hBnn : 0 ≤ B := by
    rw [hB]
    have h1 := hdec j ε hε m (ne_of_gt hm)
    rw [abs_of_pos hm] at h1
    exact le_trans (norm_nonneg _) h1
  have hsumm : Summable fun k : ℤ => ‖Fhat f ((k:ℝ)*m)‖ := summable_fhat_lattice hdec hε hm
  have hper : ∀ k : ℤ, k ≠ 0 → ‖Fhat f ((k:ℝ)*m)‖ ≤ min A (B / |(k:ℝ)|^j) := by
    intro k hk
    have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast hk
    have hk' : ((k:ℝ) * m) ≠ 0 := mul_ne_zero hkR (ne_of_gt hm)
    have h1 : ‖Fhat f ((k:ℝ)*m)‖ ≤ A := by
      rw [hA]; exact norm_fhat_le_integral hnn _
    have h2 : ‖Fhat f ((k:ℝ)*m)‖ ≤ B / |(k:ℝ)|^j := by
      rw [hB]
      have hd := hdec j ε hε ((k:ℝ)*m) hk'
      have hd1 : (T / |(k:ℝ)*m|)^j = (T/m)^j / |(k:ℝ)|^j := by
        rw [abs_mul, abs_of_pos hm]
        rw [show T / (|(k:ℝ)| * m) = (T/m) / |(k:ℝ)| by field_simp]
        rw [div_pow]
      calc ‖Fhat f ((k:ℝ)*m)‖ ≤ c j ε * T^ε * (T/|(k:ℝ)*m|)^j * supf f := hd
        _ = c j ε * T^ε * ((T/m)^j / |(k:ℝ)|^j) * supf f := by rw [hd1]
        _ = (c j ε * T^ε * (T/m)^j * supf f) / |(k:ℝ)|^j := by ring
    exact le_min h1 h2
  have hsum_min : Summable fun k : ℤ => min A (B / |(k:ℝ)|^j) := by
    have h1 : Summable fun k : ℤ => (1:ℝ)/((k:ℝ)^2) :=
      (Real.summable_one_div_int_pow (p:=2)).mpr (by norm_num)
    have h2 : Summable fun k : ℤ => B / ((k:ℝ)^2) := by
      have h2' : Summable fun k : ℤ => B * ((1:ℝ)/((k:ℝ)^2)) := h1.mul_left B
      refine h2'.congr (fun k => ?_)
      ring
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) h2
    · exact le_min hAnn (div_nonneg hBnn (by positivity))
    · rcases eq_or_ne k 0 with hk | hk
      · subst hk
        have h1' : (0:ℝ)^j = 0 := zero_pow (by omega)
        have h2' : (0:ℝ)^2 = 0 := by norm_num
        simp [h1', h2', min_eq_right hAnn]
      · have hkR : (1:ℝ) ≤ |(k:ℝ)| := by
          have := Int.one_le_abs hk
          exact_mod_cast this
        have hpos : (0:ℝ) < |(k:ℝ)|^2 := by positivity
        have hle : |(k:ℝ)|^2 ≤ |(k:ℝ)|^j := pow_le_pow_right₀ hkR (by omega : 2 ≤ j)
        have h2'' : B / |(k:ℝ)|^j ≤ B / |(k:ℝ)|^2 := div_le_div_of_nonneg_left hBnn hpos hle
        have h3 : B / |(k:ℝ)|^2 = B / ((k:ℝ)^2) := by rw [sq_abs]
        calc min A (B / |(k:ℝ)|^j) ≤ B / |(k:ℝ)|^j := min_le_right _ _
          _ ≤ B / |(k:ℝ)|^2 := h2''
          _ = B / ((k:ℝ)^2) := h3
  have hsplit := hsumm.tsum_eq_add_tsum_ite (0:ℤ)
  have h0 : ‖Fhat f (((0:ℤ):ℝ) * m)‖ = A := by
    have hz : (((0:ℤ):ℝ) * m) = 0 := by simp
    rw [hz, hA, fhat_zero_eq_integral', Complex.norm_real, Real.norm_of_nonneg hAnn]
  have hif : Summable fun k : ℤ => (if k = 0 then 0 else ‖Fhat f ((k:ℝ)*m)‖) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hsumm
    · split <;> simp
    · split
      · simp
      · exact le_rfl
  calc aliasing f m = ∑' k : ℤ, ‖Fhat f ((k:ℝ)*m)‖ := rfl
    _ = ‖Fhat f (((0:ℤ):ℝ)*m)‖ + ∑' k : ℤ, (if k = 0 then 0 else ‖Fhat f ((k:ℝ)*m)‖) := hsplit
    _ = A + ∑' k : ℤ, (if k = 0 then 0 else ‖Fhat f ((k:ℝ)*m)‖) := by rw [h0]
    _ ≤ A + ∑' k : ℤ, min A (B / |(k:ℝ)|^j) := by
        refine add_le_add le_rfl ?_
        refine Summable.tsum_le_tsum (fun k => ?_) hif hsum_min
        by_cases hk : k = 0
        · subst hk
          have h1' : (0:ℝ)^j = 0 := zero_pow (by omega)
          simp [h1', min_eq_right hAnn]
        · simp only [if_neg hk]; exact hper k hk
    _ ≤ A + 4 * A^(1-1/(j:ℝ)) * B^(1/(j:ℝ)) := by
        have h := min_sum_int_aux hAnn hBnn (by omega : 2 ≤ j)
        linarith
    _ = (∫ u, f u) + 4 * (∫ u, f u)^(1-1/(j:ℝ)) *
          (c j ε * T^ε * (T/m)^j * supf f)^(1/(j:ℝ)) := by rw [hA, hB]

end

end Work.GM.Affine
