import Mathlib
import Submission.Work.LinnikAreas.Density4.sum_Icc_filter_dvd_reindex
import Submission.Work.LinnikAreas.Density4.sum_sq_dvd_filter_coprime_reindex
import Submission.Work.LinnikAreas.Density4.sum_moebius_div_eq_coprime_count
import Submission.Work.LinnikAreas.Density4.sq_dvd_count_coprime

namespace Work.LinnikAreas.Density4

/-- The Möbius square-divisor identity: `Σ_{d² | n} μ(d) = [n squarefree]`.
For `n` squarefree the only such `d` is `1`; otherwise, choosing a prime `p` with `p² | n`, the
map `d ↦ d/p` (resp. `d ↦ p·d`) is a bijection between the squarefree divisors `d` with `d² | n`
that are divisible (resp. not divisible) by `p`, and it flips `μ`, so the sum vanishes. -/
private theorem crux_tmp (n : ℕ) :
    (∑ d ∈ n.divisors, if d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0)
      = if Squarefree n then 1 else 0 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  by_cases hsq : Squarefree n
  · rw [if_pos hsq]
    have hfilt : n.divisors.filter (fun d => d ^ 2 ∣ n) = {1} := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨_, _⟩, hd2⟩
        have hdd : d * d ∣ n := by rwa [pow_two] at hd2
        exact Nat.isUnit_iff.mp (hsq d hdd)
      · rintro rfl
        exact ⟨⟨one_dvd n, hn0⟩, by norm_num⟩
    rw [← Finset.sum_filter, hfilt, Finset.sum_singleton]
    simp
  · rw [if_neg hsq]
    obtain ⟨p, hpp, hp2n⟩ : ∃ p, Nat.Prime p ∧ p ^ 2 ∣ n := by
      by_contra h
      exact hsq ((Nat.squarefree_iff_prime_squarefree).mpr
        (fun x hx hxx => h ⟨x, hx, by rwa [pow_two]⟩))
    set T : Finset ℕ := (n.divisors.filter (fun d => d ^ 2 ∣ n)).filter (fun d => Squarefree d)
      with hT
    have memT : ∀ d, d ∈ T ↔ d ∣ n ∧ d ^ 2 ∣ n ∧ Squarefree d := by
      intro d
      rw [hT]
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨⟨hdvd, _⟩, hd2⟩, hsqd⟩
        exact ⟨hdvd, hd2, hsqd⟩
      · rintro ⟨hdvd, hd2, hsqd⟩
        exact ⟨⟨⟨hdvd, hn0⟩, hd2⟩, hsqd⟩
    have hred : (∑ d ∈ n.divisors, if d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0)
        = ∑ d ∈ T, (ArithmeticFunction.moebius d : ℝ) := by
      rw [← Finset.sum_filter]
      have hμ0 : ∀ d ∈ n.divisors.filter (fun d => d ^ 2 ∣ n),
          (ArithmeticFunction.moebius d : ℝ)
            = if Squarefree d then (ArithmeticFunction.moebius d : ℝ) else 0 := by
        intro d _
        by_cases hd : Squarefree d
        · rw [if_pos hd]
        · rw [if_neg hd, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]
          simp
      rw [Finset.sum_congr rfl hμ0, ← Finset.sum_filter, hT]
    rw [hred]
    have hpdn : p ∣ n := dvd_trans (by rw [pow_two]; exact dvd_mul_right p p) hp2n
    have hT_mul : ∀ a ∈ T, ¬ p ∣ a → p * a ∈ T := by
      intro a ha hpa
      obtain ⟨hadvd, ha2, hasq⟩ := (memT a).mp ha
      have hcop : Nat.Coprime p a := hpp.coprime_iff_not_dvd.mpr hpa
      refine (memT (p * a)).mpr ⟨?_, ?_, ?_⟩
      · exact hcop.mul_dvd_of_dvd_of_dvd hpdn hadvd
      · rw [mul_pow]
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ((hcop.pow_left 2).pow_right 2) hp2n ha2
      · exact (Nat.squarefree_mul hcop).mpr ⟨(Nat.prime_iff.mp hpp).squarefree, hasq⟩
    have hT_div : ∀ b ∈ T, p ∣ b → b / p ∈ T ∧ ¬ p ∣ b / p := by
      intro b hb hpb
      obtain ⟨hbdvd, hb2, hbsq⟩ := (memT b).mp hb
      have hpb' : p * (b / p) = b := Nat.mul_div_cancel' hpb
      have hdiv1 : b / p ∣ n := dvd_trans (Nat.div_dvd_of_dvd hpb) hbdvd
      have hdiv2 : (b / p) ^ 2 ∣ n :=
        dvd_trans ⟨p ^ 2, by rw [← mul_pow, Nat.div_mul_cancel hpb]⟩ hb2
      refine ⟨(memT (b / p)).mpr
        ⟨hdiv1, hdiv2, hbsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hpb)⟩, ?_⟩
      intro hpdiv
      have hp2b : p * p ∣ b := by
        obtain ⟨k, hk⟩ := hpdiv
        exact ⟨k, by rw [← hpb', hk]; ring⟩
      exact hpp.ne_one (Nat.isUnit_iff.mp (hbsq p hp2b))
    have hmu_mul : ∀ a ∈ T, ¬ p ∣ a →
        (ArithmeticFunction.moebius (p * a) : ℝ) = -(ArithmeticFunction.moebius a : ℝ) := by
      intro a _ hpa
      have hcop : Nat.Coprime p a := hpp.coprime_iff_not_dvd.mpr hpa
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
            (Nat.coprime_iff_gcd_eq_one.mp hcop), ArithmeticFunction.moebius_apply_prime hpp]
      push_cast
      ring
    have hsplit : (∑ d ∈ T, (ArithmeticFunction.moebius d : ℝ))
        = (∑ d ∈ T.filter (fun d => p ∣ d), (ArithmeticFunction.moebius d : ℝ))
          + (∑ d ∈ T.filter (fun d => ¬ p ∣ d), (ArithmeticFunction.moebius d : ℝ)) := by
      rw [← Finset.sum_filter_add_sum_filter_not T (fun d => p ∣ d)]
    rw [hsplit]
    have hbij : (∑ d ∈ T.filter (fun d => ¬ p ∣ d), (ArithmeticFunction.moebius d : ℝ))
        = ∑ d ∈ T.filter (fun d => p ∣ d), -(ArithmeticFunction.moebius d : ℝ) := by
      refine Finset.sum_bij (fun a _ => p * a) ?_ ?_ ?_ ?_
      · intro a ha
        rw [Finset.mem_filter] at ha ⊢
        exact ⟨hT_mul a ha.1 ha.2, dvd_mul_right p a⟩
      · intro a₁ _ a₂ _ heq
        exact Nat.mul_left_cancel hpp.pos heq
      · intro b hb
        rw [Finset.mem_filter] at hb
        exact ⟨b / p,
          Finset.mem_filter.mpr ⟨(hT_div b hb.1 hb.2).1, (hT_div b hb.1 hb.2).2⟩,
          Nat.mul_div_cancel' hb.2⟩
      · intro a ha
        rw [Finset.mem_filter] at ha
        rw [hmu_mul a ha.1 ha.2]
        ring
    rw [hbij, Finset.sum_neg_distrib]
    ring

theorem sqfree_moebius_double_sum (X r : ℕ) (hr : 1 ≤ r) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n => Nat.Coprime n r ∧ Squarefree n), (1 : ℝ))
      = ∑ m₀ ∈ r.divisors, (ArithmeticFunction.moebius m₀ : ℝ) *
          ∑ m₂ ∈ (Finset.Icc 1 X).filter (fun m₂ => Nat.Coprime m₂ r),
            (ArithmeticFunction.moebius m₂ : ℝ) * (((X / (m₀ * m₂ ^ 2)) : ℕ) : ℝ) := by
  -- crux identity, in the `Icc`-form needed by the outer sum
  have hcrux : ∀ n ∈ Finset.Icc 1 X,
      (∑ d ∈ Finset.Icc 1 X, (if d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0))
        = if Squarefree n then 1 else 0 := by
    intro n hn
    obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp hn
    have hn0 : n ≠ 0 := by omega
    have hnpos : 0 < n := by omega
    have hset : (Finset.Icc 1 X).filter (fun d => d ^ 2 ∣ n)
        = n.divisors.filter (fun d => d ^ 2 ∣ n) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨_, _⟩, hsq⟩
        exact ⟨⟨dvd_trans (by rw [pow_two]; exact dvd_mul_right d d) hsq, hn0⟩, hsq⟩
      · rintro ⟨⟨hdvd, _⟩, hsq⟩
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hnpos
        have hdd : d ≤ d ^ 2 := by
          rw [pow_two]
          exact Nat.le_mul_of_pos_right d hdpos
        exact ⟨⟨hdpos, le_trans (le_trans hdd (Nat.le_of_dvd hnpos hsq)) hnX⟩, hsq⟩
    have hswap : (∑ d ∈ Finset.Icc 1 X,
          (if d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0))
        = ∑ d ∈ n.divisors, (if d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0) := by
      conv_lhs => rw [← Finset.sum_filter]
      conv_rhs => rw [← Finset.sum_filter]
      rw [hset]
    rw [hswap, crux_tmp]
  have S1 : (∑ n ∈ (Finset.Icc 1 X).filter (fun n => Nat.Coprime n r ∧ Squarefree n), (1 : ℝ))
      = ∑ n ∈ Finset.Icc 1 X, (if Nat.Coprime n r ∧ Squarefree n then (1 : ℝ) else 0) :=
    Finset.sum_filter _ _
  have S2 : (∑ n ∈ Finset.Icc 1 X, (if Nat.Coprime n r ∧ Squarefree n then (1 : ℝ) else 0))
      = ∑ n ∈ Finset.Icc 1 X,
          (if Nat.Coprime n r then (if Squarefree n then (1 : ℝ) else 0) else 0) :=
    Finset.sum_congr rfl (fun n _ => ite_and (Nat.Coprime n r) (Squarefree n) (1 : ℝ) 0)
  have S3 : (∑ n ∈ Finset.Icc 1 X,
          (if Nat.Coprime n r then (if Squarefree n then (1 : ℝ) else 0) else 0))
      = ∑ n ∈ Finset.Icc 1 X,
          (if Nat.Coprime n r then
            (∑ d ∈ Finset.Icc 1 X, (if d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0))
           else 0) :=
    Finset.sum_congr rfl (fun n hn => by rw [← hcrux n hn])
  have S4 : (∑ n ∈ Finset.Icc 1 X,
          (if Nat.Coprime n r then
            (∑ d ∈ Finset.Icc 1 X, (if d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0))
           else 0))
      = ∑ n ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Icc 1 X,
          (if Nat.Coprime n r ∧ d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0) :=
    Finset.sum_congr rfl (fun n _ => by
      by_cases hc : Nat.Coprime n r
      · rw [if_pos hc]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        by_cases hd : d ^ 2 ∣ n
        · rw [if_pos (show Nat.Coprime n r ∧ d ^ 2 ∣ n from ⟨hc, hd⟩), if_pos hd]
        · rw [if_neg (show ¬ (Nat.Coprime n r ∧ d ^ 2 ∣ n) from fun hh => hd hh.2), if_neg hd]
      · rw [if_neg hc]
        exact (Finset.sum_eq_zero
          (fun d _ => if_neg
            (show ¬ (Nat.Coprime n r ∧ d ^ 2 ∣ n) from fun hh => hc hh.1))).symm)
  have S5 : (∑ n ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Icc 1 X,
          (if Nat.Coprime n r ∧ d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0))
      = ∑ d ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
          (if Nat.Coprime n r ∧ d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0) :=
    Finset.sum_comm
  have S6 : (∑ d ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
          (if Nat.Coprime n r ∧ d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0))
      = ∑ d ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius d : ℝ) *
          ∑ n ∈ (Finset.Icc 1 X).filter (fun n => Nat.Coprime n r ∧ d ^ 2 ∣ n), (1 : ℝ) :=
    Finset.sum_congr rfl (fun d _ => by
      rw [Finset.mul_sum, ← Finset.sum_filter]
      exact Finset.sum_congr rfl (fun n _ => by rw [mul_one]))
  have S7 : (∑ d ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius d : ℝ) *
          ∑ n ∈ (Finset.Icc 1 X).filter (fun n => Nat.Coprime n r ∧ d ^ 2 ∣ n), (1 : ℝ))
      = ∑ d ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius d : ℝ) *
          (if Nat.Coprime d r then
            ∑ m₀ ∈ r.divisors, (ArithmeticFunction.moebius m₀ : ℝ) * ((X / (m₀ * d ^ 2) : ℕ) : ℝ)
           else 0) :=
    Finset.sum_congr rfl (fun d hd => by
      rw [sq_dvd_count_coprime X d r (Finset.mem_Icc.mp hd).1 hr])
  have S8 : (∑ d ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius d : ℝ) *
          (if Nat.Coprime d r then
            ∑ m₀ ∈ r.divisors, (ArithmeticFunction.moebius m₀ : ℝ) * ((X / (m₀ * d ^ 2) : ℕ) : ℝ)
           else 0))
      = ∑ d ∈ Finset.Icc 1 X, ∑ m₀ ∈ r.divisors,
          (if Nat.Coprime d r then
            (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius m₀ : ℝ)
              * ((X / (m₀ * d ^ 2) : ℕ) : ℝ)
           else 0) :=
    Finset.sum_congr rfl (fun d _ => by
      by_cases hc : Nat.Coprime d r
      · rw [if_pos hc, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun m _ => by rw [if_pos hc]; ring)
      · simp [hc])
  have S9 : (∑ d ∈ Finset.Icc 1 X, ∑ m₀ ∈ r.divisors,
          (if Nat.Coprime d r then
            (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius m₀ : ℝ)
              * ((X / (m₀ * d ^ 2) : ℕ) : ℝ)
           else 0))
      = ∑ m₀ ∈ r.divisors, ∑ d ∈ Finset.Icc 1 X,
          (if Nat.Coprime d r then
            (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius m₀ : ℝ)
              * ((X / (m₀ * d ^ 2) : ℕ) : ℝ)
           else 0) :=
    Finset.sum_comm
  have S10 : (∑ m₀ ∈ r.divisors, ∑ d ∈ Finset.Icc 1 X,
          (if Nat.Coprime d r then
            (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius m₀ : ℝ)
              * ((X / (m₀ * d ^ 2) : ℕ) : ℝ)
           else 0))
      = ∑ m₀ ∈ r.divisors, (ArithmeticFunction.moebius m₀ : ℝ) *
          ∑ d ∈ Finset.Icc 1 X,
            (if Nat.Coprime d r then
              (ArithmeticFunction.moebius d : ℝ) * ((X / (m₀ * d ^ 2) : ℕ) : ℝ)
             else 0) :=
    Finset.sum_congr rfl (fun m₀ _ => by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      by_cases hc : Nat.Coprime d r
      · rw [if_pos hc, if_pos hc]; ring
      · rw [if_neg hc, if_neg hc, mul_zero])
  have S11 : (∑ m₀ ∈ r.divisors, (ArithmeticFunction.moebius m₀ : ℝ) *
          ∑ d ∈ Finset.Icc 1 X,
            (if Nat.Coprime d r then
              (ArithmeticFunction.moebius d : ℝ) * ((X / (m₀ * d ^ 2) : ℕ) : ℝ)
             else 0))
      = ∑ m₀ ∈ r.divisors, (ArithmeticFunction.moebius m₀ : ℝ) *
          ∑ m₂ ∈ (Finset.Icc 1 X).filter (fun m₂ => Nat.Coprime m₂ r),
            (ArithmeticFunction.moebius m₂ : ℝ) * (((X / (m₀ * m₂ ^ 2)) : ℕ) : ℝ) :=
    Finset.sum_congr rfl (fun m₀ _ => by rw [← Finset.sum_filter])
  rw [S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11]

end Work.LinnikAreas.Density4
