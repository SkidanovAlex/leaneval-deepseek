import Mathlib

namespace Work.KMTPlan.A6

open scoped BigOperators

/-- If a nonnegative real series has all its partial sums bounded by `B`, then its sum is at
most `B`. -/
private lemma tsum_le_of_sum_le {f : ℕ → ℝ} {B : ℝ}
    (hf : Summable f) (h : ∀ n, ∑ i ∈ Finset.range n, f i ≤ B) : ∑' i, f i ≤ B :=
  le_of_tendsto_of_tendsto hf.hasSum.tendsto_sum_nat tendsto_const_nhds
    (Filter.Eventually.of_forall h)

/-- For `T, c > 0`, the sum of `1/(T + c|m|)^2` over the integers is at most
`1/T^2 + 2/(cT)`, both for finite subsets of `ℤ` and for the full (summable) series.

The positive-index part is bounded by the telescoping estimate
`1/(T+c(k+1))^2 ≤ (1/c)(1/(T+ck) - 1/(T+c(k+1)))`, whose sum telescopes to `1/(cT)`. -/
theorem sum_inv_sq_linear_int_le (T c : ℝ) (hT : 0 < T) (hc : 0 < c) :
    (∀ u : Finset ℤ, ∑ m ∈ u, 1 / (T + c * |(m : ℝ)|) ^ 2 ≤ 1 / T ^ 2 + 2 / (c * T)) ∧
    (Summable (fun m : ℤ => 1 / (T + c * |(m : ℝ)|) ^ 2) ∧
      (∑' m : ℤ, 1 / (T + c * |(m : ℝ)|) ^ 2) ≤ 1 / T ^ 2 + 2 / (c * T)) := by
  set p : ℕ → ℝ := fun k => 1 / (T + c * (k:ℝ))^2 with hp
  set g : ℕ → ℝ := fun k => 1 / (T + c * (k:ℝ)) with hg
  have hp_nonneg : ∀ k, 0 ≤ p k := by intro k; rw [hp]; positivity
  have hp0 : p 0 = 1/T^2 := by rw [hp]; norm_num
  -- The telescoping inequality for one step.
  have htel : ∀ k, p (k+1) ≤ (1/c) * (g k - g (k+1)) := by
    intro k
    rw [hp, hg]
    have hx : 0 < T + c * (k:ℝ) := by positivity
    have hy : 0 < T + c * ((k+1:ℕ):ℝ) := by positivity
    have hle : T + c * (k:ℝ) ≤ T + c * ((k+1:ℕ):ℝ) := by
      push_cast; nlinarith [hc.le]
    have hkey : 1 / (T + c*((k+1:ℕ):ℝ))^2
        ≤ 1 / ((T + c*(k:ℝ)) * (T + c*((k+1:ℕ):ℝ))) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith [hx, hle])
    have heq : 1 / ((T + c*(k:ℝ)) * (T + c*((k+1:ℕ):ℝ)))
        = (1/c) * (1/(T+c*(k:ℝ)) - 1/(T+c*((k+1:ℕ):ℝ))) := by
      field_simp
      push_cast
      ring
    exact hkey.trans_eq heq
  have hg0 : g 0 = 1/T := by rw [hg]; norm_num
  have hgM : ∀ M, g M = 1/(T + c*(M:ℝ)) := by intro M; rw [hg]
  -- Summing the telescoping inequality.
  have hsum_tel : ∀ M, ∑ k ∈ Finset.range M, p (k+1) ≤ 1/(c*T) := by
    intro M
    calc ∑ k ∈ Finset.range M, p (k+1)
        ≤ ∑ k ∈ Finset.range M, (1/c) * (g k - g (k+1)) :=
          Finset.sum_le_sum (fun k _ => htel k)
      _ = (1/c) * (g 0 - g M) := by rw [← Finset.mul_sum, Finset.sum_range_sub']
      _ = (1/c) * (1/T - 1/(T + c*(M:ℝ))) := by rw [hg0, hgM]
      _ ≤ 1/(c*T) := by
          have hgm : 0 ≤ 1 / (T + c * (M:ℝ)) := by positivity
          have hle : 1/T - 1/(T + c*(M:ℝ)) ≤ 1/T := by linarith
          calc (1/c) * (1/T - 1/(T + c*(M:ℝ))) ≤ (1/c) * (1/T) :=
                mul_le_mul_of_nonneg_left hle (by positivity)
            _ = 1/(c*T) := by ring
  -- Partial sums of `p`.
  have hpartial : ∀ n : ℕ, ∑ k ∈ Finset.range n, p k ≤ 1/T^2 + 1/(c*T) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn]; simp; positivity
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      rw [Finset.sum_range_succ']
      show ∑ k ∈ Finset.range m, p (k+1) + p 0 ≤ 1/T^2 + 1/(c*T)
      calc ∑ k ∈ Finset.range m, p (k+1) + p 0
          ≤ 1/(c*T) + 1/T^2 := by
            have h1 := hsum_tel m
            have h2 := hp0
            linarith
        _ = 1/T^2 + 1/(c*T) := by ring
  -- Summability of `p`.
  have hp_summable : Summable p := by
    set d : ℝ := min T c with hd
    have hdpos : 0 < d := by rw [hd]; exact lt_min hT hc
    have hdleT : d ≤ T := by rw [hd]; exact min_le_left _ _
    have hdlc : d ≤ c := by rw [hd]; exact min_le_right _ _
    have hbound : ∀ k, p k ≤ (d^2)⁻¹ * (((k+1:ℕ):ℝ)^2)⁻¹ := by
      intro k
      rw [hp]
      have hk1 : (0:ℝ) < ((k+1:ℕ):ℝ) := by positivity
      have hk : (0:ℝ) ≤ (k:ℝ) := by positivity
      have hle : d * ((k+1:ℕ):ℝ) ≤ T + c * (k:ℝ) := by
        push_cast
        nlinarith [hdleT, hdlc, hk, hdpos]
      have hpos : 0 < d * ((k+1:ℕ):ℝ) := mul_pos hdpos hk1
      have hsq : (d * ((k+1:ℕ):ℝ))^2 ≤ (T + c*(k:ℝ))^2 := pow_le_pow_left₀ hpos.le hle 2
      have hgoal : (1:ℝ) / (d * ((k+1:ℕ):ℝ))^2 = (d^2)⁻¹ * (((k+1:ℕ):ℝ)^2)⁻¹ := by
        rw [one_div, mul_pow, mul_inv]
      exact (one_div_le_one_div_of_le (by positivity) hsq).trans_eq hgoal
    have hs : Summable (fun k : ℕ => (((k+1:ℕ):ℝ)^2)⁻¹) :=
      (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num))
    exact Summable.of_nonneg_of_le hp_nonneg hbound (hs.mul_left _)
  have htsum_p : ∑' k : ℕ, p k ≤ 1/T^2 + 1/(c*T) := tsum_le_of_sum_le hp_summable hpartial
  have htail_summable : Summable (fun k : ℕ => p (k+1)) := (summable_nat_add_iff 1).mpr hp_summable
  have htail : ∑' k : ℕ, p (k+1) ≤ 1/(c*T) := tsum_le_of_sum_le htail_summable hsum_tel
  -- Pass to `ℤ`.
  set f : ℤ → ℝ := fun m => 1 / (T + c * |(m:ℝ)|)^2 with hf
  have hfm : ∀ m : ℤ, f m = p m.natAbs := by
    intro m
    simp only [hf, hp, Nat.cast_natAbs, Int.cast_abs]
  have hneg_natAbs : ∀ n : ℕ, (-(↑n + 1) : ℤ).natAbs = n + 1 := by intro n; omega
  have hsummable_nat : Summable (fun n : ℕ => f (n:ℤ)) := by
    have he : (fun n : ℕ => f (n:ℤ)) = fun n => p n := by
      funext n
      simp only [hfm, Int.natAbs_natCast]
    rw [he]; exact hp_summable
  have hsummable_neg : Summable (fun n : ℕ => f (-(n+1))) := by
    have he : (fun n : ℕ => f (-(n+1))) = fun n => p (n+1) := by
      funext n
      rw [hfm, hneg_natAbs]
    rw [he]; exact htail_summable
  have hf_summable : Summable f := Summable.of_nat_of_neg_add_one hsummable_nat hsummable_neg
  have h_tsum_f : (∑' m : ℤ, f m) ≤ 1/T^2 + 2/(c*T) := by
    rw [tsum_of_nat_of_neg_add_one hsummable_nat hsummable_neg]
    have e1 : (∑' n : ℕ, f (n:ℤ)) = ∑' n : ℕ, p n :=
      tsum_congr (fun n => by simp only [hfm, Int.natAbs_natCast])
    have e2 : (∑' n : ℕ, f (-(n+1))) = ∑' n : ℕ, p (n+1) :=
      tsum_congr (fun n => by rw [hfm, hneg_natAbs])
    rw [e1, e2]
    calc (∑' n : ℕ, p n) + (∑' n : ℕ, p (n+1))
        ≤ (1/T^2 + 1/(c*T)) + 1/(c*T) := add_le_add htsum_p htail
      _ = 1/T^2 + 2/(c*T) := by ring
  refine ⟨fun u => ?_, hf_summable, h_tsum_f⟩
  exact (hf_summable.sum_le_tsum u (fun m _ => by rw [hf]; positivity)).trans h_tsum_f

end Work.KMTPlan.A6
