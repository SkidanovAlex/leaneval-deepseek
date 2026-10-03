import Mathlib
import Submission.Work.KMTAreas.A7.LacDevHormanderSetup

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Elementary cast helpers -/

lemma loDev_natAbs_cast (z : ℤ) : ((z.natAbs : ℝ)) = |(z : ℝ)| := by
  rw [← Int.cast_natCast, ← Int.abs_eq_natAbs, Int.cast_abs]

/-! ## Lacunary summation -/

lemma loDev_two_pow_mul_lac_le (σ : ℕ → ℕ) (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) (k m : ℕ) :
    2 ^ k * σ m ≤ σ (m + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : 2 ^ (k + 1) * σ m = 2 * (2 ^ k * σ m) := by rw [pow_succ]; ring
      rw [hstep]
      calc 2 * (2 ^ k * σ m) ≤ 2 * σ (m + k) := Nat.mul_le_mul_left 2 ih
        _ ≤ σ (m + k + 1) := hσ2 (m + k)
        _ = σ (m + (k + 1)) := by rw [Nat.add_assoc]

lemma loDev_sum_pow_half_sub_le_two (N : ℕ) (S : Finset ℕ) (hS : ∀ n ∈ S, n ≤ N) :
    ∑ n ∈ S, (1 / 2 : ℝ) ^ (N - n) ≤ 2 := by
  have hsub : S ⊆ Finset.range (N + 1) := by
    intro n hn
    rw [Finset.mem_range]
    have := hS n hn
    omega
  calc ∑ n ∈ S, (1 / 2 : ℝ) ^ (N - n)
      ≤ ∑ n ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ (N - n) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    _ = ∑ i ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ i := by
        have h := Finset.sum_range_reflect (fun i : ℕ => (1 / 2 : ℝ) ^ i) (N + 1)
        simpa [Nat.add_sub_cancel] using h
    _ ≤ 2 := sum_geometric_two_le (N + 1)

lemma loDev_sum_lac_le_two_mul (σ : ℕ → ℕ) (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1))
    {S : Finset ℕ} {T : ℝ} (hT : 0 ≤ T) (hS : ∀ n ∈ S, (σ n : ℝ) ≤ T) :
    ∑ n ∈ S, (σ n : ℝ) ≤ 2 * T := by
  rcases S.eq_empty_or_nonempty with h | h
  · rw [h]
    simp only [Finset.sum_empty]
    linarith
  · obtain ⟨N, hNmem, hNmax⟩ : ∃ N ∈ S, ∀ n ∈ S, n ≤ N :=
      ⟨S.max' h, Finset.max'_mem S h, fun n hn => Finset.le_max' S n hn⟩
    have hkey : ∀ n ∈ S, (σ n : ℝ) ≤ (σ N : ℝ) * (1 / 2 : ℝ) ^ (N - n) := by
      intro n hn
      have hnN : n ≤ N := hNmax n hn
      have hnat := loDev_two_pow_mul_lac_le σ hσ2 (N - n) n
      have hnk : n + (N - n) = N := Nat.add_sub_of_le hnN
      rw [hnk] at hnat
      have hcast : ((2 : ℝ) ^ (N - n)) * (σ n : ℝ) ≤ (σ N : ℝ) := by
        have hc := (Nat.cast_le (α := ℝ)).mpr hnat
        push_cast at hc
        simpa using hc
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (N - n) := by positivity
      have h1 : (σ n : ℝ) ≤ (σ N : ℝ) / (2 : ℝ) ^ (N - n) := by
        rw [le_div_iff₀ hpos, mul_comm]
        exact hcast
      have h2 : (σ N : ℝ) / (2 : ℝ) ^ (N - n)
          = (σ N : ℝ) * (1 / 2 : ℝ) ^ (N - n) := by
        rw [div_eq_mul_inv, one_div, inv_pow]
      rwa [h2] at h1
    calc ∑ n ∈ S, (σ n : ℝ)
        ≤ ∑ n ∈ S, T * (1 / 2 : ℝ) ^ (N - n) := by
          refine Finset.sum_le_sum fun n hn => ?_
          calc (σ n : ℝ) ≤ (σ N : ℝ) * (1 / 2 : ℝ) ^ (N - n) := hkey n hn
            _ ≤ T * (1 / 2 : ℝ) ^ (N - n) :=
                mul_le_mul_of_nonneg_right (hS N hNmem) (by positivity)
      _ = T * ∑ n ∈ S, (1 / 2 : ℝ) ^ (N - n) := by rw [Finset.mul_sum]
      _ ≤ T * 2 := mul_le_mul_of_nonneg_left (loDev_sum_pow_half_sub_le_two N S hNmax) hT
      _ = 2 * T := by ring

lemma loDev_head_sum (σ : ℕ → ℕ) (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) (U : Finset ℕ)
    {T : ℝ} (hT : 0 ≤ T) :
    ∑ n ∈ U.filter (fun n => (σ n : ℝ) ≤ T), (σ n : ℝ) ≤ 2 * T :=
  loDev_sum_lac_le_two_mul σ hσ2 hT (fun n hn => (Finset.mem_filter.mp hn).2)

lemma loDev_geom_sum_sub_le_two (S : Finset ℕ) (n₀ : ℕ) (h : ∀ n ∈ S, n₀ ≤ n) :
    ∑ n ∈ S, (1 / 2 : ℝ) ^ (n - n₀) ≤ 2 := by
  have hinj : Set.InjOn (fun n => n - n₀) (↑S : Set ℕ) := by
    intro x hx y hy hxy
    have hx' : n₀ ≤ x := h x hx
    have hy' : n₀ ≤ y := h y hy
    simp only at hxy
    omega
  rw [← Finset.sum_image hinj]
  have hsummable : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hle : ∑ k ∈ S.image (fun n => n - n₀), (1 / 2 : ℝ) ^ k ≤ ∑' k : ℕ, (1 / 2 : ℝ) ^ k :=
    hsummable.sum_le_tsum _ (fun i _ => by positivity)
  have hval : (∑' k : ℕ, (1 / 2 : ℝ) ^ k) = 2 := by
    rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
    norm_num
  linarith [hle, hval]

lemma loDev_lacunary_sum_one_div_le (σ : ℕ → ℕ) (hσ : ∀ n, 2 * σ n ≤ σ (n + 1))
    (S : Finset ℕ) {c : ℝ} (hc : 0 < c) (hS : ∀ n ∈ S, c ≤ (σ n : ℝ)) :
    ∑ n ∈ S, (1 : ℝ) / (σ n : ℝ) ≤ 2 / c := by
  rcases S.eq_empty_or_nonempty with h | hne
  · rw [h]
    simp only [Finset.sum_empty]
    positivity
  · set n₀ := S.min' hne with hn₀def
    have hn₀mem : n₀ ∈ S := by rw [hn₀def]; exact S.min'_mem hne
    have hmin : ∀ n ∈ S, n₀ ≤ n := by intro n hn; rw [hn₀def]; exact S.min'_le n hn
    have hcn₀ : c ≤ (σ n₀ : ℝ) := hS n₀ hn₀mem
    have hσn₀pos : (0 : ℝ) < (σ n₀ : ℝ) := lt_of_lt_of_le hc hcn₀
    have hgrowth : ∀ n ∈ S, (2 : ℝ) ^ (n - n₀) * (σ n₀ : ℝ) ≤ (σ n : ℝ) := by
      intro n hn
      have hn0n : n₀ ≤ n := hmin n hn
      have hkn : n₀ + (n - n₀) = n := Nat.add_sub_of_le hn0n
      have hnat : 2 ^ (n - n₀) * σ n₀ ≤ σ n := by
        have := loDev_two_pow_mul_lac_le σ hσ (n - n₀) n₀
        rwa [hkn] at this
      have hcast : (((2 ^ (n - n₀) * σ n₀ : ℕ)) : ℝ) ≤ (σ n : ℝ) := by exact_mod_cast hnat
      push_cast at hcast
      exact hcast
    have hterm : ∀ n ∈ S, (1 : ℝ) / (σ n : ℝ) ≤ (1 / 2 : ℝ) ^ (n - n₀) * (1 / (σ n₀ : ℝ)) := by
      intro n hn
      have hkey := hgrowth n hn
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (n - n₀) * (σ n₀ : ℝ) := by positivity
      calc (1 : ℝ) / (σ n : ℝ)
          ≤ 1 / ((2 : ℝ) ^ (n - n₀) * (σ n₀ : ℝ)) := one_div_le_one_div_of_le hpos hkey
        _ = (1 / 2 : ℝ) ^ (n - n₀) * (1 / (σ n₀ : ℝ)) := by
              simp only [one_div, mul_inv, inv_pow]
    have hsum : ∑ n ∈ S, (1 : ℝ) / (σ n : ℝ)
        ≤ (1 / (σ n₀ : ℝ)) * ∑ n ∈ S, (1 / 2 : ℝ) ^ (n - n₀) := by
      calc ∑ n ∈ S, (1 : ℝ) / (σ n : ℝ)
          ≤ ∑ n ∈ S, (1 / 2 : ℝ) ^ (n - n₀) * (1 / (σ n₀ : ℝ)) := Finset.sum_le_sum hterm
        _ = (1 / (σ n₀ : ℝ)) * ∑ n ∈ S, (1 / 2 : ℝ) ^ (n - n₀) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun n _ => by ring)
    calc ∑ n ∈ S, (1 : ℝ) / (σ n : ℝ)
        ≤ (1 / (σ n₀ : ℝ)) * ∑ n ∈ S, (1 / 2 : ℝ) ^ (n - n₀) := hsum
      _ ≤ (1 / (σ n₀ : ℝ)) * 2 :=
          mul_le_mul_of_nonneg_left (loDev_geom_sum_sub_le_two S n₀ hmin) (by positivity)
      _ = 2 / (σ n₀ : ℝ) := by ring
      _ ≤ 2 / c := by
          rw [div_le_div_iff₀ hσn₀pos hc]
          linarith

lemma loDev_tail_sum (σ : ℕ → ℕ) (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) (U : Finset ℕ)
    {T : ℝ} (hT : 0 < T) :
    ∑ n ∈ U.filter (fun n => T < (σ n : ℝ)), (1 : ℝ) / (σ n : ℝ) ≤ 2 / T :=
  loDev_lacunary_sum_one_div_le σ hσ2 _ hT (fun n hn => le_of_lt (Finset.mem_filter.mp hn).2)

theorem loDev_lacSumCubic (σ : ℕ → ℕ) (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) (U : Finset ℕ)
    {T : ℝ} (hT : 0 < T) :
    ∑ n ∈ U, (σ n : ℝ) / ((σ n : ℝ) + T) ^ 3 ≤ 4 / T ^ 2 := by
  have hsplit : ∑ n ∈ U, (σ n : ℝ) / ((σ n : ℝ) + T) ^ 3
      = ∑ n ∈ U.filter (fun n => (σ n : ℝ) ≤ T), (σ n : ℝ) / ((σ n : ℝ) + T) ^ 3
        + ∑ n ∈ U.filter (fun n => ¬ ((σ n : ℝ) ≤ T)),
            (σ n : ℝ) / ((σ n : ℝ) + T) ^ 3 :=
    (Finset.sum_filter_add_sum_filter_not U (fun n => (σ n : ℝ) ≤ T)
      (fun n => (σ n : ℝ) / ((σ n : ℝ) + T) ^ 3)).symm
  rw [hsplit]
  have h1 : ∑ n ∈ U.filter (fun n => (σ n : ℝ) ≤ T), (σ n : ℝ) / ((σ n : ℝ) + T) ^ 3
      ≤ 2 / T ^ 2 := by
    have hb : ∑ n ∈ U.filter (fun n => (σ n : ℝ) ≤ T), (σ n : ℝ) ≤ 2 * T :=
      loDev_head_sum σ hσ2 U hT.le
    calc ∑ n ∈ U.filter (fun n => (σ n : ℝ) ≤ T), (σ n : ℝ) / ((σ n : ℝ) + T) ^ 3
        ≤ ∑ n ∈ U.filter (fun n => (σ n : ℝ) ≤ T), (σ n : ℝ) / T ^ 3 := by
          refine Finset.sum_le_sum fun n _ => ?_
          refine div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) ?_
          exact pow_le_pow_left₀ hT.le (by linarith) 3
      _ = (∑ n ∈ U.filter (fun n => (σ n : ℝ) ≤ T), (σ n : ℝ)) / T ^ 3 := by
          rw [Finset.sum_div]
      _ ≤ (2 * T) / T ^ 3 := by
          rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < T ^ 3)
            (by positivity : (0 : ℝ) < T ^ 3)]
          exact mul_le_mul_of_nonneg_right hb (by positivity)
      _ = 2 / T ^ 2 := by first | (field_simp; ring) | field_simp
  have h2 : ∑ n ∈ U.filter (fun n => ¬ ((σ n : ℝ) ≤ T)), (σ n : ℝ) / ((σ n : ℝ) + T) ^ 3
      ≤ 2 / T ^ 2 := by
    have hfilter : U.filter (fun n => ¬ ((σ n : ℝ) ≤ T)) = U.filter (fun n => T < (σ n : ℝ)) :=
      Finset.filter_congr (fun n _ => not_le)
    have hb : ∑ n ∈ U.filter (fun n => ¬ ((σ n : ℝ) ≤ T)), (1 : ℝ) / (σ n : ℝ) ≤ 2 / T := by
      rw [hfilter]
      exact loDev_tail_sum σ hσ2 U hT
    calc ∑ n ∈ U.filter (fun n => ¬ ((σ n : ℝ) ≤ T)), (σ n : ℝ) / ((σ n : ℝ) + T) ^ 3
        ≤ ∑ n ∈ U.filter (fun n => ¬ ((σ n : ℝ) ≤ T)), (1 / T) * (1 / (σ n : ℝ)) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hTn : T < (σ n : ℝ) := not_le.mp (Finset.mem_filter.mp hn).2
          have hσnpos : (0 : ℝ) < (σ n : ℝ) := lt_trans hT hTn
          have hstep1 : (σ n : ℝ) / ((σ n : ℝ) + T) ^ 3 ≤ (σ n : ℝ) / ((σ n : ℝ)) ^ 3 := by
            refine div_le_div_of_nonneg_left hσnpos.le (pow_pos hσnpos 3) ?_
            exact pow_le_pow_left₀ hσnpos.le (by linarith) 3
          have hstep2 : (σ n : ℝ) / ((σ n : ℝ)) ^ 3 = 1 / ((σ n : ℝ)) ^ 2 := by
            field_simp
          have hstep3 : (1 : ℝ) / ((σ n : ℝ)) ^ 2 ≤ (1 / T) * (1 / (σ n : ℝ)) := by
            have hh1 : (1 : ℝ) / (σ n : ℝ) ≤ 1 / T := one_div_le_one_div_of_le hT hTn.le
            have hh2 : (0 : ℝ) ≤ 1 / (σ n : ℝ) := by positivity
            calc (1 : ℝ) / ((σ n : ℝ)) ^ 2 = (1 / (σ n : ℝ)) * (1 / (σ n : ℝ)) := by ring
              _ ≤ (1 / (σ n : ℝ)) * (1 / T) := mul_le_mul_of_nonneg_left hh1 hh2
              _ = (1 / T) * (1 / (σ n : ℝ)) := by ring
          calc (σ n : ℝ) / ((σ n : ℝ) + T) ^ 3
              ≤ (σ n : ℝ) / ((σ n : ℝ)) ^ 3 := hstep1
            _ = 1 / ((σ n : ℝ)) ^ 2 := hstep2
            _ ≤ (1 / T) * (1 / (σ n : ℝ)) := hstep3
      _ = (1 / T) * ∑ n ∈ U.filter (fun n => ¬ ((σ n : ℝ) ≤ T)), (1 : ℝ) / (σ n : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (1 / T) * (2 / T) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 2 / T ^ 2 := by first | (field_simp; ring) | field_simp
  have h4 : (4 : ℝ) / T ^ 2 = 2 / T ^ 2 + 2 / T ^ 2 := by ring
  rw [h4]
  linarith [h1, h2]

/-! ## Algebra for the scale substitution -/

lemma loDev_rpow_neg_three (m Z : ℝ) (hm : 0 < m) (hZ : 0 ≤ Z) :
    (1 + Z / m) ^ (-3 : ℝ) = m ^ 3 / (m + Z) ^ 3 := by
  have h1 : 1 + Z / m = (m + Z) / m := by field_simp
  have hpos : (0 : ℝ) < (m + Z) / m := by positivity
  rw [h1, show (-3 : ℝ) = -((3 : ℕ) : ℝ) from by norm_num, Real.rpow_neg hpos.le,
    Real.rpow_natCast, div_pow, inv_div]

lemma loDev_algebra (m Y Z B : ℝ) (hm : 0 < m) (hZ : 0 ≤ Z) :
    (1 / m) * (B * ((1 + Z / m) ^ (-3 : ℝ)) * (Y / m)) = B * Y * (m / (m + Z) ^ 3) := by
  rw [loDev_rpow_neg_three m Z hm hZ]
  first | (field_simp; ring) | field_simp

lemma loDev_algebra2 (m Y Z : ℝ) (hm : 0 < m) (hZ : 0 ≤ Z) :
    ((1 + Z / m) ^ (-3 : ℝ)) * Y / m ^ 2 = Y * (m / (m + Z) ^ 3) := by
  rw [loDev_rpow_neg_three m Z hm hZ]
  first | (field_simp; ring) | field_simp

/-! ## The Schwartz decay of the derivative -/

lemma loDev_deriv_decay (K : SchwartzMap ℝ ℂ) :
    ∃ A : ℝ, 0 < A ∧ ∀ w : ℝ, ‖deriv (K : ℝ → ℂ) w‖ ≤ A * (1 + |w|) ^ (-3 : ℝ) := by
  obtain ⟨A, hA, h⟩ :=
    Commons.Analysis.Fourier.schwartz_decay_real (SchwartzMap.derivCLM ℂ ℂ K) 3
  refine ⟨A, hA, fun w => ?_⟩
  have h' := h w
  rw [SchwartzMap.derivCLM_apply] at h'
  exact h'

/-! ## The bump part of the deviation kernel -/

lemma loDev_bump_osc_le (K : SchwartzMap ℝ ℂ) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ w : ℝ, ‖deriv (K : ℝ → ℂ) w‖ ≤ A * (1 + |w|) ^ (-3 : ℝ))
    (m : ℕ) (hm : 1 ≤ m) (y z : ℤ) (hyz : 2 * y.natAbs ≤ z.natAbs) :
    ‖bumpKernM K m (z - y) - bumpKernM K m z‖
      ≤ 8 * A * (y.natAbs : ℝ) * ((m : ℝ) / (((m : ℝ)) + ((z.natAbs : ℝ))) ^ 3) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hY : (0 : ℝ) ≤ (y.natAbs : ℝ) := Nat.cast_nonneg _
  have hZ : (0 : ℝ) ≤ (z.natAbs : ℝ) := Nat.cast_nonneg _
  set u : ℝ := (((z - y : ℤ)) : ℝ) / (m : ℝ) with hu
  set v : ℝ := ((z : ℤ) : ℝ) / (m : ℝ) with hv
  have hvabs : |v| = (z.natAbs : ℝ) / (m : ℝ) := by
    rw [hv, abs_div, abs_of_pos hmpos, loDev_natAbs_cast]
  have huvabs : |u - v| = (y.natAbs : ℝ) / (m : ℝ) := by
    have hsub : u - v = -(((y : ℤ)) : ℝ) / (m : ℝ) := by
      rw [hu, hv, ← sub_div]
      congr 1
      push_cast
      ring
    rw [hsub, abs_div, abs_neg, abs_of_pos hmpos, loDev_natAbs_cast]
  have hsmall : |u - v| ≤ |v| / 2 := by
    rw [huvabs, hvabs, div_div]
    rw [div_le_div_iff₀ hmpos (by positivity : (0 : ℝ) < (m : ℝ) * 2)]
    have h3 : (2 * (y.natAbs : ℝ)) ≤ (z.natAbs : ℝ) := by exact_mod_cast hyz
    nlinarith [h3, hmpos]
  set a : ℝ := min u v with ha
  set b : ℝ := max u v with hb
  have hab : a ≤ b := min_le_max
  have hderiv : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt (K : ℝ → ℂ) (deriv (K : ℝ → ℂ) t) (Set.Icc a b) t :=
    fun t _ => ((K.differentiable.differentiableAt).hasDerivAt).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico a b,
      ‖deriv (K : ℝ → ℂ) t‖ ≤ 8 * A * (1 + |v|) ^ (-3 : ℝ) := by
    intro t ht
    have htI : t ∈ Set.Icc a b := Set.Ico_subset_Icc_self ht
    have h1 : t ≤ max u v := by rw [ha, hb] at htI; exact htI.2
    have h2 : min u v ≤ t := by rw [ha, hb] at htI; exact htI.1
    have htv : |t - v| ≤ |u - v| := by
      have hlow : min u v ≤ v := min_le_right u v
      have hup : v ≤ max u v := le_max_right u v
      have hmaxmin : max u v - min u v = |u - v| := by
        rw [max_sub_min_eq_abs, abs_sub_comm]
      rw [abs_sub_le_iff]
      exact ⟨by linarith, by linarith⟩
    have htge : |v| / 2 ≤ |t| := by
      have h3 : |v| - |t| ≤ |v - t| := abs_sub_abs_le_abs_sub v t
      rw [abs_sub_comm] at h3
      linarith [htv, hsmall]
    have hA1 : (1 / 2) * (1 + |v|) ≤ 1 + |v| / 2 := by linarith [abs_nonneg v]
    have hpos1 : (0 : ℝ) < 1 + |v| / 2 := by positivity
    have h8 : ((1 : ℝ) / 2) ^ (-3 : ℝ) = 8 := by
      rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) from by norm_num, Real.rpow_neg (by norm_num),
        Real.rpow_natCast]
      norm_num
    calc ‖deriv (K : ℝ → ℂ) t‖ ≤ A * (1 + |t|) ^ (-3 : ℝ) := hA t
      _ ≤ A * (8 * (1 + |v|) ^ (-3 : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hA0
          calc (1 + |t|) ^ (-3 : ℝ) ≤ (1 + |v| / 2) ^ (-3 : ℝ) :=
                Real.rpow_le_rpow_of_nonpos hpos1 (by linarith) (by norm_num)
            _ ≤ ((1 / 2) * (1 + |v|)) ^ (-3 : ℝ) :=
                Real.rpow_le_rpow_of_nonpos (by positivity) hA1 (by norm_num)
            _ = 8 * (1 + |v|) ^ (-3 : ℝ) := by
                rw [Real.mul_rpow (by norm_num) (by positivity), h8]
      _ = 8 * A * (1 + |v|) ^ (-3 : ℝ) := by ring
  have hMVT : ‖(K : ℝ → ℂ) b - (K : ℝ → ℂ) a‖
      ≤ (8 * A * (1 + |v|) ^ (-3 : ℝ)) * (b - a) :=
    norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound b (Set.right_mem_Icc.mpr hab)
  have hsub2 : ‖(K : ℝ → ℂ) u - (K : ℝ → ℂ) v‖ = ‖(K : ℝ → ℂ) b - (K : ℝ → ℂ) a‖ := by
    rcases le_total u v with h | h
    · rw [hb, ha, max_eq_right h, min_eq_left h, norm_sub_rev]
    · rw [hb, ha, max_eq_left h, min_eq_right h]
  have hba : b - a = |u - v| := by
    rcases le_total u v with h | h
    · rw [hb, ha, max_eq_right h, min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [hb, ha, max_eq_left h, min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
  have hKuv : ‖(K : ℝ → ℂ) u - (K : ℝ → ℂ) v‖
      ≤ 8 * A * (1 + |v|) ^ (-3 : ℝ) * |u - v| := by
    rw [hsub2, ← hba]
    exact hMVT
  have hKeq : bumpKernM K m (z - y) - bumpKernM K m z
      = (1 : ℂ) / (((m : ℝ)) : ℂ) * ((K : ℝ → ℂ) u - (K : ℝ → ℂ) v) := by
    unfold bumpKernM
    rw [hu, hv]
    ring
  have hcoef : ‖(1 : ℂ) / (((m : ℝ)) : ℂ)‖ = 1 / (m : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg m)]
  calc ‖bumpKernM K m (z - y) - bumpKernM K m z‖
      = (1 / (m : ℝ)) * ‖(K : ℝ → ℂ) u - (K : ℝ → ℂ) v‖ := by
        rw [hKeq, norm_mul, hcoef]
    _ ≤ (1 / (m : ℝ)) * (8 * A * (1 + |v|) ^ (-3 : ℝ) * |u - v|) :=
        mul_le_mul_of_nonneg_left hKuv (by positivity)
    _ = 8 * A * (y.natAbs : ℝ) * ((m : ℝ) / (((m : ℝ)) + ((z.natAbs : ℝ))) ^ 3) := by
        rw [huvabs, hvabs]
        exact loDev_algebra (m : ℝ) (y.natAbs : ℝ) (z.natAbs : ℝ) (8 * A) hmpos hZ

/-! ## The triangular part of the deviation kernel -/

lemma loDev_tri_osc_le (K : SchwartzMap ℝ ℂ) (m : ℕ) (hm : 1 ≤ m) (y z : ℤ)
    (hyz : 2 * y.natAbs ≤ z.natAbs) :
    ‖lacConst K * (((Work.Analysis.Hilbert.triKernel (lacLevN m) (z - y)
        - Work.Analysis.Hilbert.triKernel (lacLevN m) z : ℝ)) : ℂ)‖
      ≤ (500 * ‖lacConst K‖ + 1) * (y.natAbs : ℝ)
          * ((m : ℝ) / (((m : ℝ)) + ((z.natAbs : ℝ))) ^ 3) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hY : (0 : ℝ) ≤ (y.natAbs : ℝ) := Nat.cast_nonneg _
  have hZ : (0 : ℝ) ≤ (z.natAbs : ℝ) := Nat.cast_nonneg _
  have hL : (2 : ℕ) ^ (lacLevN m) ≤ 2 * m := pow_lacLevN_le hm
  have hfour : (m : ℝ) ^ 2 / 4 ≤ (4 : ℝ) ^ (lacLevN m) := sq_div_four_le_pow_four_lacLevN m
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hXnn : (0 : ℝ) ≤ (y.natAbs : ℝ) * ((m : ℝ) / (((m : ℝ)) + ((z.natAbs : ℝ))) ^ 3) :=
    mul_nonneg hY (by positivity)
  have hcast2 : ((2 : ℕ) ^ (lacLevN m) : ℝ) = (2 : ℝ) ^ (lacLevN m) := by push_cast; ring
  have hcastz : (((2 : ℤ) ^ (lacLevN m) : ℤ) : ℝ) = (2 : ℝ) ^ (lacLevN m) := by push_cast; ring
  have hbase : ((2 : ℕ) ^ (lacLevN m) : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hL
  by_cases hcase : (z.natAbs : ℝ) ≤ 4 * (m : ℝ)
  · have hlip : |Work.Analysis.Hilbert.triKernel (lacLevN m) (z - y)
        - Work.Analysis.Hilbert.triKernel (lacLevN m) z|
        ≤ 4 * (y.natAbs : ℝ) / (m : ℝ) ^ 2 := by
      have h := triKernel_lip (lacLevN m) (z - y) z
      have hnum : |((z - y : ℤ) : ℝ) - ((z : ℤ) : ℝ)| = (y.natAbs : ℝ) := by
        rw [show ((z - y : ℤ) : ℝ) - ((z : ℤ) : ℝ) = -(((y : ℤ)) : ℝ) by push_cast; ring,
          abs_neg, loDev_natAbs_cast]
      rw [hnum] at h
      calc |Work.Analysis.Hilbert.triKernel (lacLevN m) (z - y)
            - Work.Analysis.Hilbert.triKernel (lacLevN m) z|
          ≤ (y.natAbs : ℝ) / (4 : ℝ) ^ (lacLevN m) := h
        _ ≤ (y.natAbs : ℝ) / ((m : ℝ) ^ 2 / 4) :=
            div_le_div_of_nonneg_left hY (by positivity) hfour
        _ = 4 * (y.natAbs : ℝ) / (m : ℝ) ^ 2 := by first | (field_simp; ring) | field_simp
    have hpow : (1 : ℝ) ≤ 125 * (1 + (z.natAbs : ℝ) / (m : ℝ)) ^ (-3 : ℝ) := by
      have h5 : 1 + (z.natAbs : ℝ) / (m : ℝ) ≤ 5 := by
        have h5' : (z.natAbs : ℝ) / (m : ℝ) ≤ 4 := by
          rw [div_le_iff₀ hmpos]
          linarith
        linarith
      have hcube : (1 + (z.natAbs : ℝ) / (m : ℝ)) ^ 3 ≤ 125 := by
        calc (1 + (z.natAbs : ℝ) / (m : ℝ)) ^ 3 ≤ (5 : ℝ) ^ 3 :=
              pow_le_pow_left₀ (by positivity) h5 3
          _ = 125 := by norm_num
      rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) from by norm_num,
        Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + (z.natAbs : ℝ) / (m : ℝ)),
        Real.rpow_natCast, ← div_eq_mul_inv]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 + (z.natAbs : ℝ) / (m : ℝ)) ^ 3)]
      linarith
    have hstep : (y.natAbs : ℝ) / (m : ℝ) ^ 2
        ≤ 125 * ((1 + (z.natAbs : ℝ) / (m : ℝ)) ^ (-3 : ℝ) * (y.natAbs : ℝ)
            / (m : ℝ) ^ 2) := by
      have hY2 : (0 : ℝ) ≤ (y.natAbs : ℝ) / (m : ℝ) ^ 2 := by positivity
      have h := mul_le_mul_of_nonneg_right hpow hY2
      simp only [one_mul] at h
      have h2 : 125 * (1 + (z.natAbs : ℝ) / (m : ℝ)) ^ (-3 : ℝ)
            * ((y.natAbs : ℝ) / (m : ℝ) ^ 2)
          = 125 * ((1 + (z.natAbs : ℝ) / (m : ℝ)) ^ (-3 : ℝ) * (y.natAbs : ℝ)
              / (m : ℝ) ^ 2) := by ring
      rw [h2] at h
      exact h
    have hstep' : 4 * ((y.natAbs : ℝ) / (m : ℝ) ^ 2)
        ≤ 500 * ((y.natAbs : ℝ) * ((m : ℝ) / (((m : ℝ)) + ((z.natAbs : ℝ))) ^ 3)) := by
      have h := mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 4)
      rw [loDev_algebra2 (m : ℝ) (y.natAbs : ℝ) (z.natAbs : ℝ) hmpos hZ] at h
      nlinarith [h]
    have h4 : 4 * (y.natAbs : ℝ) / (m : ℝ) ^ 2 = 4 * ((y.natAbs : ℝ) / (m : ℝ) ^ 2) := by ring
    calc ‖lacConst K‖ * |Work.Analysis.Hilbert.triKernel (lacLevN m) (z - y)
          - Work.Analysis.Hilbert.triKernel (lacLevN m) z|
        ≤ ‖lacConst K‖ * (4 * (y.natAbs : ℝ) / (m : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hlip (norm_nonneg _)
      _ ≤ ‖lacConst K‖ * (500 * ((y.natAbs : ℝ)
            * ((m : ℝ) / (((m : ℝ)) + ((z.natAbs : ℝ))) ^ 3))) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [h4]
          exact hstep'
      _ = (500 * ‖lacConst K‖) * ((y.natAbs : ℝ)
            * ((m : ℝ) / (((m : ℝ)) + ((z.natAbs : ℝ))) ^ 3)) := by ring
      _ ≤ (500 * ‖lacConst K‖ + 1) * ((y.natAbs : ℝ)
            * ((m : ℝ) / (((m : ℝ)) + ((z.natAbs : ℝ))) ^ 3)) := by
          nlinarith [hXnn, norm_nonneg (lacConst K)]
      _ = (500 * ‖lacConst K‖ + 1) * (y.natAbs : ℝ)
            * ((m : ℝ) / (((m : ℝ)) + ((z.natAbs : ℝ))) ^ 3) := by ring
  · have hcase' : 4 * (m : ℝ) < (z.natAbs : ℝ) := not_le.mp hcase
    have hfar (j : ℤ) (hj : ((2 : ℕ) ^ (lacLevN m) : ℝ) < ((j.natAbs : ℝ))) :
        Work.Analysis.Hilbert.triKernel (lacLevN m) j = 0 := by
      refine triKernel_eq_zero_of_abs (lacLevN m) ?_
      rw [hcastz, ← hcast2, ← loDev_natAbs_cast j]
      exact hj
    have hz0 : Work.Analysis.Hilbert.triKernel (lacLevN m) z = 0 := by
      refine hfar z ?_
      linarith
    have hzy : Work.Analysis.Hilbert.triKernel (lacLevN m) (z - y) = 0 := by
      refine hfar (z - y) ?_
      have htri : (z.natAbs : ℝ) ≤ ((z - y).natAbs : ℝ) + (y.natAbs : ℝ) := by
        have h := Int.natAbs_add_le (z - y) y
        have hcast := (Nat.cast_le (α := ℝ)).mpr h
        push_cast at hcast
        simpa using hcast
      have hy2 : (y.natAbs : ℝ) ≤ (z.natAbs : ℝ) / 2 := by
        have h3 : (2 * (y.natAbs : ℝ)) ≤ (z.natAbs : ℝ) := by exact_mod_cast hyz
        linarith
      linarith
    rw [hz0, hzy]
    simp only [sub_zero, abs_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _)) (by positivity)

/-! ## The single-scale difference bound -/

theorem loDev_singleScaleDiff (K : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (y z : ℤ), 2 * y.natAbs ≤ z.natAbs →
      ‖devKernM K m (z - y) - devKernM K m z‖
        ≤ C * (y.natAbs : ℝ) * ((m : ℝ) / (((m : ℝ)) + ((z.natAbs : ℝ))) ^ 3) := by
  obtain ⟨A, hApos, hA⟩ := loDev_deriv_decay K
  refine ⟨8 * A + 500 * ‖lacConst K‖ + 1, by positivity, ?_⟩
  intro m hm y z hyz
  have hbump := loDev_bump_osc_le K hApos.le hA m hm y z hyz
  have htri := loDev_tri_osc_le K m hm y z hyz
  have hdec : devKernM K m (z - y) - devKernM K m z
      = (bumpKernM K m (z - y) - bumpKernM K m z)
        - lacConst K * (((Work.Analysis.Hilbert.triKernel (lacLevN m) (z - y)
            - Work.Analysis.Hilbert.triKernel (lacLevN m) z : ℝ)) : ℂ) := by
    unfold devKernM
    push_cast
    ring
  rw [hdec]
  calc ‖(bumpKernM K m (z - y) - bumpKernM K m z)
        - lacConst K * (((Work.Analysis.Hilbert.triKernel (lacLevN m) (z - y)
            - Work.Analysis.Hilbert.triKernel (lacLevN m) z : ℝ)) : ℂ)‖
      ≤ ‖bumpKernM K m (z - y) - bumpKernM K m z‖
        + ‖lacConst K * (((Work.Analysis.Hilbert.triKernel (lacLevN m) (z - y)
            - Work.Analysis.Hilbert.triKernel (lacLevN m) z : ℝ)) : ℂ)‖ := norm_sub_le _ _
    _ ≤ 8 * A * (y.natAbs : ℝ) * ((m : ℝ) / (((m : ℝ)) + ((z.natAbs : ℝ))) ^ 3)
        + (500 * ‖lacConst K‖ + 1) * (y.natAbs : ℝ)
            * ((m : ℝ) / (((m : ℝ)) + ((z.natAbs : ℝ))) ^ 3) :=
        add_le_add hbump htri
    _ = (8 * A + 500 * ‖lacConst K‖ + 1) * (y.natAbs : ℝ)
          * ((m : ℝ) / (((m : ℝ)) + ((z.natAbs : ℝ))) ^ 3) := by ring

/-! ## The multi-scale pointwise bound -/

lemma loDev_pointwise (K : SchwartzMap ℝ ℂ) {C : ℝ} (hC : 0 < C)
    (hCb : ∀ (m : ℕ), 1 ≤ m → ∀ (y z : ℤ), 2 * y.natAbs ≤ z.natAbs →
      ‖devKernM K m (z - y) - devKernM K m z‖
        ≤ C * (y.natAbs : ℝ) * ((m : ℝ) / (((m : ℝ)) + ((z.natAbs : ℝ))) ^ 3))
    (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n) (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1))
    (U : Finset ℕ) (ω : ℕ → Bool) (y x : ℤ) (hy : y ≠ 0) (hx : 2 * y.natAbs ≤ x.natAbs) :
    ‖lacDevLin K σ U ω (x - y) - lacDevLin K σ U ω x‖
      ≤ (2 * C) * (2 * (y.natAbs : ℝ)) / ((x.natAbs : ℝ)) ^ 2 := by
  have hy1 : 1 ≤ y.natAbs := by
    have := Int.natAbs_pos.mpr hy
    omega
  have hxpos : (0 : ℝ) < (x.natAbs : ℝ) := by
    have : 0 < x.natAbs := by omega
    exact_mod_cast this
  have hdiff : lacDevLin K σ U ω (x - y) - lacDevLin K σ U ω x
      = ∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n
          * (devKern K σ n (x - y) - devKern K σ n x) := by
    rw [lacDevLin, lacDevLin, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hdiff]
  calc ‖∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n
          * (devKern K σ n (x - y) - devKern K σ n x)‖
      ≤ ∑ n ∈ U, ‖Work.KMTAreas.ADev.bSign ω n
          * (devKern K σ n (x - y) - devKern K σ n x)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ U, ‖devKern K σ n (x - y) - devKern K σ n x‖ := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (Work.KMTAreas.ADev.norm_bSign_le ω n)
    _ ≤ ∑ n ∈ U, C * (y.natAbs : ℝ)
          * (((σ n : ℝ)) / (((σ n : ℝ)) + ((x.natAbs : ℝ))) ^ 3) := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [devKern_eq_devKernM, devKern_eq_devKernM]
        exact hCb (σ n) (hσ1 n) y x hx
    _ = C * (y.natAbs : ℝ)
          * ∑ n ∈ U, (((σ n : ℝ)) / (((σ n : ℝ)) + ((x.natAbs : ℝ))) ^ 3) := by
        rw [Finset.mul_sum]
    _ ≤ C * (y.natAbs : ℝ) * (4 / (x.natAbs : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC.le (Nat.cast_nonneg _))
        exact loDev_lacSumCubic σ hσ2 U hxpos
    _ = (2 * C) * (2 * (y.natAbs : ℝ)) / ((x.natAbs : ℝ)) ^ 2 := by ring

/-! ## The final integral bound -/

lemma loDev_lintegral_majorant (C : ℝ) (hC : 0 ≤ C) {m : ℕ} (hm : 1 ≤ m) :
    (∑' x : ℤ, (if 2 * m ≤ x.natAbs then
        ENNReal.ofReal (C * (2 * (m : ℝ)) / ((x.natAbs : ℝ)) ^ 2) else 0))
      ≤ ENNReal.ofReal (4 * C) := by
  have hstep : (∑' x : ℤ, (if 2 * m ≤ x.natAbs then
        ENNReal.ofReal (C * (2 * (m : ℝ)) / ((x.natAbs : ℝ)) ^ 2) else 0))
      = ENNReal.ofReal C * (∑' x : ℤ, (if 2 * m ≤ x.natAbs then
          ENNReal.ofReal (2 * (m : ℝ) / ((x.natAbs : ℝ)) ^ 2) else 0)) := by
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun x => ?_
    by_cases hx : 2 * m ≤ x.natAbs
    · rw [if_pos hx, if_pos hx, ← ENNReal.ofReal_mul hC]
      congr 1
      ring
    · rw [if_neg hx, if_neg hx, mul_zero]
  rw [hstep]
  calc ENNReal.ofReal C * (∑' x : ℤ, (if 2 * m ≤ x.natAbs then
          ENNReal.ofReal (2 * (m : ℝ) / ((x.natAbs : ℝ)) ^ 2) else 0))
      ≤ ENNReal.ofReal C * ENNReal.ofReal 4 := by
        gcongr
        exact Commons.Analysis.Hilbert.tsum_int_ofReal_natAbs_inv_sq_le m hm
    _ = ENNReal.ofReal (4 * C) := by
        rw [← ENNReal.ofReal_mul hC]
        congr 1
        ring

/-- Discrete Hörmander condition for the linearized deviation kernel: for every Schwartz `K` there
is `C > 0` such that for every `2`-lacunary `σ` (`1 ≤ σ n`, `2 * σ n ≤ σ (n+1)`), every finite `U`,
every sign pattern `ω` and every `y ≠ 0`,
`∫⁻ x in {x : ℤ | 2 * y.natAbs ≤ x.natAbs}, ‖lin (x - y) - lin x‖ ≤ C`
with `lin = lacDevLin K σ U ω = ∑_{n∈U} (if ω n then 1 else -1) * devKern K σ n` and
`devKern K σ n j = (1/σ n) K (j/σ n) - (∫K) * triKernel (lacLev σ n) j`.  This is the exact
statement of the existing `sorry` stub `Work.KMTAreas.A7.lacDevHormander` in
`Submission/Work/KMTAreas/A7/lacDevHormander.lean`, which must NOT be imported or edited; prove it in
YOUR OWN file under the name `LoDevHormander`.  Route: the deviation kernel is band-pass at scale
`σ n` with Schwartz decay `(1/σ n)(1 + |j|/σ n)^{-2}` and vanishing first moment; split the scales
into `σ n ≲ |y|`, `σ n ≈ |y|`, `σ n ≫ |y|` and use the lacunarity (`σ n ≥ 2^n`) to telescope.  The
elementary inputs are the statements of `lacDevHormanderBumpSmooth`,
`lacDevHormanderLacSumLarge/Small`, `lacDevHormanderLintegral`, `lacDevHormanderPair`,
`lacDevHormanderTelescopeA/B`, `lacDevLacSum`, `lacDevLacSumInv` (all `sorry` stubs in the same
directory — prove the versions you need yourself in your own file), together with
`Submission/Work/Analysis/Hilbert/shift_lattice_kernel_identity.lean` and
`Submission.Work.Analysis.CzShift.lacunary_sums`. -/
theorem LoDevHormander (K : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℕ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      ∀ (U : Finset ℕ) (ω : ℕ → Bool) (y : ℤ), y ≠ 0 →
        ∫⁻ x in {x : ℤ | 2 * y.natAbs ≤ x.natAbs},
            ‖Work.KMTAreas.A7.lacDevLin K σ U ω (x - y) - Work.KMTAreas.A7.lacDevLin K σ U ω x‖ₑ
          ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hCpos, hCb⟩ := loDev_singleScaleDiff K
  refine ⟨8 * C, by linarith, ?_⟩
  intro σ hσ1 hσ2 U ω y hy
  have hy1 : 1 ≤ y.natAbs := by
    have := Int.natAbs_pos.mpr hy
    omega
  have hSmeas : MeasurableSet {x : ℤ | 2 * y.natAbs ≤ x.natAbs} :=
    Set.Countable.measurableSet (Set.to_countable _)
  have hpt : ∀ x ∈ {x : ℤ | 2 * y.natAbs ≤ x.natAbs},
      ‖lacDevLin K σ U ω (x - y) - lacDevLin K σ U ω x‖
        ≤ (2 * C) * (2 * (y.natAbs : ℝ)) / ((x.natAbs : ℝ)) ^ 2 :=
    fun x hx => loDev_pointwise K hCpos hCb σ hσ1 hσ2 U ω y x hy (by simpa using hx)
  have hmain : ∫⁻ x in {x : ℤ | 2 * y.natAbs ≤ x.natAbs},
        ‖lacDevLin K σ U ω (x - y) - lacDevLin K σ U ω x‖ₑ
          ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ ∑' x : ℤ, (if 2 * y.natAbs ≤ x.natAbs then
          ENNReal.ofReal ((2 * C) * (2 * (y.natAbs : ℝ)) / ((x.natAbs : ℝ)) ^ 2) else 0) := by
    rw [← lintegral_indicator hSmeas
      (fun x => ‖lacDevLin K σ U ω (x - y) - lacDevLin K σ U ω x‖ₑ)]
    calc ∫⁻ x, ({x : ℤ | 2 * y.natAbs ≤ x.natAbs}.indicator
            (fun x => ‖lacDevLin K σ U ω (x - y) - lacDevLin K σ U ω x‖ₑ) x)
          ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ∫⁻ x, ({x : ℤ | 2 * y.natAbs ≤ x.natAbs}.indicator
            (fun x => ENNReal.ofReal
              ((2 * C) * (2 * (y.natAbs : ℝ)) / ((x.natAbs : ℝ)) ^ 2)) x)
          ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ {x : ℤ | 2 * y.natAbs ≤ x.natAbs}
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
            calc ‖lacDevLin K σ U ω (x - y) - lacDevLin K σ U ω x‖ₑ
                = ENNReal.ofReal
                    ‖lacDevLin K σ U ω (x - y) - lacDevLin K σ U ω x‖ :=
                  (ofReal_norm (lacDevLin K σ U ω (x - y) - lacDevLin K σ U ω x)).symm
              _ ≤ ENNReal.ofReal
                    ((2 * C) * (2 * (y.natAbs : ℝ)) / ((x.natAbs : ℝ)) ^ 2) :=
                  ENNReal.ofReal_le_ofReal (hpt x hx)
          · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      _ = ∑' x : ℤ, ({x : ℤ | 2 * y.natAbs ≤ x.natAbs}.indicator
            (fun x => ENNReal.ofReal
              ((2 * C) * (2 * (y.natAbs : ℝ)) / ((x.natAbs : ℝ)) ^ 2)) x) :=
          lintegral_count _
      _ = ∑' x : ℤ, (if 2 * y.natAbs ≤ x.natAbs then
          ENNReal.ofReal ((2 * C) * (2 * (y.natAbs : ℝ)) / ((x.natAbs : ℝ)) ^ 2) else 0) := by
          refine tsum_congr fun x => ?_
          rw [Set.indicator_apply]
          by_cases hx : x ∈ {x : ℤ | 2 * y.natAbs ≤ x.natAbs}
          · rw [if_pos hx, if_pos (by simpa using hx)]
          · rw [if_neg hx, if_neg (by simpa using hx)]
  refine hmain.trans ?_
  calc ∑' x : ℤ, (if 2 * y.natAbs ≤ x.natAbs then
        ENNReal.ofReal ((2 * C) * (2 * (y.natAbs : ℝ)) / ((x.natAbs : ℝ)) ^ 2) else 0)
      ≤ ENNReal.ofReal (4 * (2 * C)) :=
        loDev_lintegral_majorant (2 * C) (by positivity) hy1
    _ ≤ ENNReal.ofReal (8 * C) := ENNReal.ofReal_le_ofReal (by linarith)

end

end Work.KMTAreas.A7
