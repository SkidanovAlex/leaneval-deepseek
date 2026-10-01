import Mathlib
import Submission.Work.ZeroFreeTables.P3.dyadicTermLe
import Submission.Work.ZeroFreeTables.P3.dyadicLogFinset_le

open scoped Classical BigOperators

noncomputable section

namespace Work.ZeroFreeTables.P3

private lemma exists_two_pow_succ_mul_ge (x R : ℝ) (hR : 0 < R) :
    ∃ k : ℕ, x ≤ (2 : ℝ) ^ (k + 1) * R := by
  obtain ⟨N, hN⟩ := exists_nat_gt (x / R)
  refine ⟨N, ?_⟩
  have hxR : x < (N : ℝ) * R := (div_lt_iff₀ hR).mp hN
  have hNle : (N : ℝ) ≤ (2 : ℝ) ^ (N + 1) := by
    have h1 : (N : ℝ) < (2 : ℝ) ^ N := by
      have := Nat.lt_two_pow_self (n := N)
      exact_mod_cast this
    have h2 : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ (N + 1) := by
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) N]
    linarith
  have := mul_le_mul_of_nonneg_right hNle (le_of_lt hR)
  linarith

private def dynLevel (R x : ℝ) : ℕ :=
  if h : 0 < R then
    Nat.find (p := fun k => x ≤ (2 : ℝ) ^ (k + 1) * R) (exists_two_pow_succ_mul_ge x R h)
  else 0

private lemma dynLevel_spec {R x : ℝ} (hR : 0 < R) :
    x ≤ (2 : ℝ) ^ (dynLevel R x + 1) * R := by
  rw [dynLevel, dif_pos hR]
  exact Nat.find_spec (exists_two_pow_succ_mul_ge x R hR)

private lemma dynLevel_min {R x : ℝ} (hR : 0 < R) {k : ℕ} (hk : k < dynLevel R x) :
    ¬ (x ≤ (2 : ℝ) ^ (k + 1) * R) := by
  rw [dynLevel, dif_pos hR] at hk
  exact Nat.find_min (exists_two_pow_succ_mul_ge x R hR) hk

private lemma two_pow_dynLevel_mul_lt {R : ℝ} (hR : 0 < R) {u : ℂ} (hu : R < ‖u‖) :
    (2 : ℝ) ^ dynLevel R ‖u‖ * R < ‖u‖ := by
  rcases Nat.eq_zero_or_pos (dynLevel R ‖u‖) with h | h
  · rw [h, pow_zero, one_mul]; exact hu
  · have hk : dynLevel R ‖u‖ - 1 < dynLevel R ‖u‖ := by omega
    have hmin := dynLevel_min (R := R) (x := ‖u‖) hR hk
    have hexp : dynLevel R ‖u‖ - 1 + 1 = dynLevel R ‖u‖ := by omega
    rw [hexp] at hmin
    exact lt_of_not_ge hmin

end Work.ZeroFreeTables.P3

namespace Work.ZeroFreeTables.P3

theorem dyadicAnnulusKernel_le {c L : ℝ} (hc : 0 ≤ c) (hL : 0 ≤ L) (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℂ → ℝ), (∀ u : ℂ, 0 ≤ m u) → Function.HasFiniteSupport m →
      (∀ ρ : ℝ, 2 ≤ ρ →
        (∑ᶠ u : ℂ, Set.indicator (Metric.closedBall (0 : ℂ) ρ) m u)
          ≤ c * ρ * (Real.log (ρ + 2) + L)) →
      ∀ R : ℝ, 2 ≤ R →
        (∑ᶠ u : ℂ, (if R < ‖u‖ then m u else 0) * (1 / ‖u‖) ^ n)
          ≤ C * (Real.log (R + 2) + L + 1) / R := by
  refine ⟨8 * c, by positivity, ?_⟩
  intro m hm_nonneg hm_fs hbound R hR
  classical
  have hRpos : 0 < R := by linarith
  have hfin : (Function.support m).Finite := hm_fs
  set S : Finset ℂ := hfin.toFinset with hSdef
  have hScoe : (↑S : Set ℂ) = Function.support m := by
    rw [hSdef]; exact Set.Finite.coe_toFinset hfin
  set T : Finset ℕ := S.image (fun u => dynLevel R ‖u‖) with hTdef
  have hInd : ∀ ρ : ℝ, (∑ u ∈ S, (if ‖u‖ ≤ ρ then m u else 0))
      = ∑ᶠ u : ℂ, Set.indicator (Metric.closedBall (0:ℂ) ρ) m u := by
    intro ρ
    have hsub : Function.support (fun u : ℂ => Set.indicator (Metric.closedBall (0:ℂ) ρ) m u)
        ⊆ (↑S : Set ℂ) := by
      intro u hu
      rw [Function.mem_support] at hu
      rw [hScoe, Function.mem_support]
      intro h0
      have hz : Set.indicator (Metric.closedBall (0:ℂ) ρ) m u = 0 := by
        rw [Set.indicator_apply]
        by_cases hh : u ∈ Metric.closedBall (0:ℂ) ρ <;> simp [hh, h0]
      exact hu hz
    have h1 : (∑ᶠ u : ℂ, Set.indicator (Metric.closedBall (0:ℂ) ρ) m u)
        = ∑ u ∈ S, (if ‖u‖ ≤ ρ then m u else 0) := by
      rw [finsum_eq_finsetSum_of_support_subset
        (fun u : ℂ => Set.indicator (Metric.closedBall (0:ℂ) ρ) m u) hsub]
      apply Finset.sum_congr rfl
      intro u _
      rw [Set.indicator_apply]
      by_cases h : u ∈ Metric.closedBall (0:ℂ) ρ
      · have hn : ‖u‖ ≤ ρ := by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h; exact h
        rw [if_pos h, if_pos hn]
      · have hn : ¬ (‖u‖ ≤ ρ) := by
          intro hc; exact h (by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hc)
        rw [if_neg h, if_neg hn]
    exact h1.symm
  have hmass : ∀ k : ℕ, (∑ u ∈ S.filter (fun u => dynLevel R ‖u‖ = k), m u)
      ≤ c * ((2:ℝ)^(k+1)*R) * (Real.log ((2:ℝ)^(k+1)*R + 2) + L) := by
    intro k
    set ρ : ℝ := (2:ℝ)^(k+1)*R with hρ
    have hρ2 : 2 ≤ ρ := by
      rw [hρ]
      have h1 : (1:ℝ) ≤ (2:ℝ)^(k+1) := one_le_pow₀ (by norm_num)
      have h2 : (0:ℝ) < (2:ℝ)^(k+1) := pow_pos (by norm_num) (k+1)
      nlinarith [hR, h1, h2]
    have h1 : (∑ u ∈ S.filter (fun u => dynLevel R ‖u‖ = k), m u)
        ≤ ∑ u ∈ S, (if ‖u‖ ≤ ρ then m u else 0) := by
      rw [show (∑ u ∈ S.filter (fun u => dynLevel R ‖u‖ = k), m u)
            = ∑ u ∈ S.filter (fun u => dynLevel R ‖u‖ = k), (if ‖u‖ ≤ ρ then m u else 0) from
          Finset.sum_congr rfl (fun u hu => by
            rw [Finset.mem_filter] at hu
            rw [if_pos (by
              have hh := dynLevel_spec (R:=R) (x:=‖u‖) hRpos
              rw [hu.2] at hh
              rw [hρ]; exact hh)])]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun u _ _ => by
          by_cases h : ‖u‖ ≤ ρ
          · rw [if_pos h]; exact hm_nonneg u
          · rw [if_neg h])
    calc (∑ u ∈ S.filter (fun u => dynLevel R ‖u‖ = k), m u)
        ≤ ∑ u ∈ S, (if ‖u‖ ≤ ρ then m u else 0) := h1
      _ = ∑ᶠ u : ℂ, Set.indicator (Metric.closedBall (0:ℂ) ρ) m u := hInd ρ
      _ ≤ c * ρ * (Real.log (ρ + 2) + L) := hbound ρ hρ2
      _ = c * ((2:ℝ)^(k+1)*R) * (Real.log ((2:ℝ)^(k+1)*R + 2) + L) := by rw [hρ]
  have hstep1 : (∑ᶠ u : ℂ, (if R < ‖u‖ then m u else 0) * (1 / ‖u‖) ^ n)
      ≤ ∑ᶠ u : ℂ, m u * (1 / ((2:ℝ)^(dynLevel R ‖u‖) * R)) ^ n := by
    apply finsum_le_finsum'
    · exact hfin.subset (fun u hu => by
        rw [Function.mem_support] at hu ⊢
        intro h0
        exact hu (by by_cases h : R < ‖u‖ <;> simp [h, h0]))
    · exact hfin.subset (fun u hu => by
        rw [Function.mem_support] at hu ⊢
        intro h0
        exact hu (by rw [h0, zero_mul]))
    · intro u
      dsimp only
      by_cases hu : R < ‖u‖
      · rw [if_pos hu, one_div_pow, one_div_pow]
        have hpos : 0 < (2:ℝ)^(dynLevel R ‖u‖) * R := by positivity
        have hlt := two_pow_dynLevel_mul_lt hRpos hu
        have hp : ((2:ℝ)^(dynLevel R ‖u‖) * R)^n ≤ ‖u‖^n :=
          pow_le_pow_left₀ (le_of_lt hpos) (le_of_lt hlt) n
        have hle : 1 / ‖u‖^n ≤ 1 / ((2:ℝ)^(dynLevel R ‖u‖) * R)^n :=
          one_div_le_one_div_of_le (pow_pos hpos n) hp
        exact mul_le_mul_of_nonneg_left hle (hm_nonneg u)
      · rw [if_neg hu, zero_mul]
        exact mul_nonneg (hm_nonneg u) (by positivity)
  have hconv : (∑ᶠ u : ℂ, m u * (1 / ((2:ℝ)^(dynLevel R ‖u‖) * R))^n)
      = ∑ u ∈ S, m u * (1 / ((2:ℝ)^(dynLevel R ‖u‖) * R))^n := by
    have hsub : Function.support
        (fun u : ℂ => m u * (1 / ((2:ℝ)^(dynLevel R ‖u‖) * R))^n) ⊆ (↑S : Set ℂ) := by
      intro u hu
      rw [Function.mem_support] at hu
      rw [hScoe, Function.mem_support]
      intro h0
      exact hu (by rw [h0, zero_mul])
    exact finsum_eq_finsetSum_of_support_subset _ hsub
  have hfib : (∑ u ∈ S, m u * (1 / ((2:ℝ)^(dynLevel R ‖u‖) * R))^n)
      = ∑ k ∈ T, (1 / ((2:ℝ)^k * R))^n * ∑ u ∈ S.filter (fun u => dynLevel R ‖u‖ = k), m u := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := fun u => dynLevel R ‖u‖)
      (f := fun u => m u * (1 / ((2:ℝ)^(dynLevel R ‖u‖) * R))^n)
      (fun u hu => by rw [hTdef]; exact Finset.mem_image_of_mem _ hu)]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mem_filter] at hu
    have : m u * (1 / ((2:ℝ)^(dynLevel R ‖u‖) * R))^n
        = (1 / ((2:ℝ)^k * R))^n * m u := by
      rw [hu.2]; exact mul_comm _ _
    exact this
  have hlog2c : ∀ k : ℕ, 0 ≤ (Real.log ((2:ℝ)^(k+1)*R + 2) + L) := by
    intro k
    have h2 : (1:ℝ) ≤ (2:ℝ)^(k+1)*R + 2 := by
      have h1 : (0:ℝ) < (2:ℝ)^(k+1) := pow_pos (by norm_num) _
      have h3 : (0:ℝ) < R := hRpos
      nlinarith [mul_pos h1 h3]
    have := Real.log_nonneg h2
    linarith
  have hterm : ∀ k : ℕ, (1 / ((2:ℝ)^k*R))^n * (∑ u ∈ S.filter (fun u => dynLevel R ‖u‖ = k), m u)
      ≤ (2*c/R) * ((1/2:ℝ)^k * (Real.log ((2:ℝ)^(k+1)*R + 2) + L)) := by
    intro k
    have hcnn : 0 ≤ (1 / ((2:ℝ)^k*R))^n := by positivity
    calc (1 / ((2:ℝ)^k*R))^n * (∑ u ∈ S.filter (fun u => dynLevel R ‖u‖ = k), m u)
        ≤ (1 / ((2:ℝ)^k*R))^n *
            (c * ((2:ℝ)^(k+1)*R) * (Real.log ((2:ℝ)^(k+1)*R + 2) + L)) :=
          mul_le_mul_of_nonneg_left (hmass k) hcnn
      _ = c * ((2:ℝ)^(k+1)*R / ((2:ℝ)^k*R)^n) * (Real.log ((2:ℝ)^(k+1)*R + 2) + L) := by
          rw [one_div_pow]; ring
      _ ≤ c * (2*(1/2:ℝ)^k/R) * (Real.log ((2:ℝ)^(k+1)*R + 2) + L) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (dyadicTermLe n hn hR k) hc)
            (hlog2c k)
      _ = (2*c/R) * ((1/2:ℝ)^k * (Real.log ((2:ℝ)^(k+1)*R + 2) + L)) := by ring
  have hstep2 : ∑ k ∈ T, (1 / ((2:ℝ)^k*R))^n * (∑ u ∈ S.filter (fun u => dynLevel R ‖u‖ = k), m u)
      ≤ ∑ k ∈ T, (2*c/R) * ((1/2:ℝ)^k * (Real.log ((2:ℝ)^(k+1)*R + 2) + L)) :=
    Finset.sum_le_sum (fun k _ => hterm k)
  have hstep3 : ∑ k ∈ T, (2*c/R) * ((1/2:ℝ)^k * (Real.log ((2:ℝ)^(k+1)*R + 2) + L))
      = (2*c/R) * ∑ k ∈ T, (1/2:ℝ)^k * (Real.log ((2:ℝ)^(k+1)*R + 2) + L) := by
    rw [Finset.mul_sum]
  calc (∑ᶠ u : ℂ, (if R < ‖u‖ then m u else 0) * (1 / ‖u‖) ^ n)
      ≤ ∑ᶠ u : ℂ, m u * (1 / ((2:ℝ)^(dynLevel R ‖u‖) * R)) ^ n := hstep1
    _ = ∑ u ∈ S, m u * (1 / ((2:ℝ)^(dynLevel R ‖u‖) * R))^n := hconv
    _ = ∑ k ∈ T, (1 / ((2:ℝ)^k*R))^n * ∑ u ∈ S.filter (fun u => dynLevel R ‖u‖ = k), m u := hfib
    _ ≤ ∑ k ∈ T, (2*c/R) * ((1/2:ℝ)^k * (Real.log ((2:ℝ)^(k+1)*R + 2) + L)) := hstep2
    _ = (2*c/R) * ∑ k ∈ T, (1/2:ℝ)^k * (Real.log ((2:ℝ)^(k+1)*R + 2) + L) := hstep3
    _ ≤ (2*c/R) * (4 * (Real.log (R+2) + L + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact dyadicLogFinset_le R L hR hL T
    _ = (8*c) * (Real.log (R+2) + L + 1) / R := by ring

end Work.ZeroFreeTables.P3

end
