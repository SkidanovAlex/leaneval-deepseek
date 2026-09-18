import Mathlib
import Submission.Commons.NumberTheory.DuffinSchaeffer.km_prop_gcd
import Submission.Commons.NumberTheory.DuffinSchaeffer.approxAddOrderOf_eq_biUnion_ball
import Submission.Commons.NumberTheory.DuffinSchaeffer.volume_ball_le_ofReal_two_mul
import Submission.Commons.NumberTheory.DuffinSchaeffer.reduced_pair_window_bound
import Submission.Commons.NumberTheory.PrimeReciprocals.prime_product_inc_le_log
import Submission.Commons.NumberTheory.DuffinSchaeffer.approxAddOrderOf_volume_of_le
import Submission.Commons.NumberTheory.DuffinSchaeffer.approxAddOrderOf_volume_eq_two_mul_Icc
import Submission.Commons.NumberTheory.DuffinSchaeffer.addWellApproximable_eq_limsup_piecewise
import Submission.Commons.MeasureTheory.tail_blocks_le_measure_limsup
import Submission.Commons.Analysis.Asymptotics.exists_Icc_sum_between_of_tail_lower

noncomputable section
open scoped BigOperators ENNReal
open Finset Filter MeasureTheory Set

namespace Commons.NumberTheory.DuffinSchaeffer

private lemma inv_one_sub_eq (p : ℕ) (hp : 2 ≤ p) :
    (1 - 1 / (p : ℝ))⁻¹ = (p : ℝ) / ((p : ℝ) - 1) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    linarith
  rw [inv_eq_iff_eq_inv]
  field_simp

private lemma inv_one_sub_le_exp_two_div (p : ℕ) (hp : 2 ≤ p) :
    (1 - 1 / (p : ℝ))⁻¹ ≤ Real.exp (2 / (p : ℝ)) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hle : (p : ℝ) / ((p : ℝ) - 1) ≤ 1 + 2 / (p : ℝ) := by
    rw [div_le_iff₀ hp1]
    have h2 : (1 + 2 / (p : ℝ)) * ((p : ℝ) - 1) = (p : ℝ) + 1 - 2 / (p : ℝ) := by
      field_simp; ring
    rw [h2]
    have hle1 : 2 / (p : ℝ) ≤ 1 := by
      rw [div_le_one hpR]; exact hp2
    linarith
  have hexp : (1 : ℝ) + 2 / (p : ℝ) ≤ Real.exp (2 / (p : ℝ)) := by
    have := Real.add_one_le_exp (2 / (p : ℝ))
    linarith
  rw [inv_one_sub_eq p hp]
  linarith

private lemma inv_one_sub_le_sq_one_add (p : ℕ) (hp : 2 ≤ p) :
    (1 - 1 / (p : ℝ))⁻¹ ≤ (1 + 1 / (p : ℝ))^2 := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [inv_one_sub_eq p hp, div_le_iff₀ hp1]
  have hkey : (1 + 1 / (p : ℝ))^2 * ((p : ℝ) - 1) - (p : ℝ)
      = ((p : ℝ)^2 - (p:ℝ) - 1) / (p:ℝ)^2 := by
    field_simp; ring
  have hnum : 0 ≤ (p : ℝ)^2 - (p:ℝ) - 1 := by nlinarith [hp2]
  have hnn : 0 ≤ ((p : ℝ)^2 - (p:ℝ) - 1) / (p:ℝ)^2 := by positivity
  linarith [hkey, hnn]

/-- The product of `(1 - 1/p)⁻¹` over a filter is at most the product over the whole set,
when every factor is at least `1`. -/
private lemma prod_filter_le_prod {S : Finset ℕ} (p : ℕ → Prop) [DecidablePred p] {f : ℕ → ℝ}
    (hf : ∀ x, x ∈ S → 1 ≤ f x) : ∏ x ∈ S.filter p, f x ≤ ∏ x ∈ S, f x := by
  refine Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.filter_subset p S) ?_ ?_
  · intro x hx
    exact le_trans zero_le_one (hf x (Finset.filter_subset p S hx))
  · intro x hx _
    exact hf x hx

/-- `∏_{p ∈ S} (1 - 1/p)⁻¹ ≤ exp (2 * Σ_{p ∈ S} 1/p)` for a set o(1 - 1 / (p : ℝ))⁻¹rimes. -/
private lemma prod_inv_one_sub_le_exp (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ ≤ Real.exp (2 * ∑ p ∈ S, 1 / (p : ℝ)) := by
  calc
    ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ ≤ ∏ p ∈ S, Real.exp (2 / (p : ℝ)) := by
      refine Finset.prod_le_prod₀ ?_ ?_
      · intro p hp
        have hp2 : 2 ≤ p := hS p hp
        have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
        have : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
          rw [sub_pos, div_lt_one hpR]; exact_mod_cast (by omega : 1 < p)
        positivity
      · intro p hp
        exact inv_one_sub_le_exp_two_div p (hS p hp)
    _ = Real.exp (∑ p ∈ S, 2 / (p : ℝ)) := (Real.exp_sum S (fun p => 2 / (p : ℝ))).symm
    _ = Real.exp (2 * ∑ p ∈ S, 1 / (p : ℝ)) := by
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => by ring)

/-- `∏_{p prime, p ≤ N} (1 - 1/p)⁻¹ ≤ (C * log N)^2`, given the Euler-product estimate
`∏ (1 + 1/p) ≤ C log N`. -/
private lemma prod_inv_one_sub_primesBelow_le (N : ℕ) (hN : 3 ≤ N) {C : ℝ}
    (hC : ∀ M : ℕ, 3 ≤ M → ∏ p ∈ Nat.primesBelow (M + 1), (1 + 1 / (p : ℝ)) ≤ C * Real.log M)
    (_hCnn : 0 ≤ C) :
    ∏ p ∈ Nat.primesBelow (N + 1), (1 - 1 / (p : ℝ))⁻¹ ≤ (C * Real.log N)^2 := by
  have h1 : ∏ p ∈ Nat.primesBelow (N + 1), (1 - 1 / (p : ℝ))⁻¹ ≤
      ∏ p ∈ Nat.primesBelow (N + 1), (1 + 1 / (p : ℝ))^2 := by
    refine Finset.prod_le_prod₀ ?_ ?_
    · intro p hp
      have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesBelow hp).two_le
      have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
      have : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
        rw [sub_pos, div_lt_one hpR]; exact_mod_cast (by omega : 1 < p)
      positivity
    · intro p hp
      exact inv_one_sub_le_sq_one_add p (Nat.prime_of_mem_primesBelow hp).two_le
  have h2 : ∏ p ∈ Nat.primesBelow (N + 1), (1 + 1 / (p : ℝ))^2
      = (∏ p ∈ Nat.primesBelow (N + 1), (1 + 1 / (p : ℝ)))^2 :=
    Finset.prod_pow _ _ _
  have h3 : (∏ p ∈ Nat.primesBelow (N + 1), (1 + 1 / (p : ℝ)))^2 ≤ (C * Real.log N)^2 := by
    have h := hC N hN
    have hnn : 0 ≤ ∏ p ∈ Nat.primesBelow (N + 1), (1 + 1 / (p : ℝ)) := by
      refine Finset.prod_nonneg (fun p hp => ?_)
      have hpR : (0 : ℝ) ≤ (p : ℝ) := by positivity
      positivity
    exact pow_le_pow_left₀ hnn h 2
  rw [h2] at h1
  linarith

/-- Elementary band estimate: the sum of `1/p` over naturals in `[t, 4t)` is at most `6`
(for `t ≥ 1`), because there are at most `4t + 2` of them and each is at most `1/t`. -/
private lemma band_sum_le (S : Finset ℕ) {t : ℝ} (ht : 1 ≤ t) :
    ∑ p ∈ S.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ (p : ℝ) < 4 * t), 1 / (p : ℝ) ≤ 6 := by
  classical
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set S' : Finset ℕ := S.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ (p : ℝ) < 4 * t) with hS'
  have hterm : ∀ p ∈ S', 1 / (p : ℝ) ≤ 1 / t := by
    intro p hp
    rw [hS', Finset.mem_filter] at hp
    exact one_div_le_one_div_of_le (by linarith [hp.2.1]) hp.2.1
  have hcard : S'.card ≤ Nat.ceil (4 * t) + 1 := by
    have hsub : S' ⊆ Finset.Icc 0 (Nat.ceil (4 * t)) := by
      intro p hp
      rw [hS', Finset.mem_filter] at hp
      rw [Finset.mem_Icc]
      refine ⟨Nat.zero_le _, ?_⟩
      have h1 : (p : ℝ) ≤ (Nat.ceil (4 * t) : ℕ) := le_trans hp.2.2.le (Nat.le_ceil (4 * t))
      exact_mod_cast h1
    calc S'.card ≤ (Finset.Icc 0 (Nat.ceil (4 * t))).card := Finset.card_le_card hsub
      _ = Nat.ceil (4 * t) + 1 := by simp
  have hsum : ∑ p ∈ S', 1 / (p : ℝ) ≤ (S'.card : ℝ) * (1 / t) := by
    have := Finset.sum_le_card_nsmul S' (fun p => 1 / (p : ℝ)) (1 / t) hterm
    simpa [nsmul_eq_mul] using this
  have hceil : ((Nat.ceil (4 * t) : ℕ) : ℝ) < 4 * t + 1 := Nat.ceil_lt_add_one (by positivity)
  have hcardR : (S'.card : ℝ) ≤ (Nat.ceil (4 * t) : ℕ) + 1 := by exact_mod_cast hcard
  have hfinal : ((Nat.ceil (4 * t) : ℕ) + 1 : ℝ) * (1 / t) ≤ 6 := by
    have h1 : ((Nat.ceil (4 * t) : ℕ) : ℝ) * (1 / t) < (4 * t + 1) * (1 / t) := by
      exact mul_lt_mul_of_pos_right hceil (by positivity)
    have h2 : (4 * t + 1) * (1 / t) = 4 + 1 / t := by field_simp
    have h3 : 1 / t ≤ 1 := by rw [div_le_one htpos]; exact ht
    linarith
  calc ∑ p ∈ S', 1 / (p : ℝ) ≤ (S'.card : ℝ) * (1 / t) := hsum
    _ ≤ ((Nat.ceil (4 * t) : ℕ) + 1 : ℝ) * (1 / t) := by
        exact mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ ≤ 6 := hfinal



private lemma lt_four_pow_succ (n : ℕ) : ((n : ℕ) : ℝ) < (4 : ℝ) ^ (n + 1) := by
  have h : ((n : ℕ) : ℝ) + 1 ≤ (4 : ℝ) ^ n := by
    have hnat : n + 1 ≤ 4 ^ n := by
      induction n with
      | zero => norm_num
      | succ k ih =>
          have h1 : k + 2 ≤ 4 * (k + 1) := by omega
          calc k + 2 ≤ 4 * (k + 1) := h1
            _ ≤ 4 * 4 ^ k := Nat.mul_le_mul_left 4 ih
            _ = 4 ^ (k + 1) := by ring
    exact_mod_cast hnat
  have hpow : (4 : ℝ) ^ n ≤ (4 : ℝ) ^ (n + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
  linarith

private lemma one_le_inv_one_sub (p : ℕ) (hp : 2 ≤ p) : 1 ≤ (1 - 1 / (p : ℝ))⁻¹ := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  rw [inv_one_sub_eq p hp, le_div_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 1)]
  linarith

private lemma filter_split {A : Finset ℕ} {M : ℝ} {g : ℕ} {T : ℝ} :
    A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ))
      = (A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ T))
        ∪ (A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ) ∧ T < (p : ℝ))) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · intro h
    by_cases hp : (p : ℝ) ≤ T
    · exact Or.inl ⟨h.1, h.2, hp⟩
    · exact Or.inr ⟨h.1, h.2, lt_of_not_ge hp⟩
  · rintro (⟨h1, h2, _⟩ | ⟨h1, h2, _⟩) <;> exact ⟨h1, h2⟩

private lemma disjoint_filter_split {A : Finset ℕ} {M : ℝ} {g : ℕ} {T : ℝ} :
    Disjoint (A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ T))
      (A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ) ∧ T < (p : ℝ))) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  simp only [Finset.mem_filter] at hp1 hp2
  linarith [hp1.2.2, hp2.2.2]

private lemma filter_eq_empty_of_lt {A : Finset ℕ} {T : ℝ}
    (h : ∀ p ∈ A, (p : ℝ) < T) :
    A.filter (fun p : ℕ => T ≤ (p : ℝ)) = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨p, hp⟩
  simp only [Finset.mem_filter] at hp
  linarith [h p hp.1, hp.2]

/-- Pointwise second-moment reduction bound (Section 5 of Koukoulopoulos–Maynard). -/
private lemma pair_P_bound {ψ : ℕ → ℝ} (hψ0 : ∀ n, 0 ≤ ψ n) (hψhalf : ∀ n, ψ n ≤ 1 / 2)
    {Cp : ℝ} (hCp : ∀ N : ℕ, 3 ≤ N → ∏ p ∈ Nat.primesBelow (N + 1), (1 + 1 / (p : ℝ)) ≤ Cp * Real.log N)
    {D : ℝ} (hD0 : 0 ≤ D) (hD1 : (Cp * Real.log 4) ^ 2 * Real.exp 20 ≤ D)
    (hD2 : Real.exp 32 ≤ D)
    {q r : ℕ} (hq1 : 1 ≤ q) (hr1 : 1 ≤ r) :
    (∏ p ∈ (Nat.primeFactors (q * r / (q.gcd r * q.gcd r))).filter
        (fun p : ℕ => max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (q.gcd r : ℝ) < (p : ℝ)),
        (1 - 1 / (p : ℝ))⁻¹)
      ≤ Real.exp 100 + D * (1 + ∑ j ∈ Finset.range (q * r + 1),
          ((j : ℝ) + 1) ^ 2 *
            (if ((q.gcd r : ℝ) ≥ max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (4 : ℝ) ^ j ∧
                10 ≤ ∑ p ∈ (Nat.primeFactors (q * r / (q.gcd r * q.gcd r))).filter
                      (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ)), 1 / (p : ℝ))
             then 1 else 0)) := by
  classical
  have hCpnn : 0 ≤ Cp := by
    have h := hCp 3 (by norm_num)
    have hprod : 1 ≤ ∏ p ∈ Nat.primesBelow (3 + 1), (1 + 1 / (p : ℝ)) := by
      refine Finset.one_le_prod₀ (fun p hp => ?_)
      have : (0:ℝ) ≤ 1 / (p:ℝ) := by positivity
      linarith
    have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
    nlinarith [h, hprod, hlog]
  set A : Finset ℕ := Nat.primeFactors (q * r / (q.gcd r * q.gcd r)) with hA
  set M : ℝ := max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) with hM
  set g : ℕ := q.gcd r with hg
  have h2A : ∀ p ∈ A, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hple : ∀ p ∈ A, p ≤ q * r := by
    intro p hp
    have hdvd : p ∣ q * r / (q.gcd r * q.gcd r) := Nat.dvd_of_mem_primeFactors hp
    have hgg : q.gcd r * q.gcd r ≤ q * r :=
      Nat.le_of_dvd (Nat.mul_pos hq1 hr1) (Nat.mul_dvd_mul (Nat.gcd_dvd_left q r) (Nat.gcd_dvd_right q r))
    have hpos : 0 < q * r / (q.gcd r * q.gcd r) :=
      Nat.div_pos hgg (Nat.mul_pos (Nat.gcd_pos_of_pos_left r hq1) (Nat.gcd_pos_of_pos_left r hq1))
    exact le_trans (Nat.le_of_dvd hpos hdvd) (Nat.div_le_self _ _)
  have hprime_lt : ∀ p ∈ A, (p : ℝ) < (4 : ℝ) ^ (q * r + 1) := by
    intro p hp
    have h1 : (p : ℝ) ≤ ((q * r : ℕ) : ℝ) := by exact_mod_cast hple p hp
    have h2 : ((q * r : ℕ) : ℝ) < (4 : ℝ) ^ (q * r + 1) := lt_four_pow_succ (q * r)
    linarith
  have hAempty : A.filter (fun p : ℕ => (4 : ℝ) ^ (q * r + 1) ≤ (p : ℝ)) = ∅ :=
    filter_eq_empty_of_lt (A := A) (T := (4 : ℝ) ^ (q * r + 1)) hprime_lt
  have hPpos : 0 < ∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)), (1 - 1 / (p : ℝ))⁻¹ := by
    refine Finset.prod_pos (fun p hp => ?_)
    exact lt_of_lt_of_le zero_lt_one (one_le_inv_one_sub p (h2A p (Finset.mem_filter.mp hp).1))
  have hPle_exp : (∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)), (1 - 1 / (p : ℝ))⁻¹)
      ≤ Real.exp (2 * ∑ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)), 1 / (p : ℝ)) := by
    calc ∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)), (1 - 1 / (p : ℝ))⁻¹
        ≤ ∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)), Real.exp (2 / (p : ℝ)) := by
          refine Finset.prod_le_prod₀ (fun p hp => ?_) ?_
          · exact le_of_lt (lt_of_lt_of_le zero_lt_one (one_le_inv_one_sub p (h2A p (Finset.mem_filter.mp hp).1)))
          · intro p hp
            exact inv_one_sub_le_exp_two_div p (h2A p (Finset.mem_filter.mp hp).1)
      _ = Real.exp (∑ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)), 2 / (p : ℝ)) :=
            (Real.exp_sum _ _).symm
      _ = Real.exp (2 * ∑ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)), 1 / (p : ℝ)) := by
          congr 1
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun p _ => by ring)
  by_cases hbig : (∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)), (1 - 1 / (p : ℝ))⁻¹) ≤ Real.exp 100
  · have hsum0 : 0 ≤ ∑ j ∈ Finset.range (q * r + 1),
        ((j : ℝ) + 1) ^ 2 *
          (if ((q.gcd r : ℝ) ≥ M / (4 : ℝ) ^ j ∧
              10 ≤ ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ)), 1 / (p : ℝ))
           then 1 else 0) := by
      refine Finset.sum_nonneg (fun j hj => ?_)
      by_cases h : ((q.gcd r : ℝ) ≥ M / (4 : ℝ) ^ j ∧
              10 ≤ ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ)), 1 / (p : ℝ))
      · simp only [h, if_true]; positivity
      · simp only [h, if_false, mul_zero, le_refl]
    have : 0 ≤ D * (1 + ∑ j ∈ Finset.range (q * r + 1),
        ((j : ℝ) + 1) ^ 2 *
          (if ((q.gcd r : ℝ) ≥ M / (4 : ℝ) ^ j ∧
              10 ≤ ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ)), 1 / (p : ℝ))
           then 1 else 0)) := by
      apply mul_nonneg hD0; linarith
    linarith
  · push_neg at hbig
    have hS_A : 50 ≤ ∑ p ∈ A, 1 / (p : ℝ) := by
      have hle : Real.exp (2 * ∑ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)), 1 / (p : ℝ))
          ≤ Real.exp (2 * ∑ p ∈ A, 1 / (p : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hsub : A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)) ⊆ A := Finset.filter_subset _ _
        have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => 1 / (p : ℝ)) hsub
          (fun p hp _ => by positivity)
        linarith
      have hlog : Real.log (Real.exp 100)
          ≤ Real.log (∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)), (1 - 1 / (p : ℝ))⁻¹) :=
        Real.log_le_log (Real.exp_pos 100) (le_of_lt hbig)
      rw [Real.log_exp] at hlog
      have hlog2 : Real.log (∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)), (1 - 1 / (p : ℝ))⁻¹)
          ≤ 2 * ∑ p ∈ A, 1 / (p : ℝ) := by
        calc Real.log (∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)), (1 - 1 / (p : ℝ))⁻¹)
            ≤ Real.log (Real.exp (2 * ∑ p ∈ A, 1 / (p : ℝ))) :=
              Real.log_le_log hPpos (le_trans hPle_exp hle)
          _ = 2 * ∑ p ∈ A, 1 / (p : ℝ) := Real.log_exp _
      linarith
    have hfilt0 : A.filter (fun p : ℕ => (4 : ℝ) ^ 0 ≤ (p : ℝ)) = A := by
      apply Finset.filter_true_of_mem
      intro p hp
      simp only [pow_zero]
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) (h2A p hp))
    have hQ0 : 10 ≤ ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ 0 ≤ (p : ℝ)), 1 / (p : ℝ) := by
      rw [hfilt0]; linarith
    have hex : ∃ j : ℕ, ¬ (10 ≤ ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ)), 1 / (p : ℝ)) := by
      refine ⟨q * r + 1, ?_⟩
      rw [hAempty]; norm_num
    let J0 : ℕ := Nat.find hex
    have hJ0spec : ¬ (10 ≤ ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ J0 ≤ (p : ℝ)), 1 / (p : ℝ)) :=
      Nat.find_spec hex
    have hJ0pos : 1 ≤ J0 := by
      have hpos : 0 < J0 := by
        show 0 < Nat.find hex
        rw [Nat.find_pos hex]
        exact fun h => h hQ0
      omega
    let j : ℕ := J0 - 1
    have hjsucc : j + 1 = J0 := by omega
    have hjQ : 10 ≤ ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ)), 1 / (p : ℝ) := by
      have hlt : j < J0 := by omega
      have := Nat.find_min hex hlt
      by_contra h
      exact this h
    have hjQ1 : ¬ (10 ≤ ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ (j + 1) ≤ (p : ℝ)), 1 / (p : ℝ)) := by
      rw [hjsucc]; exact hJ0spec
    have hjle : j ≤ q * r := by
      have hw : ¬ (10 ≤ ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ (q * r + 1) ≤ (p : ℝ)), 1 / (p : ℝ)) := by
        rw [hAempty]; norm_num
      have h1 : Nat.find hex ≤ q * r + 1 := Nat.find_le hw
      show j ≤ q * r
      omega
    have hLj : 10 ≤ ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ)), 1 / (p : ℝ) := hjQ
    have hLj1 : ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ (j + 1) ≤ (p : ℝ)), 1 / (p : ℝ) < 10 :=
      not_le.mp hjQ1
    have ht1 : 1 ≤ (4 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have ht1pos : 0 < (4 : ℝ) ^ j := lt_of_lt_of_le zero_lt_one ht1
    have hgposR : (0 : ℝ) < (g : ℝ) := by
      rw [hg]; exact_mod_cast Nat.gcd_pos_of_pos_left r hq1
    rcases lt_or_ge (M / (g : ℝ)) ((4 : ℝ) ^ j) with hcase | hcase
    · -- case `M/g < 4^j`
      have hMlt : M < (4 : ℝ) ^ j * (g : ℝ) := (div_lt_iff₀ hgposR).mp hcase
      -- product split
      have hpP : (∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)), (1 - 1 / (p : ℝ))⁻¹)
          = (∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (4 : ℝ) ^ (j+1)), (1 - 1 / (p : ℝ))⁻¹)
            * (∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ) ∧ (4 : ℝ) ^ (j+1) < (p : ℝ)), (1 - 1 / (p : ℝ))⁻¹) := by
        rw [filter_split (A := A) (M := M) (g := g) (T := (4 : ℝ) ^ (j+1)),
          Finset.prod_union (disjoint_filter_split (A := A) (M := M) (g := g) (T := (4 : ℝ) ^ (j+1)))]
      have hfirst : (∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (4 : ℝ) ^ (j+1)), (1 - 1 / (p : ℝ))⁻¹)
          ≤ (Cp * Real.log 4) ^ 2 * ((j : ℝ) + 1) ^ 2 := by
        have hsub : A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (4 : ℝ) ^ (j+1)) ⊆
            Nat.primesBelow (4 ^ (j+1) + 1) := by
          intro p hp
          rw [Finset.mem_filter] at hp
          rw [Nat.mem_primesBelow]
          refine ⟨?_, Nat.prime_of_mem_primeFactors hp.1⟩
          have h2 : (p : ℝ) ≤ ((4 : ℝ) ^ (j+1)) := hp.2.2
          have h3 : (p : ℝ) ≤ ((4 ^ (j+1) : ℕ) : ℝ) := by push_cast; exact h2
          have h4 : p ≤ 4 ^ (j+1) := by exact_mod_cast h3
          exact Nat.lt_succ_of_le h4
        have h1 : (∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (4 : ℝ) ^ (j+1)), (1 - 1 / (p : ℝ))⁻¹)
            ≤ ∏ p ∈ Nat.primesBelow (4 ^ (j+1) + 1), (1 - 1 / (p : ℝ))⁻¹ := by
          refine Finset.prod_le_prod_of_subset_of_one_le₀ hsub ?_ ?_
          · intro p hp
            exact le_trans zero_le_one (one_le_inv_one_sub p (h2A p (Finset.mem_filter.mp hp).1))
          · intro p hp _
            exact one_le_inv_one_sub p (Nat.prime_of_mem_primesBelow hp).two_le
        have h2 : ∏ p ∈ Nat.primesBelow (4 ^ (j+1) + 1), (1 - 1 / (p : ℝ))⁻¹
            ≤ (Cp * Real.log 4) ^ 2 * ((j : ℝ) + 1) ^ 2 := by
          have hN3 : 3 ≤ 4 ^ (j+1) := by
            have h43 : (3:ℕ) ≤ 4 := by norm_num
            exact le_trans h43 (Nat.le_self_pow (by omega : j + 1 ≠ 0) 4)
          have h3 := prod_inv_one_sub_primesBelow_le (4 ^ (j+1)) hN3 hCp hCpnn
          have hlog : Real.log ((4 ^ (j+1) : ℕ) : ℝ) = ((j:ℝ)+1) * Real.log 4 := by
            rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
            push_cast; ring
          rw [hlog] at h3
          calc ∏ p ∈ Nat.primesBelow (4 ^ (j+1) + 1), (1 - 1 / (p : ℝ))⁻¹
              ≤ (Cp * (((j:ℝ)+1) * Real.log 4))^2 := h3
            _ = (Cp * Real.log 4)^2 * ((j:ℝ)+1)^2 := by ring
        linarith
      have hsecond : (∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ) ∧ (4 : ℝ) ^ (j+1) < (p : ℝ)), (1 - 1 / (p : ℝ))⁻¹)
          ≤ Real.exp 20 := by
        have hsub : A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ) ∧ (4 : ℝ) ^ (j+1) < (p : ℝ)) ⊆
            A.filter (fun p : ℕ => (4 : ℝ) ^ (j+1) ≤ (p : ℝ)) := by
          intro p hp
          rw [Finset.mem_filter] at hp ⊢
          exact ⟨hp.1, le_of_lt hp.2.2⟩
        calc (∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ) ∧ (4 : ℝ) ^ (j+1) < (p : ℝ)), (1 - 1 / (p : ℝ))⁻¹)
            ≤ ∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ) ∧ (4 : ℝ) ^ (j+1) < (p : ℝ)), Real.exp (2 / (p : ℝ)) := by
              refine Finset.prod_le_prod₀ (fun p hp => ?_) ?_
              · exact le_of_lt (lt_of_lt_of_le zero_lt_one (one_le_inv_one_sub p (h2A p (Finset.mem_filter.mp hp).1)))
              · intro p hp
                exact inv_one_sub_le_exp_two_div p (h2A p (Finset.mem_filter.mp hp).1)
          _ = Real.exp (∑ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ) ∧ (4 : ℝ) ^ (j+1) < (p : ℝ)), 2 / (p : ℝ)) :=
              (Real.exp_sum _ _).symm
          _ ≤ Real.exp (∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ (j+1) ≤ (p : ℝ)), 2 / (p : ℝ)) := by
              apply Real.exp_le_exp.mpr
              exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => by positivity)
          _ = Real.exp (2 * ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ (j+1) ≤ (p : ℝ)), 1 / (p : ℝ)) := by
              congr 1
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun p _ => by ring)
          _ ≤ Real.exp 20 := by
              apply Real.exp_le_exp.mpr; linarith
      have hPbound : (∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)), (1 - 1 / (p : ℝ))⁻¹)
          ≤ D * ((j : ℝ) + 1) ^ 2 := by
        rw [hpP]
        have h2nn : (0:ℝ) ≤ ∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ) ∧ (4 : ℝ) ^ (j+1) < (p : ℝ)), (1 - 1 / (p : ℝ))⁻¹ :=
          Finset.prod_nonneg (fun p hp => le_of_lt (lt_of_lt_of_le zero_lt_one
            (one_le_inv_one_sub p (h2A p (Finset.mem_filter.mp hp).1))))
        have hAnn : (0:ℝ) ≤ (Cp * Real.log 4) ^ 2 * ((j : ℝ) + 1) ^ 2 := by positivity
        calc (∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (4 : ℝ) ^ (j+1)), (1 - 1 / (p : ℝ))⁻¹)
              * (∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ) ∧ (4 : ℝ) ^ (j+1) < (p : ℝ)), (1 - 1 / (p : ℝ))⁻¹)
            ≤ ((Cp * Real.log 4) ^ 2 * ((j : ℝ) + 1) ^ 2) * Real.exp 20 :=
              mul_le_mul hfirst hsecond h2nn hAnn
          _ ≤ D * ((j : ℝ) + 1) ^ 2 := by nlinarith [hD1, sq_nonneg ((j:ℝ)+1), Real.exp_pos 20]
      have hcond : ((q.gcd r : ℝ) ≥ M / (4 : ℝ) ^ j ∧
          10 ≤ ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ)), 1 / (p : ℝ)) := by
        constructor
        · have hgg : M / (4 : ℝ) ^ j ≤ (g : ℝ) := by
            rw [div_le_iff₀ ht1pos]
            simpa [mul_comm] using hMlt.le
          rw [hg] at hgg
          exact hgg
        · exact hLj
      have hmem : j ∈ Finset.range (q * r + 1) := by rw [Finset.mem_range]; omega
      let Fsum : ℕ → ℝ := fun j' => ((j' : ℝ) + 1) ^ 2 *
            (if ((q.gcd r : ℝ) ≥ M / (4 : ℝ) ^ j' ∧
                10 ≤ ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ j' ≤ (p : ℝ)), 1 / (p : ℝ))
             then 1 else 0)
      have hFsum_nn : ∀ j' ∈ Finset.range (q * r + 1), 0 ≤ Fsum j' := by
        intro j' hj'
        by_cases h : ((q.gcd r : ℝ) ≥ M / (4 : ℝ) ^ j' ∧
            10 ≤ ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ j' ≤ (p : ℝ)), 1 / (p : ℝ))
        · simp only [Fsum, h, if_true]; positivity
        · simp only [Fsum, h, if_false, mul_zero, le_refl]
      have hFj : Fsum j = ((j : ℝ) + 1) ^ 2 := by
        show ((j : ℝ) + 1) ^ 2 * (if ((q.gcd r : ℝ) ≥ M / (4 : ℝ) ^ j ∧
            10 ≤ ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ)), 1 / (p : ℝ)) then 1 else 0)
          = ((j : ℝ) + 1) ^ 2
        rw [if_pos hcond, mul_one]
      have hsumge : ((j : ℝ) + 1) ^ 2 ≤ ∑ j' ∈ Finset.range (q * r + 1), Fsum j' := by
        have hle := Finset.single_le_sum hFsum_nn hmem
        rwa [hFj] at hle
      have hfin : D * (1 + ((j : ℝ) + 1) ^ 2) ≤ D * (1 + ∑ j' ∈ Finset.range (q * r + 1), Fsum j') := by
        apply mul_le_mul_of_nonneg_left _ hD0
        linarith
      have hsqt : (0:ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by positivity
      have hmulD : D * ((j : ℝ) + 1) ^ 2 ≤ D * (1 + ((j : ℝ) + 1) ^ 2) := by nlinarith [hD0, hsqt]
      linarith [hPbound, hfin, hmulD, Real.exp_pos 100]
    · -- case `4^j ≤ M/g`
      have hsub : A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)) ⊆
          A.filter (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ)) := by
        intro p hp
        rw [Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, le_trans hcase hp.2.le⟩
      have hsum16 : ∑ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)), 1 / (p : ℝ) ≤ 16 := by
        have h1 : ∑ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)), 1 / (p : ℝ)
            ≤ ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ)), 1 / (p : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => by positivity)
        have hset : A.filter (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ))
            = (A.filter (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ) ∧ (p : ℝ) < (4 : ℝ) ^ (j+1)))
              ∪ (A.filter (fun p : ℕ => (4 : ℝ) ^ (j+1) ≤ (p : ℝ))) := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_union]
          constructor
          · intro h
            by_cases hp : (p : ℝ) < (4 : ℝ) ^ (j+1)
            · exact Or.inl ⟨h.1, h.2, hp⟩
            · exact Or.inr ⟨h.1, by push_neg at hp; exact hp⟩
          · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
            · exact ⟨h1, h2⟩
            · exact ⟨h1, le_trans (le_of_lt (pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self j))) h2⟩
        have hdisj : Disjoint (A.filter (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ) ∧ (p : ℝ) < (4 : ℝ) ^ (j+1)))
            (A.filter (fun p : ℕ => (4 : ℝ) ^ (j+1) ≤ (p : ℝ))) := by
          rw [Finset.disjoint_left]
          intro p hp1 hp2
          simp only [Finset.mem_filter] at hp1 hp2
          linarith [hp1.2.2, hp2.2]
        have hband : ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ) ∧ (p : ℝ) < (4 : ℝ) ^ (j+1)), 1 / (p : ℝ) ≤ 6 := by
          have hband0 := band_sum_le A ht1
          have hfe : A.filter (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ) ∧ (p : ℝ) < (4 : ℝ) ^ (j+1))
              = A.filter (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ) ∧ (p : ℝ) < 4 * (4 : ℝ) ^ j) := by
            apply Finset.filter_congr
            intro p hp
            rw [pow_succ]
            ring_nf
          rw [hfe]; exact hband0
        have hsplit : ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ)), 1 / (p : ℝ)
            = (∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ) ∧ (p : ℝ) < (4 : ℝ) ^ (j+1)), 1 / (p : ℝ))
              + ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ (j+1) ≤ (p : ℝ)), 1 / (p : ℝ) := by
          rw [hset, Finset.sum_union hdisj]
        linarith [h1, hsplit, hband, hLj1]
      have hbound : (∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)), (1 - 1 / (p : ℝ))⁻¹) ≤ Real.exp 32 := by
        calc (∏ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)), (1 - 1 / (p : ℝ))⁻¹)
            ≤ Real.exp (2 * ∑ p ∈ A.filter (fun p : ℕ => M / (g : ℝ) < (p : ℝ)), 1 / (p : ℝ)) := hPle_exp
          _ ≤ Real.exp 32 := by
              apply Real.exp_le_exp.mpr; linarith
      have hsum0 : 0 ≤ ∑ j' ∈ Finset.range (q * r + 1),
          ((j' : ℝ) + 1) ^ 2 *
            (if ((q.gcd r : ℝ) ≥ M / (4 : ℝ) ^ j' ∧
                10 ≤ ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ j' ≤ (p : ℝ)), 1 / (p : ℝ))
             then 1 else 0) := by
        refine Finset.sum_nonneg (fun j' hj' => ?_)
        by_cases h : ((q.gcd r : ℝ) ≥ M / (4 : ℝ) ^ j' ∧
                10 ≤ ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ j' ≤ (p : ℝ)), 1 / (p : ℝ))
        · simp only [h, if_true]; positivity
        · simp only [h, if_false, mul_zero, le_refl]
      have : Real.exp 32 ≤ D * (1 + ∑ j' ∈ Finset.range (q * r + 1),
          ((j' : ℝ) + 1) ^ 2 *
            (if ((q.gcd r : ℝ) ≥ M / (4 : ℝ) ^ j' ∧
                10 ≤ ∑ p ∈ A.filter (fun p : ℕ => (4 : ℝ) ^ j' ≤ (p : ℝ)), 1 / (p : ℝ))
             then 1 else 0)) := by
        nlinarith [hD0, hD2, hsum0]
      linarith [hbound, this, Real.exp_pos 100]



private lemma half_pow_sum_le (n : ℕ) : ∑ j ∈ Finset.range n, ((1 / 2 : ℝ) ^ j) ≤ 2 := by
  have h1 : ((1 / 2 : ℝ) ^ n - 1) / ((1 / 2 : ℝ) - 1) = 2 - 2 * (1 / 2 : ℝ) ^ n := by
    field_simp
    ring
  rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1), h1]
  have h2 : 0 ≤ 2 * (1 / 2 : ℝ) ^ n := by positivity
  linarith

private lemma sq_succ_le_hundred_mul_two_pow (j : ℕ) : ((j : ℝ) + 1) ^ 2 ≤ 100 * 2 ^ j := by
  induction j with
  | zero => norm_num
  | succ k ih =>
      rcases Nat.lt_or_ge k 2 with hk | hk
      · interval_cases k <;> norm_num
      · have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        have h1 : ((k : ℝ) + 2) ^ 2 ≤ 2 * ((k : ℝ) + 1) ^ 2 := by nlinarith
        have h2 : (2 : ℝ) * ((k : ℝ) + 1) ^ 2 ≤ 2 * (100 * 2 ^ k) := by linarith
        have h3 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
        push_cast
        rw [h3]
        linarith

private lemma sum_sq_div_four_pow_le (n : ℕ) :
    ∑ j ∈ Finset.range n, (((j : ℝ) + 1) ^ 2 / (4 : ℝ) ^ j) ≤ 400 := by
  have hterm : ∀ j : ℕ, ((j : ℝ) + 1) ^ 2 / (4 : ℝ) ^ j ≤ 100 * (1 / 2 : ℝ) ^ j := by
    intro j
    have h4 : (0 : ℝ) < (4 : ℝ) ^ j := by positivity
    rw [div_le_iff₀ h4]
    have hsp := sq_succ_le_hundred_mul_two_pow j
    have h : (1 / 2 : ℝ) ^ j * (4 : ℝ) ^ j = (2 : ℝ) ^ j := by
      rw [← mul_pow]; norm_num
    have hthis : 100 * (1 / 2 : ℝ) ^ j * (4 : ℝ) ^ j = 100 * 2 ^ j := by
      rw [mul_assoc, h]
    rw [hthis]
    exact hsp
  calc ∑ j ∈ Finset.range n, (((j : ℝ) + 1) ^ 2 / (4 : ℝ) ^ j)
      ≤ ∑ j ∈ Finset.range n, 100 * (1 / 2 : ℝ) ^ j := Finset.sum_le_sum (fun j _ => hterm j)
    _ = 100 * ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j := by rw [Finset.mul_sum]
    _ ≤ 100 * 2 := by
        have := half_pow_sum_le n
        linarith
    _ = 200 := by norm_num
    _ ≤ 400 := by norm_num



theorem km_pair_product_sum_bound :
    ∃ K : ℝ, 0 < K ∧
      ∀ (ψ : ℕ → ℝ), (∀ n, 0 ≤ ψ n) → (∀ n, ψ n ≤ 1 / 2) →
      ∀ (X Y : ℕ), 1 ≤ X → X ≤ Y →
        (1 : ℝ) ≤ ∑ q ∈ Finset.Icc X Y, (q.totient : ℝ) * ψ q / q →
        (∑ q ∈ Finset.Icc X Y, (q.totient : ℝ) * ψ q / q) ≤ 2 →
        (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
          ((q.totient : ℝ) * ψ q / q) * ((r.totient : ℝ) * ψ r / r) *
            ∏ p ∈ (Nat.primeFactors (q * r / (q.gcd r * q.gcd r))).filter
                    (fun p : ℕ => max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (q.gcd r : ℝ) < (p : ℝ)),
                    (1 - 1 / (p : ℝ))⁻¹) ≤ K := by
  classical
  obtain ⟨C2, hC2pos, hC2⟩ := km_prop_gcd
  obtain ⟨Cp, hCpnn, hCp⟩ := Commons.NumberTheory.PrimeReciprocals.prime_product_inc_le_log
  set D : ℝ := max ((Cp * Real.log 4) ^ 2 * Real.exp 20) (Real.exp 32) with hDdef
  have hD0 : 0 ≤ D := le_trans (by positivity) (le_max_left _ _)
  have hD1 : (Cp * Real.log 4) ^ 2 * Real.exp 20 ≤ D := le_max_left _ _
  have hD2 : Real.exp 32 ≤ D := le_max_right _ _
  refine ⟨4 * Real.exp 100 + 4 * D + D * C2 * 400, by positivity, ?_⟩
  intro ψ hψ0 hψhalf X Y hX hXY hS1 hS2
  set w : ℕ → ℝ := fun q => (q.totient : ℝ) * ψ q / q with hwdef
  have hw0 : ∀ q, 0 ≤ w q :=
    fun q => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hψ0 q)) (Nat.cast_nonneg q)
  have hSsq : (∑ q ∈ Finset.Icc X Y, w q) ^ 2 ≤ 4 := by nlinarith [hS1, hS2]
  set G : ℕ → ℕ → ℕ → ℝ := fun j q r =>
      if ((q.gcd r : ℝ) ≥ max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (4 : ℝ) ^ j ∧
          10 ≤ ∑ p ∈ (Nat.primeFactors (q * r / (q.gcd r * q.gcd r))).filter
                (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ)), 1 / (p : ℝ))
      then 1 else 0 with hGdef
  have hG0 : ∀ j q r, 0 ≤ G j q r := by
    intro j q r
    by_cases h : ((q.gcd r : ℝ) ≥ max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (4 : ℝ) ^ j ∧
        10 ≤ ∑ p ∈ (Nat.primeFactors (q * r / (q.gcd r * q.gcd r))).filter
              (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ)), 1 / (p : ℝ))
    · simp only [hGdef, h, if_true]; norm_num
    · simp only [hGdef, h, if_false, le_refl]
  -- `km_prop_gcd` controls the level-`j` mass
  have hinner : ∀ j : ℕ, (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y, w q * w r * G j q r)
      ≤ C2 / (4 : ℝ) ^ j := by
    intro j
    have h1 : (1 : ℝ) ≤ (4 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hkg := hC2 ψ hψ0 hψhalf X Y hX hXY ⟨hS1, hS2⟩ ((4 : ℝ) ^ j) h1
    have hsum_eq : (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y, w q * w r * G j q r)
        = ∑ p ∈ (Finset.Icc X Y).product (Finset.Icc X Y),
            (if ((p.1.gcd p.2 : ℝ) ≥
                    max ((p.2 : ℝ) * ψ p.1) ((p.1 : ℝ) * ψ p.2) / (4 : ℝ) ^ j ∧
                 10 ≤ ∑ r ∈ (Nat.primeFactors (p.1 * p.2 / (p.1.gcd p.2 * p.1.gcd p.2))).filter
                          (fun r : ℕ => (4 : ℝ) ^ j ≤ (r : ℝ)), 1 / (r : ℝ))
             then ((p.1.totient : ℝ) * ψ p.1 / p.1) * ((p.2.totient : ℝ) * ψ p.2 / p.2)
             else 0) := by
      rw [show (∑ p ∈ (Finset.Icc X Y).product (Finset.Icc X Y),
            (if ((p.1.gcd p.2 : ℝ) ≥
                    max ((p.2 : ℝ) * ψ p.1) ((p.1 : ℝ) * ψ p.2) / (4 : ℝ) ^ j ∧
                 10 ≤ ∑ r ∈ (Nat.primeFactors (p.1 * p.2 / (p.1.gcd p.2 * p.1.gcd p.2))).filter
                          (fun r : ℕ => (4 : ℝ) ^ j ≤ (r : ℝ)), 1 / (r : ℝ))
             then ((p.1.totient : ℝ) * ψ p.1 / p.1) * ((p.2.totient : ℝ) * ψ p.2 / p.2)
             else 0))
          = ∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
            (fun p : ℕ × ℕ =>
            (if ((p.1.gcd p.2 : ℝ) ≥
                    max ((p.2 : ℝ) * ψ p.1) ((p.1 : ℝ) * ψ p.2) / (4 : ℝ) ^ j ∧
                 10 ≤ ∑ r ∈ (Nat.primeFactors (p.1 * p.2 / (p.1.gcd p.2 * p.1.gcd p.2))).filter
                          (fun r : ℕ => (4 : ℝ) ^ j ≤ (r : ℝ)), 1 / (r : ℝ))
             then ((p.1.totient : ℝ) * ψ p.1 / p.1) * ((p.2.totient : ℝ) * ψ p.2 / p.2)
             else 0)) (q, r) from Finset.sum_product _ _ _]
      refine Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (fun r hr => ?_))
      by_cases h : ((q.gcd r : ℝ) ≥ max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (4 : ℝ) ^ j ∧
          10 ≤ ∑ p ∈ (Nat.primeFactors (q * r / (q.gcd r * q.gcd r))).filter
                (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ)), 1 / (p : ℝ)) <;>
        simp [hGdef, hwdef, h]
    rw [hsum_eq]
    exact hkg
  -- pointwise second-moment reduction
  have hpairbound : ∀ q ∈ Finset.Icc X Y, ∀ r ∈ Finset.Icc X Y,
      (∏ p ∈ (Nat.primeFactors (q * r / (q.gcd r * q.gcd r))).filter
            (fun p : ℕ => max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (q.gcd r : ℝ) < (p : ℝ)),
            (1 - 1 / (p : ℝ))⁻¹)
        ≤ Real.exp 100 + D * (1 + ∑ j ∈ Finset.range (Y * Y + 1), ((j : ℝ) + 1) ^ 2 * G j q r) := by
    intro q hq r hr
    have hq1 : 1 ≤ q := le_trans hX (Finset.mem_Icc.mp hq).1
    have hr1 : 1 ≤ r := le_trans hX (Finset.mem_Icc.mp hr).1
    have hqY : q ≤ Y := (Finset.mem_Icc.mp hq).2
    have hrY : r ≤ Y := (Finset.mem_Icc.mp hr).2
    have hmul : q * r + 1 ≤ Y * Y + 1 := by nlinarith
    have h := pair_P_bound hψ0 hψhalf hCp hD0 hD1 hD2 hq1 hr1
    have hsumle : (∑ j ∈ Finset.range (q * r + 1),
          ((j : ℝ) + 1) ^ 2 *
            (if ((q.gcd r : ℝ) ≥ max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (4 : ℝ) ^ j ∧
                10 ≤ ∑ p ∈ (Nat.primeFactors (q * r / (q.gcd r * q.gcd r))).filter
                      (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ)), 1 / (p : ℝ))
             then 1 else 0))
        ≤ ∑ j ∈ Finset.range (Y * Y + 1), ((j : ℝ) + 1) ^ 2 * G j q r := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro j hj
        rw [Finset.mem_range] at hj ⊢
        omega
      · intro j hj hjn
        by_cases hc : ((q.gcd r : ℝ) ≥ max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (4 : ℝ) ^ j ∧
            10 ≤ ∑ p ∈ (Nat.primeFactors (q * r / (q.gcd r * q.gcd r))).filter
                  (fun p : ℕ => (4 : ℝ) ^ j ≤ (p : ℝ)), 1 / (p : ℝ))
        · rw [if_pos hc]; positivity
        · rw [if_neg hc]; positivity
    nlinarith [h, hsumle, hD0]
  -- the double sum is bounded by the reduced two-term expression
  let R : Finset ℕ := Finset.range (Y * Y + 1)
  let Asq : ℕ → ℝ := fun j => ((j : ℝ) + 1) ^ 2
  let inner : ℕ → ℝ := fun j => ∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y, w q * w r * G j q r
  let SS : ℝ := (∑ q ∈ Finset.Icc X Y, w q) * ∑ r ∈ Finset.Icc X Y, w r
  have hSS_def : SS = (∑ q ∈ Finset.Icc X Y, w q) * ∑ r ∈ Finset.Icc X Y, w r := rfl
  have hR_nonneg : ∀ j ∈ R, (0:ℝ) ≤ Asq j := fun j _ => by positivity
  have hmain : (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y, w q * w r *
        (∏ p ∈ (Nat.primeFactors (q * r / (q.gcd r * q.gcd r))).filter
              (fun p : ℕ => max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (q.gcd r : ℝ) < (p : ℝ)),
              (1 - 1 / (p : ℝ))⁻¹))
      ≤ (Real.exp 100 + D) * SS + D * (∑ j ∈ R, Asq j * inner j) := by
    have h1 : (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y, w q * w r *
          (∏ p ∈ (Nat.primeFactors (q * r / (q.gcd r * q.gcd r))).filter
                (fun p : ℕ => max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (q.gcd r : ℝ) < (p : ℝ)),
                (1 - 1 / (p : ℝ))⁻¹))
        ≤ ∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
            ((Real.exp 100 + D) * (w q * w r) + D * (∑ j ∈ R, Asq j * (w q * w r * G j q r))) := by
      refine Finset.sum_le_sum (fun q hq => Finset.sum_le_sum (fun r hr => ?_))
      have hpb := hpairbound q hq r hr
      have hww : 0 ≤ w q * w r := mul_nonneg (hw0 q) (hw0 r)
      have hsum : w q * w r * (∑ j ∈ R, Asq j * G j q r)
          = ∑ j ∈ R, Asq j * (w q * w r * G j q r) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j hj => by ring)
      have hstep : w q * w r * (Real.exp 100 + D * (1 + ∑ j ∈ R, Asq j * G j q r))
          = (Real.exp 100 + D) * (w q * w r) + D * (∑ j ∈ R, Asq j * (w q * w r * G j q r)) := by
        calc w q * w r * (Real.exp 100 + D * (1 + ∑ j ∈ R, Asq j * G j q r))
            = Real.exp 100 * (w q * w r) + D * (w q * w r)
              + D * (w q * w r * (∑ j ∈ R, Asq j * G j q r)) := by ring
          _ = Real.exp 100 * (w q * w r) + D * (w q * w r)
              + D * (∑ j ∈ R, Asq j * (w q * w r * G j q r)) := by rw [hsum]
          _ = (Real.exp 100 + D) * (w q * w r)
              + D * (∑ j ∈ R, Asq j * (w q * w r * G j q r)) := by ring
      calc w q * w r * (∏ p ∈ (Nat.primeFactors (q * r / (q.gcd r * q.gcd r))).filter
                (fun p : ℕ => max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (q.gcd r : ℝ) < (p : ℝ)),
                (1 - 1 / (p : ℝ))⁻¹)
          ≤ w q * w r * (Real.exp 100 + D * (1 + ∑ j ∈ R, Asq j * G j q r)) :=
            mul_le_mul_of_nonneg_left hpb hww
        _ = _ := hstep
    calc (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y, w q * w r *
          (∏ p ∈ (Nat.primeFactors (q * r / (q.gcd r * q.gcd r))).filter
                (fun p : ℕ => max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (q.gcd r : ℝ) < (p : ℝ)),
                (1 - 1 / (p : ℝ))⁻¹))
        ≤ ∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
            ((Real.exp 100 + D) * (w q * w r) + D * (∑ j ∈ R, Asq j * (w q * w r * G j q r))) := h1
      _ = (Real.exp 100 + D) * SS + D * (∑ j ∈ R, Asq j * inner j) := by
          have hA : (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
              (Real.exp 100 + D) * (w q * w r)) = (Real.exp 100 + D) * SS := by
            have h1 : (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
                (Real.exp 100 + D) * (w q * w r))
                = (Real.exp 100 + D) * (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y, w q * w r) := by
              simp only [← Finset.mul_sum]
            have h2 : (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y, w q * w r)
                = (∑ q ∈ Finset.Icc X Y, w q) * ∑ r ∈ Finset.Icc X Y, w r := by
              rw [← Finset.sum_mul_sum]
            rw [h1, h2, hSS_def]
          have hB : (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
              D * (∑ j ∈ R, Asq j * (w q * w r * G j q r)))
              = D * (∑ j ∈ R, Asq j * inner j) := by
            have h1 : (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
                D * (∑ j ∈ R, Asq j * (w q * w r * G j q r)))
                = D * (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
                    ∑ j ∈ R, Asq j * (w q * w r * G j q r)) := by
              simp only [← Finset.mul_sum]
            have h2 : (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
                    ∑ j ∈ R, Asq j * (w q * w r * G j q r))
                = ∑ j ∈ R, Asq j * inner j := by
              calc (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
                    ∑ j ∈ R, Asq j * (w q * w r * G j q r))
                  = ∑ q ∈ Finset.Icc X Y, (∑ j ∈ R, ∑ r ∈ Finset.Icc X Y,
                      Asq j * (w q * w r * G j q r)) :=
                    Finset.sum_congr rfl (fun q _ => Finset.sum_comm)
                _ = ∑ j ∈ R, ∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
                      Asq j * (w q * w r * G j q r) := Finset.sum_comm
                _ = ∑ j ∈ R, Asq j * (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
                      w q * w r * G j q r) := by
                    refine Finset.sum_congr rfl (fun j _ => ?_)
                    rw [Finset.mul_sum]
                    congr 1
                    ext q
                    rw [Finset.mul_sum]
                _ = ∑ j ∈ R, Asq j * inner j := rfl
            rw [h1, h2]
          simp only [Finset.sum_add_distrib]
          rw [hA, hB]
  have hSS_le : SS ≤ 4 := by
    rw [hSS_def, ← sq]; exact hSsq
  have hfinal : (∑ j ∈ R, Asq j * inner j) ≤ C2 * 400 := by
    calc (∑ j ∈ R, Asq j * inner j) ≤ ∑ j ∈ R, Asq j * (C2 / (4 : ℝ) ^ j) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          exact mul_le_mul_of_nonneg_left (hinner j) (hR_nonneg j hj)
      _ = C2 * ∑ j ∈ R, Asq j / (4 : ℝ) ^ j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j hj => ?_)
          simp only [Asq]
          ring
      _ ≤ C2 * 400 := by
          have h4 := sum_sq_div_four_pow_le (Y * Y + 1)
          have : (∑ j ∈ R, Asq j / (4 : ℝ) ^ j) = ∑ j ∈ Finset.range (Y * Y + 1), (((j : ℝ) + 1) ^ 2 / (4 : ℝ) ^ j) := rfl
          rw [this]
          exact mul_le_mul_of_nonneg_left h4 hC2pos.le
  have hmain2 : (Real.exp 100 + D) * SS + D * (∑ j ∈ R, Asq j * inner j)
      ≤ (Real.exp 100 + D) * 4 + D * (C2 * 400) := by
    have h1 : (Real.exp 100 + D) * SS ≤ (Real.exp 100 + D) * 4 :=
      mul_le_mul_of_nonneg_left hSS_le (by positivity)
    have h2 : D * (∑ j ∈ R, Asq j * inner j) ≤ D * (C2 * 400) :=
      mul_le_mul_of_nonneg_left hfinal hD0
    linarith
  have hgoal : (Real.exp 100 + D) * 4 + D * (C2 * 400) ≤ 4 * Real.exp 100 + 4 * D + D * C2 * 400 := by
    ring_nf
    exact le_refl _
  linarith [hmain, hmain2, hgoal]




private lemma weight_le_half {δ : ℕ → ℝ} (hδ : ∀ n, 0 ≤ δ n)
    (hsmall : ∀ n : ℕ, (n : ℝ) * δ n ≤ 1 / 2) : ∀ n : ℕ, (n.totient : ℝ) * δ n ≤ 1 / 2 := by
  intro n
  have ht : (n.totient : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.totient_le n)
  calc (n.totient : ℝ) * δ n ≤ (n : ℝ) * δ n := mul_le_mul_of_nonneg_right ht (hδ n)
    _ ≤ 1 / 2 := hsmall n

private lemma tail_weight_sum_ge_one {δ : ℕ → ℝ} (hδ : ∀ n, 0 ≤ δ n)
    (h : ¬ Summable fun n : ℕ => (n.totient : ℝ) * δ n) :
    ∀ N : ℕ, ∃ Y ≥ N, (1 : ℝ) ≤ ∑ n ∈ Finset.Icc N Y, (n.totient : ℝ) * δ n := by
  classical
  let w : ℕ → ℝ := fun n => (n.totient : ℝ) * δ n
  have hw : ∀ n, 0 ≤ w n := fun n => mul_nonneg (Nat.cast_nonneg _) (hδ n)
  have hT : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, w i) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hw).mp h
  intro N
  rcases (Filter.tendsto_atTop_atTop.mp hT) (1 + ∑ i ∈ Finset.range (N + 1), w i) with ⟨n0, hn0⟩
  let M : ℕ := max n0 (N + 1)
  let Y : ℕ := M - 1
  have hNY : N ≤ Y := by dsimp [Y, M]; omega
  refine ⟨Y, hNY, ?_⟩
  have hPM : (1 + ∑ i ∈ Finset.range (N + 1), w i) ≤ ∑ i ∈ Finset.range M, w i :=
    hn0 M (le_max_left n0 (N + 1))
  have hMN : N ≤ M := by dsimp [M]; omega
  have hsplit : (∑ i ∈ Finset.range N, w i) + (∑ i ∈ Finset.Ico N M, w i) =
      ∑ i ∈ Finset.range M, w i := by
    simpa using (Finset.sum_range_add_sum_Ico w (h := hMN))
  have hnonneg : 0 ≤ ∑ i ∈ Finset.range N, w i := Finset.sum_nonneg (fun i hi => hw i)
  have hR : ∑ i ∈ Finset.range (N + 1), w i = (∑ i ∈ Finset.range N, w i) + w N :=
    Finset.sum_range_succ w N
  have hIco_eq : (∑ i ∈ Finset.Ico N M, w i) = ∑ n ∈ Finset.Icc N Y, w n := by
    congr 1
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    constructor <;> intro h <;> constructor
    · exact h.1
    · have hnY : n ≤ Y := by have : n < M := h.2; dsimp [Y]; omega
      exact hnY
    · exact h.1
    · have hnY : n ≤ Y := h.2
      have hnM : n < M := by dsimp [Y] at hnY; omega
      exact hnM
  have hwN : 0 ≤ w N := hw N
  nlinarith

/-- L² Cauchy–Schwarz for `ℝ≥0∞`-valued functions, squared form. -/
private lemma lintegral_sq_mul_le' {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, f x * g x ∂μ) * (∫⁻ x, f x * g x ∂μ) ≤
      (∫⁻ x, f x ^ (2 : ℝ) ∂μ) * (∫⁻ x, g x ^ (2 : ℝ) ∂μ) := by
  classical
  have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := (2 : ℝ)) (q := (2 : ℝ))
    Real.HolderConjugate.two_two hf hg
  let A : ℝ≥0∞ := (∫⁻ x, f x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
  let B : ℝ≥0∞ := (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
  have hmain : (∫⁻ x, f x * g x ∂μ) ≤ A * B := by
    simpa [A, B] using h1
  have half_sq (x : ℝ≥0∞) : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
    calc
      x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        rw [← pow_two, ← ENNReal.rpow_two]
      _ = x ^ ((1 / 2 : ℝ) * (2 : ℝ)) := by rw [ENNReal.rpow_mul]
      _ = x ^ (1 : ℝ) := by norm_num
      _ = x := by rw [ENNReal.rpow_one]
  calc
    (∫⁻ x, f x * g x ∂μ) * (∫⁻ x, f x * g x ∂μ) ≤ (A * B) * (A * B) := by
      exact mul_le_mul' hmain hmain
    _ = (A * A) * (B * B) := by ring
    _ = (∫⁻ x, f x ^ (2 : ℝ) ∂μ) * (∫⁻ x, g x ^ (2 : ℝ) ∂μ) := by
      rw [show A * A = (∫⁻ x, f x ^ (2 : ℝ) ∂μ) by
        simpa [A] using half_sq (∫⁻ x, f x ^ (2 : ℝ) ∂μ)]
      rw [show B * B = (∫⁻ x, g x ^ (2 : ℝ) ∂μ) by
        simpa [B] using half_sq (∫⁻ x, g x ^ (2 : ℝ) ∂μ)]


-- TEMPORARY placeholder for the deep lemma (to be imported from Commons)

private lemma weight_nonneg {δ : ℕ → ℝ} (hδ : ∀ n, 0 ≤ δ n) : ∀ n : ℕ, 0 ≤ (n.totient : ℝ) * δ n :=
  fun n => mul_nonneg (Nat.cast_nonneg _) (hδ n)

private lemma second_moment_Icc {α : Type*} [MeasurableSpace α] (μ : Measure α) (X Y : ℕ)
    (s : ℕ → Set α) (hs : ∀ q, q ∈ Finset.Icc X Y → MeasurableSet (s q)) :
    ((∑ q ∈ Finset.Icc X Y, μ (s q)) ^ 2 : ℝ≥0∞) ≤
      μ (⋃ q ∈ Finset.Icc X Y, s q) *
        (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y, μ (s q ∩ s r)) := by
  classical
  let F : Finset ℕ := Finset.Icc X Y
  let c : ℕ → α → ℝ≥0∞ := fun q => (s q).indicator (fun _ => (1 : ℝ≥0∞))
  let f : α → ℝ≥0∞ := fun x => ∑ q ∈ F, c q x
  let g : α → ℝ≥0∞ := (⋃ q ∈ F, s q).indicator (fun _ => (1 : ℝ≥0∞))
  have hU_meas : MeasurableSet (⋃ q ∈ F, s q) := by
    dsimp [F]
    exact Finset.measurableSet_biUnion (s := Finset.Icc X Y) (fun q hq => hs q hq)
  have hc_meas (q : ℕ) (hq : q ∈ F) : Measurable (c q) := by
    dsimp [c]
    exact Measurable.indicator measurable_const (hs q (by simpa [F] using hq))
  have hf_meas : Measurable f := by
    dsimp [f]
    exact Finset.measurable_sum F (fun q hq => hc_meas q hq)
  have hg_meas : Measurable g := by
    dsimp [g]
    exact Measurable.indicator measurable_const hU_meas
  have hf_aemeas : AEMeasurable f μ := hf_meas.aemeasurable
  have hg_aemeas : AEMeasurable g μ := hg_meas.aemeasurable
  have h_fg : f * g = f := by
    funext x
    by_cases hx : x ∈ (⋃ q ∈ F, s q)
    · simp [f, g, hx]
    · have hc0 : ∀ q ∈ F, c q x = 0 := by
        intro q hq
        have hni : x ∉ s q := fun hxi => hx (mem_iUnion₂.mpr ⟨q, hq, hxi⟩)
        simp [c, hni]
      rw [show f x = 0 by
        dsimp [f]
        exact Finset.sum_eq_zero (fun q hq => hc0 q hq)]
      simp [g, hx]
  have hc_mul (q r : ℕ) (hq : q ∈ F) (hr : r ∈ F) :
      c q * c r = (s q ∩ s r).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hxi : x ∈ s q <;> by_cases hxj : x ∈ s r <;> simp [c, hxi, hxj]
  have h_f_mul : ∀ x : α, f x * f x = ∑ q ∈ F, ∑ r ∈ F, c q x * c r x := by
    intro x
    simp only [f]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro q _
    rw [Finset.mul_sum]
  have h_int_f : (∫⁻ x, f x ∂μ) = ∑ q ∈ F, μ (s q) := by
    calc
      (∫⁻ x, f x ∂μ) = ∫⁻ x, (∑ q ∈ F, c q x) ∂μ := by rfl
      _ = ∑ q ∈ F, (∫⁻ x, c q x ∂μ) := by
        exact lintegral_finsetSum F (fun q hq => hc_meas q hq)
      _ = ∑ q ∈ F, μ (s q) := by
        refine Finset.sum_congr rfl ?_
        intro q hq
        dsimp [c]
        simpa using lintegral_indicator_const (hs q (by simpa [F] using hq)) (1 : ℝ≥0∞)
  have h_int_fg : (∫⁻ x, f x * g x ∂μ) = ∑ q ∈ F, μ (s q) := by
    calc
      (∫⁻ x, f x * g x ∂μ) = ∫⁻ x, f x ∂μ := by
        apply lintegral_congr
        intro x
        exact congrFun h_fg x
      _ = ∑ q ∈ F, μ (s q) := h_int_f
  have hg_pow (x : α) : g x ^ (2 : ℝ) = g x := by
    rw [ENNReal.rpow_two]
    by_cases hx : x ∈ (⋃ q ∈ F, s q) <;> simp [g, hx]
  have h_int_g2 : (∫⁻ x, g x ^ (2 : ℝ) ∂μ) = μ (⋃ q ∈ F, s q) := by
    calc
      (∫⁻ x, g x ^ (2 : ℝ) ∂μ) = ∫⁻ x, g x ∂μ := by
        apply lintegral_congr
        intro x
        exact hg_pow x
      _ = μ (⋃ q ∈ F, s q) := by
        dsimp [g]
        simpa using lintegral_indicator_const hU_meas (1 : ℝ≥0∞)
  have h_int_f2 : (∫⁻ x, f x ^ (2 : ℝ) ∂μ) = ∑ q ∈ F, ∑ r ∈ F, μ (s q ∩ s r) := by
    calc
      (∫⁻ x, f x ^ (2 : ℝ) ∂μ) = ∫⁻ x, f x * f x ∂μ := by
        apply lintegral_congr
        intro x
        rw [ENNReal.rpow_two, pow_two]
      _ = ∫⁻ x, (∑ q ∈ F, ∑ r ∈ F, c q x * c r x) ∂μ := by
        apply lintegral_congr
        intro x
        exact h_f_mul x
      _ = ∑ q ∈ F, ∑ r ∈ F, (∫⁻ x, c q x * c r x ∂μ) := by
        calc
          (∫⁻ x, (∑ q ∈ F, ∑ r ∈ F, c q x * c r x) ∂μ)
              = ∑ q ∈ F, (∫⁻ x, (∑ r ∈ F, c q x * c r x) ∂μ) := by
                  exact lintegral_finsetSum F (fun q hq =>
                    Finset.measurable_sum F (fun r hr => (hc_meas q hq).mul (hc_meas r hr)))
          _ = ∑ q ∈ F, ∑ r ∈ F, (∫⁻ x, c q x * c r x ∂μ) := by
              apply Finset.sum_congr rfl
              intro q hqF
              exact lintegral_finsetSum F (fun r hrF => (hc_meas q hqF).mul (hc_meas r hrF))
      _ = ∑ q ∈ F, ∑ r ∈ F, μ (s q ∩ s r) := by
        refine Finset.sum_congr rfl ?_
        intro q hqF
        refine Finset.sum_congr rfl ?_
        intro r hrF
        calc
          (∫⁻ x, c q x * c r x ∂μ)
              = ∫⁻ x, ((s q ∩ s r).indicator (fun _ => (1 : ℝ≥0∞))) x ∂μ := by
                  apply lintegral_congr
                  intro x
                  exact congrFun (hc_mul q r hqF hrF) x
          _ = μ (s q ∩ s r) := by
              simpa using lintegral_indicator_const
                (MeasurableSet.inter (hs q (by simpa [F] using hqF)) (hs r (by simpa [F] using hrF))) (1 : ℝ≥0∞)

  have hcs := lintegral_sq_mul_le' μ hf_aemeas hg_aemeas
  calc
    ((∑ q ∈ Finset.Icc X Y, μ (s q)) ^ 2 : ℝ≥0∞)
        = (∑ q ∈ F, μ (s q)) * (∑ q ∈ F, μ (s q)) := by
            rw [pow_two]
    _ = (∫⁻ x, f x * g x ∂μ) * (∫⁻ x, f x * g x ∂μ) := by rw [← h_int_fg]
    _ ≤ (∫⁻ x, f x ^ (2 : ℝ) ∂μ) * (∫⁻ x, g x ^ (2 : ℝ) ∂μ) := hcs
    _ = (∑ q ∈ F, ∑ r ∈ F, μ (s q ∩ s r)) * μ (⋃ q ∈ F, s q) := by rw [h_int_f2, h_int_g2]
    _ = μ (⋃ q ∈ F, s q) * (∑ q ∈ F, ∑ r ∈ F, μ (s q ∩ s r)) := by rw [mul_comm]
    _ = μ (⋃ q ∈ Finset.Icc X Y, s q) *
        (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y, μ (s q ∩ s r)) := by
            simp [F]

/-- Second-moment lower bound with division, indexed by the block `Icc X Y`. -/
private lemma measure_union_lower_Icc (X Y : ℕ) (s : ℕ → Set UnitAddCircle)
    (hs : ∀ q, q ∈ Finset.Icc X Y → MeasurableSet (s q)) {L U : ℝ≥0∞}
    (hL : L ≤ ∑ q ∈ Finset.Icc X Y, volume (s q))
    (hU : (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y, volume (s q ∩ s r)) ≤ U) :
    L ^ 2 / U ≤ volume (⋃ q ∈ Finset.Icc X Y, s q) := by
  have hsm := second_moment_Icc (μ := volume) X Y s hs
  have h1 : L ^ 2 ≤ (∑ q ∈ Finset.Icc X Y, volume (s q)) ^ 2 := by
    exact ENNReal.pow_le_pow_left (n := 2) hL
  have h3 : volume (⋃ q ∈ Finset.Icc X Y, s q) *
      (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y, volume (s q ∩ s r)) ≤
      volume (⋃ q ∈ Finset.Icc X Y, s q) * U := by
    exact mul_le_mul' le_rfl hU
  have hle : L ^ 2 ≤ volume (⋃ q ∈ Finset.Icc X Y, s q) * U := by
    exact le_trans (le_trans h1 hsm) h3
  exact ENNReal.div_le_of_le_mul hle

/-- Lower bound for the measure of the union of the approximation sets over a block. -/
private lemma union_measure_lower_block {δ : ℕ → ℝ} (hδ : ∀ n, 0 ≤ δ n)
    (hsmall : ∀ n : ℕ, (n : ℝ) * δ n ≤ 1 / 2) {K : ℝ} (hK0 : 0 < K)
    (X Y : ℕ) (hX : 1 ≤ X)
    (hS1 : (1 : ℝ) ≤ ∑ q ∈ Finset.Icc X Y, (q.totient : ℝ) * δ q)
    (hS2 : ∑ q ∈ Finset.Icc X Y, (q.totient : ℝ) * δ q ≤ 3 / 2)
    (hpair : (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
      MeasureTheory.volume (approxAddOrderOf UnitAddCircle q (δ q) ∩
        approxAddOrderOf UnitAddCircle r (δ r))) ≤ ENNReal.ofReal K) :
    ENNReal.ofReal 4 / ENNReal.ofReal K ≤
      MeasureTheory.volume (⋃ q ∈ Finset.Icc X Y, approxAddOrderOf UnitAddCircle q (δ q)) := by
  classical
  let A : ℕ → Set UnitAddCircle := fun q => approxAddOrderOf UnitAddCircle q (δ q)
  let S : ℝ := ∑ q ∈ Finset.Icc X Y, (q.totient : ℝ) * δ q
  let L : ℝ≥0∞ := ENNReal.ofReal (2 * S)
  let U : ℝ≥0∞ := ENNReal.ofReal K
  have hX0 : X ≠ 0 := by omega
  have hA_meas : ∀ q, q ∈ Finset.Icc X Y → MeasurableSet (A q) := by
    intro q hq
    dsimp [A]
    rw [approxAddOrderOf]
    exact Metric.isOpen_thickening.measurableSet
  have hL : L ≤ ∑ q ∈ Finset.Icc X Y, volume (A q) := by
    dsimp [L, A]
    rw [approxAddOrderOf_volume_eq_two_mul_Icc X Y hX0 δ hδ hsmall]
  have hU : (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y, volume (A q ∩ A r)) ≤ U := by
    dsimp [U, A]
    simpa using hpair
  have hμ := measure_union_lower_Icc X Y A hA_meas (L := L) (U := U) hL hU
  have hLsq : ENNReal.ofReal 4 ≤ L ^ 2 := by
    dsimp [L]
    have h2S : (0 : ℝ) ≤ 2 * S := by
      have hS : 0 ≤ S := by
        dsimp [S]
        exact Finset.sum_nonneg (fun q hq => weight_nonneg hδ q)
      positivity
    have hpow : (ENNReal.ofReal (2 * S)) ^ 2 = ENNReal.ofReal ((2 * S) ^ 2) := by
      exact (ENNReal.ofReal_pow h2S 2).symm
    rw [hpow]
    apply ENNReal.ofReal_le_ofReal
    have hS1' : (1 : ℝ) ≤ S := by simpa [S] using hS1
    nlinarith
  have hc_le : ENNReal.ofReal 4 / ENNReal.ofReal K ≤ L ^ 2 / U := by
    rw [ENNReal.le_div_iff_mul_le (h0 := Or.inl (by
      dsimp [U]; exact (ENNReal.ofReal_pos.mpr hK0).ne')) (ht := Or.inl (by
      dsimp [U]; exact ENNReal.ofReal_ne_top))]
    calc
      (ENNReal.ofReal 4 / ENNReal.ofReal K) * U = ENNReal.ofReal 4 := by
        dsimp [U]
        rw [ENNReal.div_mul_cancel (by exact (ENNReal.ofReal_pos.mpr hK0).ne')
          (by exact ENNReal.ofReal_ne_top)]
      _ ≤ L ^ 2 := hLsq
  exact le_trans hc_le hμ

/-- Membership in a union indexed by a finset. -/
private lemma mem_biUnion_finset {ι : Type*} {A : Finset ι} {f : ι → Set UnitAddCircle}
    {x : UnitAddCircle} (h : x ∈ ⋃ a ∈ A, f a) : ∃ a ∈ A, x ∈ f a := by
  simpa only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] using h

/-- A point in the intersection of two balls forces the centres to be close. -/
private lemma ball_inter_subset_of_dist (x : UnitAddCircle) {y z : UnitAddCircle} {α β : ℝ}
    (h : x ∈ Metric.ball y α ∩ Metric.ball z β) : dist y z < α + β := by
  have h1 : dist x y < α := by simpa [dist_comm] using h.1
  have h2 : dist x z < β := h.2
  calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
    _ = dist x y + dist x z := by rw [dist_comm y x]
    _ < α + β := add_lt_add h1 h2

/-- **Geometry step.**  The volume of the intersection of the level-`q` and level-`r`
approximating sets is at most `2·min α β` times the number of reduced pairs of centres at
distance `< α + β`. -/
theorem inter_volume_le_two_mul_min_mul_card (q r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    MeasureTheory.volume
        (approxAddOrderOf UnitAddCircle q α ∩ approxAddOrderOf UnitAddCircle r β) ≤
      ENNReal.ofReal (2 * min α β) *
        ((((Finset.range q).filter (fun a : ℕ => a.gcd q = 1)).product
          ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
          (fun ab : ℕ × ℕ =>
            dist (((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)
                 (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle) < α + β)).card := by
  classical
  let A : Finset ℕ := (Finset.range q).filter (fun a : ℕ => a.gcd q = 1)
  let B : Finset ℕ := (Finset.range r).filter (fun b : ℕ => b.gcd r = 1)
  let ptq : ℕ → UnitAddCircle := fun a => (((a : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)
  let ptr : ℕ → UnitAddCircle := fun b => (((b : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)
  let E : ℕ × ℕ → Set UnitAddCircle := fun ab => Metric.ball (ptq ab.1) α ∩ Metric.ball (ptr ab.2) β
  let H : ℕ × ℕ → Prop := fun ab => dist (ptq ab.1) (ptr ab.2) < α + β
  have hleft : approxAddOrderOf UnitAddCircle q α = ⋃ a ∈ A, Metric.ball (ptq a) α := by
    simpa [A, ptq] using approxAddOrderOf_eq_biUnion_ball q hq α
  have hright : approxAddOrderOf UnitAddCircle r β = ⋃ b ∈ B, Metric.ball (ptr b) β := by
    simpa [B, ptr] using approxAddOrderOf_eq_biUnion_ball r hr β
  have hset : approxAddOrderOf UnitAddCircle q α ∩ approxAddOrderOf UnitAddCircle r β =
      ⋃ ab ∈ A.product B, E ab := by
    rw [hleft, hright]
    ext x
    constructor
    · intro hx
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨a, ha, hxa⟩ := mem_biUnion_finset hx1
      obtain ⟨b, hb, hxb⟩ := mem_biUnion_finset hx2
      exact mem_iUnion₂.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, ⟨hxa, hxb⟩⟩
    · intro hx
      obtain ⟨ab, hab, hxE⟩ := mem_biUnion_finset hx
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      have hxE' : x ∈ Metric.ball (ptq ab.1) α ∩ Metric.ball (ptr ab.2) β := hxE
      exact ⟨mem_iUnion₂.mpr ⟨ab.1, ha, hxE'.1⟩, mem_iUnion₂.mpr ⟨ab.2, hb, hxE'.2⟩⟩
  have hle : ∀ ab ∈ A.product B, MeasureTheory.volume (E ab) ≤
      (if H ab then ENNReal.ofReal (2 * min α β) else 0) := by
    intro ab _
    by_cases hc : H ab
    · rw [if_pos hc]
      have h1 : MeasureTheory.volume (E ab) ≤ MeasureTheory.volume (Metric.ball (ptq ab.1) α) :=
        measure_mono inter_subset_left
      have h2 : MeasureTheory.volume (Metric.ball (ptq ab.1) α) ≤ ENNReal.ofReal (2 * α) :=
        volume_ball_le_ofReal_two_mul _ hα
      have h3 : MeasureTheory.volume (Metric.ball (ptr ab.2) β) ≤ ENNReal.ofReal (2 * β) :=
        volume_ball_le_ofReal_two_mul _ hβ
      have h4 : MeasureTheory.volume (E ab) ≤ ENNReal.ofReal (2 * β) :=
        le_trans (measure_mono inter_subset_right) h3
      calc MeasureTheory.volume (E ab)
          ≤ min (ENNReal.ofReal (2 * α)) (ENNReal.ofReal (2 * β)) := le_min (le_trans h1 h2) h4
        _ = ENNReal.ofReal (min (2 * α) (2 * β)) := (ENNReal.ofReal_min (2*α) (2*β)).symm
        _ = ENNReal.ofReal (2 * min α β) := by
              congr 1
              exact (mul_min_of_nonneg α β (by norm_num)).symm
    · rw [if_neg hc]
      have hempty : E ab = ∅ := by
        refine eq_empty_iff_forall_notMem.mpr (fun x hx => ?_)
        exact absurd (ball_inter_subset_of_dist x hx) (not_lt.mpr (not_lt.mp hc))
      rw [hempty, measure_empty]
  calc MeasureTheory.volume
        (approxAddOrderOf UnitAddCircle q α ∩ approxAddOrderOf UnitAddCircle r β)
      = MeasureTheory.volume (⋃ ab ∈ A.product B, E ab) := by rw [hset]
    _ ≤ ∑ ab ∈ A.product B, MeasureTheory.volume (E ab) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ ab ∈ A.product B, (if H ab then ENNReal.ofReal (2 * min α β) else 0) :=
        Finset.sum_le_sum hle
    _ = ENNReal.ofReal (2 * min α β) *
        (((A.product B).filter H).card : ℝ≥0∞) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = ENNReal.ofReal (2 * min α β) *
        (((((Finset.range q).filter (fun a : ℕ => a.gcd q = 1)).product
          ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
          (fun ab : ℕ × ℕ =>
            dist (((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)
                 (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle) < α + β)).card : ℝ≥0∞) := by
        rfl



noncomputable section
open scoped BigOperators ENNReal
open Finset Metric MeasureTheory Set


/-- Number of reduced pairs of centres at circle-distance `< Δ`. -/
private def closePairCount (q r : ℕ) (Δ : ℝ) : ℕ :=
  ((((Finset.range q).filter (fun a : ℕ => a.gcd q = 1)).product
    ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
    (fun ab : ℕ × ℕ =>
      ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
         (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < Δ)).card

/-- The prime product over the primes of `qr/gcd(q,r)^2` above a threshold. -/
private def pairProd (q r : ℕ) (t : ℝ) : ℝ :=
  ∏ p ∈ (Nat.primeFactors (q * r / (q.gcd r * q.gcd r))).filter
      (fun p : ℕ => t < (p : ℝ)), (1 - 1 / (p : ℝ))⁻¹

/-- The per-pair volume bound, derived from the geometry lemma and the (hypothetical) count
bound for close reduced pairs. -/
theorem pair_volume_bound
    (count_bound : ∀ (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (hqr : q ≠ r) (Δ : ℝ), 0 ≤ Δ →
      (closePairCount q r Δ : ℝ) ≤ 8000 * Δ * (q.totient : ℝ) * (r.totient : ℝ) *
        pairProd q r ((q : ℝ) * (r : ℝ) * Δ / (q.gcd r : ℝ)))
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    MeasureTheory.volume (approxAddOrderOf UnitAddCircle m (δ m) ∩
        approxAddOrderOf UnitAddCircle n (δ n)) ≤
      ENNReal.ofReal 8000 * ENNReal.ofReal (2 * ((m.totient : ℝ) * δ m)) *
        ENNReal.ofReal (2 * ((n.totient : ℝ) * δ n)) *
        ENNReal.ofReal (pairProd m n ((m : ℝ) * (n : ℝ) * max (δ m) (δ n) / (m.gcd n : ℝ))) := by
  classical
  set g : ℕ := m.gcd n with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left n hm
  set Psm : ℝ := pairProd m n ((m : ℝ) * (n : ℝ) * (δ m + δ n) / (g : ℝ)) with hPsm
  set Pbig : ℝ := pairProd m n ((m : ℝ) * (n : ℝ) * max (δ m) (δ n) / (g : ℝ)) with hPbig
  have hPbig_eq : Pbig = pairProd m n ((m : ℝ) * (n : ℝ) * max (δ m) (δ n) / (m.gcd n : ℝ)) := by
    rw [hPbig, hg]
  -- (1) transfer: `Psm ≤ Pbig`
  have htrans : Psm ≤ Pbig := by
    rw [hPsm, hPbig, pairProd, pairProd]
    refine Finset.prod_le_prod_of_subset_of_one_le₀ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      refine ⟨hp.1, lt_of_le_of_lt ?_ hp.2⟩
      have hgR : (0:ℝ) < (g:ℝ) := by exact_mod_cast hgpos
      have hle : max (δ m) (δ n) ≤ δ m + δ n :=
        max_le (le_add_of_nonneg_right (hδ n)) (le_add_of_nonneg_left (hδ m))
      have hqr : (0:ℝ) ≤ (m:ℝ)*(n:ℝ) := by positivity
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle hqr) hgR.le
    · intro p hp
      simp only [Finset.mem_filter] at hp
      have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp.1).two_le
      have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
      have hp1 : (0:ℝ) < 1 - 1/(p:ℝ) := by
        have hle : (1:ℝ)/(p:ℝ) ≤ 1/2 := by
          rw [div_le_iff₀ (by linarith)]; linarith
        linarith
      positivity
    · intro p hp hnot
      simp only [Finset.mem_filter] at hp
      have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp.1).two_le
      have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
      have h1p : (0:ℝ) < 1/(p:ℝ) := by positivity
      have hone : (1:ℝ) - 1/(p:ℝ) ≤ 1 := by linarith
      have hp1 : (0:ℝ) < 1 - 1/(p:ℝ) := by
        have hle : (1:ℝ)/(p:ℝ) ≤ 1/2 := by
          rw [div_le_iff₀ (by linarith)]; linarith
        linarith
      exact (one_le_inv₀ hp1).mpr hone
  -- (2) the count bound, in the form of the geometry lemma
  have hfilt : ((((Finset.range m).filter (fun a : ℕ => a.gcd m = 1)).product
        ((Finset.range n).filter (fun b : ℕ => b.gcd n = 1))).filter
        (fun ab : ℕ × ℕ =>
          dist (((ab.1 : ℝ) / (m : ℝ) : ℝ) : UnitAddCircle)
               (((ab.2 : ℝ) / (n : ℝ) : ℝ) : UnitAddCircle) < δ m + δ n)).card
      = closePairCount m n (δ m + δ n) := by
    rw [closePairCount]
    congr 1
    ext ab
    simp only [Finset.mem_filter, dist_eq_norm]
  have hcard : ((closePairCount m n (δ m + δ n) : ℕ) : ℝ) ≤
      8000 * (δ m + δ n) * (m.totient : ℝ) * (n.totient : ℝ) * Psm := by
    have hc := count_bound m n hm hn hmn (δ m + δ n) (by linarith [hδ m, hδ n])
    rw [hPsm, pairProd, hg]
    exact hc
  -- (3) geometry
  have hgeo := inter_volume_le_two_mul_min_mul_card m n hm hn (δ m) (δ n) (hδ m) (hδ n)
  have hgeo' : MeasureTheory.volume (approxAddOrderOf UnitAddCircle m (δ m) ∩
      approxAddOrderOf UnitAddCircle n (δ n))
      ≤ ENNReal.ofReal (2 * min (δ m) (δ n)) * (closePairCount m n (δ m + δ n) : ℝ≥0∞) := by
    refine le_trans hgeo ?_
    rw [hfilt]
  have hP0 : 0 ≤ Psm := by
    rw [hPsm, pairProd]
    refine Finset.prod_nonneg (fun p hp => ?_)
    simp only [Finset.mem_filter] at hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp.1).two_le
    have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    have hle : (1:ℝ)/(p:ℝ) ≤ 1/2 := by rw [div_le_iff₀ (by linarith)]; linarith
    have hpos : (0:ℝ) < 1 - 1/(p:ℝ) := by linarith
    positivity
  have hstep1 : MeasureTheory.volume (approxAddOrderOf UnitAddCircle m (δ m) ∩
      approxAddOrderOf UnitAddCircle n (δ n))
      ≤ ENNReal.ofReal (2 * min (δ m) (δ n)) * ENNReal.ofReal
          (8000 * (δ m + δ n) * (m.totient : ℝ) * (n.totient : ℝ) * Psm) := by
    refine le_trans hgeo' ?_
    rw [← ENNReal.ofReal_natCast (closePairCount m n (δ m + δ n))]
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hcard)
  have hreal : 2 * min (δ m) (δ n) * (8000 * (δ m + δ n) * (m.totient : ℝ) * (n.totient : ℝ) * Psm)
      ≤ 8000 * (2 * ((m.totient : ℝ) * δ m)) * (2 * ((n.totient : ℝ) * δ n)) * Pbig := by
    have h1 : 2 * min (δ m) (δ n) * (δ m + δ n) ≤ 4 * (δ m * δ n) := by
      nlinarith [min_le_left (δ m) (δ n), min_le_right (δ m) (δ n), hδ m, hδ n]
    have hA : 0 ≤ 8000 * ((m.totient : ℝ) * (n.totient : ℝ)) :=
      mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hbb : 0 ≤ 4 * (δ m * δ n) := mul_nonneg (by norm_num) (mul_nonneg (hδ m) (hδ n))
    have hcc : 0 ≤ 8000 * ((m.totient : ℝ) * (n.totient : ℝ)) * Psm :=
      mul_nonneg hA hP0
    have hcc2 : 0 ≤ 4 * (δ m * δ n) := hbb
    calc 2 * min (δ m) (δ n) * (8000 * (δ m + δ n) * (m.totient : ℝ) * (n.totient : ℝ) * Psm)
        = (2 * min (δ m) (δ n) * (δ m + δ n)) *
            (8000 * ((m.totient : ℝ) * (n.totient : ℝ)) * Psm) := by ring
      _ ≤ (4 * (δ m * δ n)) * (8000 * ((m.totient : ℝ) * (n.totient : ℝ)) * Pbig) :=
          mul_le_mul h1 (mul_le_mul_of_nonneg_left htrans hA) hcc hcc2
      _ = 8000 * (2 * ((m.totient : ℝ) * δ m)) * (2 * ((n.totient : ℝ) * δ n)) * Pbig := by ring
  have hstep2 : ENNReal.ofReal (2 * min (δ m) (δ n)) * ENNReal.ofReal
        (8000 * (δ m + δ n) * (m.totient : ℝ) * (n.totient : ℝ) * Psm)
      ≤ ENNReal.ofReal 8000 * ENNReal.ofReal (2 * ((m.totient : ℝ) * δ m)) *
        ENNReal.ofReal (2 * ((n.totient : ℝ) * δ n)) * ENNReal.ofReal Pbig := by
    have hA : (0:ℝ) ≤ 2 * ((m.totient : ℝ) * δ m) :=
      mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (hδ m))
    have hB : (0:ℝ) ≤ 2 * ((n.totient : ℝ) * δ n) :=
      mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (hδ n))
    have hφm : (0:ℝ) ≤ (m.totient : ℝ) := Nat.cast_nonneg _
    have hφn : (0:ℝ) ≤ (n.totient : ℝ) := Nat.cast_nonneg _
    have hΔ : 0 ≤ δ m + δ n := by linarith [hδ m, hδ n]
    have hX : (0:ℝ) ≤ 2 * min (δ m) (δ n) := by
      have := le_min (hδ m) (hδ n); linarith
    have hY : (0:ℝ) ≤ 8000 * (δ m + δ n) * (m.totient : ℝ) * (n.totient : ℝ) * Psm :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hΔ) hφm) hφn) hP0
    calc ENNReal.ofReal (2 * min (δ m) (δ n)) * ENNReal.ofReal
          (8000 * (δ m + δ n) * (m.totient : ℝ) * (n.totient : ℝ) * Psm)
        = ENNReal.ofReal (2 * min (δ m) (δ n) *
            (8000 * (δ m + δ n) * (m.totient : ℝ) * (n.totient : ℝ) * Psm)) := by
            rw [ENNReal.ofReal_mul hX]
      _ ≤ ENNReal.ofReal (8000 * (2 * ((m.totient : ℝ) * δ m)) *
            (2 * ((n.totient : ℝ) * δ n)) * Pbig) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal 8000 * ENNReal.ofReal (2 * ((m.totient : ℝ) * δ m)) *
          ENNReal.ofReal (2 * ((n.totient : ℝ) * δ n)) * ENNReal.ofReal Pbig := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 8000)]
          rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hA :
            (0:ℝ) ≤ 8000 * (2 * ((m.totient : ℝ) * δ m)))]
          rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hA) hB :
            (0:ℝ) ≤ 8000 * (2 * ((m.totient : ℝ) * δ m)) * (2 * ((n.totient : ℝ) * δ n)))]
  refine le_trans hstep1 ?_
  rw [hPbig_eq]
  exact hstep2


/-- Main theorem: under the smallness hypothesis `n * δ n ≤ 1 / 2`, divergence of the
totient-weighted series gives a well-approximable set of positive measure. -/
theorem km_positive_small (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hsmall : ∀ n : ℕ, (n : ℝ) * δ n ≤ 1 / 2)
    (h : ¬ Summable fun n : ℕ => n.totient * δ n) :
    0 < MeasureTheory.volume (addWellApproximable UnitAddCircle δ) := by
  classical
  set c₁ : ℝ := 8000 with hc₁def
  have hc₁pos : 0 < c₁ := by rw [hc₁def]; norm_num
  -- the count bound for close reduced pairs, in the normalisation used here
  have hcount : ∀ (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (hqr : q ≠ r) (Δ : ℝ), 0 ≤ Δ →
      (closePairCount q r Δ : ℝ) ≤ 8000 * Δ * (q.totient : ℝ) * (r.totient : ℝ) *
        pairProd q r ((q : ℝ) * (r : ℝ) * Δ / (q.gcd r : ℝ)) := by
    intro q r hq hr hqr Δ hΔ
    have hc := Commons.NumberTheory.DuffinSchaeffer.reduced_pair_window_bound q r hq hr hqr Δ hΔ
    dsimp only at hc
    rw [pairProd]
    have hcast : ((q * r / q.gcd r : ℕ) : ℝ) = (q:ℝ)*(r:ℝ)/(q.gcd r : ℝ) := by
      have hdiv : q.gcd r ∣ q * r := dvd_mul_of_dvd_left (Nat.gcd_dvd_left q r) r
      have hne : ((q.gcd r : ℕ) : ℝ) ≠ 0 := by
        have hpos : q.gcd r ≠ 0 := by
          have := Nat.gcd_pos_of_pos_left r hq
          omega
        exact_mod_cast hpos
      rw [Nat.cast_div hdiv hne, Nat.cast_mul]
    rw [hcast] at hc
    rw [show Δ * ((q:ℝ)*(r:ℝ)/(q.gcd r : ℝ)) = (q:ℝ)*(r:ℝ)*Δ/(q.gcd r : ℝ) by ring] at hc
    exact hc
  obtain ⟨Karith, hKarithpos, hKarith⟩ := km_pair_product_sum_bound
  set w : ℕ → ℝ := fun q => (q.totient : ℝ) * δ q with hwdef
  have hw0 : ∀ q, 0 ≤ w q := fun q => mul_nonneg (Nat.cast_nonneg _) (hδ q)
  -- per-pair volume bound: geometry + count of close reduced pairs
  have hPV' : ∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n),
      MeasureTheory.volume (approxAddOrderOf UnitAddCircle m (δ m) ∩
          approxAddOrderOf UnitAddCircle n (δ n)) ≤
        ENNReal.ofReal c₁ * ENNReal.ofReal (2 * w m) * ENNReal.ofReal (2 * w n) *
          ENNReal.ofReal (∏ p ∈ (Nat.primeFactors (m * n / (m.gcd n * m.gcd n))).filter
              (fun p : ℕ => (m : ℝ) * (n : ℝ) * max (δ m) (δ n) / (m.gcd n : ℝ) < (p : ℝ)),
              (1 - 1 / (p : ℝ))⁻¹) := by
    intro m n hm hn hmn
    have h := pair_volume_bound hcount δ hδ m n hm hn hmn
    rw [pairProd] at h
    rw [hc₁def, hwdef]
    exact h
  -- the pair-sum second moment bound
  have hblocks : ∀ X : ℕ, 1 ≤ X → ∃ Y : ℕ, X < Y ∧
      (1 : ℝ) ≤ ∑ q ∈ Finset.Icc X Y, w q ∧ ∑ q ∈ Finset.Icc X Y, w q ≤ 3 / 2 := by
    intro X hX
    have htail : ∀ N : ℕ, ∃ Y ≥ N, (1 : ℝ) ≤ ∑ n ∈ Finset.Icc N Y, w n := by
      intro N
      have := tail_weight_sum_ge_one (δ := δ) hδ ?_
      · exact this N
      · simpa [hwdef] using h
    exact Commons.Analysis.Asymptotics.exists_Icc_sum_between_of_tail_lower w hw0
      (fun n => by
        rw [hwdef]
        exact weight_le_half (δ := δ) hδ hsmall n) htail X
  set U : ℝ := 4 + 4 * c₁ * Karith with hUdef
  have hUpos : 0 < U := by
    rw [hUdef]; nlinarith [hc₁pos, hKarithpos]
  -- pair-sum bound over a block
  have hpairsum : ∀ X Y : ℕ, 1 ≤ X → X ≤ Y →
      (1 : ℝ) ≤ ∑ q ∈ Finset.Icc X Y, w q →
      (∑ q ∈ Finset.Icc X Y, w q) ≤ 3 / 2 →
      (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
          MeasureTheory.volume (approxAddOrderOf UnitAddCircle q (δ q) ∩
            approxAddOrderOf UnitAddCircle r (δ r))) ≤ ENNReal.ofReal U := by
    intro X Y hX hXY hS1 hS2
    set A : ℕ → Set UnitAddCircle := fun n => approxAddOrderOf UnitAddCircle n (δ n) with hAdef
    set Pq : ℕ → ℕ → ℝ := fun q r => ∏ p ∈ (Nat.primeFactors (q * r / (q.gcd r * q.gcd r))).filter
                (fun p : ℕ => (q : ℝ) * (r : ℝ) * max (δ q) (δ r) / (q.gcd r : ℝ) < (p : ℝ)),
                (1 - 1 / (p : ℝ))⁻¹ with hPq
    have hPq_nonneg : ∀ q r, 0 ≤ Pq q r := by
      intro q r
      rw [hPq]
      refine Finset.prod_nonneg (fun p hp => ?_)
      rw [Finset.mem_filter] at hp
      have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp.1).two_le
      have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
      have : (0:ℝ) < 1 - 1/(p:ℝ) := by
        rw [sub_pos, div_lt_one hpR]; exact_mod_cast (by omega : 1 < p)
      positivity
    -- diagonal
    have hdiag : (∑ q ∈ Finset.Icc X Y, MeasureTheory.volume (A q)) ≤ ENNReal.ofReal 4 := by
      have hX0 : X ≠ 0 := by omega
      have h1 : (∑ q ∈ Finset.Icc X Y, MeasureTheory.volume (A q))
          = ENNReal.ofReal (2 * ∑ q ∈ Finset.Icc X Y, w q) := by
        rw [hAdef]
        have := approxAddOrderOf_volume_eq_two_mul_Icc X Y hX0 δ hδ hsmall
        simpa [hwdef] using this
      rw [h1]
      apply ENNReal.ofReal_le_ofReal
      linarith
    -- off-diagonal
    have hpe : ∀ q ∈ Finset.Icc X Y, ∀ r ∈ (Finset.Icc X Y).erase q,
        MeasureTheory.volume (A q ∩ A r) ≤ ENNReal.ofReal (4 * c₁ * w q * w r * Pq q r) := by
      intro q hq r hr
      have hq1 : 1 ≤ q := le_trans hX (Finset.mem_Icc.mp hq).1
      have hr1 : 1 ≤ r := le_trans hX (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hr)).1
      have hqr : q ≠ r := ((Finset.mem_erase.mp hr).1).symm
      have hb := hPV' q r (by omega) (by omega) hqr
      have h1 : ENNReal.ofReal c₁ * ENNReal.ofReal (2 * w q) * ENNReal.ofReal (2 * w r) *
            ENNReal.ofReal (Pq q r) = ENNReal.ofReal (4 * c₁ * w q * w r * Pq q r) := by
        have hwq : (0:ℝ) ≤ w q := hw0 q
        have hwr : (0:ℝ) ≤ w r := hw0 r
        rw [← ENNReal.ofReal_mul (le_of_lt hc₁pos)]
        rw [← ENNReal.ofReal_mul (mul_nonneg (le_of_lt hc₁pos) (mul_nonneg (by norm_num) hwq))]
        rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (le_of_lt hc₁pos)
          (mul_nonneg (by norm_num) hwq)) (mul_nonneg (by norm_num) hwr))]
        congr 1
        ring
      rw [h1] at hb
      exact hb
    have hoff : (∑ q ∈ Finset.Icc X Y, ∑ r ∈ (Finset.Icc X Y).erase q, MeasureTheory.volume (A q ∩ A r))
        ≤ ENNReal.ofReal (4 * c₁ * Karith) := by
      have hfold_inner : ∀ q, (∑ r ∈ Finset.Icc X Y,
            ENNReal.ofReal (4 * c₁ * w q * w r * Pq q r))
          = ENNReal.ofReal (∑ r ∈ Finset.Icc X Y, 4 * c₁ * w q * w r * Pq q r) := by
        intro q
        exact (ENNReal.ofReal_sum_of_nonneg (fun r hr => by
          exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hc₁pos))
            (hw0 q)) (hw0 r)) (hPq_nonneg q r))).symm
      have hfold_outer : (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
            ENNReal.ofReal (4 * c₁ * w q * w r * Pq q r))
          = ENNReal.ofReal (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
              4 * c₁ * w q * w r * Pq q r) := by
        have hstep : ∀ q ∈ Finset.Icc X Y, (∑ r ∈ Finset.Icc X Y,
              ENNReal.ofReal (4 * c₁ * w q * w r * Pq q r))
            = ENNReal.ofReal (∑ r ∈ Finset.Icc X Y, 4 * c₁ * w q * w r * Pq q r) :=
          fun q _ => hfold_inner q
        rw [Finset.sum_congr rfl hstep]
        exact (ENNReal.ofReal_sum_of_nonneg (fun q hq => by
          refine Finset.sum_nonneg (fun r hr => ?_)
          exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hc₁pos))
            (hw0 q)) (hw0 r)) (hPq_nonneg q r))).symm
      calc (∑ q ∈ Finset.Icc X Y, ∑ r ∈ (Finset.Icc X Y).erase q, MeasureTheory.volume (A q ∩ A r))
          ≤ ∑ q ∈ Finset.Icc X Y, ∑ r ∈ (Finset.Icc X Y).erase q,
              ENNReal.ofReal (4 * c₁ * w q * w r * Pq q r) := by
            refine Finset.sum_le_sum (fun q hq => Finset.sum_le_sum (fun r hr => hpe q hq r hr))
        _ ≤ ∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
              ENNReal.ofReal (4 * c₁ * w q * w r * Pq q r) := by
            refine Finset.sum_le_sum (fun q hq => Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.erase_subset _ _) (fun r hr _ => by positivity))
        _ = ENNReal.ofReal (4 * c₁ * (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
                w q * w r * Pq q r)) := by
            rw [hfold_outer]
            congr 1
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun q hq => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun r hr => by ring)
        _ ≤ ENNReal.ofReal (4 * c₁ * Karith) := by
            apply ENNReal.ofReal_le_ofReal
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            -- the arithmetic (pair-product sum) bound, in the ψ-normalization
            have hsumψ : (∑ q ∈ Finset.Icc X Y, (q.totient : ℝ) * ((q:ℝ) * δ q) / q)
                = ∑ q ∈ Finset.Icc X Y, w q := by
              refine Finset.sum_congr rfl (fun q hq => ?_)
              rw [hwdef]
              have hq0 : (q:ℝ) ≠ 0 := by
                have : 1 ≤ q := le_trans hX (Finset.mem_Icc.mp hq).1
                positivity
              field_simp
            have hbound := hKarith (fun q => (q:ℝ) * δ q)
              (fun q => mul_nonneg (Nat.cast_nonneg q) (hδ q))
              (fun q => by have := hsmall q; linarith)
              X Y hX hXY (by rw [hsumψ]; exact hS1) (by rw [hsumψ]; linarith)
            refine le_trans ?_ hbound
            refine Finset.sum_le_sum (fun q hq => Finset.sum_le_sum (fun r hr => ?_))
            have hq1 : 1 ≤ q := le_trans hX (Finset.mem_Icc.mp hq).1
            have hr1 : 1 ≤ r := le_trans hX (Finset.mem_Icc.mp hr).1
            have hmax : max ((r:ℝ) * ((q:ℝ) * δ q)) ((q:ℝ) * ((r:ℝ) * δ r))
                = (q:ℝ) * (r:ℝ) * max (δ q) (δ r) := by
              rw [show (r:ℝ) * ((q:ℝ) * δ q) = (q:ℝ) * ((r:ℝ) * δ q) by ring,
                  show (q:ℝ) * ((r:ℝ) * δ r) = (q:ℝ) * ((r:ℝ) * δ r) by ring]
              rw [← mul_max_of_nonneg ((r:ℝ) * δ q) ((r:ℝ) * δ r) (Nat.cast_nonneg q),
                  ← mul_max_of_nonneg (δ q) (δ r) (Nat.cast_nonneg r)]
              ring
            have h1 : (q.totient : ℝ) * ((q:ℝ) * δ q) / q = (q.totient : ℝ) * δ q := by
              have hq0 : (q:ℝ) ≠ 0 := by positivity
              field_simp
            have h2 : (r.totient : ℝ) * ((r:ℝ) * δ r) / r = (r.totient : ℝ) * δ r := by
              have hr0 : (r:ℝ) ≠ 0 := by positivity
              field_simp
            refine le_of_eq ?_
            rw [h1, h2]
            congr 1
            rw [hPq]
            refine Finset.prod_congr ?_ (fun p hp => rfl)
            apply Finset.filter_congr
            intro p hp
            rw [hmax]
    -- combine diagonal and off-diagonal
    have hsumsplit : (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y, MeasureTheory.volume (A q ∩ A r))
        = (∑ q ∈ Finset.Icc X Y, MeasureTheory.volume (A q))
          + ∑ q ∈ Finset.Icc X Y, ∑ r ∈ (Finset.Icc X Y).erase q, MeasureTheory.volume (A q ∩ A r) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun q hq => ?_)
      rw [← Finset.sum_erase_add _ _ hq]
      rw [Set.inter_self]
      ring
    rw [hsumsplit]
    calc (∑ q ∈ Finset.Icc X Y, MeasureTheory.volume (A q))
          + ∑ q ∈ Finset.Icc X Y, ∑ r ∈ (Finset.Icc X Y).erase q, MeasureTheory.volume (A q ∩ A r)
        ≤ ENNReal.ofReal 4 + ENNReal.ofReal (4 * c₁ * Karith) := add_le_add hdiag hoff
      _ = ENNReal.ofReal U := by
          rw [← ENNReal.ofReal_add (by norm_num) (by positivity)]
  -- final assembly
  let s : ℕ → Set UnitAddCircle := fun n => if 0 < n then approxAddOrderOf UnitAddCircle n (δ n) else ∅
  let cst : ℝ≥0∞ := ENNReal.ofReal 4 / ENNReal.ofReal U
  have hcstpos : 0 < cst := by
    dsimp [cst]
    exact ENNReal.div_pos (by norm_num) ENNReal.ofReal_ne_top
  have hblock_measure : ∀ N : ℕ, ∃ Y : ℕ, N < Y ∧ cst ≤ volume (⋃ n ∈ Finset.Icc N Y, s n) := by
    intro N
    let X : ℕ := max N 1
    have hX1 : X ≥ 1 := by dsimp [X]; omega
    have hXN : N ≤ X := by dsimp [X]; omega
    rcases hblocks X hX1 with ⟨Y, hXY, hS1, hS2⟩
    have hps := hpairsum X Y hX1 (le_of_lt hXY) hS1 hS2
    have hX0 : X ≠ 0 := by omega
    -- total measure of the block equals ofReal (2S)
    have htot : (∑ q ∈ Finset.Icc X Y, volume (approxAddOrderOf UnitAddCircle q (δ q)))
        = ENNReal.ofReal (2 * ∑ q ∈ Finset.Icc X Y, w q) := by
      have := approxAddOrderOf_volume_eq_two_mul_Icc X Y hX0 δ hδ hsmall
      simpa [hwdef] using this
    -- second moment lower bound
    have hL : ENNReal.ofReal (2 * ∑ q ∈ Finset.Icc X Y, w q) ≤
        ∑ q ∈ Finset.Icc X Y, volume (approxAddOrderOf UnitAddCircle q (δ q)) := le_of_eq htot.symm
    have hU0 : ENNReal.ofReal U ≠ 0 := (ENNReal.ofReal_pos.mpr hUpos).ne'
    have hUt : ENNReal.ofReal U ≠ ∞ := ENNReal.ofReal_ne_top
    have hμ := (second_moment_Icc (μ := volume) X Y (fun q => approxAddOrderOf UnitAddCircle q (δ q))
        (fun q hq => by
          rw [approxAddOrderOf]
          exact Metric.isOpen_thickening.measurableSet))
    have hμlow : ENNReal.ofReal (2 * ∑ q ∈ Finset.Icc X Y, w q) ^ 2 / ENNReal.ofReal U ≤
        volume (⋃ q ∈ Finset.Icc X Y, approxAddOrderOf UnitAddCircle q (δ q)) := by
      have h1 : ENNReal.ofReal (2 * ∑ q ∈ Finset.Icc X Y, w q) ^ 2 ≤
          (∑ q ∈ Finset.Icc X Y, volume (approxAddOrderOf UnitAddCircle q (δ q))) ^ 2 :=
        ENNReal.pow_le_pow_left hL
      have h2 : (∑ q ∈ Finset.Icc X Y, volume (approxAddOrderOf UnitAddCircle q (δ q))) ^ 2 ≤
          volume (⋃ q ∈ Finset.Icc X Y, approxAddOrderOf UnitAddCircle q (δ q)) *
            (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
              volume (approxAddOrderOf UnitAddCircle q (δ q) ∩ approxAddOrderOf UnitAddCircle r (δ r))) := hμ
      have h3 : volume (⋃ q ∈ Finset.Icc X Y, approxAddOrderOf UnitAddCircle q (δ q)) *
            (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y,
              volume (approxAddOrderOf UnitAddCircle q (δ q) ∩ approxAddOrderOf UnitAddCircle r (δ r)))
          ≤ volume (⋃ q ∈ Finset.Icc X Y, approxAddOrderOf UnitAddCircle q (δ q)) * ENNReal.ofReal U :=
        mul_le_mul' le_rfl hps
      exact ENNReal.div_le_of_le_mul (le_trans (le_trans h1 h2) h3)
    have hcst_le : cst ≤ volume (⋃ q ∈ Finset.Icc X Y, approxAddOrderOf UnitAddCircle q (δ q)) := by
      dsimp [cst]
      refine le_trans ?_ hμlow
      rw [ENNReal.le_div_iff_mul_le (h0 := Or.inl hU0) (ht := Or.inl hUt)]
      calc (ENNReal.ofReal 4 / ENNReal.ofReal U) * ENNReal.ofReal U = ENNReal.ofReal 4 := by
            rw [ENNReal.div_mul_cancel hU0 ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal (2 * ∑ q ∈ Finset.Icc X Y, w q) ^ 2 := by
            rw [show (ENNReal.ofReal (2 * ∑ q ∈ Finset.Icc X Y, w q)) ^ 2
                = ENNReal.ofReal ((2 * ∑ q ∈ Finset.Icc X Y, w q) ^ 2) from
              (ENNReal.ofReal_pow (by positivity) 2).symm]
            apply ENNReal.ofReal_le_ofReal
            nlinarith [hS1]
    refine ⟨Y, ?_, ?_⟩
    · exact lt_of_le_of_lt hXN hXY
    · have hsub : (⋃ q ∈ Finset.Icc X Y, approxAddOrderOf UnitAddCircle q (δ q)) ⊆
          ⋃ n ∈ Finset.Icc N Y, s n := by
        intro x hx
        rcases mem_iUnion₂.mp hx with ⟨q, hq, hxA⟩
        refine mem_iUnion₂.mpr ⟨q, ?_, ?_⟩
        · rw [Finset.mem_Icc]
          exact ⟨le_trans hXN (Finset.mem_Icc.mp hq).1, (Finset.mem_Icc.mp hq).2⟩
        · have hqpos : 0 < q := lt_of_lt_of_le (by omega : 0 < 1) (le_trans hX1 (Finset.mem_Icc.mp hq).1)
          dsimp [s]
          rw [if_pos hqpos]
          exact hxA
      exact le_trans hcst_le (measure_mono hsub)
  have hs_null : ∀ n, NullMeasurableSet (s n) volume := by
    intro n
    dsimp [s]
    by_cases hn : 0 < n
    · have hmeas : MeasurableSet (approxAddOrderOf UnitAddCircle n (δ n)) := by
        rw [approxAddOrderOf]
        exact Metric.isOpen_thickening.measurableSet
      simpa [hn] using hmeas.nullMeasurableSet
    · simp [hn]
  have hlim : cst ≤ volume (limsup s atTop) :=
    Commons.MeasureTheory.tail_blocks_le_measure_limsup (μ := volume) s hs_null hcstpos hblock_measure
  have hident : limsup s atTop = addWellApproximable UnitAddCircle δ := by
    simpa [s] using (addWellApproximable_eq_limsup_piecewise δ).symm
  have hmain : cst ≤ volume (addWellApproximable UnitAddCircle δ) := by
    rw [← hident]; exact hlim
  exact lt_of_lt_of_le hcstpos hmain

end
end Commons.NumberTheory.DuffinSchaeffer
