import Mathlib
import Submission.Work.FIArea6V.OneModFour.prime_zeta_lower_log
import Submission.Commons.NumberTheory.FriedlanderIwaniec.chi4_prime_recip_converges
import Submission.Commons.NumberTheory.DirichletCharacter.chi4_prime_recip_rate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open Finset

namespace Work.FIArea6V

noncomputable section

/-! ## The quadratic character `χ₄` modulo `4`, real valued -/

/-- The quadratic character `χ₄` modulo `4`, as a real valued function on `ℕ`. -/
def chi4RV (n : ℕ) : ℝ := ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ)

lemma chi4RV_eq_if (n : ℕ) :
    chi4RV n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 := by
  unfold chi4RV
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  push_cast
  by_cases h : n % 2 = 0 <;> simp [h]

lemma chi4RV_abs_le_one (n : ℕ) : |chi4RV n| ≤ 1 := by
  rw [chi4RV_eq_if]; split_ifs <;> norm_num

/-- The sequence `n ↦ χ₄(n)/n`, extended by `0` on the non-primes. -/
def chi4PrimeRecip (n : ℕ) : ℝ := if n.Prime then chi4RV n / (n : ℝ) else 0

lemma chi4PrimeRecip_zero : chi4PrimeRecip 0 = 0 := by
  rw [chi4PrimeRecip]; simp

/-! ## A uniform Abel (partial summation) bound -/

/-- If the partial sums of `g` are bounded by `K` and `W` is antitone and nonnegative, then
the partial sums of `g · W` are bounded by `K · W 0`. -/
lemma abel_uniform_bound {g W : ℕ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hW0 : 0 ≤ W 0) (hanti : Antitone W) (hWnn : ∀ n, 0 ≤ W n)
    (hF : ∀ N, |∑ n ∈ range N, g n| ≤ K) :
    ∀ N, |∑ n ∈ range N, g n * W n| ≤ K * W 0 := by
  intro N
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [sum_range_zero, abs_zero]
    exact mul_nonneg hK hW0
  have hgoal : (∑ n ∈ range N, g n * W n) = ∑ n ∈ range N, W n • g n := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [smul_eq_mul, mul_comm]
  rw [hgoal, Finset.sum_range_by_parts W g N]
  simp only [smul_eq_mul]
  have h1 : |W (N - 1) * (∑ i ∈ range N, g i)| ≤ W (N - 1) * K := by
    rw [abs_mul, abs_of_nonneg (hWnn (N - 1))]
    exact mul_le_mul_of_nonneg_left (hF N) (hWnn (N - 1))
  have h2 : |∑ i ∈ range (N - 1), (W (i + 1) - W i) * (∑ j ∈ range (i + 1), g j)|
      ≤ ∑ i ∈ range (N - 1), (W i - W (i + 1)) * K := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
    intro i _
    have hle : W (i + 1) - W i ≤ 0 := by have := hanti (Nat.le_succ i); linarith
    have hnn : 0 ≤ W i - W (i + 1) := by have := hanti (Nat.le_succ i); linarith
    rw [abs_mul, abs_of_nonpos hle]
    calc -(W (i + 1) - W i) * |∑ j ∈ range (i + 1), g j|
        = (W i - W (i + 1)) * |∑ j ∈ range (i + 1), g j| := by ring
      _ ≤ (W i - W (i + 1)) * K := mul_le_mul_of_nonneg_left (hF (i + 1)) hnn
  have htel : ∑ i ∈ range (N - 1), (W i - W (i + 1)) = W 0 - W (N - 1) := by
    have h : ∑ i ∈ range (N - 1), (W (i + 1) - W i) = W (N - 1) - W 0 :=
      Finset.sum_range_sub W (N - 1)
    have h2 : ∑ i ∈ range (N - 1), (W i - W (i + 1))
        = -∑ i ∈ range (N - 1), (W (i + 1) - W i) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [h2, h]; ring
  calc |W (N - 1) * (∑ i ∈ range N, g i)
          - ∑ i ∈ range (N - 1), (W (i + 1) - W i) * (∑ j ∈ range (i + 1), g j)|
      ≤ |W (N - 1) * (∑ i ∈ range N, g i)|
          + |∑ i ∈ range (N - 1), (W (i + 1) - W i) * (∑ j ∈ range (i + 1), g j)| := by
        have := abs_add_le (W (N - 1) * (∑ i ∈ range N, g i))
          (-(∑ i ∈ range (N - 1), (W (i + 1) - W i) * (∑ j ∈ range (i + 1), g j)))
        simpa [sub_eq_add_neg, abs_neg] using this
    _ ≤ W (N - 1) * K + ∑ i ∈ range (N - 1), (W i - W (i + 1)) * K := add_le_add h1 h2
    _ = W (N - 1) * K + (W 0 - W (N - 1)) * K := by rw [← Finset.sum_mul, htel]
    _ = K * W 0 := by ring

/-! ## The `χ₄`-twisted prime sum is uniformly bounded on `1 < σ ≤ 2` -/

theorem chi4_twisted_prime_sum_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      |∑' p : Nat.Primes, chi4RV (p : ℕ) * ((p : ℕ) : ℝ) ^ (-σ)| ≤ C := by
  obtain ⟨L, C0, hC0pos, hrate⟩ :=
    Commons.NumberTheory.DirichletCharacter.chi4_prime_recip_rate
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : 0 < |L| + C0 * (Real.log 2) ^ (-10 : ℝ) := by
    have : 0 < C0 * (Real.log 2) ^ (-10 : ℝ) :=
      mul_pos hC0pos (Real.rpow_pos_of_pos hlog2pos _)
    linarith [abs_nonneg L]
  refine ⟨|L| + C0 * (Real.log 2) ^ (-10 : ℝ), hKpos, ?_⟩
  intro σ hσ1 hσ2
  set K : ℝ := |L| + C0 * (Real.log 2) ^ (-10 : ℝ) with hKdef
  have hKnn : 0 ≤ K := le_of_lt hKpos
  -- Bound on the partial sums of `chi4PrimeRecip`.
  have hFbound : ∀ N : ℕ, |∑ n ∈ range N, chi4PrimeRecip n| ≤ K := by
    intro N
    rcases lt_or_ge N 2 with hN | hN
    · have hN01 : N = 0 ∨ N = 1 := by omega
      rcases hN01 with rfl | rfl
      · simp only [range_zero, sum_empty, abs_zero]; exact hKnn
      · rw [range_one, sum_singleton, chi4PrimeRecip_zero, abs_zero]; exact hKnn
    · have hsum : (∑ n ∈ range N, chi4PrimeRecip n)
          = ∑ p ∈ Nat.primesBelow N, chi4RV p / (p : ℝ) := by
        rw [show Nat.primesBelow N = (range N).filter Nat.Prime from rfl, Finset.sum_filter]
        refine Finset.sum_congr rfl fun n _ => ?_
        by_cases hpn : n.Prime <;> simp [chi4PrimeRecip, hpn]
      rw [hsum]
      have hr : |(∑ p ∈ Nat.primesBelow N, chi4RV p / (p : ℝ)) - L|
          ≤ C0 * (Real.log (N : ℝ)) ^ (-10 : ℝ) := by
        simpa only [chi4RV] using hrate N hN
      have hlogN : Real.log 2 ≤ Real.log (N : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hN)
      have hpowle : (Real.log (N : ℝ)) ^ (-10 : ℝ) ≤ (Real.log 2) ^ (-10 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hlog2pos hlogN (by norm_num)
      have hmul : C0 * (Real.log (N : ℝ)) ^ (-10 : ℝ) ≤ C0 * (Real.log 2) ^ (-10 : ℝ) :=
        mul_le_mul_of_nonneg_left hpowle (le_of_lt hC0pos)
      calc |∑ p ∈ Nat.primesBelow N, chi4RV p / (p : ℝ)|
          = |(∑ p ∈ Nat.primesBelow N, chi4RV p / (p : ℝ)) - L + L| := by ring_nf
        _ ≤ |(∑ p ∈ Nat.primesBelow N, chi4RV p / (p : ℝ)) - L| + |L| := abs_add_le _ _
        _ ≤ C0 * (Real.log (N : ℝ)) ^ (-10 : ℝ) + |L| := add_le_add hr le_rfl
        _ ≤ C0 * (Real.log 2) ^ (-10 : ℝ) + |L| := by linarith
        _ = K := by rw [hKdef]; ring
  -- The decreasing weight `W m = (m+1)^{-(σ-1)}`.
  set W : ℕ → ℝ := fun m => ((m + 1 : ℕ) : ℝ) ^ (-(σ - 1)) with hWdef
  have hW0nn : 0 ≤ W 0 := by rw [hWdef]; positivity
  have hW0val : W 0 = 1 := by rw [hWdef]; norm_num
  have hWnn : ∀ m, 0 ≤ W m := fun m => by rw [hWdef]; positivity
  have hanti : Antitone W := by
    intro a b hab
    rw [hWdef]
    have ha : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := by positivity
    have hle : ((a + 1 : ℕ) : ℝ) ≤ ((b + 1 : ℕ) : ℝ) := by
      have : a + 1 ≤ b + 1 := by omega
      exact_mod_cast this
    exact Real.rpow_le_rpow_of_nonpos ha hle (by linarith : -(σ - 1) ≤ 0)
  set g : ℕ → ℝ := fun m => chi4PrimeRecip (m + 1) with hgdef
  have hGbound : ∀ N, |∑ m ∈ range N, g m| ≤ K := by
    intro N
    have hshift : (∑ m ∈ range N, g m) = ∑ n ∈ range (N + 1), chi4PrimeRecip n := by
      rw [hgdef, Finset.sum_range_succ' (f := chi4PrimeRecip) N, chi4PrimeRecip_zero, add_zero]
    rw [hshift]
    exact hFbound (N + 1)
  have habel := abel_uniform_bound hKnn hW0nn hanti hWnn hGbound
  -- Summability and identification of the series with the Abel sum.
  have hsummable_rec : Summable (fun n : ℕ => chi4PrimeRecip n * (n : ℝ) ^ (-(σ - 1))) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => (n : ℝ) ^ (-σ)) ?_ ?_
    · exact Real.summable_nat_rpow.mpr (by linarith : -σ < -1)
    · intro n
      rw [Real.norm_eq_abs]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        rw [chi4PrimeRecip_zero, zero_mul, abs_zero]
        exact Real.rpow_nonneg (Nat.cast_nonneg 0) _
      · by_cases hpn : n.Prime
        · have hnpos : (0 : ℝ) < (n : ℝ) := by
            have := hpn.pos; exact_mod_cast this
          rw [chi4PrimeRecip, if_pos hpn, abs_mul, abs_div,
            abs_of_nonneg (Real.rpow_nonneg (le_of_lt hnpos) _),
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
          calc |chi4RV n| / (n : ℝ) * (n : ℝ) ^ (-(σ - 1))
              = |chi4RV n| * ((n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (-(σ - 1))) := by
                rw [div_eq_mul_inv, ← Real.rpow_neg_one (n : ℝ)]; ring
            _ ≤ 1 * ((n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (-(σ - 1))) := by
                refine mul_le_mul_of_nonneg_right (chi4RV_abs_le_one n) ?_
                positivity
            _ = (n : ℝ) ^ (-σ) := by
                rw [one_mul, ← Real.rpow_add hnpos,
                  show (-1 : ℝ) + -(σ - 1) = -σ from by ring]
        · rw [chi4PrimeRecip, if_neg hpn, zero_mul, abs_zero]
          exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hident1 : (∑' p : Nat.Primes, chi4RV (p : ℕ) * ((p : ℕ) : ℝ) ^ (-σ))
      = ∑' n : ℕ, (if n.Prime then chi4RV n * (n : ℝ) ^ (-σ) else 0) :=
    Nat.Primes.tsum_eq_tsum_ite (fun n : ℕ => chi4RV n * (n : ℝ) ^ (-σ))
  have hident2 : (∑' n : ℕ, (if n.Prime then chi4RV n * (n : ℝ) ^ (-σ) else 0))
      = ∑' n : ℕ, chi4PrimeRecip n * (n : ℝ) ^ (-(σ - 1)) := by
    refine tsum_congr fun n => ?_
    by_cases hpn : n.Prime
    · have hnpos : (0 : ℝ) < (n : ℝ) := by
        have := hpn.pos; exact_mod_cast this
      rw [if_pos hpn, chi4PrimeRecip, if_pos hpn, div_eq_mul_inv,
        ← Real.rpow_neg_one (n : ℝ), mul_assoc, ← Real.rpow_add hnpos,
        show (-1 : ℝ) + -(σ - 1) = -σ from by ring]
    · rw [if_neg hpn, chi4PrimeRecip, if_neg hpn, zero_mul]
  have hident3 : (∑' n : ℕ, chi4PrimeRecip n * (n : ℝ) ^ (-(σ - 1)))
      = chi4PrimeRecip 0 * ((0 : ℕ) : ℝ) ^ (-(σ - 1))
        + ∑' m : ℕ, chi4PrimeRecip (m + 1) * ((m + 1 : ℕ) : ℝ) ^ (-(σ - 1)) :=
    Summable.tsum_eq_zero_add hsummable_rec
  have hS : (∑' n : ℕ, chi4PrimeRecip n * (n : ℝ) ^ (-(σ - 1)))
      = ∑' m : ℕ, g m * W m := by
    rw [hident3, chi4PrimeRecip_zero, zero_mul, zero_add]
  have hsummable_gW : Summable (fun m : ℕ => g m * W m) := by
    have h : Summable (fun m : ℕ => chi4PrimeRecip (m + 1) * ((m + 1 : ℕ) : ℝ) ^ (-(σ - 1))) :=
      hsummable_rec.comp_injective (f := fun n : ℕ => chi4PrimeRecip n * (n : ℝ) ^ (-(σ - 1)))
        (fun a b hab => by omega)
    simpa only [hgdef, hWdef] using h
  have hBoundS : |∑' m : ℕ, g m * W m| ≤ K * W 0 := by
    refine le_of_tendsto (hsummable_gW.hasSum.tendsto_sum_nat.abs) (Filter.Eventually.of_forall ?_)
    intro N
    exact habel N
  have hfinal : |∑' p : Nat.Primes, chi4RV (p : ℕ) * ((p : ℕ) : ℝ) ^ (-σ)|
      ≤ |L| + C0 * (Real.log 2) ^ (-10 : ℝ) := by
    rw [hident1, hident2, hS]
    rw [hW0val, mul_one, hKdef] at hBoundS
    exact hBoundS
  exact hfinal

/-! ## The splitting identity -/

/-- For every prime `p`, the indicator of `p ≡ 1 (mod 4)` equals `(1 + χ₄(p))/2`, except at
the prime `2`, which is subtracted off. -/
lemma chi4RV_pointwise (σ : ℝ) (p : Nat.Primes) :
    (if (p : ℕ) % 4 = 1 then ((p : ℕ) : ℝ) ^ (-σ) else 0)
      = (1 / 2) * (((p : ℕ) : ℝ) ^ (-σ) + chi4RV (p : ℕ) * ((p : ℕ) : ℝ) ^ (-σ))
        - (1 / 2) * (if (p : ℕ) = 2 then ((p : ℕ) : ℝ) ^ (-σ) else 0) := by
  have hp : (p : ℕ).Prime := p.property
  have hcases : (p : ℕ) % 4 = 1 ∨ (p : ℕ) % 4 = 2 ∨ (p : ℕ) % 4 = 3 := by
    have hlt : (p : ℕ) % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have hne : (p : ℕ) % 4 ≠ 0 := by
      intro h
      have hdvd : 4 ∣ (p : ℕ) := Nat.dvd_of_mod_eq_zero h
      rcases hp.eq_one_or_self_of_dvd 4 hdvd with h1 | h4
      · norm_num at h1
      · rw [← h4] at hp; norm_num at hp
    omega
  rcases hcases with h | h | h
  · have h2 : (p : ℕ) ≠ 2 := by intro hh; rw [hh] at h; norm_num at h
    have hc : chi4RV (p : ℕ) = 1 := by rw [chi4RV_eq_if, if_neg (by omega), if_pos h]
    rw [if_pos h, if_neg h2, hc]; ring
  · have h2 : (p : ℕ) = 2 := by
      rcases hp.eq_two_or_odd with hh | hh
      · exact hh
      · omega
    have hc : chi4RV (p : ℕ) = 0 := by rw [h2, chi4RV_eq_if]; norm_num
    rw [if_neg (by omega : ¬ (p : ℕ) % 4 = 1), if_pos h2, hc]; ring
  · have h2 : (p : ℕ) ≠ 2 := by intro hh; rw [hh] at h; norm_num at h
    have hc : chi4RV (p : ℕ) = -1 := by rw [chi4RV_eq_if, if_neg (by omega), if_neg (by omega)]
    rw [if_neg (by omega : ¬ (p : ℕ) % 4 = 1), if_neg h2, hc]; ring

/-- The prime sum over `p ≡ 1 (mod 4)` splits into the full prime zeta sum and the
`χ₄`-twisted prime sum. -/
lemma oneModFour_tsum_eq (σ : ℝ) (hσ : 1 < σ) :
    (∑' p : Nat.Primes, (if (p : ℕ) % 4 = 1 then ((p : ℕ) : ℝ) ^ (-σ) else 0))
      = (1 / 2) * (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ))
        + (1 / 2) * (∑' p : Nat.Primes, chi4RV (p : ℕ) * ((p : ℕ) : ℝ) ^ (-σ))
        - (1 / 2) * (2 : ℝ) ^ (-σ) := by
  have hA : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-σ)) :=
    (Nat.Primes.summable_rpow (r := -σ)).mpr (by linarith)
  have hB : Summable (fun p : Nat.Primes => chi4RV (p : ℕ) * ((p : ℕ) : ℝ) ^ (-σ)) := by
    refine Summable.of_norm_bounded hA (fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (chi4RV_abs_le_one _)
  have hC : Summable (fun p : Nat.Primes => (if (p : ℕ) = 2 then ((p : ℕ) : ℝ) ^ (-σ) else 0)) := by
    refine Summable.of_norm_bounded hA (fun p => ?_)
    rw [Real.norm_eq_abs]
    by_cases hp : (p : ℕ) = 2
    · rw [if_pos hp]
      exact le_of_eq (by rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)])
    · rw [if_neg hp, abs_zero]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hCval : (∑' p : Nat.Primes, (if (p : ℕ) = 2 then ((p : ℕ) : ℝ) ^ (-σ) else 0))
      = (2 : ℝ) ^ (-σ) := by
    rw [Nat.Primes.tsum_eq_tsum_ite (f := fun n : ℕ => if n = 2 then (n : ℝ) ^ (-σ) else 0)]
    rw [tsum_eq_single 2]
    · rw [if_pos Nat.prime_two, if_pos rfl]; norm_num
    · intro n hn
      by_cases hp : n.Prime
      · rw [if_pos hp, if_neg hn]
      · rw [if_neg hp]
  have hstep1 : (∑' p : Nat.Primes, (if (p : ℕ) % 4 = 1 then ((p : ℕ) : ℝ) ^ (-σ) else 0))
      = ∑' p : Nat.Primes, ((1 / 2) * (((p : ℕ) : ℝ) ^ (-σ)
          + chi4RV (p : ℕ) * ((p : ℕ) : ℝ) ^ (-σ))
          - (1 / 2) * (if (p : ℕ) = 2 then ((p : ℕ) : ℝ) ^ (-σ) else 0)) :=
    tsum_congr (fun p => chi4RV_pointwise σ p)
  rw [hstep1]
  rw [Summable.tsum_sub ((hA.add hB).mul_left (1 / 2)) (hC.mul_left (1 / 2))]
  rw [tsum_mul_left (f := fun p : Nat.Primes =>
      ((p : ℕ) : ℝ) ^ (-σ) + chi4RV (p : ℕ) * ((p : ℕ) : ℝ) ^ (-σ)) (a := (1 / 2 : ℝ))]
  rw [tsum_mul_left (f := fun p : Nat.Primes =>
      (if (p : ℕ) = 2 then ((p : ℕ) : ℝ) ^ (-σ) else 0)) (a := (1 / 2 : ℝ))]
  rw [Summable.tsum_add (L := SummationFilter.unconditional Nat.Primes) hA hB]
  rw [hCval]
  ring

/-! ## The target -/

theorem sum_one_mod_four_rpow_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (1 / 256) * Real.log (1 / (σ - 1)) - C
        ≤ ∑' p : Nat.Primes, (if (p : ℕ) % 4 = 1 then (((p : ℕ) : ℝ) ^ (-σ)) else 0) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FIArea6V.OneModFour.prime_zeta_lower_log
  obtain ⟨C₂, hC₂pos, hC₂⟩ := chi4_twisted_prime_sum_bounded
  refine ⟨C₁ / 2 + C₂ / 2 + 1 / 4, by positivity, ?_⟩
  intro σ hσ1 hσ2
  have hid := oneModFour_tsum_eq σ hσ1
  rw [hid]
  have hS := hC₁ σ hσ1 hσ2
  have hL : -(C₂) ≤ ∑' p : Nat.Primes, chi4RV (p : ℕ) * ((p : ℕ) : ℝ) ^ (-σ) :=
    neg_le_of_abs_le (hC₂ σ hσ1 hσ2)
  have hlog : 0 ≤ Real.log (1 / (σ - 1)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < σ - 1)]
    linarith
  have h2 : (2 : ℝ) ^ (-σ) ≤ 1 / 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (by linarith : -σ ≤ -1)
    simpa [Real.rpow_neg_one] using h
  have hkey : (1 / 2) * Real.log (1 / (σ - 1)) - (1 / 2) * C₁ - (1 / 2) * C₂ - 1 / 4
      ≤ (1 / 2) * (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ))
        + (1 / 2) * (∑' p : Nat.Primes, chi4RV (p : ℕ) * ((p : ℕ) : ℝ) ^ (-σ))
        - (1 / 2) * (2 : ℝ) ^ (-σ) := by
    nlinarith [hS, hL, h2]
  have hfrac : (0 : ℝ) ≤ 1 / 2 - 1 / 256 := by norm_num
  nlinarith [hkey, mul_nonneg hfrac hlog]

end

end Work.FIArea6V
