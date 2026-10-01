import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Work.LinnikAreas.Density4.sum_inv_exp_neg_sqrt_log_div

namespace Work.LinnikAreas.JutilaPieces

open Finset
open scoped BigOperators

noncomputable section

/-!
# Uniform boundedness of `Σ_{n ≤ V} (1/n) · muRecipSum(V/n)²`

We prove that the weighted mean square of the Möbius reciprocal partial sums
`muRecipSum M = Σ_{m ≤ M} μ(m)/m` is uniformly bounded:
`Σ_{n ≤ V} (1/n) · muRecipSum(V/n)² ≤ K` for an absolute constant `K`.

The proof splits the range at `2n ≤ V`.

* If `2n ≤ V` then `V/n ≥ 2`, and the de la Vallée Poussin decay of the Möbius reciprocal
  sums (`muRecipSum M = O(exp(-c√log M))`, proved in `Commons` and usable there for arbitrary
  *real* arguments `x ≥ 2`) applied at the real point `x = V/n` gives
  `muRecipSum(V/n)² ≤ C² exp(-2c√log(V/n))`.  Summing this against `1/n` is exactly the
  quantity bounded by `Commons.Analysis.Asymptotics.sum_exp_neg_sqrt_log_div` (available as
  `Work.LinnikAreas.Density4.sum_inv_exp_neg_sqrt_log_div`); its finiteness is the statement
  `∫^∞ exp(-2c√log u) du/u < ∞` in disguise.
* If `V < 2n` then `1 ≤ V/n < 2`, so `V/n = 1` and the summand is just `1/n`; the range
  `n > V/2` contributes the bounded harmonic tail `Σ_{n > V/2} 1/n ≤ 2`.
-/

/-- `(C exp(-cA))² = C² exp(-2cA)`. -/
private lemma sq_mul_exp_eq (C c A : ℝ) :
    (C * Real.exp (-(c * A))) ^ 2 = C ^ 2 * Real.exp (-((2 * c) * A)) := by
  have h : Real.exp (-(c * A)) * Real.exp (-(c * A)) = Real.exp (-((2 * c) * A)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc (C * Real.exp (-(c * A))) ^ 2
      = C ^ 2 * (Real.exp (-(c * A)) * Real.exp (-(c * A))) := by ring
    _ = C ^ 2 * Real.exp (-((2 * c) * A)) := by rw [h]

/-- **The decay bound at the real point `V/n`.**  The uniform de la Vallée Poussin bound for
`muRecipSum` (assumed here through its defining property `hdec` on real arguments `x ≥ 2`),
applied to `x = V/n ≥ 2`, bounds `muRecipSum (V/n) = Σ_{m ≤ V/n} μ(m)/m`.  The point is that
`⌊(V:ℝ)/n⌋₊ = V/n`, so the real-argument form of the decay estimate applies directly to the
*natural* quotient `V/n`, with no floor error. -/
lemma abs_muRecipSum_div_le_exp {C0 c : ℝ}
    (hdec : ∀ x : ℝ, 2 ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)|
        ≤ C0 * Real.exp (-(c * Real.sqrt (Real.log x)))) :
    ∀ V n : ℕ, 1 ≤ n → 2 * n ≤ V →
      |Commons.NumberTheory.Moebius.muRecipSum (V / n)| ≤
        C0 * Real.exp (-(c * Real.sqrt (Real.log ((V : ℝ) / (n : ℝ))))) := by
  intro V n hn hVn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hx2 : (2 : ℝ) ≤ (V : ℝ) / (n : ℝ) := by
    rw [le_div_iff₀ hn0]
    have h : ((2 * n : ℕ) : ℝ) ≤ (V : ℝ) := by exact_mod_cast hVn
    push_cast at h
    linarith
  have hfloor : ⌊(V : ℝ) / (n : ℝ)⌋₊ = V / n := by
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  have h := hdec ((V : ℝ) / (n : ℝ)) hx2
  rw [hfloor] at h
  exact h

/-- If `n ≤ V < 2n` then the quotient `V/n` is `1`, so `muRecipSum (V/n) = 1`. -/
lemma muRecipSum_div_eq_one_of_lt {V n : ℕ} (hn : 1 ≤ n) (hnV : n ≤ V) (hVn : V < 2 * n) :
    Commons.NumberTheory.Moebius.muRecipSum (V / n) = 1 := by
  have hn0 : 0 < n := by omega
  have hge : 1 ≤ V / n := by
    rw [Nat.le_div_iff_mul_le hn0]; omega
  have hlt : V / n < 2 := by
    rw [Nat.div_lt_iff_lt_mul hn0]; omega
  have h1 : V / n = 1 := by omega
  rw [h1]
  simp [Commons.NumberTheory.Moebius.muRecipSum]

/-- The harmonic tail over `n ∈ (V/2, V]` is bounded by `2`.  On that range `V/n = 1`, so the
summand of `Icc 1 V ∖ {n ≤ V/2}` is exactly `1/n`, and there are at most `V` of them, each
`≤ 2/V`. -/
lemma sum_muRecipSq_large_le_two (V : ℕ) :
    (∑ n ∈ (Finset.Icc 1 V).filter (fun n => V < 2 * n),
      (1 / (n : ℝ)) * (Commons.NumberTheory.Moebius.muRecipSum (V / n)) ^ 2) ≤ 2 := by
  rcases Nat.eq_zero_or_pos V with h0 | hV
  · subst h0; simp
  · have hVpos : (0 : ℝ) < (V : ℝ) := by exact_mod_cast hV
    have hterm : ∀ n ∈ (Finset.Icc 1 V).filter (fun n => V < 2 * n),
        (1 / (n : ℝ)) * (Commons.NumberTheory.Moebius.muRecipSum (V / n)) ^ 2
          ≤ 2 / (V : ℝ) := by
      intro n hn
      obtain ⟨hnIcc, hVn⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn1, hnV⟩ := Finset.mem_Icc.mp hnIcc
      rw [muRecipSum_div_eq_one_of_lt hn1 hnV hVn, one_pow, mul_one]
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      rw [div_le_div_iff₀ hn0 hVpos]
      have h : (V : ℝ) < 2 * (n : ℝ) := by exact_mod_cast hVn
      linarith
    have hcard : (((Finset.Icc 1 V).filter (fun n => V < 2 * n)).card : ℝ) ≤ (V : ℝ) := by
      have hc : ((Finset.Icc 1 V).filter (fun n => V < 2 * n)).card ≤ V := by
        calc ((Finset.Icc 1 V).filter (fun n => V < 2 * n)).card
            ≤ (Finset.Icc 1 V).card := Finset.card_le_card (Finset.filter_subset _ _)
          _ = V := by rw [Nat.card_Icc]; omega
      exact_mod_cast hc
    calc (∑ n ∈ (Finset.Icc 1 V).filter (fun n => V < 2 * n),
            (1 / (n : ℝ)) * (Commons.NumberTheory.Moebius.muRecipSum (V / n)) ^ 2)
        ≤ ∑ _n ∈ (Finset.Icc 1 V).filter (fun n => V < 2 * n), 2 / (V : ℝ) :=
          Finset.sum_le_sum hterm
      _ = (((Finset.Icc 1 V).filter (fun n => V < 2 * n)).card : ℝ) * (2 / (V : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (V : ℝ) * (2 / (V : ℝ)) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 := by field_simp

lemma sum_muRecipSq_div_le :
    ∃ K : ℝ, 0 < K ∧ ∀ V : ℕ, 1 ≤ V →
      (∑ n ∈ Finset.Icc 1 V,
        (1 / (n : ℝ)) * (Commons.NumberTheory.Moebius.muRecipSum (V / n)) ^ 2) ≤ K := by
  obtain ⟨c, C0, hc, _hC0, hdec⟩ :=
    Commons.NumberTheory.Moebius.moebius_recip_sum_exp_decay
  obtain ⟨K₁, hK₁, hsum⟩ :=
    Work.LinnikAreas.Density4.sum_inv_exp_neg_sqrt_log_div (2 * c) (by positivity)
  have hKpos : 0 < C0 ^ 2 * K₁ + 2 := by nlinarith [sq_nonneg C0, hK₁]
  refine ⟨C0 ^ 2 * K₁ + 2, hKpos, ?_⟩
  intro V hV
  -- split the range according to whether `2n ≤ V`
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 V) (fun n => 2 * n ≤ V)
    (fun n => (1 / (n : ℝ)) * (Commons.NumberTheory.Moebius.muRecipSum (V / n)) ^ 2)
  -- the range `2n ≤ V`: use the exponential decay of `muRecipSum` at the point `V/n`
  have hsmall : (∑ n ∈ (Finset.Icc 1 V).filter (fun n => 2 * n ≤ V),
      (1 / (n : ℝ)) * (Commons.NumberTheory.Moebius.muRecipSum (V / n)) ^ 2) ≤ C0 ^ 2 * K₁ := by
    have hterm : ∀ n ∈ (Finset.Icc 1 V).filter (fun n => 2 * n ≤ V),
        (1 / (n : ℝ)) * (Commons.NumberTheory.Moebius.muRecipSum (V / n)) ^ 2
          ≤ C0 ^ 2 * ((1 / (n : ℝ)) *
              Real.exp (-((2 * c) * Real.sqrt (Real.log ((V : ℝ) / (n : ℝ)))))) := by
      intro n hn
      obtain ⟨hnIcc, hn2⟩ := Finset.mem_filter.mp hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnIcc).1
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hb := abs_muRecipSum_div_le_exp hdec V n hn1 hn2
      have hsq : (Commons.NumberTheory.Moebius.muRecipSum (V / n)) ^ 2
          ≤ (C0 * Real.exp (-(c * Real.sqrt (Real.log ((V : ℝ) / (n : ℝ)))))) ^ 2 := by
        rw [← sq_abs (Commons.NumberTheory.Moebius.muRecipSum (V / n))]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      calc (1 / (n : ℝ)) * (Commons.NumberTheory.Moebius.muRecipSum (V / n)) ^ 2
          ≤ (1 / (n : ℝ)) *
              (C0 * Real.exp (-(c * Real.sqrt (Real.log ((V : ℝ) / (n : ℝ)))))) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = C0 ^ 2 * ((1 / (n : ℝ)) *
              Real.exp (-((2 * c) * Real.sqrt (Real.log ((V : ℝ) / (n : ℝ)))))) := by
            rw [sq_mul_exp_eq]; ring
    calc (∑ n ∈ (Finset.Icc 1 V).filter (fun n => 2 * n ≤ V),
            (1 / (n : ℝ)) * (Commons.NumberTheory.Moebius.muRecipSum (V / n)) ^ 2)
        ≤ ∑ n ∈ (Finset.Icc 1 V).filter (fun n => 2 * n ≤ V),
            C0 ^ 2 * ((1 / (n : ℝ)) *
              Real.exp (-((2 * c) * Real.sqrt (Real.log ((V : ℝ) / (n : ℝ)))))) :=
          Finset.sum_le_sum hterm
      _ = C0 ^ 2 * ∑ n ∈ (Finset.Icc 1 V).filter (fun n => 2 * n ≤ V),
            (1 / (n : ℝ)) * Real.exp (-((2 * c) * Real.sqrt (Real.log ((V : ℝ) / (n : ℝ))))) := by
          rw [Finset.mul_sum]
      _ ≤ C0 ^ 2 * K₁ := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg C0)
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
            (hsum V hV)
          intro i hi _
          have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
          have hi0 : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi1
          positivity
  -- the range `V < 2n`: the summand is `1/n`
  have hlarge : (∑ n ∈ (Finset.Icc 1 V).filter (fun n => ¬ 2 * n ≤ V),
      (1 / (n : ℝ)) * (Commons.NumberTheory.Moebius.muRecipSum (V / n)) ^ 2) ≤ 2 := by
    have hset : (Finset.Icc 1 V).filter (fun n => ¬ 2 * n ≤ V)
        = (Finset.Icc 1 V).filter (fun n => V < 2 * n) := by
      apply Finset.filter_congr
      intro n _
      exact not_le
    rw [hset]
    exact sum_muRecipSq_large_le_two V
  calc (∑ n ∈ Finset.Icc 1 V,
          (1 / (n : ℝ)) * (Commons.NumberTheory.Moebius.muRecipSum (V / n)) ^ 2)
      = (∑ n ∈ (Finset.Icc 1 V).filter (fun n => 2 * n ≤ V),
          (1 / (n : ℝ)) * (Commons.NumberTheory.Moebius.muRecipSum (V / n)) ^ 2)
        + (∑ n ∈ (Finset.Icc 1 V).filter (fun n => ¬ 2 * n ≤ V),
          (1 / (n : ℝ)) * (Commons.NumberTheory.Moebius.muRecipSum (V / n)) ^ 2) :=
        hsplit.symm
    _ ≤ C0 ^ 2 * K₁ + 2 := add_le_add hsmall hlarge

end

end Work.LinnikAreas.JutilaPieces
