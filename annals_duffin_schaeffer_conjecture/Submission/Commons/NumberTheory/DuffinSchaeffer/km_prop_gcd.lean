import Mathlib
import Submission.Commons.NumberTheory.Tenenbaum.multiplicative_average_bound
import Submission.Commons.NumberTheory.DuffinSchaeffer.padic_ratio_decomp
import Submission.Commons.NumberTheory.DuffinSchaeffer.gcd_ratio_decomp
import Submission.Commons.NumberTheory.DuffinSchaeffer.shellDelta_fold

set_option maxHeartbeats 4000000

open scoped BigOperators
open Finset

namespace Commons.NumberTheory.DuffinSchaeffer

noncomputable section

-- =====================   Helper lemmas (anatomy of integers)  =====================




/-- `Lt t n` is the sum of `1/p` over the primes `p ≥ t` dividing `n`. -/
def Lt (t : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primeFactors n).filter (fun p : ℕ => t ≤ (p : ℝ)), (1 : ℝ) / (p : ℝ)

lemma Lt_nonneg (t : ℝ) (n : ℕ) : 0 ≤ Lt t n :=
  Finset.sum_nonneg (fun p _ => by positivity)

lemma exp_mul_Lt (a t : ℝ) (n : ℕ) :
    Real.exp (a * Lt t n) =
      ∏ p ∈ (Nat.primeFactors n).filter (fun p : ℕ => t ≤ (p : ℝ)), Real.exp (a / (p : ℝ)) := by
  rw [Lt, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl ?_
  intro p _
  rw [mul_one_div]

lemma indicator_le_exp (a c w : ℝ) (ha : 0 ≤ a) :
    (if c ≤ w then (1 : ℝ) else 0) ≤ Real.exp (a * w) * Real.exp (-(a * c)) := by
  have hkey : Real.exp (a * w) * Real.exp (-(a * c)) = Real.exp (a * (w - c)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hkey]
  by_cases h : c ≤ w
  · rw [if_pos h]
    exact Real.one_le_exp (mul_nonneg ha (sub_nonneg.mpr h))
  · rw [if_neg h]
    exact Real.exp_nonneg _

/-- For `0 ≤ x ≤ 1`, `exp x - 1 ≤ e · x`. -/
lemma exp_sub_one_le_exp_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 ≤ Real.exp 1 * x := by
  have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (by linarith : 0 ≤ 1 - x) hx0 (by ring : (1 - x) + x = 1)
  have hc' : Real.exp x ≤ (1 - x) * 1 + x * Real.exp 1 := by
    simpa [smul_eq_mul] using hc
  nlinarith

/-- The exponent sum occurring in the multiplicative average bound is bounded
uniformly in `t ≥ 2` when the parameter `a` equals `20 t`. -/
lemma expSum_le (N : ℕ) (t a : ℝ) (ht : 2 ≤ t) (ha : 0 ≤ a) (hat : a ≤ 20 * t) :
    (∑ q ∈ (Nat.primesLE N).filter (fun q : ℕ => t ≤ (q : ℝ)),
        (Real.exp (a / (q : ℝ)) - 1) / (q : ℝ)) ≤ 21 * Real.exp 20 := by
  set A : Finset ℕ := (Nat.primesLE N).filter (fun q : ℕ => t ≤ (q : ℝ)) with hA
  set A1 : Finset ℕ := A.filter (fun q : ℕ => (q : ℝ) ≤ 20 * t) with hA1
  set A2 : Finset ℕ := A.filter (fun q : ℕ => ¬ ((q : ℝ) ≤ 20 * t)) with hA2
  have ht0 : 0 < t := by linarith
  have hsplit : (∑ q ∈ A, (Real.exp (a / (q : ℝ)) - 1) / (q : ℝ))
      = (∑ q ∈ A1, (Real.exp (a / (q : ℝ)) - 1) / (q : ℝ))
        + (∑ q ∈ A2, (Real.exp (a / (q : ℝ)) - 1) / (q : ℝ)) := by
    have h := Finset.sum_filter_add_sum_filter_not A (fun q : ℕ => (q : ℝ) ≤ 20 * t)
        (fun q : ℕ => (Real.exp (a / (q : ℝ)) - 1) / (q : ℝ))
    rw [hA1, hA2]
    exact h.symm
  rw [hsplit]
  have hq_ge_t : ∀ q ∈ A, t ≤ (q : ℝ) := by
    intro q hq
    simp only [hA, Finset.mem_filter] at hq
    exact hq.2
  have hq_le_N : ∀ q ∈ A, q ≤ N := by
    intro q hq
    simp only [hA, Finset.mem_filter, Nat.mem_primesLE] at hq
    exact hq.1.1
  have hq_prime : ∀ q ∈ A, Nat.Prime q := by
    intro q hq
    simp only [hA, Finset.mem_filter, Nat.mem_primesLE] at hq
    exact hq.1.2
  have hqpos : ∀ q ∈ A, (0:ℝ) < (q:ℝ) := by
    intro q hq
    have := Nat.Prime.pos (hq_prime q hq)
    exact_mod_cast this
  have hS1 : (∑ q ∈ A1, (Real.exp (a / (q : ℝ)) - 1) / (q : ℝ)) ≤ 20 * Real.exp 20 := by
    have hterm : ∀ q ∈ A1, (Real.exp (a / (q : ℝ)) - 1) / (q : ℝ) ≤ Real.exp 20 / t := by
      intro q hq
      simp only [hA1, Finset.mem_filter] at hq
      obtain ⟨hqA, _⟩ := hq
      have hqt : t ≤ (q:ℝ) := hq_ge_t q hqA
      have hq0 : (0:ℝ) < (q:ℝ) := hqpos q hqA
      have hratio : a / (q:ℝ) ≤ 20 := by
        rw [div_le_iff₀ hq0]; nlinarith
      have hexp : Real.exp (a / (q:ℝ)) ≤ Real.exp 20 := (Real.exp_le_exp).2 hratio
      have hstep1 : (Real.exp (a / (q : ℝ)) - 1) / (q : ℝ) ≤ Real.exp (a/(q:ℝ)) / (q:ℝ) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hq0)
        linarith [Real.exp_pos (a/(q:ℝ))]
      have hstep2 : Real.exp (a/(q:ℝ)) / (q:ℝ) ≤ Real.exp 20 / (q:ℝ) :=
        div_le_div_of_nonneg_right hexp (le_of_lt hq0)
      have hstep3 : Real.exp 20 / (q:ℝ) ≤ Real.exp 20 / t :=
        div_le_div_of_nonneg_left (Real.exp_nonneg 20) ht0 hqt
      linarith [hstep1, hstep2, hstep3]
    calc (∑ q ∈ A1, (Real.exp (a / (q : ℝ)) - 1) / (q : ℝ))
        ≤ ∑ q ∈ A1, Real.exp 20 / t := Finset.sum_le_sum hterm
      _ = (A1.card : ℝ) * (Real.exp 20 / t) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (20 * t) * (Real.exp 20 / t) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hsub : A1 ⊆ Finset.Icc 1 ⌊20*t⌋₊ := by
              intro q hq
              simp only [hA1, Finset.mem_filter] at hq
              obtain ⟨hqA, hqle⟩ := hq
              have hq1 : 1 ≤ q := Nat.Prime.one_le (hq_prime q hqA)
              have hfloor : q ≤ ⌊20*t⌋₊ := Nat.le_floor (by exact_mod_cast hqle)
              exact Finset.mem_Icc.mpr ⟨hq1, hfloor⟩
            have hc1 : A1.card ≤ ⌊20*t⌋₊ := by
              have h2 := Finset.card_le_card hsub
              rw [Nat.card_Icc] at h2
              omega
            have h3 : ((⌊20*t⌋₊ : ℕ) : ℝ) ≤ 20*t := Nat.floor_le (by linarith)
            have : (A1.card : ℝ) ≤ (⌊20*t⌋₊ : ℝ) := by exact_mod_cast hc1
            linarith
      _ = 20 * Real.exp 20 := by
            rw [mul_div_assoc', show (20*t) * Real.exp 20 = t * (20 * Real.exp 20) by ring,
                mul_div_cancel_left₀ (20 * Real.exp 20) (ne_of_gt ht0)]
  have hS2 : (∑ q ∈ A2, (Real.exp (a / (q : ℝ)) - 1) / (q : ℝ)) ≤ 2 * Real.exp 1 := by
    have hterm : ∀ q ∈ A2, (Real.exp (a / (q : ℝ)) - 1) / (q : ℝ)
        ≤ Real.exp 1 * a * (1 / (q : ℝ)^2) := by
      intro q hq
      simp only [hA2, Finset.mem_filter] at hq
      obtain ⟨hqA, hqgt⟩ := hq
      have hq0 : (0:ℝ) < (q:ℝ) := hqpos q hqA
      have hx0 : 0 ≤ a / (q:ℝ) := by positivity
      have hx1 : a / (q:ℝ) ≤ 1 := by
        rw [div_le_one hq0]
        have : 20*t < (q:ℝ) := lt_of_not_ge hqgt
        linarith
      have hexp := exp_sub_one_le_exp_mul hx0 hx1
      calc (Real.exp (a / (q : ℝ)) - 1) / (q : ℝ)
          ≤ (Real.exp 1 * (a/(q:ℝ))) / (q:ℝ) := div_le_div_of_nonneg_right hexp (le_of_lt hq0)
        _ = Real.exp 1 * a * (1 / (q : ℝ)^2) := by
              field_simp
    calc (∑ q ∈ A2, (Real.exp (a / (q : ℝ)) - 1) / (q : ℝ))
        ≤ ∑ q ∈ A2, Real.exp 1 * a * (1 / (q : ℝ)^2) := Finset.sum_le_sum hterm
      _ = Real.exp 1 * a * (∑ q ∈ A2, 1 / (q : ℝ)^2) := by
            rw [Finset.mul_sum]
      _ ≤ Real.exp 1 * a * (2 / (20*t)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have hsub : A2 ⊆ Finset.Ioo ⌊20*t⌋₊ (N+1) := by
              intro q hq
              simp only [hA2, Finset.mem_filter] at hq
              obtain ⟨hqA, hqgt⟩ := hq
              have hqN : q ≤ N := hq_le_N q hqA
              have hfl : ⌊20*t⌋₊ < q := by
                have h2 : (⌊20*t⌋₊ : ℝ) ≤ 20*t := Nat.floor_le (by linarith)
                have h3 : (⌊20*t⌋₊ : ℝ) < (q:ℝ) := lt_of_le_of_lt h2 (lt_of_not_ge hqgt)
                exact_mod_cast h3
              exact Finset.mem_Ioo.mpr ⟨hfl, by omega⟩
            have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun i _ _ => by positivity : ∀ i ∈ Finset.Ioo ⌊20*t⌋₊ (N+1), i ∉ A2 → 0 ≤ 1 / (i:ℝ)^2)
            have htail : (∑ i ∈ Finset.Ioo ⌊20*t⌋₊ (N+1), (1:ℝ)/(i:ℝ)^2) ≤ 2/((⌊20*t⌋₊:ℝ)+1) := by
              have h := sum_Ioo_inv_sq_le (α := ℝ) ⌊20*t⌋₊ (N+1)
              simpa [one_div] using h
            have hden : (20*t : ℝ) ≤ (⌊20*t⌋₊ : ℝ) + 1 := le_of_lt (Nat.lt_floor_add_one (20*t))
            have hd2 : 2 / ((⌊20*t⌋₊:ℝ)+1) ≤ 2 / (20*t) :=
              div_le_div_of_nonneg_left (by norm_num) (by linarith : (0:ℝ) < 20*t) hden
            linarith [hle, htail, hd2]
      _ ≤ 2 * Real.exp 1 := by
            have h2pos : (0:ℝ) < 2/(20*t) := by positivity
            have hle1 : Real.exp 1 * a * (2/(20*t)) ≤ Real.exp 1 * (20*t) * (2/(20*t)) := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt h2pos)
              exact mul_le_mul_of_nonneg_left hat (Real.exp_nonneg 1)
            refine hle1.trans ?_
            rw [mul_div_assoc', show Real.exp 1 * (20*t) * 2 = (20*t) * (2 * Real.exp 1) by ring,
                mul_div_cancel_left₀ (2 * Real.exp 1) (ne_of_gt (by linarith : (0:ℝ) < 20*t))]
  have he20 : 2 * Real.exp 1 ≤ Real.exp 20 := by
    have h1 : (2:ℝ) < Real.exp 1 := Real.exp_one_gt_two
    have h2 : Real.exp 2 ≤ Real.exp 20 := Real.exp_le_exp.mpr (by norm_num)
    have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  linarith [hS1, hS2, he20]

lemma anatomy_unweighted_aux (N : ℕ) (t c : ℝ) (ht : 2 ≤ t) (hc : 0 < c) :
    (((Finset.Icc 1 N).filter (fun n : ℕ => c ≤ Lt t n)).card : ℝ)
      ≤ Real.exp (21 * Real.exp 20) * (N : ℝ) * Real.exp (-(20 * c * t)) := by
  have ha : 0 ≤ 20 * t := by linarith
  have hcard : (((Finset.Icc 1 N).filter (fun n : ℕ => c ≤ Lt t n)).card : ℝ)
      = ∑ n ∈ Finset.Icc 1 N, (if c ≤ Lt t n then (1:ℝ) else 0) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun n _ => by by_cases h : c ≤ Lt t n <;> simp [h])
  have hstep1 : (((Finset.Icc 1 N).filter (fun n : ℕ => c ≤ Lt t n)).card : ℝ)
      ≤ ∑ n ∈ Finset.Icc 1 N, Real.exp ((20*t) * Lt t n) * Real.exp (-((20*t) * c)) := by
    rw [hcard]
    apply Finset.sum_le_sum
    intro n _
    exact indicator_le_exp (20*t) c (Lt t n) ha
  have hstep2 : (∑ n ∈ Finset.Icc 1 N, Real.exp ((20*t) * Lt t n) * Real.exp (-((20*t) * c)))
      = Real.exp (-((20*t) * c)) * (∑ n ∈ Finset.Icc 1 N, Real.exp ((20*t) * Lt t n)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hstep3 : (∑ n ∈ Finset.Icc 1 N, Real.exp ((20*t) * Lt t n))
      = ∑ n ∈ Finset.Icc 1 N, ∏ p ∈ (Nat.primeFactors n).filter (fun p : ℕ => t ≤ (p:ℝ)),
            Real.exp ((20*t)/(p:ℝ)) := by
    apply Finset.sum_congr rfl
    intro n _
    exact exp_mul_Lt (20*t) t n
  have hstep4 : (∑ n ∈ Finset.Icc 1 N, ∏ p ∈ (Nat.primeFactors n).filter (fun p : ℕ => t ≤ (p:ℝ)),
            Real.exp ((20*t)/(p:ℝ)))
      ≤ (N:ℝ) * Real.exp (∑ q ∈ (Nat.primesLE N).filter (fun q : ℕ => t ≤ (q:ℝ)),
            (Real.exp ((20*t)/(q:ℝ)) - 1)/(q:ℝ)) :=
    Commons.NumberTheory.Tenenbaum.multiplicative_average_bound_core t (20*t) N ha
  have hstep5 : Real.exp (∑ q ∈ (Nat.primesLE N).filter (fun q : ℕ => t ≤ (q:ℝ)),
            (Real.exp ((20*t)/(q:ℝ)) - 1)/(q:ℝ)) ≤ Real.exp (21 * Real.exp 20) :=
    Real.exp_le_exp.mpr (expSum_le N t (20*t) ht ha (le_refl _))
  calc (((Finset.Icc 1 N).filter (fun n : ℕ => c ≤ Lt t n)).card : ℝ)
      ≤ Real.exp (-((20*t) * c)) * (∑ n ∈ Finset.Icc 1 N, Real.exp ((20*t) * Lt t n)) := by
        rw [← hstep2]; exact hstep1
    _ = Real.exp (-((20*t) * c)) * (∑ n ∈ Finset.Icc 1 N, ∏ p ∈ (Nat.primeFactors n).filter (fun p : ℕ => t ≤ (p:ℝ)),
            Real.exp ((20*t)/(p:ℝ))) := by rw [hstep3]
    _ ≤ Real.exp (-((20*t) * c)) * ((N:ℝ) * Real.exp (∑ q ∈ (Nat.primesLE N).filter (fun q : ℕ => t ≤ (q:ℝ)),
            (Real.exp ((20*t)/(q:ℝ)) - 1)/(q:ℝ))) := by
          apply mul_le_mul_of_nonneg_left hstep4 (Real.exp_nonneg _)
    _ ≤ Real.exp (-((20*t) * c)) * ((N:ℝ) * Real.exp (21 * Real.exp 20)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          exact mul_le_mul_of_nonneg_left hstep5 (by positivity)
    _ = Real.exp (21 * Real.exp 20) * (N : ℝ) * Real.exp (-(20 * c * t)) := by
          rw [show -((20*t)*c) = -(20*c*t) by ring]; ring



lemma prod_one_add_le_exp_sum (w : ℕ → ℝ) (s : Finset ℕ) (h0 : ∀ p ∈ s, 0 ≤ w p) :
    (∏ p ∈ s, (1 + w p)) ≤ Real.exp (∑ p ∈ s, w p) := by
  calc (∏ p ∈ s, (1 + w p)) ≤ ∏ p ∈ s, Real.exp (w p) := by
        refine Finset.prod_le_prod₀ ?_ ?_
        · intro p hp; exact add_nonneg zero_le_one (h0 p hp)
        · intro p hp; simpa [add_comm] using (Real.add_one_le_exp (w p))
    _ = Real.exp (∑ p ∈ s, w p) := (Real.exp_sum s w).symm

def Hfun (t a : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else ∏ p ∈ (Nat.primeFactors n).filter (fun p : ℕ => t ≤ (p : ℝ)), Real.exp (a / (p : ℝ))

lemma Hfun_zero (t a : ℝ) : Hfun t a 0 = 0 := rfl

lemma Hfun_one (t a : ℝ) : Hfun t a 1 = 1 := by
  simp [Hfun]

lemma Hfun_eq_exp (t a : ℝ) {n : ℕ} (hn : n ≠ 0) : Hfun t a n = Real.exp (a * Lt t n) := by
  rw [Hfun, if_neg hn, exp_mul_Lt]

lemma Hfun_mul_coprime (t a : ℝ) {m n : ℕ} (h : m.Coprime n) :
    Hfun t a (m * n) = Hfun t a m * Hfun t a n := by
  rcases eq_or_ne m 0 with hm | hm
  · subst hm
    have hn : n = 1 := by simpa [Nat.gcd_zero_left] using h
    subst hn
    simp [Hfun]
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    have hm1 : m = 1 := by simpa [Nat.gcd_zero_right] using h
    subst hm1
    simp [Hfun]
  rw [Hfun, if_neg (mul_ne_zero hm hn), Hfun, if_neg hm, Hfun, if_neg hn,
    Nat.primeFactors_mul hm hn, Finset.filter_union]
  rw [Finset.prod_union]
  exact (Nat.Coprime.disjoint_primeFactors h).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

def HA (t a : ℝ) : ArithmeticFunction ℝ := ⟨Hfun t a, Hfun_zero t a⟩

lemma HA_apply (t a : ℝ) (n : ℕ) : (HA t a) n = Hfun t a n := rfl

lemma HA_isMult (t a : ℝ) : (HA t a).IsMultiplicative :=
  ⟨Hfun_one t a, fun {m n} h => Hfun_mul_coprime t a h⟩

def phiA : ArithmeticFunction ℝ := ⟨fun n => (n.totient : ℝ), by simp [Nat.totient_zero]⟩

lemma phiA_isMult : phiA.IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · show (((1:ℕ).totient : ℕ) : ℝ) = 1
    simp [Nat.totient_one]
  · intro m n h
    show (((m*n).totient : ℕ) : ℝ) = (m.totient : ℝ) * (n.totient : ℝ)
    rw [Nat.totient_mul h]; push_cast; ring

lemma conv_apply (t a : ℝ) (M : ℕ) :
    (HA t a * phiA) M = ∑ d ∈ M.divisors, Hfun t a d * ((M / d).totient : ℝ) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun i j => (HA t a) i * phiA j)]
  rfl

lemma conv_factor (t a : ℝ) {M : ℕ} (hM : M ≠ 0) :
    (HA t a * phiA) M
      = ∏ p ∈ M.primeFactors, (HA t a * phiA) (p ^ (M.factorization p)) := by
  have hm : (HA t a * phiA).IsMultiplicative :=
    ArithmeticFunction.IsMultiplicative.mul (HA_isMult t a) phiA_isMult
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization (HA t a * phiA) hm hM,
    ← M.support_factorization, Finsupp.prod]

lemma HA_pow_eq (t a : ℝ) {p k : ℕ} (hp : Nat.Prime p) (hk : 1 ≤ k) :
    (HA t a) (p ^ k) = if t ≤ (p : ℝ) then Real.exp (a / (p : ℝ)) else 1 := by
  rw [HA_apply, Hfun, if_neg (pow_ne_zero k hp.ne_zero),
    Nat.primeFactors_prime_pow (by omega : k ≠ 0) hp, Finset.filter_singleton]
  by_cases h : t ≤ (p : ℝ) <;> simp [h]

lemma Hfun_pow_eq (t a : ℝ) {p k : ℕ} (hp : Nat.Prime p) (hk : 1 ≤ k) :
    Hfun t a (p ^ k) = if t ≤ (p : ℝ) then Real.exp (a / (p : ℝ)) else 1 := by
  rw [← HA_apply t a (p^k)]
  exact HA_pow_eq t a hp hk

lemma sum_totient_prime_pow_pred (p k : ℕ) (hp : Nat.Prime p) (hk : 1 ≤ k) :
    ∑ i ∈ Finset.range k, ((p^i).totient : ℝ) = (p:ℝ)^(k-1) := by
  have h := Nat.sum_totient (p^(k-1))
  rw [Nat.divisors_prime_pow hp (k-1), Finset.sum_map] at h
  simp only [Function.Embedding.coeFn_mk] at h
  have hk' : k - 1 + 1 = k := by omega
  rw [hk'] at h
  exact_mod_cast h

lemma local_factor (t a : ℝ) {p k : ℕ} (hp : Nat.Prime p) (hk : 1 ≤ k) :
    (HA t a * phiA) (p ^ k)
      = (p:ℝ)^k * (if t ≤ (p : ℝ) then 1 + (Real.exp (a / (p : ℝ)) - 1) / (p : ℝ) else 1) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  set c : ℝ := (if t ≤ (p:ℝ) then Real.exp (a/(p:ℝ)) else 1) with hc
  have hck : ∀ i : ℕ, 1 ≤ i → Hfun t a (p^i) = c := by
    intro i hi
    rw [Hfun_pow_eq t a hp hi, hc]
  have hg0 : Hfun t a (p^0) * (((p^k)/(p^0)).totient : ℝ) = ((p^k).totient : ℝ) := by
    rw [pow_zero, Nat.div_one, Hfun_one, one_mul]
  have hA : ∑ i ∈ Finset.range k, Hfun t a (p^(i+1)) * (((p^k)/(p^(i+1))).totient : ℝ)
      = ∑ i ∈ Finset.range k, c * (((p^(k-1-i)).totient : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i + 1 ≤ k := by have := Finset.mem_range.mp hi; omega
    have h1 : Hfun t a (p^(i+1)) = c := hck (i+1) (by omega)
    have h2 : p^k / p^(i+1) = p^(k-1-i) := by
      rw [Nat.pow_div hik hp.pos]
      congr 1
      omega
    rw [h1, h2]
  have hsumA : ∑ i ∈ Finset.range (k+1), Hfun t a (p^i) * (((p^k)/(p^i)).totient : ℝ)
      = (((p^k).totient : ℝ)) + c * ∑ i ∈ Finset.range k, (((p^(k-1-i)).totient : ℝ)) := by
    rw [Finset.sum_range_succ', hg0, hA, Finset.mul_sum, add_comm]
  rw [conv_apply, Nat.sum_divisors_prime_pow hp, hsumA]
  have hsumB : ∑ i ∈ Finset.range k, (((p^(k-1-i)).totient : ℝ)) = (p:ℝ)^(k-1) := by
    have h := Finset.sum_range_reflect (fun j : ℕ => (((p^j).totient : ℝ))) k
    rw [h]
    exact sum_totient_prime_pow_pred p k hp hk
  rw [hsumB]
  rw [Nat.totient_prime_pow hp (by omega : 0 < k), hc]
  push_cast
  rw [Nat.cast_sub hp.one_le]
  have hpk : (p:ℝ)^k = (p:ℝ)^(k-1) * (p:ℝ) := by
    rw [mul_comm, ← pow_succ']; congr 1; omega
  by_cases htp : t ≤ (p:ℝ)
  · rw [if_pos htp, if_pos htp, hpk]
    field_simp
    ring
  · rw [if_neg htp, if_neg htp, hpk]
    ring

lemma prod_factorization_eq (M : ℕ) (hM : M ≠ 0) :
    ∏ p ∈ M.primeFactors, (p:ℝ) ^ (M.factorization p) = (M:ℝ) := by
  have h : ∏ p ∈ M.primeFactors, p ^ (M.factorization p) = M := by
    rw [← M.support_factorization, ← Finsupp.prod]
    exact Nat.prod_factorization_pow_eq_self hM
  exact_mod_cast h

lemma prod_bound (t a : ℝ) {M : ℕ} (hM : M ≠ 0) (ht : 2 ≤ t) (ha : 0 ≤ a) (hat : a ≤ 20 * t) :
    (HA t a * phiA) M ≤ (M:ℝ) * Real.exp (21 * Real.exp 20) := by
  have hfac : ∀ p ∈ M.primeFactors, (HA t a * phiA) (p ^ (M.factorization p))
      = (p:ℝ)^(M.factorization p) *
        (if t ≤ (p:ℝ) then 1 + (Real.exp (a/(p:ℝ)) - 1)/(p:ℝ) else 1) := by
    intro p hp
    have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
    have hdvd : p ∣ M := (Nat.mem_primeFactors.mp hp).2.1
    have hk : 1 ≤ M.factorization p := by
      have h2 : p ^ 1 ∣ M := by simpa using hdvd
      exact (Nat.Prime.pow_dvd_iff_le_factorization (p := p) (k := 1) (n := M) hpp hM).mp h2
    exact local_factor t a hpp hk
  rw [conv_factor t a hM, Finset.prod_congr rfl hfac, Finset.prod_mul_distrib,
    prod_factorization_eq M hM]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Finset.prod_filter]
  have hw : ∀ p ∈ (Nat.primesLE M).filter (fun p : ℕ => t ≤ (p:ℝ)),
      0 ≤ (Real.exp (a/(p:ℝ)) - 1)/(p:ℝ) := by
    intro p hp
    have hp0 : (0:ℝ) < (p:ℝ) := by
      have := Nat.Prime.pos (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
      exact_mod_cast this
    exact div_nonneg (sub_nonneg.mpr (Real.one_le_exp (div_nonneg ha (by positivity)))) (le_of_lt hp0)
  have hsub : (M.primeFactors).filter (fun p : ℕ => t ≤ (p:ℝ))
      ⊆ (Nat.primesLE M).filter (fun p : ℕ => t ≤ (p:ℝ)) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp.1).1
    have hdvd : p ∣ M := (Nat.mem_primeFactors.mp hp.1).2.1
    exact ⟨Nat.mem_primesLE.mpr ⟨Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hdvd, hpp⟩, hp.2⟩
  calc ∏ p ∈ (M.primeFactors).filter (fun p : ℕ => t ≤ (p:ℝ)),
          (1 + (Real.exp (a/(p:ℝ)) - 1)/(p:ℝ))
      ≤ Real.exp (∑ p ∈ (M.primeFactors).filter (fun p : ℕ => t ≤ (p:ℝ)),
          (Real.exp (a/(p:ℝ)) - 1)/(p:ℝ)) := by
        apply prod_one_add_le_exp_sum
        intro p hp
        have hp0 : (0:ℝ) < (p:ℝ) := by
          have := Nat.Prime.pos (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1
          exact_mod_cast this
        exact div_nonneg (sub_nonneg.mpr (Real.one_le_exp (div_nonneg ha (by positivity)))) (le_of_lt hp0)
    _ ≤ Real.exp (∑ p ∈ (Nat.primesLE M).filter (fun p : ℕ => t ≤ (p:ℝ)),
          (Real.exp (a/(p:ℝ)) - 1)/(p:ℝ)) := by
        apply Real.exp_le_exp.mpr
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hw i hi)
    _ ≤ Real.exp (21 * Real.exp 20) := Real.exp_le_exp.mpr (expSum_le M t a ht ha hat)

lemma anatomy_divisor_aux (M : ℕ) (t c : ℝ) (ht : 2 ≤ t) (hc : 0 < c) :
    (∑ m ∈ M.divisors, (if c ≤ Lt t m then ((M/m).totient : ℝ) else 0))
      ≤ Real.exp (21 * Real.exp 20) * (M:ℝ) * Real.exp (-(20 * c * t)) := by
  rcases eq_or_ne M 0 with hM | hM
  · subst hM; simp
  have ha : 0 ≤ 20*t := by linarith
  have hstep : (∑ m ∈ M.divisors, (if c ≤ Lt t m then ((M/m).totient : ℝ) else 0))
      ≤ Real.exp (-((20*t) * c)) * ((HA t (20*t) * phiA) M) := by
    rw [conv_apply t (20*t) M, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    have hm0 : m ≠ 0 := by
      intro h
      rw [Nat.mem_divisors] at hm
      exact hm.2 (Nat.eq_zero_of_zero_dvd (h ▸ hm.1))
    have hc1 : (if c ≤ Lt t m then (1:ℝ) else 0)
        ≤ Real.exp (-((20*t)*c)) * Hfun t (20*t) m := by
      rw [Hfun_eq_exp t (20*t) hm0]
      calc (if c ≤ Lt t m then (1:ℝ) else 0)
          ≤ Real.exp ((20*t) * Lt t m) * Real.exp (-((20*t) * c)) :=
            indicator_le_exp (20*t) c (Lt t m) ha
        _ = Real.exp (-((20*t)*c)) * Real.exp ((20*t) * Lt t m) := by ring
    have hφ : 0 ≤ ((M/m).totient : ℝ) := by positivity
    have hsplit : (if c ≤ Lt t m then ((M/m).totient : ℝ) else 0)
        = (if c ≤ Lt t m then (1:ℝ) else 0) * ((M/m).totient : ℝ) := by
      by_cases h : c ≤ Lt t m
      · simp only [if_pos h, one_mul]
      · simp only [if_neg h, zero_mul]
    rw [hsplit]
    calc (if c ≤ Lt t m then (1:ℝ) else 0) * ((M/m).totient:ℝ)
        ≤ (Real.exp (-((20*t)*c)) * Hfun t (20*t) m) * ((M/m).totient:ℝ) :=
          mul_le_mul_of_nonneg_right hc1 hφ
      _ = Real.exp (-((20*t)*c)) * (Hfun t (20*t) m * ((M/m).totient:ℝ)) := by ring
  calc (∑ m ∈ M.divisors, (if c ≤ Lt t m then ((M/m).totient : ℝ) else 0))
      ≤ Real.exp (-((20*t) * c)) * ((HA t (20*t) * phiA) M) := hstep
    _ ≤ Real.exp (-((20*t) * c)) * ((M:ℝ) * Real.exp (21 * Real.exp 20)) :=
        mul_le_mul_of_nonneg_left (prod_bound t (20*t) hM ht ha (le_refl _)) (Real.exp_nonneg _)
    _ = Real.exp (21 * Real.exp 20) * (M:ℝ) * Real.exp (-(20 * c * t)) := by
        rw [show -((20*t)*c) = -(20*c*t) by ring]; ring

theorem anatomy_divisor :
    ∃ K : ℝ, 0 < K ∧ ∃ β : ℝ, 0 < β ∧
      ∀ (M : ℕ) (t c : ℝ), 2 ≤ t → 0 < c → c ≤ 1 →
        (Finset.sum M.divisors (fun m : ℕ =>
            if c ≤ Finset.sum ((Nat.primeFactors m).filter (fun p : ℕ => t ≤ (p : ℝ)))
                (fun p : ℕ => (1 : ℝ) / (p : ℝ)) then ((M / m).totient : ℝ) else 0))
        ≤ K * (M : ℝ) * Real.exp (-(β * c * t)) := by
  exact ⟨Real.exp (21 * Real.exp 20), Real.exp_pos _, 20, by norm_num,
    fun M t c ht hc _ => anatomy_divisor_aux M t c ht hc⟩



-- =====================   Helper lemmas (decay away from the diagonal)  =====================


/-- Bernoulli-type inequality for the exponent `5/3`. -/
lemma rpow_bern {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    1 - (5/3:ℝ) * (1 - t) ≤ t ^ ((5:ℝ)/3) := by
  set s : ℝ := t ^ ((1:ℝ)/3) with hs
  have hs0 : 0 ≤ s := Real.rpow_nonneg h0 _
  have hs1 : s ≤ 1 := Real.rpow_le_one h0 h1 (by norm_num)
  have hs3 : s ^ 3 = t := by
    rw [hs, ← Real.rpow_natCast (t ^ ((1:ℝ)/3)) 3]
    rw [← Real.rpow_mul h0]
    norm_num
  have hs5 : s ^ 5 = t ^ ((5:ℝ)/3) := by
    rw [hs, ← Real.rpow_natCast (t ^ ((1:ℝ)/3)) 5]
    rw [← Real.rpow_mul h0]
    norm_num
  rw [← hs5, ← hs3]
  have hid : (s-1)^2 * (3*s^3+6*s^2+4*s+2) = 3*s^5 - 5*s^3 + 2 := by ring
  have hnn : 0 ≤ (3*s^3+6*s^2+4*s+2) := by nlinarith [sq_nonneg s, mul_nonneg hs0 (sq_nonneg s), hs0]
  have := mul_nonneg (sq_nonneg (s-1)) hnn
  rw [hid] at this
  linarith

/-- For `0 ≤ lam < 1`, the sum of `lam ^ dist i j` over an initial segment is bounded. -/
lemma lam_dist_sum_range (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam < 1) (N i : ℕ) (hi : i ≤ N) :
    ∑ j ∈ Finset.range (N+1), lam ^ (Nat.dist i j) ≤ 1 + 2 * lam / (1 - lam) := by
  have h1 : (0:ℝ) < 1 - lam := by linarith
  have hgeom : ∀ n : ℕ, ∑ k ∈ Finset.range n, lam ^ (k+1) ≤ lam / (1 - lam) := by
    intro n
    have h2 : ∑ k ∈ Finset.range n, lam ^ (k+1) = lam * ∑ k ∈ Finset.range n, lam ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_succ]; ring
    rw [h2]
    have h3 : ∑ k ∈ Finset.range n, lam ^ k ≤ 1/(1-lam) := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp only [Finset.range_zero, Finset.sum_empty]
        exact div_nonneg zero_le_one (le_of_lt h1)
      · have hne : lam ≠ 1 := ne_of_lt hl1
        rw [geom_sum_eq hne]
        have heq : (lam^n - 1)/(lam - 1) = (1 - lam^n)/(1 - lam) := by
          rw [show (1:ℝ) - lam^n = -(lam^n - 1) by ring,
            show (1:ℝ) - lam = -(lam - 1) by ring, neg_div_neg_eq]
        rw [heq]
        apply div_le_div_of_nonneg_right _ (le_of_lt h1)
        have : (0:ℝ) ≤ lam^n := by positivity
        linarith
    calc lam * ∑ k ∈ Finset.range n, lam ^ k ≤ lam * (1/(1-lam)) :=
          mul_le_mul_of_nonneg_left h3 hl0
      _ = lam/(1-lam) := by ring
  have hsplit : ∑ j ∈ Finset.range (N+1), lam ^ (Nat.dist i j)
      = (∑ j ∈ Finset.range i, lam ^ (Nat.dist i j))
        + ∑ k ∈ Finset.range (N+1-i), lam ^ (Nat.dist i (i+k)) := by
    conv_lhs => rw [show N + 1 = i + (N + 1 - i) by omega, Finset.sum_range_add]
  have hA : ∑ j ∈ Finset.range i, lam ^ (Nat.dist i j) = ∑ k ∈ Finset.range i, lam ^ (k+1) := by
    rw [← Finset.sum_range_reflect (fun k => lam^(k+1)) i]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < i := Finset.mem_range.mp hj
    have h1' : Nat.dist i j = i - j := Nat.dist_eq_sub_of_le_right (n := i) (m := j) (by omega)
    have h2' : i - 1 - j + 1 = i - j := by omega
    rw [h1', ← h2']
  have hB1 : ∑ k ∈ Finset.range (N+1-i), lam ^ (Nat.dist i (i+k))
      = ∑ k ∈ Finset.range (N+1-i), lam ^ k := by
    apply Finset.sum_congr rfl
    intro k hk
    have h1' : Nat.dist (i+k) i = k := by
      rw [Nat.dist_eq_sub_of_le_right (n := i+k) (m := i) (by omega)]
      omega
    rw [Nat.dist_comm, h1']
  have hB2 : ∑ k ∈ Finset.range (N+1-i), lam ^ k
      = (1:ℝ) + ∑ k ∈ Finset.range (N-i), lam ^ (k+1) := by
    have hNi : N + 1 - i = (N - i) + 1 := by omega
    rw [hNi, Finset.sum_range_succ']
    ring
  rw [hsplit, hA, hB1, hB2]
  have hA' : ∑ k ∈ Finset.range i, lam ^ (k+1) ≤ lam/(1-lam) := hgeom i
  have hB' : ∑ k ∈ Finset.range (N-i), lam ^ (k+1) ≤ lam/(1-lam) := hgeom (N-i)
  have h2l : (2:ℝ)*lam/(1-lam) = lam/(1-lam) + lam/(1-lam) := by ring
  linarith [hA', hB', h2l]

/-- The `lam`-distance sum over the indices different from `i`. -/
lemma lam_dist_sum_ne (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam < 1) (N i : ℕ) (hi : i ≤ N) :
    ∑ j ∈ (Finset.range (N+1)).filter (fun j => j ≠ i), lam ^ (Nat.dist i j)
      ≤ 2 * lam / (1 - lam) := by
  have h1 := lam_dist_sum_range lam hl0 hl1 N i hi
  have hs := Finset.sum_filter_add_sum_filter_not (Finset.range (N+1)) (fun j => j ≠ i)
    (fun j => lam ^ (Nat.dist i j))
  have h4 : (Finset.range (N+1)).filter (fun j => ¬ j ≠ i) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, hjne⟩; exact not_not.mp hjne
    · rintro rfl; exact ⟨by omega, not_not_intro rfl⟩
  rw [h4] at hs
  simp only [Finset.sum_singleton, Nat.dist_self, pow_zero] at hs
  have : (1 + 2 * lam / (1 - lam)) - 1 = 2 * lam / (1 - lam) := by ring
  linarith [h1, hs, this]

/-- Termwise Cauchy-Schwarz comparison. -/
lemma xy_le_rpow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h1 : x * y ≤ 1) :
    x * y ≤ (x^((5:ℝ)/3))^((1:ℝ)/2) * (y^((5:ℝ)/3))^((1:ℝ)/2) := by
  rcases eq_or_lt_of_le (mul_nonneg hx hy) with h0 | h0
  · rw [← h0]
    exact mul_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hx (5/3:ℝ)) ((1:ℝ)/2))
      (Real.rpow_nonneg (Real.rpow_nonneg hy (5/3:ℝ)) ((1:ℝ)/2))
  · have h := Real.rpow_le_rpow_of_exponent_ge h0 h1 (by norm_num : (5:ℝ)/6 ≤ 1)
    rw [Real.rpow_one] at h
    have h2 : (x*y)^((5:ℝ)/6) = (x^((5:ℝ)/3))^((1:ℝ)/2) * (y^((5:ℝ)/3))^((1:ℝ)/2) := by
      rw [show (5:ℝ)/6 = ((5:ℝ)/3)*((1:ℝ)/2) by norm_num]
      rw [Real.rpow_mul (mul_nonneg hx hy)]
      rw [Real.mul_rpow hx hy]
      rw [Real.mul_rpow (Real.rpow_nonneg hx (5/3:ℝ)) (Real.rpow_nonneg hy (5/3:ℝ))]
    rw [h2] at h
    exact h

lemma sq_rpow_half {z : ℝ} (h : 0 ≤ z) : (z^((1:ℝ)/2))^2 = z := by
  simpa [Real.sqrt_eq_rpow] using Real.sq_sqrt h

lemma mul_rpow_half {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a*b)^((1:ℝ)/2) = a^((1:ℝ)/2) * b^((1:ℝ)/2) := by
  simpa [Real.sqrt_eq_rpow] using Real.sqrt_mul ha b

lemma mul_rpow_half_symm {a b : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b) :
    a^((1:ℝ)/2) * b^((1:ℝ)/2) = (a*b)^((1:ℝ)/2) := (mul_rpow_half ha _hb).symm

/-- Cauchy-Schwarz for a nested double sum. -/
lemma cs_prod (s t : Finset ℕ) (a b : ℕ → ℕ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ t, a i j * b i j)^2
      ≤ (∑ i ∈ s, ∑ j ∈ t, a i j^2) * (∑ i ∈ s, ∑ j ∈ t, b i j^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (s ×ˢ t)
    (fun p : ℕ × ℕ => a p.1 p.2) (fun p : ℕ × ℕ => b p.1 p.2)
  simpa [Finset.sum_product] using h

/-- The main Cauchy-Schwarz bound on the `lam`-weighted sum. -/
lemma lam_cs_bound (N : ℕ) (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (x y : ℕ → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hy0 : ∀ j, 0 ≤ y j)
    (hx1 : ∀ i, x i ≤ 1) (hy1 : ∀ j, y j ≤ 1)
    (hxs : ∑ i ∈ Finset.range (N+1), x i ^ ((5:ℝ)/3) = 1)
    (hys : ∑ j ∈ Finset.range (N+1), y j ^ ((5:ℝ)/3) = 1) :
    ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1), lam ^ (Nat.dist i j) * x i * y j
      ≤ 1 + 2 * lam / (1 - lam) := by
  have h1 : (0:ℝ) < 1 - lam := by linarith
  set A : ℝ := ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
      lam ^ (Nat.dist i j) * x i * y j with hA
  set B : ℝ := ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
      (lam ^ (Nat.dist i j) * x i ^ ((5:ℝ)/3))^((1:ℝ)/2)
        * (lam ^ (Nat.dist i j) * y j ^ ((5:ℝ)/3))^((1:ℝ)/2) with hB
  set C1 : ℝ := ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
      lam ^ (Nat.dist i j) * x i ^ ((5:ℝ)/3) with hC1
  set C2 : ℝ := ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
      lam ^ (Nat.dist i j) * y j ^ ((5:ℝ)/3) with hC2
  have hAB : A ≤ B := by
    rw [hA, hB]
    apply Finset.sum_le_sum; intro i hi
    apply Finset.sum_le_sum; intro j hj
    have hxy : x i * y j ≤ 1 := by
      have := mul_le_mul (hx1 i) (hy1 j) (hy0 j) zero_le_one
      simpa using this
    have h := xy_le_rpow (hx0 i) (hy0 j) hxy
    have hL : lam ^ (Nat.dist i j) * x i * y j = lam ^ (Nat.dist i j) * (x i * y j) := by ring
    have hpow : (0:ℝ) ≤ lam ^ (Nat.dist i j) := pow_nonneg hl0 _
    have hR : (lam ^ (Nat.dist i j) * x i ^ ((5:ℝ)/3))^((1:ℝ)/2)
          * (lam ^ (Nat.dist i j) * y j ^ ((5:ℝ)/3))^((1:ℝ)/2)
        = lam ^ (Nat.dist i j) * ((x i^((5:ℝ)/3))^((1:ℝ)/2) * (y j^((5:ℝ)/3))^((1:ℝ)/2)) := by
      rw [mul_rpow_half hpow (Real.rpow_nonneg (hx0 i) _),
        mul_rpow_half hpow (Real.rpow_nonneg (hy0 j) _)]
      have hsq : (lam ^ (Nat.dist i j))^((1:ℝ)/2) * (lam ^ (Nat.dist i j))^((1:ℝ)/2)
          = lam ^ (Nat.dist i j) := by
        rw [← sq]; exact sq_rpow_half hpow
      rw [show (lam ^ (Nat.dist i j))^((1:ℝ)/2) * (x i ^ ((5:ℝ)/3))^((1:ℝ)/2)
            * ((lam ^ (Nat.dist i j))^((1:ℝ)/2) * (y j ^ ((5:ℝ)/3))^((1:ℝ)/2))
          = ((lam ^ (Nat.dist i j))^((1:ℝ)/2) * (lam ^ (Nat.dist i j))^((1:ℝ)/2))
            * ((x i ^ ((5:ℝ)/3))^((1:ℝ)/2) * (y j ^ ((5:ℝ)/3))^((1:ℝ)/2)) from by ring]
      rw [hsq]
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  -- Cauchy-Schwarz
  have hcs : B^2 ≤ C1 * C2 := by
    have h := cs_prod (Finset.range (N+1)) (Finset.range (N+1))
      (fun i j => (lam ^ (Nat.dist i j) * x i ^ ((5:ℝ)/3))^((1:ℝ)/2))
      (fun i j => (lam ^ (Nat.dist i j) * y j ^ ((5:ℝ)/3))^((1:ℝ)/2))
    have e1 : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
          ((lam ^ (Nat.dist i j) * x i ^ ((5:ℝ)/3))^((1:ℝ)/2))^2) = C1 := by
      rw [hC1]
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      rw [mul_rpow_half (pow_nonneg hl0 _) (Real.rpow_nonneg (hx0 i) _), mul_pow,
        sq_rpow_half (pow_nonneg hl0 _), sq_rpow_half (Real.rpow_nonneg (hx0 i) _)]
    have e2 : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
          ((lam ^ (Nat.dist i j) * y j ^ ((5:ℝ)/3))^((1:ℝ)/2))^2) = C2 := by
      rw [hC2]
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      rw [mul_rpow_half (pow_nonneg hl0 _) (Real.rpow_nonneg (hy0 j) _), mul_pow,
        sq_rpow_half (pow_nonneg hl0 _), sq_rpow_half (Real.rpow_nonneg (hy0 j) _)]
    rw [e1, e2] at h
    rw [hB]
    exact h
  have hC1u : C1 ≤ (1 + 2*lam/(1-lam)) * 1 := by
    have hmid : C1 ≤ (1 + 2*lam/(1-lam)) * (∑ i ∈ Finset.range (N+1), x i ^ ((5:ℝ)/3)) := by
      rw [hC1, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i ≤ N := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi
      have h := lam_dist_sum_range lam hl0 hl1 N i hiN
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (hx0 i) _)
    calc C1 ≤ (1 + 2*lam/(1-lam)) * (∑ i ∈ Finset.range (N+1), x i ^ ((5:ℝ)/3)) := hmid
      _ = (1 + 2*lam/(1-lam)) * 1 := by rw [hxs]
  have hC2u : C2 ≤ (1 + 2*lam/(1-lam)) * 1 := by
    have hinner : ∀ j ∈ Finset.range (N+1),
        ∑ i ∈ Finset.range (N+1), lam ^ (Nat.dist i j) * y j ^ ((5:ℝ)/3)
        ≤ (1 + 2*lam/(1-lam)) * y j ^ ((5:ℝ)/3) := by
      intro j hj
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hy0 j) _)
      have hjN : j ≤ N := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj
      calc ∑ i ∈ Finset.range (N+1), lam ^ (Nat.dist i j)
          = ∑ i ∈ Finset.range (N+1), lam ^ (Nat.dist j i) := by
            apply Finset.sum_congr rfl; intro i _; rw [Nat.dist_comm]
        _ ≤ 1 + 2*lam/(1-lam) := lam_dist_sum_range lam hl0 hl1 N j hjN
    have hmid : C2 ≤ (1 + 2*lam/(1-lam)) * (∑ j ∈ Finset.range (N+1), y j ^ ((5:ℝ)/3)) := by
      rw [hC2]
      calc (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1), lam ^ (Nat.dist i j) * y j ^ ((5:ℝ)/3))
          = ∑ j ∈ Finset.range (N+1), ∑ i ∈ Finset.range (N+1), lam ^ (Nat.dist i j) * y j ^ ((5:ℝ)/3) :=
            Finset.sum_comm
        _ ≤ ∑ j ∈ Finset.range (N+1), (1 + 2*lam/(1-lam)) * y j ^ ((5:ℝ)/3) := Finset.sum_le_sum hinner
        _ = (1 + 2*lam/(1-lam)) * ∑ j ∈ Finset.range (N+1), y j ^ ((5:ℝ)/3) := by rw [Finset.mul_sum]
    calc C2 ≤ (1 + 2*lam/(1-lam)) * (∑ j ∈ Finset.range (N+1), y j ^ ((5:ℝ)/3)) := hmid
      _ = (1 + 2*lam/(1-lam)) * 1 := by rw [hys]
  have hBnn : 0 ≤ B := by
    rw [hB]
    apply Finset.sum_nonneg; intro i hi
    apply Finset.sum_nonneg; intro j hj
    exact mul_nonneg (Real.rpow_nonneg (mul_nonneg (pow_nonneg hl0 _) (Real.rpow_nonneg (hx0 i) _)) _)
      (Real.rpow_nonneg (mul_nonneg (pow_nonneg hl0 _) (Real.rpow_nonneg (hy0 j) _)) _)
  have hRHS0 : (0:ℝ) ≤ 1 + 2*lam/(1-lam) := by
    have h2 : (0:ℝ) ≤ 2*lam/(1-lam) := div_nonneg (by linarith) (le_of_lt h1)
    linarith
  have hC2nn : 0 ≤ C2 := by
    rw [hC2]
    apply Finset.sum_nonneg; intro i hi
    apply Finset.sum_nonneg; intro j hj
    exact mul_nonneg (pow_nonneg hl0 _) (Real.rpow_nonneg (hy0 j) _)
  have hbound : B ≤ 1 + 2*lam/(1-lam) := by
    have hRHS : (0:ℝ) ≤ 1 + 2*lam/(1-lam) := hRHS0
    have hsq : B^2 ≤ (1 + 2*lam/(1-lam))^2 := by
      refine hcs.trans ?_
      calc C1 * C2 ≤ ((1 + 2*lam/(1-lam)) * 1) * ((1 + 2*lam/(1-lam)) * 1) :=
            mul_le_mul hC1u hC2u hC2nn (by simpa using hRHS0)
        _ = (1 + 2*lam/(1-lam))^2 := by ring
    have h3 := sq_le_sq.mp hsq
    rwa [abs_of_nonneg hBnn, abs_of_nonneg hRHS] at h3
  exact hAB.trans hbound


/-- Bernoulli-type inequality for the exponent `1/6` (concave case). -/
lemma rpow_bern_small {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t ^ ((1:ℝ)/6) ≤ 1 - (1/6:ℝ) * (1 - t) := by
  set s : ℝ := t ^ ((1:ℝ)/6) with hs
  have hs0 : 0 ≤ s := Real.rpow_nonneg h0 _
  have hs6 : s^6 = t := by
    rw [hs, ← Real.rpow_natCast (t^((1:ℝ)/6)) 6, ← Real.rpow_mul h0]
    norm_num
  rw [← hs6]
  have hid : (s-1)^2 * (s^4+2*s^3+3*s^2+4*s+5) = s^6 - 6*s + 5 := by ring
  have hnn : 0 ≤ (s^4+2*s^3+3*s^2+4*s+5) := by nlinarith [sq_nonneg s, mul_nonneg hs0 (sq_nonneg s)]
  have := mul_nonneg (sq_nonneg (s-1)) hnn
  rw [hid] at this
  linarith

/-- A family of nonnegative terms whose square sum is `≤ 1` is bounded by `1`. -/
lemma le_one_of_sq_le_one {z : ℝ} (hz : 0 ≤ z) (h : z^2 ≤ 1) : z ≤ 1 := by
  have h2 : z^2 ≤ (1:ℝ)^2 := by simpa using h
  have h3 := sq_le_sq.mp h2
  rwa [abs_of_nonneg hz, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1)] at h3

/-- Cauchy-Schwarz with square roots. -/
lemma cs_sqrt {s : Finset ℕ} {a b : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (∑ i ∈ s, a i^((1:ℝ)/2) * b i^((1:ℝ)/2))^2 ≤ (∑ i ∈ s, a i) * (∑ i ∈ s, b i) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => a i^((1:ℝ)/2)) (fun i => b i^((1:ℝ)/2))
  have e1 : (∑ i ∈ s, (a i^((1:ℝ)/2))^2) = ∑ i ∈ s, a i := by
    apply Finset.sum_congr rfl; intro i hi; exact sq_rpow_half (ha i)
  have e2 : (∑ i ∈ s, (b i^((1:ℝ)/2))^2) = ∑ i ∈ s, b i := by
    apply Finset.sum_congr rfl; intro i hi; exact sq_rpow_half (hb i)
  rwa [e1, e2] at h

/-- Part 1 of the decay lemma: lower bound for `c1`. -/
lemma decay_part1 (N : ℕ) (lam c1 : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hc1 : 0 < c1)
    (m : ℕ → ℕ → ℝ) (x y : ℕ → ℝ)
    (hm0 : ∀ i j, 0 ≤ m i j) (hx0 : ∀ i, 0 ≤ x i) (hy0 : ∀ j, 0 ≤ y j)
    (hx1 : ∀ i, x i ≤ 1) (hy1 : ∀ j, y j ≤ 1)
    (hmsum : ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1), m i j = 1)
    (hxs : ∑ i ∈ Finset.range (N+1), x i ^ ((5:ℝ)/3) = 1)
    (hys : ∑ j ∈ Finset.range (N+1), y j ^ ((5:ℝ)/3) = 1)
    (hb : ∀ i j, m i j ≤ c1 * ((if i = j then 1 else Real.exp 1 * lam ^ (Nat.dist i j)) * x i * y j)) :
    (1 - lam) / (1 - lam + 2 * Real.exp 1) ≤ c1 := by
  have hl0 : 0 ≤ lam := le_of_lt hlam0
  have h1 : (0:ℝ) < 1 - lam := by linarith
  have hdiag : ∑ i ∈ Finset.range (N+1), x i * y i ≤ 1 := by
    have h1' : ∀ i ∈ Finset.range (N+1),
        x i * y i ≤ (x i ^ ((5:ℝ)/3))^((1:ℝ)/2) * (y i ^ ((5:ℝ)/3))^((1:ℝ)/2) := by
      intro i hi
      have hxy : x i * y i ≤ 1 := by
        have := mul_le_mul (hx1 i) (hy1 i) (hy0 i) zero_le_one
        simpa using this
      exact xy_le_rpow (hx0 i) (hy0 i) hxy
    have h2 : (∑ i ∈ Finset.range (N+1),
        (x i ^ ((5:ℝ)/3))^((1:ℝ)/2) * (y i ^ ((5:ℝ)/3))^((1:ℝ)/2))^2 ≤ 1 := by
      have h := cs_sqrt (s := Finset.range (N+1)) (a := fun i => x i ^ ((5:ℝ)/3))
        (b := fun i => y i ^ ((5:ℝ)/3)) (fun i => Real.rpow_nonneg (hx0 i) _)
        (fun i => Real.rpow_nonneg (hy0 i) _)
      rw [hxs, hys, mul_one] at h
      exact h
    have hnonneg : 0 ≤ ∑ i ∈ Finset.range (N+1),
        (x i ^ ((5:ℝ)/3))^((1:ℝ)/2) * (y i ^ ((5:ℝ)/3))^((1:ℝ)/2) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (Real.rpow_nonneg (hx0 i) _) _)
        (Real.rpow_nonneg (Real.rpow_nonneg (hy0 i) _) _)
    calc ∑ i ∈ Finset.range (N+1), x i * y i
        ≤ ∑ i ∈ Finset.range (N+1),
            (x i ^ ((5:ℝ)/3))^((1:ℝ)/2) * (y i ^ ((5:ℝ)/3))^((1:ℝ)/2) := Finset.sum_le_sum h1'
      _ ≤ 1 := le_one_of_sq_le_one hnonneg h2
  have hoff : ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
      lam ^ (Nat.dist i j) * x i * y j ≤ 1 + 2 * lam / (1 - lam) :=
    lam_cs_bound N lam hl0 hlam1 x y hx0 hy0 hx1 hy1 hxs hys
  -- A := the linearised weight sum
  set A : ℝ := (∑ i ∈ Finset.range (N+1), x i * y i)
      + Real.exp 1 * (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
          lam ^ (Nat.dist i j) * x i * y j) with hA
  have hle : 1 ≤ c1 * A := by
    have hpoint : ∀ i ∈ Finset.range (N+1), ∀ j ∈ Finset.range (N+1),
        m i j ≤ c1 * ((if i = j then x i * y i else 0)
          + Real.exp 1 * (lam ^ (Nat.dist i j) * x i * y j)) := by
      intro i hi j hj
      have hij := hb i j
      by_cases h : i = j
      · subst h
        have heq : (if i = i then (1:ℝ) else Real.exp 1 * lam ^ (Nat.dist i i)) * x i * y i
            = x i * y i := by simp
        rw [heq] at hij
        have hxy : 0 ≤ x i * y i := mul_nonneg (hx0 i) (hy0 i)
        have hE : 0 ≤ Real.exp 1 * (lam ^ (Nat.dist i i) * x i * y i) :=
          mul_nonneg (le_of_lt (Real.exp_pos 1))
            (mul_nonneg (mul_nonneg (pow_nonneg hl0 _) (hx0 i)) (hy0 i))
        simp only [if_true]
        nlinarith [hij, hxy, hE]
      · have heq : (if i = j then (1:ℝ) else Real.exp 1 * lam ^ (Nat.dist i j)) * x i * y j
            = Real.exp 1 * (lam ^ (Nat.dist i j) * x i * y j) := by
          simp only [if_neg h]; ring
        rw [heq] at hij
        simp only [if_neg h]
        linarith [hij]
    have hsumle : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1), m i j)
        ≤ c1 * (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
            ((if i = j then x i * y i else 0)
              + Real.exp 1 * (lam ^ (Nat.dist i j) * x i * y j))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro j hj
      exact hpoint i hi j hj
    rw [hmsum] at hsumle
    have hinner : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
            ((if i = j then x i * y i else 0)
              + Real.exp 1 * (lam ^ (Nat.dist i j) * x i * y j))) = A := by
      rw [hA]
      simp only [Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl; intro i hi
        rw [Finset.sum_ite_eq, if_pos hi]
      · have hstep : ∀ i, (∑ j ∈ Finset.range (N+1), Real.exp 1 * (lam ^ (Nat.dist i j) * x i * y j))
            = Real.exp 1 * (∑ j ∈ Finset.range (N+1), lam ^ (Nat.dist i j) * x i * y j) := by
          intro i; rw [Finset.mul_sum]
        simp only [hstep]
        rw [← Finset.mul_sum]
    rw [hinner] at hsumle
    exact hsumle
  have hApos : 0 < A := by
    have h2 : 0 < c1 * A := lt_of_lt_of_le zero_lt_one hle
    exact pos_of_mul_pos_right h2 (le_of_lt hc1)
  have hc1ge : 1 / A ≤ c1 := by
    rw [div_le_iff₀ hApos]; exact hle
  -- A ≤ (1-lam+2e)/(1-lam)
  have hAub : A ≤ 1 + Real.exp 1 * (1 + 2 * lam / (1 - lam)) := by
    rw [hA]
    have := mul_le_mul_of_nonneg_left hoff (Real.exp_nonneg 1)
    linarith [hdiag, this]
  have hA' : A * (1 - lam) ≤ 1 - lam + 2 * Real.exp 1 := by
    have h2 : A * (1-lam) ≤ (1 + Real.exp 1 * (1 + 2 * lam / (1 - lam))) * (1-lam) :=
      mul_le_mul_of_nonneg_right hAub (le_of_lt h1)
    have h3 : (1 + Real.exp 1 * (1 + 2 * lam / (1 - lam))) * (1-lam)
        = (1 - lam) + Real.exp 1 * ((1 - lam) + 2 * lam) := by
      field_simp
    rw [h3] at h2
    have h4 : (1 - lam) + 2 * lam ≤ 2 := by linarith
    have h5 : Real.exp 1 * ((1 - lam) + 2 * lam) ≤ Real.exp 1 * 2 :=
      mul_le_mul_of_nonneg_left h4 (le_of_lt (Real.exp_pos 1))
    linarith [h2, h5]
  have hd1 : 0 < 1 - lam + 2*Real.exp 1 := by
    have := Real.exp_pos 1; linarith
  have hineq : (1 - lam) / (1 - lam + 2 * Real.exp 1) ≤ 1 / A := by
    have h1' : (1 - lam) ≤ (1 / A) * (1 - lam + 2 * Real.exp 1) := by
      have h2 : (1 / A) * (1 - lam + 2 * Real.exp 1) = (1 - lam + 2 * Real.exp 1) / A := by ring
      rw [h2, le_div_iff₀ hApos]
      nlinarith [hA']
    exact (div_le_iff₀ hd1).mpr h1'
  exact hineq.trans hc1ge


lemma pow56_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a*b)^((5:ℝ)/6) = (a^((5:ℝ)/3))^((1:ℝ)/2) * (b^((5:ℝ)/3))^((1:ℝ)/2) := by
  rw [show (5:ℝ)/6 = ((5:ℝ)/3)*((1:ℝ)/2) by norm_num]
  rw [Real.rpow_mul (mul_nonneg ha hb), Real.mul_rpow ha hb,
    Real.mul_rpow (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _)]

lemma eq_sixth_mul {z : ℝ} (h : 0 ≤ z) : z = z^((1:ℝ)/6) * z^((5:ℝ)/6) := by
  rw [← Real.rpow_add' h (by norm_num : ((1:ℝ)/6 + 5/6) ≠ 0)]
  norm_num

/-- The `lam`-distance sum restricted to indices at distance at least `2`. -/
lemma lam_dist_far_le (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam < 1) (N i : ℕ) :
    ∑ j ∈ (Finset.range (N+1)).filter (fun j => 2 ≤ Nat.dist i j), lam ^ (Nat.dist i j)
      ≤ 2 * lam^2 / (1-lam) := by
  have hla : (0:ℝ) < 1 - lam := by linarith
  have hbase : ∀ n : ℕ, ∑ a ∈ Finset.range n, lam ^ a ≤ 1/(1-lam) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp only [Finset.range_zero, Finset.sum_empty]
      exact div_nonneg zero_le_one (le_of_lt hla)
    · rw [geom_sum_eq (ne_of_lt hl1)]
      have heq : (lam^n - 1)/(lam-1) = (1 - lam^n)/(1-lam) := by
        rw [show (1:ℝ) - lam^n = -(lam^n - 1) by ring,
          show (1:ℝ) - lam = -(lam - 1) by ring, neg_div_neg_eq]
      rw [heq]
      apply div_le_div_of_nonneg_right _ (le_of_lt hla)
      have : (0:ℝ) ≤ lam^n := pow_nonneg hl0 n
      linarith
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Finset.range (N+1)).filter (fun j => 2 ≤ Nat.dist i j)) (fun j => j < i)
    (fun j => lam ^ (Nat.dist i j))
  have hLow : (∑ j ∈ ((Finset.range (N+1)).filter (fun j => 2 ≤ Nat.dist i j)).filter
        (fun j => j < i), lam ^ (Nat.dist i j)) ≤ lam^2/(1-lam) := by
    have hsub : ((Finset.range (N+1)).filter (fun j => 2 ≤ Nat.dist i j)).filter
        (fun j => j < i) ⊆ Finset.range (i-1) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      obtain ⟨⟨hjN, hjd⟩, hji⟩ := hj
      have hd : Nat.dist i j = i - j := Nat.dist_eq_sub_of_le_right (le_of_lt hji)
      rw [hd] at hjd
      omega
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => pow_nonneg hl0 _)).trans ?_
    have heq : ∑ j ∈ Finset.range (i-1), lam ^ (Nat.dist i j)
        = ∑ x ∈ Finset.range (i-1), lam ^ (x+2) := by
      rw [show (∑ j ∈ Finset.range (i-1), lam ^ (Nat.dist i j))
          = ∑ j ∈ Finset.range (i-1), lam ^ ((i-1-1-j)+2) from by
        apply Finset.sum_congr rfl; intro j hj
        have hjlt : j < i - 1 := Finset.mem_range.mp hj
        have hd : Nat.dist i j = i - j := Nat.dist_eq_sub_of_le_right (by omega)
        rw [hd]; congr 1; omega]
      rw [Finset.sum_range_reflect (fun x => lam ^ (x + 2)) (i-1)]
    rw [heq]
    calc ∑ x ∈ Finset.range (i-1), lam ^ (x+2)
        = lam^2 * ∑ x ∈ Finset.range (i-1), lam ^ x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro x hx; rw [pow_add]; ring
      _ ≤ lam^2 * (1/(1-lam)) := mul_le_mul_of_nonneg_left (hbase (i-1)) (sq_nonneg lam)
      _ = lam^2/(1-lam) := by ring
  have hHigh : (∑ j ∈ ((Finset.range (N+1)).filter (fun j => 2 ≤ Nat.dist i j)).filter
        (fun j => ¬ j < i), lam ^ (Nat.dist i j)) ≤ lam^2/(1-lam) := by
    have hsub : ((Finset.range (N+1)).filter (fun j => 2 ≤ Nat.dist i j)).filter
        (fun j => ¬ j < i) ⊆ (Finset.range (N - i - 1)).image (fun b => i + 2 + b) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      obtain ⟨⟨hjN, hjd⟩, hji⟩ := hj
      have hji' : i ≤ j := not_lt.mp hji
      have hd : Nat.dist i j = j - i := by
        rw [Nat.dist_comm]; exact Nat.dist_eq_sub_of_le_right hji'
      rw [hd] at hjd
      refine Finset.mem_image.mpr ⟨j - i - 2, ?_, ?_⟩
      · simp only [Finset.mem_range]; omega
      · show i + 2 + (j - i - 2) = j
        omega
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => pow_nonneg hl0 _)).trans ?_
    rw [Finset.sum_image (f := fun j => lam ^ (Nat.dist i j)) (g := fun b => i + 2 + b)
      (s := Finset.range (N - i - 1)) (by intro a _ b _ hab; exact Nat.add_left_cancel hab)]
    have heq : ∑ b ∈ Finset.range (N-i-1), lam ^ (Nat.dist i (i+2+b))
        = ∑ b ∈ Finset.range (N-i-1), lam ^ (b+2) := by
      apply Finset.sum_congr rfl; intro b hb
      have h1 : Nat.dist i (i+2+b) = (i+2+b) - i := by
        rw [Nat.dist_comm]; exact Nat.dist_eq_sub_of_le_right (by omega)
      rw [h1]; congr 1; omega
    rw [heq]
    calc ∑ b ∈ Finset.range (N-i-1), lam ^ (b+2)
        = lam^2 * ∑ b ∈ Finset.range (N-i-1), lam ^ b := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b hb; rw [pow_add]; ring
      _ ≤ lam^2 * (1/(1-lam)) := mul_le_mul_of_nonneg_left (hbase (N-i-1)) (sq_nonneg lam)
      _ = lam^2/(1-lam) := by ring
  calc (∑ j ∈ (Finset.range (N+1)).filter (fun j => 2 ≤ Nat.dist i j), lam ^ (Nat.dist i j))
      = (∑ j ∈ ((Finset.range (N+1)).filter (fun j => 2 ≤ Nat.dist i j)).filter
            (fun j => j < i), lam ^ (Nat.dist i j))
        + (∑ j ∈ ((Finset.range (N+1)).filter (fun j => 2 ≤ Nat.dist i j)).filter
            (fun j => ¬ j < i), lam ^ (Nat.dist i j)) := hsplit.symm
    _ ≤ lam^2/(1-lam) + lam^2/(1-lam) := add_le_add hLow hHigh
    _ = 2 * lam^2 / (1 - lam) := by ring


/-- Variant of `lam_dist_sum_ne` with the distance written in the other order. -/
lemma lam_dist_sum_ne' (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam < 1) (N i : ℕ) (hi : i ≤ N) :
    ∑ j ∈ (Finset.range (N+1)).filter (fun j => j ≠ i), lam ^ (Nat.dist j i)
      ≤ 2 * lam / (1 - lam) := by
  rw [show (∑ j ∈ (Finset.range (N+1)).filter (fun j => j ≠ i), lam ^ (Nat.dist j i))
      = ∑ j ∈ (Finset.range (N+1)).filter (fun j => j ≠ i), lam ^ (Nat.dist i j) from by
    apply Finset.sum_congr rfl; intro j hj; rw [Nat.dist_comm j i]]
  exact lam_dist_sum_ne lam hl0 hl1 N i hi

/-- Variant of `lam_dist_far_le` with the distance written in the other order. -/
lemma lam_dist_far_le' (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam < 1) (N i : ℕ) :
    ∑ j ∈ (Finset.range (N+1)).filter (fun j => 2 ≤ Nat.dist j i), lam ^ (Nat.dist j i)
      ≤ 2 * lam^2 / (1-lam) := by
  rw [show (∑ j ∈ (Finset.range (N+1)).filter (fun j => 2 ≤ Nat.dist j i), lam ^ (Nat.dist j i))
      = ∑ j ∈ (Finset.range (N+1)).filter (fun j => 2 ≤ Nat.dist i j), lam ^ (Nat.dist i j) from by
    apply Finset.sum_congr
    · ext j; simp only [Finset.mem_filter]; rw [Nat.dist_comm j i]
    · intro j hj; rw [Nat.dist_comm j i]]
  exact lam_dist_far_le lam hl0 hl1 N i

lemma part2_core (N : ℕ) (lam c1 : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 29/31)
    (hc1 : 0 < c1) (hc1le : c1 ≤ 1)
    (m : ℕ → ℕ → ℝ) (x y : ℕ → ℝ)
    (hm0 : ∀ i j, 0 ≤ m i j) (hx0 : ∀ i, 0 ≤ x i) (hy0 : ∀ j, 0 ≤ y j)
    (hx1 : ∀ i, x i ≤ 1) (hy1 : ∀ j, y j ≤ 1)
    (hmsum : ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1), m i j = 1)
    (hxs : ∑ i ∈ Finset.range (N+1), x i ^ ((5:ℝ)/3) = 1)
    (hys : ∑ j ∈ Finset.range (N+1), y j ^ ((5:ℝ)/3) = 1)
    (hb : ∀ i j, m i j ≤ c1 * ((if i = j then 1 else Real.exp 1 * lam ^ (Nat.dist i j)) * x i * y j)) :
    ∃ k ∈ Finset.range (N+1), (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
        (if 2 ≤ Nat.dist i k + Nat.dist j k then m i j else 0))
      ≤ 10^16 * (lam^(3:ℝ) + lam^((7:ℝ)/2)) := by
  have hl0 : 0 ≤ lam := le_of_lt hlam0
  have hlam1' : lam < 1 := by linarith
  obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image (Finset.range (N+1))
    (fun i => x i * y i) ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
  set g : ℝ := 1 - x k * y k with hg
  have hg0 : 0 ≤ g := by
    have : x k * y k ≤ 1 := by
      have := mul_le_mul (hx1 k) (hy1 k) (hy0 k) zero_le_one
      simpa using this
    rw [hg]; linarith
  have hxytop : x k * y k = 1 - g := by rw [hg]; ring
  -- `x i * y i ≤ 1 - g` for all `i`
  have hxy_le : ∀ i ∈ Finset.range (N+1), x i * y i ≤ 1 - g := by
    intro i hi
    have := hkmax i hi
    rw [hxytop] at this; exact this
  have hxky0 : (0:ℝ) ≤ x k * y k := mul_nonneg (hx0 k) (hy0 k)
  have h1mg0 : 0 ≤ 1 - g := by rw [hg]; linarith
  have h1mg1 : 1 - g ≤ 1 := by linarith
  -- tail bounds for x and y
  have hxk_ge : 1 - (5/3) * g ≤ x k ^ ((5:ℝ)/3) := by
    have hxk_ge : 1 - g ≤ x k := by
      have h2 : x k * y k ≤ x k := by
        calc x k * y k ≤ x k * 1 := mul_le_mul_of_nonneg_left (hy1 k) (hx0 k)
          _ = x k := mul_one _
      rw [hxytop] at h2; exact h2
    have h3 := rpow_bern h1mg0 h1mg1
    have h4 : (1-g) ^ ((5:ℝ)/3) ≤ x k ^ ((5:ℝ)/3) :=
      Real.rpow_le_rpow h1mg0 hxk_ge (by norm_num)
    linarith [h3, h4]
  have hyk_ge : 1 - (5/3) * g ≤ y k ^ ((5:ℝ)/3) := by
    have hyk_ge : 1 - g ≤ y k := by
      have h2 : x k * y k ≤ y k := by
        calc x k * y k ≤ 1 * y k := mul_le_mul_of_nonneg_right (hx1 k) (hy0 k)
          _ = y k := one_mul _
      rw [hxytop] at h2; exact h2
    have h3 := rpow_bern h1mg0 h1mg1
    have h4 : (1-g) ^ ((5:ℝ)/3) ≤ y k ^ ((5:ℝ)/3) :=
      Real.rpow_le_rpow h1mg0 hyk_ge (by norm_num)
    linarith [h3, h4]
  have hx_tail : ∑ i ∈ Finset.range (N+1), (if i = k then 0 else x i ^ ((5:ℝ)/3)) ≤ (5/3) * g := by
    have h2 : ∑ i ∈ Finset.range (N+1), x i ^ ((5:ℝ)/3) - x k ^ ((5:ℝ)/3)
        = ∑ i ∈ Finset.range (N+1), (if i = k then 0 else x i ^ ((5:ℝ)/3)) := by
      have h3 : ∀ i ∈ Finset.range (N+1),
          (if i = k then (0:ℝ) else x i ^ ((5:ℝ)/3)) = x i ^ ((5:ℝ)/3) - (if i = k then x k ^ ((5:ℝ)/3) else 0) := by
        intro i hi
        by_cases hik : i = k
        · subst hik; simp
        · simp [hik]
      rw [Finset.sum_congr rfl h3, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos hk]
    rw [← h2, hxs]
    linarith
  have hy_tail : ∑ j ∈ Finset.range (N+1), (if j = k then 0 else y j ^ ((5:ℝ)/3)) ≤ (5/3) * g := by
    have h2 : ∑ j ∈ Finset.range (N+1), y j ^ ((5:ℝ)/3) - y k ^ ((5:ℝ)/3)
        = ∑ j ∈ Finset.range (N+1), (if j = k then 0 else y j ^ ((5:ℝ)/3)) := by
      have h3 : ∀ j ∈ Finset.range (N+1),
          (if j = k then (0:ℝ) else y j ^ ((5:ℝ)/3)) = y j ^ ((5:ℝ)/3) - (if j = k then y k ^ ((5:ℝ)/3) else 0) := by
        intro j hj
        by_cases hjk : j = k
        · subst hjk; simp
        · simp [hjk]
      rw [Finset.sum_congr rfl h3, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos hk]
    rw [← h2, hys]
    linarith
  -- individual bounds away from k
  have hsu : (1:ℝ) ≤ 1 + 2 * lam / (1 - lam) := by
    have h2 : (0:ℝ) ≤ 2*lam/(1-lam) := div_nonneg (by linarith) (by linarith)
    linarith
  have hxb : ∀ i ∈ Finset.range (N+1), i ≠ k → x i ≤ ((5/3) * g) ^ ((3:ℝ)/5) := by
    intro i hi hik
    have hle : x i ^ ((5:ℝ)/3) ≤ (5/3) * g := by
      have : x i ^ ((5:ℝ)/3) ≤ ∑ j ∈ Finset.range (N+1), (if j = k then 0 else x j ^ ((5:ℝ)/3)) := by
        have := Finset.single_le_sum (f := fun j => if j = k then (0:ℝ) else x j ^ ((5:ℝ)/3))
          (fun j hj => by by_cases h : j = k <;> simp [h, Real.rpow_nonneg (hx0 j) _]) hi
        rwa [if_neg hik] at this
      linarith [this, hx_tail]
    calc x i = (x i ^ ((5:ℝ)/3)) ^ ((3:ℝ)/5) := by
          rw [← Real.rpow_mul (hx0 i)]; norm_num
      _ ≤ ((5/3) * g) ^ ((3:ℝ)/5) := Real.rpow_le_rpow (Real.rpow_nonneg (hx0 i) _) hle (by norm_num)
  have hyb : ∀ j ∈ Finset.range (N+1), j ≠ k → y j ≤ ((5/3) * g) ^ ((3:ℝ)/5) := by
    intro j hj hjk
    have hle : y j ^ ((5:ℝ)/3) ≤ (5/3) * g := by
      have : y j ^ ((5:ℝ)/3) ≤ ∑ i ∈ Finset.range (N+1), (if i = k then 0 else y i ^ ((5:ℝ)/3)) := by
        have := Finset.single_le_sum (f := fun i => if i = k then (0:ℝ) else y i ^ ((5:ℝ)/3))
          (fun i hi => by by_cases h : i = k <;> simp [h, Real.rpow_nonneg (hy0 i) _]) hj
        rwa [if_neg hjk] at this
      linarith [this, hy_tail]
    calc y j = (y j ^ ((5:ℝ)/3)) ^ ((3:ℝ)/5) := by
          rw [← Real.rpow_mul (hy0 j)]; norm_num
      _ ≤ ((5/3) * g) ^ ((3:ℝ)/5) := Real.rpow_le_rpow (Real.rpow_nonneg (hy0 j) _) hle (by norm_num)
  -- the diagonal sum
  have hdiagsum : (∑ i ∈ Finset.range (N+1), m i i) ≤ 1 - (1/6) * g := by
    have h1 : ∀ i, m i i ≤ x i * y i := by
      intro i
      have := hb i i
      have heq : (if i = i then (1:ℝ) else Real.exp 1 * lam ^ (Nat.dist i i)) * x i * y i = x i * y i := by simp
      rw [heq] at this
      nlinarith [this, hc1le, mul_nonneg (hx0 i) (hy0 i)]
    have h2 : (∑ i ∈ Finset.range (N+1), x i * y i) ≤ 1 - (1/6) * g := by
      have h3 : ∀ i ∈ Finset.range (N+1),
          x i * y i ≤ (1 - g) ^ ((1:ℝ)/6) * ((x i * y i) ^ ((5:ℝ)/6)) := by
        intro i hi
        have hxy0 : 0 ≤ x i * y i := mul_nonneg (hx0 i) (hy0 i)
        have hxy1 : x i * y i ≤ 1 - g := hxy_le i hi
        conv_lhs => rw [eq_sixth_mul hxy0]
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hxy0 _)
        exact Real.rpow_le_rpow hxy0 hxy1 (by norm_num)
      have h4 : (∑ i ∈ Finset.range (N+1), (x i * y i) ^ ((5:ℝ)/6)) ≤ 1 := by
        have h5 : (∑ i ∈ Finset.range (N+1),
            (x i ^ ((5:ℝ)/3))^((1:ℝ)/2) * (y i ^ ((5:ℝ)/3))^((1:ℝ)/2))^2 ≤ 1 := by
          have h := cs_sqrt (s := Finset.range (N+1)) (a := fun i => x i ^ ((5:ℝ)/3))
            (b := fun i => y i ^ ((5:ℝ)/3)) (fun i => Real.rpow_nonneg (hx0 i) _)
            (fun i => Real.rpow_nonneg (hy0 i) _)
          rw [hxs, hys, mul_one] at h
          exact h
        have hnn : 0 ≤ ∑ i ∈ Finset.range (N+1),
            (x i ^ ((5:ℝ)/3))^((1:ℝ)/2) * (y i ^ ((5:ℝ)/3))^((1:ℝ)/2) :=
          Finset.sum_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (Real.rpow_nonneg (hx0 i) _) _)
            (Real.rpow_nonneg (Real.rpow_nonneg (hy0 i) _) _)
        have h6 : ∑ i ∈ Finset.range (N+1), (x i * y i) ^ ((5:ℝ)/6)
            = ∑ i ∈ Finset.range (N+1),
              (x i ^ ((5:ℝ)/3))^((1:ℝ)/2) * (y i ^ ((5:ℝ)/3))^((1:ℝ)/2) :=
          Finset.sum_congr rfl fun i _ => pow56_eq (hx0 i) (hy0 i)
        rw [h6]
        exact le_one_of_sq_le_one hnn h5
      calc ∑ i ∈ Finset.range (N+1), x i * y i
          ≤ ∑ i ∈ Finset.range (N+1), (1 - g) ^ ((1:ℝ)/6) * (x i * y i) ^ ((5:ℝ)/6) :=
            Finset.sum_le_sum h3
        _ = (1 - g) ^ ((1:ℝ)/6) * ∑ i ∈ Finset.range (N+1), (x i * y i) ^ ((5:ℝ)/6) := by
            rw [Finset.mul_sum]
        _ ≤ (1 - g) ^ ((1:ℝ)/6) * 1 := mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg h1mg0 _)
        _ ≤ 1 - (1/6) * g := by
            have := rpow_bern_small h1mg0 h1mg1
            linarith
    calc (∑ i ∈ Finset.range (N+1), m i i) ≤ ∑ i ∈ Finset.range (N+1), x i * y i :=
          Finset.sum_le_sum (fun i _ => h1 i)
      _ ≤ 1 - (1/6) * g := h2
  -- abbreviations
  have h5g0 : (0:ℝ) ≤ (5/3) * g := by positivity
  have hla : 0 < 1 - lam := by linarith
  have hCg_def : 2 * lam / (1-lam) ≤ 31 * lam := by
    rw [div_le_iff₀ hla]
    nlinarith [hlam1]
  -- the `T1b` sum over pairs with both indices away from `k`
  set K1 : Finset (ℕ × ℕ) := (Finset.range (N+1) ×ˢ Finset.range (N+1)).filter
      (fun p : ℕ × ℕ => p.1 ≠ k ∧ p.2 ≠ k ∧ p.1 ≠ p.2) with hK1
  have hT1b : (∑ p ∈ K1, m p.1 p.2) ≤ 200 * lam * g ^ ((6:ℝ)/5) := by
    have hpt : ∀ p ∈ K1, m p.1 p.2 ≤ c1 * Real.exp 1 * ((5/3) * g) ^ ((1:ℝ)/5)
        * (lam ^ (Nat.dist p.1 p.2)
          * (((x p.1 ^ ((5:ℝ)/3))^((1:ℝ)/2)) * ((y p.2 ^ ((5:ℝ)/3))^((1:ℝ)/2)))) := by
      intro p hp
      rw [hK1, Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hi, hj⟩, hik, hjk, hij⟩ := hp
      have hb' := hb p.1 p.2
      rw [if_neg hij] at hb'
      have hxi : x p.1 ≤ ((5/3) * g) ^ ((3:ℝ)/5) := hxb p.1 hi hik
      have hyj : y p.2 ≤ ((5/3) * g) ^ ((3:ℝ)/5) := hyb p.2 hj hjk
      have hxy0 : 0 ≤ x p.1 * y p.2 := mul_nonneg (hx0 p.1) (hy0 p.2)
      have hxy : x p.1 * y p.2 ≤ ((5/3) * g) ^ ((6:ℝ)/5) := by
        calc x p.1 * y p.2 ≤ ((5/3) * g) ^ ((3:ℝ)/5) * ((5/3) * g) ^ ((3:ℝ)/5) :=
              mul_le_mul hxi hyj (hy0 p.2) (Real.rpow_nonneg h5g0 _)
          _ = ((5/3) * g) ^ ((6:ℝ)/5) := by
              rw [← Real.rpow_add' h5g0 (by norm_num : ((3:ℝ)/5 + 3/5) ≠ 0)]
              norm_num
      have hkey : x p.1 * y p.2 ≤ ((5/3) * g) ^ ((1:ℝ)/5)
          * (((x p.1 ^ ((5:ℝ)/3))^((1:ℝ)/2)) * ((y p.2 ^ ((5:ℝ)/3))^((1:ℝ)/2))) := by
        calc x p.1 * y p.2 = (x p.1 * y p.2) ^ ((1:ℝ)/6) * (x p.1 * y p.2) ^ ((5:ℝ)/6) :=
              eq_sixth_mul hxy0
          _ ≤ (((5/3) * g) ^ ((6:ℝ)/5)) ^ ((1:ℝ)/6) * (x p.1 * y p.2) ^ ((5:ℝ)/6) := by
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hxy0 _)
              exact Real.rpow_le_rpow hxy0 hxy (by norm_num)
          _ = ((5/3) * g) ^ ((1:ℝ)/5) * (x p.1 * y p.2) ^ ((5:ℝ)/6) := by
              rw [← Real.rpow_mul h5g0]
              norm_num
          _ = ((5/3) * g) ^ ((1:ℝ)/5)
              * (((x p.1 ^ ((5:ℝ)/3))^((1:ℝ)/2)) * ((y p.2 ^ ((5:ℝ)/3))^((1:ℝ)/2))) := by
              rw [pow56_eq (hx0 p.1) (hy0 p.2)]
      have hnn : (0:ℝ) ≤ c1 * Real.exp 1 * lam ^ (Nat.dist p.1 p.2) := by positivity
      calc m p.1 p.2 ≤ c1 * Real.exp 1 * lam ^ (Nat.dist p.1 p.2) * (x p.1 * y p.2) := by
            nlinarith [hb']
        _ ≤ c1 * Real.exp 1 * lam ^ (Nat.dist p.1 p.2)
              * (((5/3) * g) ^ ((1:ℝ)/5)
                * (((x p.1 ^ ((5:ℝ)/3))^((1:ℝ)/2)) * ((y p.2 ^ ((5:ℝ)/3))^((1:ℝ)/2)))) :=
              mul_le_mul_of_nonneg_left hkey hnn
        _ = c1 * Real.exp 1 * ((5/3) * g) ^ ((1:ℝ)/5)
              * (lam ^ (Nat.dist p.1 p.2)
                * (((x p.1 ^ ((5:ℝ)/3))^((1:ℝ)/2)) * ((y p.2 ^ ((5:ℝ)/3))^((1:ℝ)/2)))) := by ring
    have hsum : (∑ p ∈ K1, m p.1 p.2) ≤ c1 * Real.exp 1 * ((5/3) * g) ^ ((1:ℝ)/5)
        * (∑ p ∈ K1, lam ^ (Nat.dist p.1 p.2)
            * (((x p.1 ^ ((5:ℝ)/3))^((1:ℝ)/2)) * ((y p.2 ^ ((5:ℝ)/3))^((1:ℝ)/2)))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hpt
    have hcsb : (∑ p ∈ K1, lam ^ (Nat.dist p.1 p.2)
        * (((x p.1 ^ ((5:ℝ)/3))^((1:ℝ)/2)) * ((y p.2 ^ ((5:ℝ)/3))^((1:ℝ)/2))))
        ≤ (2*lam/(1-lam)) * ((5/3) * g) := by
      rw [hK1]
      have hAB : (∑ p ∈ (Finset.range (N+1) ×ˢ Finset.range (N+1)).filter
            (fun p : ℕ × ℕ => p.1 ≠ k ∧ p.2 ≠ k ∧ p.1 ≠ p.2),
            lam ^ (Nat.dist p.1 p.2)
            * (((x p.1 ^ ((5:ℝ)/3))^((1:ℝ)/2)) * ((y p.2 ^ ((5:ℝ)/3))^((1:ℝ)/2))))
          = ∑ p ∈ (Finset.range (N+1) ×ˢ Finset.range (N+1)).filter
            (fun p : ℕ × ℕ => p.1 ≠ k ∧ p.2 ≠ k),
            (if p.1 = p.2 then 0 else
              (lam ^ (Nat.dist p.1 p.2) * x p.1 ^ ((5:ℝ)/3))^((1:ℝ)/2)
              * (lam ^ (Nat.dist p.1 p.2) * y p.2 ^ ((5:ℝ)/3))^((1:ℝ)/2)) := by
        rw [Finset.sum_filter, Finset.sum_filter]
        apply Finset.sum_congr rfl; intro p hp
        by_cases hc : p.1 ≠ k ∧ p.2 ≠ k
        · by_cases hij : p.1 = p.2
          · simp [hc, hij]
          · rw [if_pos ⟨hc.1, hc.2, hij⟩, if_neg hij]
            have hpow : (0:ℝ) ≤ lam ^ (Nat.dist p.1 p.2) := pow_nonneg hl0 _
            rw [mul_rpow_half hpow (Real.rpow_nonneg (hx0 p.1) _),
              mul_rpow_half hpow (Real.rpow_nonneg (hy0 p.2) _)]
            have hsq2 : (lam ^ (Nat.dist p.1 p.2))^((1:ℝ)/2) * (lam ^ (Nat.dist p.1 p.2))^((1:ℝ)/2)
                = lam ^ (Nat.dist p.1 p.2) := by rw [← sq]; exact sq_rpow_half hpow
            rw [if_pos hc]
            rw [show (lam ^ (Nat.dist p.1 p.2))^((1:ℝ)/2) * (x p.1 ^ ((5:ℝ)/3))^((1:ℝ)/2)
                  * ((lam ^ (Nat.dist p.1 p.2))^((1:ℝ)/2) * (y p.2 ^ ((5:ℝ)/3))^((1:ℝ)/2))
                = ((lam ^ (Nat.dist p.1 p.2))^((1:ℝ)/2) * (lam ^ (Nat.dist p.1 p.2))^((1:ℝ)/2))
                  * (((x p.1 ^ ((5:ℝ)/3))^((1:ℝ)/2)) * ((y p.2 ^ ((5:ℝ)/3))^((1:ℝ)/2))) from by ring]
            rw [hsq2]
        · rw [if_neg (fun h => hc ⟨h.1, h.2.1⟩), if_neg hc] <;> rfl
      rw [hAB, Finset.sum_filter, Finset.sum_product]
      -- rewrite the paired indicator as a single indicator on `A*B`
      have hstep : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
            (if i ≠ k ∧ j ≠ k then
              (if i = j then 0 else
                (lam ^ (Nat.dist i j) * x i ^ ((5:ℝ)/3))^((1:ℝ)/2)
                * (lam ^ (Nat.dist i j) * y j ^ ((5:ℝ)/3))^((1:ℝ)/2)) else 0))
          = ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
              (if i ≠ k ∧ j ≠ k ∧ i ≠ j then
                (lam ^ (Nat.dist i j) * x i ^ ((5:ℝ)/3))^((1:ℝ)/2)
                * (lam ^ (Nat.dist i j) * y j ^ ((5:ℝ)/3))^((1:ℝ)/2) else 0) := by
        apply Finset.sum_congr rfl; intro i hi
        apply Finset.sum_congr rfl; intro j hj
        by_cases hc : i ≠ k ∧ j ≠ k
        · rw [if_pos hc]
          by_cases hij : i = j
          · rw [if_pos hij, if_neg (fun h => h.2.2 hij)]
          · rw [if_neg hij, if_pos ⟨hc.1, hc.2, hij⟩]
        · rw [if_neg hc, if_neg (fun h => hc ⟨h.1, h.2.1⟩)]
      rw [hstep]
      -- abbreviations
      set A : ℕ → ℕ → ℝ := fun i j => (lam ^ (Nat.dist i j) * x i ^ ((5:ℝ)/3))^((1:ℝ)/2) with hAdef
      set B : ℕ → ℕ → ℝ := fun i j => (lam ^ (Nat.dist i j) * y j ^ ((5:ℝ)/3))^((1:ℝ)/2) with hBdef
      -- bounds on the two squares
      have hsqA : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
            (if i ≠ k ∧ j ≠ k ∧ i ≠ j then A i j else 0)^2)
          ≤ (2*lam/(1-lam)) * ((5/3) * g) := by
        have h1 : ∀ i ∈ Finset.range (N+1),
            (∑ j ∈ Finset.range (N+1), (if i ≠ k ∧ j ≠ k ∧ i ≠ j then A i j else 0)^2)
            ≤ (if i = k then 0 else x i ^ ((5:ℝ)/3) * (2*lam/(1-lam))) := by
          intro i hi
          have hiN : i ≤ N := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi
          by_cases hik : i = k
          · subst hik
            rw [if_pos rfl]
            refine le_of_eq (Finset.sum_eq_zero fun j hj => ?_)
            rw [show (if i ≠ i ∧ j ≠ i ∧ i ≠ j then A i j else 0) = 0 by
              rw [if_neg (fun h => h.1 rfl)], sq, mul_zero]
          · rw [if_neg hik]
            have h21 : (∑ j ∈ Finset.range (N+1), (if i ≠ k ∧ j ≠ k ∧ i ≠ j then A i j else 0)^2)
                = ∑ j ∈ Finset.range (N+1),
                    (if i ≠ k ∧ j ≠ k ∧ i ≠ j then lam ^ (Nat.dist i j) * x i ^ ((5:ℝ)/3) else 0) := by
              apply Finset.sum_congr rfl; intro j hj
              by_cases hc : i ≠ k ∧ j ≠ k ∧ i ≠ j
              · rw [if_pos hc, if_pos hc, hAdef]
                simp only []
                exact sq_rpow_half (mul_nonneg (pow_nonneg hl0 _) (Real.rpow_nonneg (hx0 i) _))
              · rw [if_neg hc, if_neg hc, sq, mul_zero]
            rw [h21]
            have h22 : (∑ j ∈ Finset.range (N+1),
                    (if i ≠ k ∧ j ≠ k ∧ i ≠ j then lam ^ (Nat.dist i j) * x i ^ ((5:ℝ)/3) else 0))
                = x i ^ ((5:ℝ)/3) * (∑ j ∈ Finset.range (N+1),
                    (if i ≠ k ∧ j ≠ k ∧ i ≠ j then lam ^ (Nat.dist i j) else 0)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro j hj
              by_cases hc : i ≠ k ∧ j ≠ k ∧ i ≠ j
              · rw [if_pos hc, if_pos hc]; ring
              · rw [if_neg hc, if_neg hc]; ring
            rw [h22]
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (hx0 i) _)
            calc (∑ j ∈ Finset.range (N+1),
                    (if i ≠ k ∧ j ≠ k ∧ i ≠ j then lam ^ (Nat.dist i j) else 0))
                ≤ ∑ j ∈ Finset.range (N+1), (if j ≠ i then lam ^ (Nat.dist i j) else 0) := by
                  apply Finset.sum_le_sum; intro j hj
                  by_cases hc : i ≠ k ∧ j ≠ k ∧ i ≠ j
                  · rw [if_pos hc, if_pos (Ne.symm hc.2.2)]
                  · rw [if_neg hc]
                    by_cases hji : j ≠ i
                    · rw [if_pos hji]; exact pow_nonneg hl0 _
                    · rw [if_neg hji]
              _ = ∑ j ∈ (Finset.range (N+1)).filter (fun j => j ≠ i), lam ^ (Nat.dist i j) := by
                  rw [Finset.sum_filter]
              _ ≤ 2*lam/(1-lam) := lam_dist_sum_ne lam hl0 hlam1' N i hiN
        calc (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
              (if i ≠ k ∧ j ≠ k ∧ i ≠ j then A i j else 0)^2)
            ≤ ∑ i ∈ Finset.range (N+1), (if i = k then 0 else x i ^ ((5:ℝ)/3) * (2*lam/(1-lam))) :=
              Finset.sum_le_sum h1
          _ = (2*lam/(1-lam)) * (∑ i ∈ Finset.range (N+1), (if i = k then 0 else x i ^ ((5:ℝ)/3))) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro i hi
              by_cases hik : i = k
              · simp [hik]
              · simp only [hik, if_false]; ring
          _ ≤ (2*lam/(1-lam)) * ((5/3) * g) :=
              mul_le_mul_of_nonneg_left hx_tail (by positivity)
      have hsqB : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
            (if i ≠ k ∧ j ≠ k ∧ i ≠ j then B i j else 0)^2)
          ≤ (2*lam/(1-lam)) * ((5/3) * g) := by
        have h1 : ∀ j ∈ Finset.range (N+1),
            (∑ i ∈ Finset.range (N+1), (if i ≠ k ∧ j ≠ k ∧ i ≠ j then B i j else 0)^2)
            ≤ (if j = k then 0 else y j ^ ((5:ℝ)/3) * (2*lam/(1-lam))) := by
          intro j hj
          have hjN : j ≤ N := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj
          by_cases hjk : j = k
          · subst hjk
            rw [if_pos rfl]
            refine le_of_eq (Finset.sum_eq_zero fun i hi => ?_)
            rw [show (if i ≠ j ∧ j ≠ j ∧ i ≠ j then B i j else 0) = 0 by
              rw [if_neg (fun h => h.2.1 rfl)], sq, mul_zero]
          · rw [if_neg hjk]
            have h21 : (∑ i ∈ Finset.range (N+1), (if i ≠ k ∧ j ≠ k ∧ i ≠ j then B i j else 0)^2)
                = ∑ i ∈ Finset.range (N+1),
                    (if i ≠ k ∧ j ≠ k ∧ i ≠ j then lam ^ (Nat.dist i j) * y j ^ ((5:ℝ)/3) else 0) := by
              apply Finset.sum_congr rfl; intro i hi
              by_cases hc : i ≠ k ∧ j ≠ k ∧ i ≠ j
              · rw [if_pos hc, if_pos hc, hBdef]
                simp only []
                exact sq_rpow_half (mul_nonneg (pow_nonneg hl0 _) (Real.rpow_nonneg (hy0 j) _))
              · rw [if_neg hc, if_neg hc, sq, mul_zero]
            rw [h21]
            have h22 : (∑ i ∈ Finset.range (N+1),
                    (if i ≠ k ∧ j ≠ k ∧ i ≠ j then lam ^ (Nat.dist i j) * y j ^ ((5:ℝ)/3) else 0))
                = y j ^ ((5:ℝ)/3) * (∑ i ∈ Finset.range (N+1),
                    (if i ≠ k ∧ j ≠ k ∧ i ≠ j then lam ^ (Nat.dist i j) else 0)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro i hi
              by_cases hc : i ≠ k ∧ j ≠ k ∧ i ≠ j
              · rw [if_pos hc, if_pos hc]; ring
              · rw [if_neg hc, if_neg hc]; ring
            rw [h22]
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (hy0 j) _)
            calc (∑ i ∈ Finset.range (N+1),
                    (if i ≠ k ∧ j ≠ k ∧ i ≠ j then lam ^ (Nat.dist i j) else 0))
                ≤ ∑ i ∈ Finset.range (N+1), (if i ≠ j then lam ^ (Nat.dist i j) else 0) := by
                  apply Finset.sum_le_sum; intro i hi
                  by_cases hc : i ≠ k ∧ j ≠ k ∧ i ≠ j
                  · rw [if_pos hc, if_pos hc.2.2]
                  · rw [if_neg hc]
                    by_cases hij : i ≠ j
                    · rw [if_pos hij]; exact pow_nonneg hl0 _
                    · rw [if_neg hij]
              _ = ∑ i ∈ (Finset.range (N+1)).filter (fun i => i ≠ j), lam ^ (Nat.dist i j) := by
                  rw [Finset.sum_filter]
              _ ≤ 2*lam/(1-lam) := by
                  calc ∑ i ∈ (Finset.range (N+1)).filter (fun i => i ≠ j), lam ^ (Nat.dist i j)
                      = ∑ i ∈ (Finset.range (N+1)).filter (fun i => i ≠ j), lam ^ (Nat.dist j i) := by
                        apply Finset.sum_congr rfl; intro i _; rw [Nat.dist_comm]
                    _ ≤ 2*lam/(1-lam) := lam_dist_sum_ne lam hl0 hlam1' N j hjN
        calc (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
              (if i ≠ k ∧ j ≠ k ∧ i ≠ j then B i j else 0)^2)
            = ∑ j ∈ Finset.range (N+1), ∑ i ∈ Finset.range (N+1),
              (if i ≠ k ∧ j ≠ k ∧ i ≠ j then B i j else 0)^2 := Finset.sum_comm
          _ ≤ ∑ j ∈ Finset.range (N+1), (if j = k then 0 else y j ^ ((5:ℝ)/3) * (2*lam/(1-lam))) :=
              Finset.sum_le_sum h1
          _ = (2*lam/(1-lam)) * (∑ j ∈ Finset.range (N+1), (if j = k then 0 else y j ^ ((5:ℝ)/3))) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro j hj
              by_cases hjk : j = k
              · simp [hjk]
              · simp only [hjk, if_false]; ring
          _ ≤ (2*lam/(1-lam)) * ((5/3) * g) :=
              mul_le_mul_of_nonneg_left hy_tail (by positivity)
      -- Cauchy-Schwarz
      have hcs := cs_prod (Finset.range (N+1)) (Finset.range (N+1))
        (fun i j => if i ≠ k ∧ j ≠ k ∧ i ≠ j then A i j else 0)
        (fun i j => if i ≠ k ∧ j ≠ k ∧ i ≠ j then B i j else 0)
      have hprod : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
            (if i ≠ k ∧ j ≠ k ∧ i ≠ j then A i j else 0)
            * (if i ≠ k ∧ j ≠ k ∧ i ≠ j then B i j else 0))
          = ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
              (if i ≠ k ∧ j ≠ k ∧ i ≠ j then A i j * B i j else 0) := by
        apply Finset.sum_congr rfl; intro i hi
        apply Finset.sum_congr rfl; intro j hj
        by_cases hc : i ≠ k ∧ j ≠ k ∧ i ≠ j
        · rw [if_pos hc, if_pos hc, if_pos hc]
        · rw [if_neg hc, if_neg hc, if_neg hc]; ring
      rw [hprod] at hcs
      have hSnn : 0 ≤ ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
          (if i ≠ k ∧ j ≠ k ∧ i ≠ j then A i j * B i j else 0) :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
          by_cases hc : i ≠ k ∧ j ≠ k ∧ i ≠ j
          · rw [if_pos hc]
            exact mul_nonneg (Real.rpow_nonneg (mul_nonneg (pow_nonneg hl0 _) (Real.rpow_nonneg (hx0 i) _)) _)
              (Real.rpow_nonneg (mul_nonneg (pow_nonneg hl0 _) (Real.rpow_nonneg (hy0 j) _)) _)
          · rw [if_neg hc]
      have hle : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
          (if i ≠ k ∧ j ≠ k ∧ i ≠ j then A i j * B i j else 0)) ≤ (2*lam/(1-lam)) * ((5/3) * g) := by
        have hCgnn : 0 ≤ (2*lam/(1-lam)) * ((5/3) * g) := mul_nonneg (by positivity) (by positivity)
        have hsq : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
              (if i ≠ k ∧ j ≠ k ∧ i ≠ j then A i j * B i j else 0))^2
            ≤ ((2*lam/(1-lam)) * ((5/3) * g))^2 := by
          have h2 : ((2*lam/(1-lam)) * ((5/3) * g))^2
              = ((2*lam/(1-lam)) * ((5/3) * g)) * ((2*lam/(1-lam)) * ((5/3) * g)) := sq _
          rw [h2]
          exact hcs.trans ((mul_le_mul hsqA hsqB (by positivity) (by positivity)).trans (le_of_eq (by ring)))
        have h3 := sq_le_sq.mp hsq
        rwa [abs_of_nonneg hSnn, abs_of_nonneg hCgnn] at h3
      have hAeq : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
          (if i ≠ k ∧ j ≠ k ∧ i ≠ j then A i j * B i j else 0))
          = ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
              (if i ≠ k ∧ j ≠ k ∧ i ≠ j then
                (lam ^ (Nat.dist i j) * x i ^ ((5:ℝ)/3))^((1:ℝ)/2)
                * (lam ^ (Nat.dist i j) * y j ^ ((5:ℝ)/3))^((1:ℝ)/2) else 0) := rfl
      rw [hAeq] at hle
      exact hle
    have hT1bb : (∑ p ∈ K1, m p.1 p.2) ≤ 200 * lam * g ^ ((6:ℝ)/5) := by
      have hc1e : c1 * Real.exp 1 ≤ 3 := by
        have h2 : Real.exp 1 ≤ 3 := by
          have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
        nlinarith [hc1le, h2]
      have h53b : ((5/3):ℝ) ^ ((6:ℝ)/5) ≤ 2 := by
        have h1 : ((5/3):ℝ) ^ ((6:ℝ)/5) = (((5/3):ℝ)^6) ^ ((1:ℝ)/5) := by
          rw [show ((6:ℝ)/5) = (6:ℝ) * ((1:ℝ)/5) by norm_num]
          rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 5/3)]
          rw [show ((5/3):ℝ)^((6:ℝ)) = ((5/3):ℝ)^6 from Real.rpow_natCast (5/3) 6]
        rw [h1]
        calc (((5/3):ℝ)^6) ^ ((1:ℝ)/5) ≤ (32:ℝ) ^ ((1:ℝ)/5) :=
              Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)
          _ = 2 := by
              rw [show (32:ℝ) = (2:ℝ)^5 by norm_num]
              rw [show ((2:ℝ)^5) = (2:ℝ)^((5:ℝ)) from (Real.rpow_natCast 2 5).symm]
              rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
              rw [show (5:ℝ) * ((1:ℝ)/5) = (1:ℝ) by norm_num]
              exact Real.rpow_one 2
      have hfac : ((5/3) * g) ^ ((1:ℝ)/5) * ((5/3) * g) = ((5/3) * g) ^ ((6:ℝ)/5) := by
        calc ((5/3) * g) ^ ((1:ℝ)/5) * ((5/3) * g)
            = ((5/3) * g) ^ ((1:ℝ)/5) * ((5/3) * g) ^ (1:ℝ) := by rw [Real.rpow_one]
          _ = ((5/3) * g) ^ ((1:ℝ)/5 + 1) :=
              (Real.rpow_add' h5g0 (by norm_num : ((1:ℝ)/5 + 1) ≠ 0)).symm
          _ = ((5/3) * g) ^ ((6:ℝ)/5) := by norm_num
      refine hsum.trans ?_
      calc c1 * Real.exp 1 * ((5/3) * g) ^ ((1:ℝ)/5)
            * (∑ p ∈ K1, lam ^ (Nat.dist p.1 p.2)
              * (((x p.1 ^ ((5:ℝ)/3))^((1:ℝ)/2)) * ((y p.2 ^ ((5:ℝ)/3))^((1:ℝ)/2))))
          ≤ c1 * Real.exp 1 * ((5/3) * g) ^ ((1:ℝ)/5) * ((2*lam/(1-lam)) * ((5/3) * g)) :=
            mul_le_mul_of_nonneg_left hcsb (by positivity)
        _ ≤ 3 * ((5/3) * g) ^ ((1:ℝ)/5) * ((31*lam) * ((5/3) * g)) := by
            have hA : (0:ℝ) ≤ ((5/3) * g) ^ ((1:ℝ)/5) := Real.rpow_nonneg h5g0 _
            have hB : (0:ℝ) ≤ (2*lam/(1-lam)) * ((5/3) * g) :=
              mul_nonneg (div_nonneg (by linarith [hlam0]) (le_of_lt hla)) h5g0
            have e1 : c1 * Real.exp 1 * ((5/3) * g) ^ ((1:ℝ)/5)
                ≤ 3 * ((5/3) * g) ^ ((1:ℝ)/5) := mul_le_mul_of_nonneg_right hc1e hA
            have e2 : (2*lam/(1-lam)) * ((5/3) * g) ≤ (31*lam) * ((5/3) * g) :=
              mul_le_mul_of_nonneg_right hCg_def h5g0
            exact (mul_le_mul_of_nonneg_right e1 hB).trans
              (mul_le_mul_of_nonneg_left e2 (by positivity))
        _ = 93 * lam * (((5/3) * g) ^ ((1:ℝ)/5) * ((5/3) * g)) := by ring
        _ = 93 * lam * ((5/3) * g) ^ ((6:ℝ)/5) := by rw [hfac]
        _ = 93 * lam * (((5/3):ℝ) ^ ((6:ℝ)/5) * g ^ ((6:ℝ)/5)) := by
            rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 5/3) hg0]
        _ ≤ 93 * lam * (2 * g ^ ((6:ℝ)/5)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right h53b (Real.rpow_nonneg hg0 _)
        _ = 186 * lam * g ^ ((6:ℝ)/5) := by ring
        _ ≤ 200 * lam * g ^ ((6:ℝ)/5) := by
            have hg0' : (0:ℝ) ≤ g ^ ((6:ℝ)/5) := Real.rpow_nonneg hg0 _
            nlinarith [hlam0, hg0']
    exact hT1bb
  -- ================= constants and auxiliaries =================
  have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have h53c : ((5/3):ℝ) ^ ((3:ℝ)/5) ≤ 2 := by
    have h1 : ((5/3):ℝ) ^ ((3:ℝ)/5) = (((5/3):ℝ)^3) ^ ((1:ℝ)/5) := by
      rw [show ((3:ℝ)/5) = (3:ℝ) * ((1:ℝ)/5) by norm_num]
      rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 5/3)]
      rw [show ((5/3):ℝ)^((3:ℝ)) = ((5/3):ℝ)^3 from Real.rpow_natCast (5/3) 3]
    rw [h1]
    calc (((5/3):ℝ)^3) ^ ((1:ℝ)/5) ≤ (32:ℝ) ^ ((1:ℝ)/5) :=
          Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)
      _ = 2 := by
          rw [show (32:ℝ) = (2:ℝ)^5 by norm_num]
          rw [show ((2:ℝ)^5) = (2:ℝ)^((5:ℝ)) from (Real.rpow_natCast 2 5).symm]
          rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
          rw [show (5:ℝ) * ((1:ℝ)/5) = (1:ℝ) by norm_num]
          exact Real.rpow_one 2
  have h53d : ((5/3):ℝ) ^ ((6:ℝ)/5) ≤ 2 := by
    have h1 : ((5/3):ℝ) ^ ((6:ℝ)/5) = (((5/3):ℝ)^6) ^ ((1:ℝ)/5) := by
      rw [show ((6:ℝ)/5) = (6:ℝ) * ((1:ℝ)/5) by norm_num]
      rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 5/3)]
      rw [show ((5/3):ℝ)^((6:ℝ)) = ((5/3):ℝ)^6 from Real.rpow_natCast (5/3) 6]
    rw [h1]
    calc (((5/3):ℝ)^6) ^ ((1:ℝ)/5) ≤ (32:ℝ) ^ ((1:ℝ)/5) :=
          Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)
      _ = 2 := by
          rw [show (32:ℝ) = (2:ℝ)^5 by norm_num]
          rw [show ((2:ℝ)^5) = (2:ℝ)^((5:ℝ)) from (Real.rpow_natCast 2 5).symm]
          rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
          rw [show (5:ℝ) * ((1:ℝ)/5) = (1:ℝ) by norm_num]
          exact Real.rpow_one 2
  have h2lam : 2 / (1 - lam) ≤ 31 := by
    rw [div_le_iff₀ hla]; nlinarith [hlam1]
  have hcoef : Real.exp 1 * ((5/3):ℝ)^((3:ℝ)/5) * (2/(1-lam)) ≤ 186 := by
    have he : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    have hp0 : 0 ≤ ((5/3):ℝ)^((3:ℝ)/5) := Real.rpow_nonneg (by norm_num) _
    have hq0 : 0 ≤ 2/(1-lam) := div_nonneg (by norm_num) (le_of_lt hla)
    calc Real.exp 1 * ((5/3):ℝ)^((3:ℝ)/5) * (2/(1-lam))
        ≤ 3 * ((5/3):ℝ)^((3:ℝ)/5) * (2/(1-lam)) := by
          apply mul_le_mul_of_nonneg_right _ hq0
          exact mul_le_mul_of_nonneg_right he hp0
      _ ≤ 3 * 2 * (2/(1-lam)) := by
          apply mul_le_mul_of_nonneg_right _ hq0
          exact mul_le_mul_of_nonneg_left h53c (by norm_num)
      _ ≤ 3 * 2 * 31 := mul_le_mul_of_nonneg_left h2lam (by norm_num)
      _ = 186 := by norm_num
  have hcoef2 : Real.exp 1 * ((5/3):ℝ)^((3:ℝ)/5) * (2*lam^2/(1-lam)) ≤ 200 * lam^2 := by
    have h0 : 0 ≤ lam^2 := sq_nonneg lam
    calc Real.exp 1 * ((5/3):ℝ)^((3:ℝ)/5) * (2*lam^2/(1-lam))
        = (Real.exp 1 * ((5/3):ℝ)^((3:ℝ)/5) * (2/(1-lam))) * lam^2 := by ring
      _ ≤ 186 * lam^2 := mul_le_mul_of_nonneg_right hcoef h0
      _ ≤ 200 * lam^2 := by nlinarith [h0]
  have hgle1 : g ≤ 1 := by linarith [hxky0]
  have hg6le : g ^ ((6:ℝ)/5) ≤ g ^ ((3:ℝ)/5) := by
    have hfac : g ^ ((6:ℝ)/5) = g ^ ((3:ℝ)/5) * g ^ ((3:ℝ)/5) := by
      rw [← Real.rpow_add' hg0 (by norm_num : ((3:ℝ)/5 + 3/5) ≠ 0)]
      norm_num
    rw [hfac]
    calc g ^ ((3:ℝ)/5) * g ^ ((3:ℝ)/5) ≤ g ^ ((3:ℝ)/5) * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one hg0 hgle1 (by norm_num))
            (Real.rpow_nonneg hg0 _)
      _ = g ^ ((3:ℝ)/5) := by ring
  have hxyta : ∀ i ∈ Finset.range (N+1), i ≠ k → x i * y i ≤ ((5/3) * g) ^ ((6:ℝ)/5) := by
    intro i hi hik
    have hxi : x i ≤ ((5/3) * g) ^ ((3:ℝ)/5) := hxb i hi hik
    have hyi : y i ≤ ((5/3) * g) ^ ((3:ℝ)/5) := hyb i hi hik
    calc x i * y i ≤ ((5/3) * g) ^ ((3:ℝ)/5) * ((5/3) * g) ^ ((3:ℝ)/5) :=
          mul_le_mul hxi hyi (hy0 i) (Real.rpow_nonneg h5g0 _)
      _ = ((5/3) * g) ^ ((6:ℝ)/5) := by
          rw [← Real.rpow_add' h5g0 (by norm_num : ((3:ℝ)/5 + 3/5) ≠ 0)]
          norm_num
  have hfac2 : ((5/3) * g) ^ ((1:ℝ)/5) * ((5/3) * g) = ((5/3) * g) ^ ((6:ℝ)/5) := by
    calc ((5/3) * g) ^ ((1:ℝ)/5) * ((5/3) * g)
        = ((5/3) * g) ^ ((1:ℝ)/5) * ((5/3) * g) ^ (1:ℝ) := by rw [Real.rpow_one]
      _ = ((5/3) * g) ^ ((1:ℝ)/5 + 1) :=
          (Real.rpow_add' h5g0 (by norm_num : ((1:ℝ)/5 + 1) ≠ 0)).symm
      _ = ((5/3) * g) ^ ((6:ℝ)/5) := by norm_num
  -- ================= geometric bounds =================
  have hgeom : ∀ n : ℕ, ∑ a ∈ Finset.range n, lam ^ a ≤ 1/(1-lam) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp only [Finset.range_zero, Finset.sum_empty]
      exact div_nonneg zero_le_one (le_of_lt hla)
    · rw [geom_sum_eq (ne_of_lt hlam1')]
      have heq : (lam^n - 1)/(lam-1) = (1 - lam^n)/(1-lam) := by
        rw [show (1:ℝ) - lam^n = -(lam^n - 1) by ring,
          show (1:ℝ) - lam = -(lam - 1) by ring, neg_div_neg_eq]
      rw [heq]
      apply div_le_div_of_nonneg_right _ (le_of_lt hla)
      have : (0:ℝ) ≤ lam^n := pow_nonneg hl0 n
      linarith
  -- ================= T1a : sum over i != k of m i i =================
  have hmii : ∀ i, m i i ≤ x i * y i := by
    intro i
    have hb' := hb i i
    have heq : (if i = i then (1:ℝ) else Real.exp 1 * lam ^ (Nat.dist i i)) * x i * y i
        = x i * y i := by simp
    rw [heq] at hb'
    nlinarith [hb', hc1le, mul_nonneg (hx0 i) (hy0 i)]
  have hT1a : (∑ i ∈ Finset.range (N+1), (if i ≠ k then m i i else 0))
      ≤ 2 * g ^ ((6:ℝ)/5) := by
    have step1 : (∑ i ∈ Finset.range (N+1), (if i ≠ k then m i i else 0))
        ≤ ∑ i ∈ Finset.range (N+1), (if i = k then 0 else x i * y i) := by
      apply Finset.sum_le_sum; intro i hi
      by_cases hik : i = k
      · rw [if_neg (fun h => h hik), if_pos hik]
      · rw [if_pos hik, if_neg hik]; exact hmii i
    have step2 : (∑ i ∈ Finset.range (N+1), (if i = k then 0 else x i * y i))
        ≤ ((5/3) * g) ^ ((1:ℝ)/5)
          * (∑ i ∈ Finset.range (N+1), (if i = k then 0 else (x i * y i) ^ ((5:ℝ)/6))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro i hi
      by_cases hik : i = k
      · rw [if_pos hik, if_pos hik]; simp
      · rw [if_neg hik, if_neg hik]
        have hxy0 : 0 ≤ x i * y i := mul_nonneg (hx0 i) (hy0 i)
        have hxy2 : x i * y i ≤ ((5/3) * g) ^ ((6:ℝ)/5) := hxyta i hi hik
        calc x i * y i = (x i * y i) ^ ((1:ℝ)/6) * (x i * y i) ^ ((5:ℝ)/6) := eq_sixth_mul hxy0
          _ ≤ (((5/3) * g) ^ ((6:ℝ)/5)) ^ ((1:ℝ)/6) * (x i * y i) ^ ((5:ℝ)/6) := by
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hxy0 _)
              exact Real.rpow_le_rpow hxy0 hxy2 (by norm_num)
          _ = ((5/3) * g) ^ ((1:ℝ)/5) * (x i * y i) ^ ((5:ℝ)/6) := by
              rw [← Real.rpow_mul h5g0]; norm_num
    have step3 : (∑ i ∈ Finset.range (N+1), (if i = k then 0 else (x i * y i) ^ ((5:ℝ)/6)))
        ≤ (5/3) * g := by
      have hfil : (∑ i ∈ Finset.range (N+1), (if i = k then 0 else (x i * y i) ^ ((5:ℝ)/6)))
          = ∑ i ∈ (Finset.range (N+1)).filter (fun i => i ≠ k), (x i * y i) ^ ((5:ℝ)/6) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl; intro i hi
        by_cases hik : i = k <;> simp [hik]
      rw [hfil]
      have hfil' : (∑ i ∈ (Finset.range (N+1)).filter (fun i => i ≠ k), (x i * y i) ^ ((5:ℝ)/6))
          = ∑ i ∈ (Finset.range (N+1)).filter (fun i => i ≠ k),
              (x i ^ ((5:ℝ)/3))^((1:ℝ)/2) * (y i ^ ((5:ℝ)/3))^((1:ℝ)/2) := by
        apply Finset.sum_congr rfl; intro i hi; exact pow56_eq (hx0 i) (hy0 i)
      rw [hfil']
      have hxT : (∑ i ∈ (Finset.range (N+1)).filter (fun i => i ≠ k), x i ^ ((5:ℝ)/3))
          ≤ (5/3) * g := by
        rw [Finset.sum_filter]
        have : (∑ i ∈ Finset.range (N+1), (if i ≠ k then x i ^ ((5:ℝ)/3) else 0))
            = ∑ i ∈ Finset.range (N+1), (if i = k then 0 else x i ^ ((5:ℝ)/3)) := by
          apply Finset.sum_congr rfl; intro i hi
          by_cases hik : i = k <;> simp [hik]
        rw [this]; exact hx_tail
      have hyT : (∑ i ∈ (Finset.range (N+1)).filter (fun i => i ≠ k), y i ^ ((5:ℝ)/3))
          ≤ (5/3) * g := by
        rw [Finset.sum_filter]
        have : (∑ i ∈ Finset.range (N+1), (if i ≠ k then y i ^ ((5:ℝ)/3) else 0))
            = ∑ i ∈ Finset.range (N+1), (if i = k then 0 else y i ^ ((5:ℝ)/3)) := by
          apply Finset.sum_congr rfl; intro i hi
          by_cases hik : i = k <;> simp [hik]
        rw [this]; exact hy_tail
      have hcs := cs_sqrt (s := (Finset.range (N+1)).filter (fun i => i ≠ k))
        (a := fun i => x i ^ ((5:ℝ)/3)) (b := fun i => y i ^ ((5:ℝ)/3))
        (fun i => Real.rpow_nonneg (hx0 i) _) (fun i => Real.rpow_nonneg (hy0 i) _)
      have hY0 : (0:ℝ) ≤ (5/3) * g := h5g0
      have hz0 : 0 ≤ ∑ i ∈ (Finset.range (N+1)).filter (fun i => i ≠ k),
          (x i ^ ((5:ℝ)/3))^((1:ℝ)/2) * (y i ^ ((5:ℝ)/3))^((1:ℝ)/2) :=
        Finset.sum_nonneg fun i _ => mul_nonneg
          (Real.rpow_nonneg (Real.rpow_nonneg (hx0 i) _) _)
          (Real.rpow_nonneg (Real.rpow_nonneg (hy0 i) _) _)
      have hsq : ((∑ i ∈ (Finset.range (N+1)).filter (fun i => i ≠ k),
          (x i ^ ((5:ℝ)/3))^((1:ℝ)/2) * (y i ^ ((5:ℝ)/3))^((1:ℝ)/2)))^2
          ≤ ((5/3) * g)^2 := by
        refine hcs.trans ?_
        calc (∑ i ∈ (Finset.range (N+1)).filter (fun i => i ≠ k), x i ^ ((5:ℝ)/3))
              * (∑ i ∈ (Finset.range (N+1)).filter (fun i => i ≠ k), y i ^ ((5:ℝ)/3))
            ≤ ((5/3) * g) * ((5/3) * g) :=
              mul_le_mul hxT hyT (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hy0 i) _) hY0
          _ = ((5/3) * g)^2 := (sq _).symm
      have hfin := sq_le_sq.mp hsq
      rwa [abs_of_nonneg hz0, abs_of_nonneg hY0] at hfin
    calc (∑ i ∈ Finset.range (N+1), (if i ≠ k then m i i else 0))
        ≤ ((5/3) * g) ^ ((1:ℝ)/5) * ((5/3) * g) :=
          step1.trans (step2.trans (mul_le_mul_of_nonneg_left step3 (Real.rpow_nonneg h5g0 _)))
      _ = ((5/3):ℝ) ^ ((6:ℝ)/5) * g ^ ((6:ℝ)/5) := by
          rw [hfac2, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 5/3) hg0]
      _ ≤ 2 * g ^ ((6:ℝ)/5) := mul_le_mul_of_nonneg_right h53d (Real.rpow_nonneg hg0 _)
  -- ================= term bounds for the "k-row" sums =================
  have hbk : ∀ j ∈ Finset.range (N+1), j ≠ k →
      m k j ≤ Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5) * lam ^ (Nat.dist j k) := by
    intro j hj hjk
    have hb' := hb k j
    rw [if_neg (Ne.symm hjk)] at hb'
    rw [Nat.dist_comm k j] at hb'
    have hyj : y j ≤ ((5/3)*g) ^ ((3:ℝ)/5) := hyb j hj hjk
    have hE0 : 0 ≤ Real.exp 1 * lam ^ (Nat.dist j k) := by positivity
    have h2' : c1 * (Real.exp 1 * lam ^ (Nat.dist j k) * x k * y j)
        ≤ Real.exp 1 * lam ^ (Nat.dist j k) * x k * y j := by
      apply mul_le_of_le_one_left _ hc1le
      exact mul_nonneg (mul_nonneg hE0 (hx0 k)) (hy0 j)
    have h3' : Real.exp 1 * lam ^ (Nat.dist j k) * x k * y j
        ≤ Real.exp 1 * lam ^ (Nat.dist j k) * y j := by
      have h4' : 0 ≤ Real.exp 1 * lam ^ (Nat.dist j k) * y j := mul_nonneg hE0 (hy0 j)
      calc Real.exp 1 * lam ^ (Nat.dist j k) * x k * y j
          = (Real.exp 1 * lam ^ (Nat.dist j k) * y j) * x k := by ring
        _ ≤ (Real.exp 1 * lam ^ (Nat.dist j k) * y j) * 1 :=
            mul_le_mul_of_nonneg_left (hx1 k) h4'
        _ = Real.exp 1 * lam ^ (Nat.dist j k) * y j := by ring
    have h5' : Real.exp 1 * lam ^ (Nat.dist j k) * y j
        ≤ Real.exp 1 * lam ^ (Nat.dist j k) * ((5/3)*g) ^ ((3:ℝ)/5) :=
      mul_le_mul_of_nonneg_left hyj hE0
    linarith [hb', h2', h3', h5']
  have hbi : ∀ i ∈ Finset.range (N+1), i ≠ k →
      m i k ≤ Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5) * lam ^ (Nat.dist i k) := by
    intro i hi hik
    have hb' := hb i k
    rw [if_neg hik] at hb'
    have hxi : x i ≤ ((5/3)*g) ^ ((3:ℝ)/5) := hxb i hi hik
    have hE0 : 0 ≤ Real.exp 1 * lam ^ (Nat.dist i k) := by positivity
    have h2' : c1 * (Real.exp 1 * lam ^ (Nat.dist i k) * x i * y k)
        ≤ Real.exp 1 * lam ^ (Nat.dist i k) * x i * y k := by
      apply mul_le_of_le_one_left _ hc1le
      exact mul_nonneg (mul_nonneg hE0 (hx0 i)) (hy0 k)
    have h3' : Real.exp 1 * lam ^ (Nat.dist i k) * x i * y k
        ≤ Real.exp 1 * lam ^ (Nat.dist i k) * x i := by
      have h4' : 0 ≤ Real.exp 1 * lam ^ (Nat.dist i k) * x i := mul_nonneg hE0 (hx0 i)
      calc Real.exp 1 * lam ^ (Nat.dist i k) * x i * y k
          = (Real.exp 1 * lam ^ (Nat.dist i k) * x i) * y k := by ring
        _ ≤ (Real.exp 1 * lam ^ (Nat.dist i k) * x i) * 1 :=
            mul_le_mul_of_nonneg_left (hy1 k) h4'
        _ = Real.exp 1 * lam ^ (Nat.dist i k) * x i := by ring
    have h5' : Real.exp 1 * lam ^ (Nat.dist i k) * x i
        ≤ Real.exp 1 * lam ^ (Nat.dist i k) * ((5/3)*g) ^ ((3:ℝ)/5) :=
      mul_le_mul_of_nonneg_left hxi hE0
    linarith [hb', h2', h3', h5']
  -- ================= sum over j != k of m k j =================
  have hS2 : (∑ j ∈ Finset.range (N+1), (if j ≠ k then m k j else 0))
      ≤ 186 * lam * g ^ ((3:ℝ)/5) := by
    have h1 : ∀ j ∈ Finset.range (N+1), (if j ≠ k then m k j else 0)
        ≤ Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5) * (if j ≠ k then lam ^ (Nat.dist j k) else 0) := by
      intro j hj
      by_cases hjk : j ≠ k
      · rw [if_pos hjk, if_pos hjk]; exact hbk j hj hjk
      · rw [if_neg hjk, if_neg hjk]; positivity
    calc (∑ j ∈ Finset.range (N+1), (if j ≠ k then m k j else 0))
        ≤ ∑ j ∈ Finset.range (N+1),
            Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5) * (if j ≠ k then lam ^ (Nat.dist j k) else 0) :=
          Finset.sum_le_sum h1
      _ = Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5)
            * (∑ j ∈ Finset.range (N+1), (if j ≠ k then lam ^ (Nat.dist j k) else 0)) := by
          rw [Finset.mul_sum]
      _ = Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5)
            * (∑ j ∈ (Finset.range (N+1)).filter (fun j => j ≠ k), lam ^ (Nat.dist j k)) := by
          rw [Finset.sum_filter]
      _ ≤ Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5) * (2*lam/(1-lam)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact lam_dist_sum_ne' lam hl0 hlam1' N k hkN
      _ ≤ 186 * lam * g ^ ((3:ℝ)/5) := by
          rw [show Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5) * (2*lam/(1-lam))
              = (Real.exp 1 * ((5/3):ℝ)^((3:ℝ)/5) * (2/(1-lam))) * (lam * g ^ ((3:ℝ)/5)) by
                rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 5/3) hg0]; ring]
          have h0 : 0 ≤ lam * g ^ ((3:ℝ)/5) :=
            mul_nonneg (le_of_lt hlam0) (Real.rpow_nonneg hg0 _)
          calc (Real.exp 1 * ((5/3):ℝ)^((3:ℝ)/5) * (2/(1-lam))) * (lam * g ^ ((3:ℝ)/5))
              ≤ 186 * (lam * g ^ ((3:ℝ)/5)) := mul_le_mul_of_nonneg_right hcoef h0
            _ = 186 * lam * g ^ ((3:ℝ)/5) := by ring
  have hS3 : (∑ i ∈ Finset.range (N+1), (if i ≠ k then m i k else 0))
      ≤ 186 * lam * g ^ ((3:ℝ)/5) := by
    have h1 : ∀ i ∈ Finset.range (N+1), (if i ≠ k then m i k else 0)
        ≤ Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5) * (if i ≠ k then lam ^ (Nat.dist i k) else 0) := by
      intro i hi
      by_cases hik : i ≠ k
      · rw [if_pos hik, if_pos hik]; exact hbi i hi hik
      · rw [if_neg hik, if_neg hik]; positivity
    calc (∑ i ∈ Finset.range (N+1), (if i ≠ k then m i k else 0))
        ≤ ∑ i ∈ Finset.range (N+1),
            Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5) * (if i ≠ k then lam ^ (Nat.dist i k) else 0) :=
          Finset.sum_le_sum h1
      _ = Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5)
            * (∑ i ∈ Finset.range (N+1), (if i ≠ k then lam ^ (Nat.dist i k) else 0)) := by
          rw [Finset.mul_sum]
      _ = Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5)
            * (∑ i ∈ (Finset.range (N+1)).filter (fun i => i ≠ k), lam ^ (Nat.dist i k)) := by
          rw [Finset.sum_filter]
      _ ≤ Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5) * (2*lam/(1-lam)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact lam_dist_sum_ne' lam hl0 hlam1' N k hkN
      _ ≤ 186 * lam * g ^ ((3:ℝ)/5) := by
          rw [show Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5) * (2*lam/(1-lam))
              = (Real.exp 1 * ((5/3):ℝ)^((3:ℝ)/5) * (2/(1-lam))) * (lam * g ^ ((3:ℝ)/5)) by
                rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 5/3) hg0]; ring]
          have h0 : 0 ≤ lam * g ^ ((3:ℝ)/5) :=
            mul_nonneg (le_of_lt hlam0) (Real.rpow_nonneg hg0 _)
          calc (Real.exp 1 * ((5/3):ℝ)^((3:ℝ)/5) * (2/(1-lam))) * (lam * g ^ ((3:ℝ)/5))
              ≤ 186 * (lam * g ^ ((3:ℝ)/5)) := mul_le_mul_of_nonneg_right hcoef h0
            _ = 186 * lam * g ^ ((3:ℝ)/5) := by ring
  -- ================= sum over dist >= 2 in the k-row =================
  have hT2s : (∑ j ∈ Finset.range (N+1), (if 2 ≤ Nat.dist j k then m k j else 0))
      ≤ 200 * lam^2 * g ^ ((3:ℝ)/5) := by
    have h1 : ∀ j ∈ Finset.range (N+1), (if 2 ≤ Nat.dist j k then m k j else 0)
        ≤ Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5) * (if 2 ≤ Nat.dist j k then lam ^ (Nat.dist j k) else 0) := by
      intro j hj
      by_cases hd : 2 ≤ Nat.dist j k
      · rw [if_pos hd, if_pos hd]
        have hjk : j ≠ k := by intro h; subst h; rw [Nat.dist_self] at hd; omega
        exact hbk j hj hjk
      · rw [if_neg hd, if_neg hd]; positivity
    calc (∑ j ∈ Finset.range (N+1), (if 2 ≤ Nat.dist j k then m k j else 0))
        ≤ ∑ j ∈ Finset.range (N+1),
            Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5) * (if 2 ≤ Nat.dist j k then lam ^ (Nat.dist j k) else 0) :=
          Finset.sum_le_sum h1
      _ = Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5)
            * (∑ j ∈ Finset.range (N+1), (if 2 ≤ Nat.dist j k then lam ^ (Nat.dist j k) else 0)) := by
          rw [Finset.mul_sum]
      _ = Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5)
            * (∑ j ∈ (Finset.range (N+1)).filter (fun j => 2 ≤ Nat.dist j k),
                lam ^ (Nat.dist j k)) := by
          rw [Finset.sum_filter]
      _ ≤ Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5) * (2*lam^2/(1-lam)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact lam_dist_far_le' lam hl0 hlam1' N k
      _ ≤ 200 * lam^2 * g ^ ((3:ℝ)/5) := by
          rw [show Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5) * (2*lam^2/(1-lam))
              = (Real.exp 1 * ((5/3):ℝ)^((3:ℝ)/5) * (2*lam^2/(1-lam))) * g ^ ((3:ℝ)/5) by
                rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 5/3) hg0]; ring]
          exact mul_le_mul_of_nonneg_right hcoef2 (Real.rpow_nonneg hg0 _)
  have hT3s : (∑ i ∈ Finset.range (N+1), (if 2 ≤ Nat.dist i k then m i k else 0))
      ≤ 200 * lam^2 * g ^ ((3:ℝ)/5) := by
    have h1 : ∀ i ∈ Finset.range (N+1), (if 2 ≤ Nat.dist i k then m i k else 0)
        ≤ Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5) * (if 2 ≤ Nat.dist i k then lam ^ (Nat.dist i k) else 0) := by
      intro i hi
      by_cases hd : 2 ≤ Nat.dist i k
      · rw [if_pos hd, if_pos hd]
        have hik : i ≠ k := by intro h; subst h; rw [Nat.dist_self] at hd; omega
        exact hbi i hi hik
      · rw [if_neg hd, if_neg hd]; positivity
    calc (∑ i ∈ Finset.range (N+1), (if 2 ≤ Nat.dist i k then m i k else 0))
        ≤ ∑ i ∈ Finset.range (N+1),
            Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5) * (if 2 ≤ Nat.dist i k then lam ^ (Nat.dist i k) else 0) :=
          Finset.sum_le_sum h1
      _ = Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5)
            * (∑ i ∈ Finset.range (N+1), (if 2 ≤ Nat.dist i k then lam ^ (Nat.dist i k) else 0)) := by
          rw [Finset.mul_sum]
      _ = Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5)
            * (∑ i ∈ (Finset.range (N+1)).filter (fun i => 2 ≤ Nat.dist i k),
                lam ^ (Nat.dist i k)) := by
          rw [Finset.sum_filter]
      _ ≤ Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5) * (2*lam^2/(1-lam)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact lam_dist_far_le' lam hl0 hlam1' N k
      _ ≤ 200 * lam^2 * g ^ ((3:ℝ)/5) := by
          rw [show Real.exp 1 * ((5/3)*g) ^ ((3:ℝ)/5) * (2*lam^2/(1-lam))
              = (Real.exp 1 * ((5/3):ℝ)^((3:ℝ)/5) * (2*lam^2/(1-lam))) * g ^ ((3:ℝ)/5) by
                rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 5/3) hg0]; ring]
          exact mul_le_mul_of_nonneg_right hcoef2 (Real.rpow_nonneg hg0 _)
  -- ================= double-sum conversions =================
  have hAeq2 : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
      (if i ≠ k ∧ j ≠ k ∧ i ≠ j then m i j else 0)) = ∑ p ∈ K1, m p.1 p.2 := by
    rw [hK1, Finset.sum_filter, Finset.sum_product]
  have hBeq2 : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
      (if i = k ∧ j ≠ k then m i j else 0))
      = ∑ j ∈ Finset.range (N+1), (if j ≠ k then m k j else 0) := by
    have h1 : ∀ i ∈ Finset.range (N+1),
        (∑ j ∈ Finset.range (N+1), (if i = k ∧ j ≠ k then m i j else 0))
          = (if i = k then ∑ j ∈ Finset.range (N+1), (if j ≠ k then m k j else 0) else 0) := by
      intro i hi
      by_cases hik : i = k
      · rw [if_pos hik]
        apply Finset.sum_congr rfl; intro j hj
        by_cases hjk : j ≠ k
        · rw [if_pos ⟨hik, hjk⟩, if_pos hjk, hik]
        · rw [if_neg (fun h => hjk h.2), if_neg hjk]
      · rw [if_neg hik]
        exact Finset.sum_eq_zero (fun j hj => by rw [if_neg (fun h => hik h.1)])
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq', if_pos hk]
  have hCeq2 : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
      (if j = k ∧ i ≠ k then m i j else 0))
      = ∑ i ∈ Finset.range (N+1), (if i ≠ k then m i k else 0) := by
    apply Finset.sum_congr rfl; intro i hi
    rw [show (∑ j ∈ Finset.range (N+1), (if j = k ∧ i ≠ k then m i j else 0))
        = ∑ j ∈ Finset.range (N+1), (if j = k then (if i ≠ k then m i j else 0) else 0) from by
      apply Finset.sum_congr rfl; intro j hj
      by_cases hjk : j = k
      · by_cases hik : i ≠ k
        · rw [if_pos ⟨hjk, hik⟩, if_pos hjk, if_pos hik]
        · rw [if_neg (fun h => hik h.2), if_pos hjk, if_neg hik]
      · rw [if_neg (fun h => hjk h.1), if_neg hjk]]
    rw [Finset.sum_ite_eq', if_pos hk]
  have hDeq2 : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
      (if i = j ∧ i ≠ k then m i j else 0))
      = ∑ i ∈ Finset.range (N+1), (if i ≠ k then m i i else 0) := by
    apply Finset.sum_congr rfl; intro i hi
    rw [show (∑ j ∈ Finset.range (N+1), (if i = j ∧ i ≠ k then m i j else 0))
        = ∑ j ∈ Finset.range (N+1), (if i = j then (if i ≠ k then m i j else 0) else 0) from by
      apply Finset.sum_congr rfl; intro j hj
      by_cases hij : i = j
      · by_cases hik : i ≠ k
        · rw [if_pos ⟨hij, hik⟩, if_pos hij, if_pos hik]
        · rw [if_neg (fun h => hik h.2), if_pos hij, if_neg hik]
      · rw [if_neg (fun h => hij h.1), if_neg hij]]
    rw [Finset.sum_ite_eq, if_pos hi]
  have hBeq2' : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
      (if i = k ∧ 2 ≤ Nat.dist j k then m i j else 0))
      = ∑ j ∈ Finset.range (N+1), (if 2 ≤ Nat.dist j k then m k j else 0) := by
    have h1 : ∀ i ∈ Finset.range (N+1),
        (∑ j ∈ Finset.range (N+1), (if i = k ∧ 2 ≤ Nat.dist j k then m i j else 0))
          = (if i = k then ∑ j ∈ Finset.range (N+1),
              (if 2 ≤ Nat.dist j k then m k j else 0) else 0) := by
      intro i hi
      by_cases hik : i = k
      · rw [if_pos hik]
        apply Finset.sum_congr rfl; intro j hj
        by_cases hd : 2 ≤ Nat.dist j k
        · rw [if_pos ⟨hik, hd⟩, if_pos hd, hik]
        · rw [if_neg (fun h => hd h.2), if_neg hd]
      · rw [if_neg hik]
        exact Finset.sum_eq_zero (fun j hj => by rw [if_neg (fun h => hik h.1)])
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq', if_pos hk]
  have hCeq2' : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
      (if j = k ∧ 2 ≤ Nat.dist i k then m i j else 0))
      = ∑ i ∈ Finset.range (N+1), (if 2 ≤ Nat.dist i k then m i k else 0) := by
    apply Finset.sum_congr rfl; intro i hi
    rw [show (∑ j ∈ Finset.range (N+1), (if j = k ∧ 2 ≤ Nat.dist i k then m i j else 0))
        = ∑ j ∈ Finset.range (N+1),
            (if j = k then (if 2 ≤ Nat.dist i k then m i j else 0) else 0) from by
      apply Finset.sum_congr rfl; intro j hj
      by_cases hjk : j = k
      · by_cases hd : 2 ≤ Nat.dist i k
        · rw [if_pos ⟨hjk, hd⟩, if_pos hjk, if_pos hd]
        · rw [if_neg (fun h => hd h.2), if_pos hjk, if_neg hd]
      · rw [if_neg (fun h => hjk h.1), if_neg hjk]]
    rw [Finset.sum_ite_eq', if_pos hk]
  -- ================= splitting the bad set =================
  have hsplitA : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
        (if 2 ≤ Nat.dist i k + Nat.dist j k then m i j else 0))
      ≤ (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
          (if i ≠ k ∧ j ≠ k ∧ i ≠ j then m i j else 0))
        + (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
          (if i = k ∧ 2 ≤ Nat.dist j k then m i j else 0))
        + (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
          (if j = k ∧ 2 ≤ Nat.dist i k then m i j else 0))
        + (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
          (if i = j ∧ i ≠ k then m i j else 0)) := by
    have itnn : ∀ (P : Prop) [Decidable P] (a : ℝ), 0 ≤ a → 0 ≤ (if P then a else 0) := by
      intro P _ a ha; by_cases h : P <;> simp [h, ha]
    have hpt : ∀ i ∈ Finset.range (N+1), ∀ j ∈ Finset.range (N+1),
        (if 2 ≤ Nat.dist i k + Nat.dist j k then m i j else 0)
        ≤ (if i ≠ k ∧ j ≠ k ∧ i ≠ j then m i j else 0)
          + (if i = k ∧ 2 ≤ Nat.dist j k then m i j else 0)
          + (if j = k ∧ 2 ≤ Nat.dist i k then m i j else 0)
          + (if i = j ∧ i ≠ k then m i j else 0) := by
      intro i hi j hj
      have hm := hm0 i j
      by_cases hP : 2 ≤ Nat.dist i k + Nat.dist j k
      · rw [if_pos hP]
        have key : (i ≠ k ∧ j ≠ k ∧ i ≠ j) ∨ (i = k ∧ 2 ≤ Nat.dist j k)
            ∨ (j = k ∧ 2 ≤ Nat.dist i k) ∨ (i = j ∧ i ≠ k) := by
          by_cases hik : i = k
          · subst hik
            refine Or.inr (Or.inl ⟨rfl, ?_⟩)
            rwa [Nat.dist_self, zero_add] at hP
          · by_cases hjk : j = k
            · subst hjk
              refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
              rwa [Nat.dist_self, add_zero] at hP
            · by_cases hij : i = j
              · exact Or.inr (Or.inr (Or.inr ⟨hij, hik⟩))
              · exact Or.inl ⟨hik, hjk, hij⟩
        rcases key with h | h | h | h
        · rw [if_pos h]
          linarith [itnn (i = k ∧ 2 ≤ Nat.dist j k) (m i j) hm,
            itnn (j = k ∧ 2 ≤ Nat.dist i k) (m i j) hm,
            itnn (i = j ∧ i ≠ k) (m i j) hm]
        · rw [if_pos h]
          linarith [itnn (i ≠ k ∧ j ≠ k ∧ i ≠ j) (m i j) hm,
            itnn (j = k ∧ 2 ≤ Nat.dist i k) (m i j) hm,
            itnn (i = j ∧ i ≠ k) (m i j) hm]
        · rw [if_pos h]
          linarith [itnn (i ≠ k ∧ j ≠ k ∧ i ≠ j) (m i j) hm,
            itnn (i = k ∧ 2 ≤ Nat.dist j k) (m i j) hm,
            itnn (i = j ∧ i ≠ k) (m i j) hm]
        · rw [if_pos h]
          linarith [itnn (i ≠ k ∧ j ≠ k ∧ i ≠ j) (m i j) hm,
            itnn (i = k ∧ 2 ≤ Nat.dist j k) (m i j) hm,
            itnn (j = k ∧ 2 ≤ Nat.dist i k) (m i j) hm]
      · rw [if_neg hP]
        linarith [itnn (i ≠ k ∧ j ≠ k ∧ i ≠ j) (m i j) hm,
          itnn (i = k ∧ 2 ≤ Nat.dist j k) (m i j) hm,
          itnn (j = k ∧ 2 ≤ Nat.dist i k) (m i j) hm,
          itnn (i = j ∧ i ≠ k) (m i j) hm]
    calc (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
          (if 2 ≤ Nat.dist i k + Nat.dist j k then m i j else 0))
        ≤ ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
            ((if i ≠ k ∧ j ≠ k ∧ i ≠ j then m i j else 0)
              + (if i = k ∧ 2 ≤ Nat.dist j k then m i j else 0)
              + (if j = k ∧ 2 ≤ Nat.dist i k then m i j else 0)
              + (if i = j ∧ i ≠ k then m i j else 0)) :=
          Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hpt i hi j hj))
      _ = _ := by simp only [Finset.sum_add_distrib]
  -- ================= assembly =================
  have hneq : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1), (if i ≠ j then m i j else 0))
      = 1 - ∑ i ∈ Finset.range (N+1), m i i := by
    have h1 : ∀ i ∈ Finset.range (N+1),
        (∑ j ∈ Finset.range (N+1), (if i ≠ j then m i j else 0))
          = (∑ j ∈ Finset.range (N+1), m i j) - m i i := by
      intro i hi
      have h2 : (∑ j ∈ Finset.range (N+1), m i j)
          = (∑ j ∈ Finset.range (N+1), (if i ≠ j then m i j else 0)) + m i i := by
        have hs := Finset.sum_filter_add_sum_filter_not (Finset.range (N+1))
          (fun j => i ≠ j) (fun j => m i j)
        rw [Finset.sum_filter, Finset.sum_filter] at hs
        have h3 : (∑ j ∈ Finset.range (N+1), (if ¬ i ≠ j then m i j else 0)) = m i i := by
          have h4 : (∑ j ∈ Finset.range (N+1), (if ¬ i ≠ j then m i j else 0))
              = ∑ j ∈ Finset.range (N+1), (if i = j then m i j else 0) := by
            apply Finset.sum_congr rfl; intro j hj
            by_cases hij : i = j <;> simp [hij]
          rw [h4, Finset.sum_ite_eq, if_pos hi]
        linarith [hs, h3]
      linarith [h2]
    calc (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1), (if i ≠ j then m i j else 0))
        = ∑ i ∈ Finset.range (N+1), ((∑ j ∈ Finset.range (N+1), m i j) - m i i) :=
          Finset.sum_congr rfl h1
      _ = (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1), m i j)
            - ∑ i ∈ Finset.range (N+1), m i i :=
          Finset.sum_sub_distrib (f := fun i => ∑ j ∈ Finset.range (N+1), m i j)
            (g := fun i => m i i)
      _ = 1 - ∑ i ∈ Finset.range (N+1), m i i := by rw [hmsum]
  have hoffeq : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1), (if i ≠ j then m i j else 0))
      = (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
          (if i ≠ k ∧ j ≠ k ∧ i ≠ j then m i j else 0))
        + (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
          (if i = k ∧ j ≠ k then m i j else 0))
        + (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
          (if j = k ∧ i ≠ k then m i j else 0)) := by
    have hpt : ∀ i j, (if i ≠ j then m i j else 0)
        = (if i ≠ k ∧ j ≠ k ∧ i ≠ j then m i j else 0)
          + (if i = k ∧ j ≠ k then m i j else 0)
          + (if j = k ∧ i ≠ k then m i j else 0) := by
      intro i j
      by_cases hij : i ≠ j
      · rw [if_pos hij]
        by_cases hik : i = k
        · have e1 : (if i ≠ k ∧ j ≠ k ∧ i ≠ j then m i j else 0) = 0 := if_neg (fun h => h.1 hik)
          have e2 : (if i = k ∧ j ≠ k then m i j else 0) = m i j :=
            if_pos ⟨hik, fun h => hij (hik.trans h.symm)⟩
          have e3 : (if j = k ∧ i ≠ k then m i j else 0) = 0 := if_neg (fun h => h.2 hik)
          rw [e1, e2, e3]; ring
        · by_cases hjk : j = k
          · have e1 : (if i ≠ k ∧ j ≠ k ∧ i ≠ j then m i j else 0) = 0 :=
              if_neg (fun h => h.2.1 hjk)
            have e2 : (if i = k ∧ j ≠ k then m i j else 0) = 0 := if_neg (fun h => hik h.1)
            have e3 : (if j = k ∧ i ≠ k then m i j else 0) = m i j := if_pos ⟨hjk, hik⟩
            rw [e1, e2, e3]; ring
          · have e1 : (if i ≠ k ∧ j ≠ k ∧ i ≠ j then m i j else 0) = m i j :=
              if_pos ⟨hik, hjk, hij⟩
            have e2 : (if i = k ∧ j ≠ k then m i j else 0) = 0 := if_neg (fun h => hik h.1)
            have e3 : (if j = k ∧ i ≠ k then m i j else 0) = 0 := if_neg (fun h => hjk h.1)
            rw [e1, e2, e3]; ring
      · have hji : i = j := not_not.mp hij
        have e1 : (if i ≠ k ∧ j ≠ k ∧ i ≠ j then m i j else 0) = 0 := if_neg (fun h => h.2.2 hji)
        have e2 : (if i = k ∧ j ≠ k then m i j else 0) = 0 := if_neg (fun h => h.2 (hji.symm.trans h.1))
        have e3 : (if j = k ∧ i ≠ k then m i j else 0) = 0 := if_neg (fun h => h.2 (hji.trans h.1))
        rw [if_neg hij, e1, e2, e3]; ring
    calc (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1), (if i ≠ j then m i j else 0))
        = ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
            ((if i ≠ k ∧ j ≠ k ∧ i ≠ j then m i j else 0)
              + (if i = k ∧ j ≠ k then m i j else 0)
              + (if j = k ∧ i ≠ k then m i j else 0)) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hsixth : (1/6) * g ≤ 200 * lam * g^((6:ℝ)/5) + 372 * lam * g^((3:ℝ)/5) := by
    have hA1 : (1/6) * g ≤ 1 - ∑ i ∈ Finset.range (N+1), m i i := by linarith [hdiagsum]
    rw [← hneq] at hA1
    have hoff3 := hoffeq
    rw [hBeq2, hCeq2] at hoff3
    rw [hoff3] at hA1
    have hAT : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
        (if i ≠ k ∧ j ≠ k ∧ i ≠ j then m i j else 0)) ≤ 200 * lam * g ^ ((6:ℝ)/5) :=
      (le_of_eq hAeq2).trans hT1b
    linarith [hA1, hAT, hS2, hS3]
  have h6 : (1/6) * g ≤ 572 * lam * g ^ ((3:ℝ)/5) := by
    have h2 : 200 * lam * g ^ ((6:ℝ)/5) ≤ 200 * lam * g ^ ((3:ℝ)/5) :=
      mul_le_mul_of_nonneg_left hg6le (by positivity)
    linarith [hsixth, h2]
  have h7 : g ^ ((2:ℝ)/5) ≤ 20592 * lam := by
    have hfac : g ^ ((2:ℝ)/5) * g ^ ((3:ℝ)/5) = g := by
      rw [← Real.rpow_add' hg0 (by norm_num : ((2:ℝ)/5 + 3/5) ≠ 0)]
      rw [show ((2:ℝ)/5 + 3/5) = (1:ℝ) by norm_num]
      exact Real.rpow_one g
    rcases eq_or_lt_of_le hg0 with h0 | hpos
    · have hle0 : g ^ ((2:ℝ)/5) ≤ 0 := by
        have h := Real.rpow_le_rpow hg0 h0.symm.le (by norm_num : (0:ℝ) ≤ (2:ℝ)/5)
        simpa [Real.zero_rpow (by norm_num : ((2:ℝ)/5) ≠ 0)] using h
      linarith [hle0, hlam0]
    · have h3 : 0 < g ^ ((3:ℝ)/5) := Real.rpow_pos_of_pos hpos _
      have h8 : (1/6) * g ^ ((2:ℝ)/5) * g ^ ((3:ℝ)/5)
          ≤ (572*lam) * g ^ ((3:ℝ)/5) := by
        have he : (1/6) * g ^ ((2:ℝ)/5) * g ^ ((3:ℝ)/5) = (1/6) * g := by
          rw [show (1/6) * g ^ ((2:ℝ)/5) * g ^ ((3:ℝ)/5)
              = (1/6) * (g ^ ((2:ℝ)/5) * g ^ ((3:ℝ)/5)) by ring]
          rw [hfac]
        rw [he]; exact h6
      have h9 := le_of_mul_le_mul_right h8 h3
      linarith
  have hg_bound : g ≤ (25000 * lam) ^ ((5:ℝ)/2) := by
    have h11 : g ≤ (20592 * lam) ^ ((5:ℝ)/2) := by
      have he : (g ^ ((2:ℝ)/5)) ^ ((5:ℝ)/2) = g := by
        rw [← Real.rpow_mul hg0]
        rw [show ((2:ℝ)/5) * (5/2) = (1:ℝ) by norm_num]
        exact Real.rpow_one g
      rw [← he]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hg0 _) h7 (by norm_num)
    have h12 : (20592 * lam) ^ ((5:ℝ)/2) ≤ (25000 * lam) ^ ((5:ℝ)/2) :=
      Real.rpow_le_rpow (by positivity) (by nlinarith [hlam0]) (by norm_num)
    linarith
  have hgA : g ^ ((6:ℝ)/5) ≤ 25000^3 * lam ^ (3:ℝ) := by
    have h := Real.rpow_le_rpow hg0 hg_bound (by norm_num : (0:ℝ) ≤ (6:ℝ)/5)
    have h2 : ((25000*lam) ^ ((5:ℝ)/2)) ^ ((6:ℝ)/5) = 25000^3 * lam ^ (3:ℝ) := by
      rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ 25000*lam)]
      rw [show ((5:ℝ)/2) * ((6:ℝ)/5) = (3:ℝ) by norm_num]
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 25000) (le_of_lt hlam0)]
      rw [show (25000:ℝ)^((3:ℝ)) = 25000^3 from Real.rpow_natCast 25000 3]
    rwa [h2] at h
  have hgB : g ^ ((3:ℝ)/5) ≤ 25000^((3:ℝ)/2) * lam^((3:ℝ)/2) := by
    have h := Real.rpow_le_rpow hg0 hg_bound (by norm_num : (0:ℝ) ≤ (3:ℝ)/5)
    have h2 : ((25000*lam) ^ ((5:ℝ)/2)) ^ ((3:ℝ)/5) = 25000^((3:ℝ)/2) * lam^((3:ℝ)/2) := by
      rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ 25000*lam)]
      rw [show ((5:ℝ)/2) * ((3:ℝ)/5) = ((3:ℝ)/2) by norm_num]
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 25000) (le_of_lt hlam0)]
    rwa [h2] at h
  have hbound1 : 200 * lam * g ^ ((6:ℝ)/5) ≤ 4*10^15 * lam ^ (3:ℝ) := by
    have h1 : 200 * lam * g ^ ((6:ℝ)/5) ≤ 200 * lam * (25000^3 * lam ^ (3:ℝ)) :=
      mul_le_mul_of_nonneg_left hgA (by positivity)
    have h2 : lam * lam ^ (3:ℝ) ≤ lam ^ (3:ℝ) := by
      have h3 : lam ^ (1:ℝ) * lam ^ (3:ℝ) = lam ^ (4:ℝ) := by
        rw [← Real.rpow_add' (le_of_lt hlam0) (by norm_num : ((1:ℝ) + 3) ≠ 0)]
        norm_num
      have h4 : lam ^ (4:ℝ) ≤ lam ^ (3:ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hlam0 hlam1'.le (by norm_num : (3:ℝ) ≤ 4)
      calc lam * lam ^ (3:ℝ) = lam ^ (1:ℝ) * lam ^ (3:ℝ) := by rw [Real.rpow_one]
        _ = lam ^ (4:ℝ) := h3
        _ ≤ lam ^ (3:ℝ) := h4
    calc 200 * lam * g ^ ((6:ℝ)/5) ≤ 200 * lam * (25000^3 * lam ^ (3:ℝ)) := h1
      _ = (200 * 25000^3) * (lam * lam ^ (3:ℝ)) := by ring
      _ ≤ (200 * 25000^3) * lam ^ (3:ℝ) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 4*10^15 * lam ^ (3:ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (le_of_lt hlam0) _)
          norm_num
  have hbound2 : 2 * g ^ ((6:ℝ)/5) ≤ 4*10^15 * lam ^ (3:ℝ) := by
    calc 2 * g ^ ((6:ℝ)/5) ≤ 2 * (25000^3 * lam ^ (3:ℝ)) :=
          mul_le_mul_of_nonneg_left hgA (by norm_num)
      _ = (2 * 25000^3) * lam ^ (3:ℝ) := by ring
      _ ≤ 4*10^15 * lam ^ (3:ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (le_of_lt hlam0) _)
          norm_num
  have hbound3 : 400 * lam^2 * g ^ ((3:ℝ)/5) ≤ 10^16 * lam^((7:ℝ)/2) := by
    have h1 : 400 * lam^2 * g ^ ((3:ℝ)/5)
        ≤ 400 * lam^2 * (25000^((3:ℝ)/2) * lam^((3:ℝ)/2)) :=
      mul_le_mul_of_nonneg_left hgB (by positivity)
    have h4 : lam^2 * lam^((3:ℝ)/2) = lam^((7:ℝ)/2) := by
      rw [show lam^2 = lam^((2:ℝ)) from (Real.rpow_natCast lam 2).symm]
      rw [← Real.rpow_add' hl0 (by norm_num : ((2:ℝ) + 3/2) ≠ 0)]
      norm_num
    have h5 : (400 * 25000^((3:ℝ)/2) : ℝ) ≤ 10^16 := by
      have h6 : (25000:ℝ)^((3:ℝ)/2) ≤ 25000^2 := by
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 25000)
          (by norm_num : ((3:ℝ)/2) ≤ 2)
        rwa [show (25000:ℝ)^(2:ℝ) = 25000^2 from Real.rpow_natCast 25000 2] at h
      nlinarith [h6]
    have h3 : (400:ℝ) * lam^2 * (25000^((3:ℝ)/2) * lam^((3:ℝ)/2))
        ≤ 10^16 * lam^((7:ℝ)/2) := by
      rw [show (400:ℝ) * lam^2 * (25000^((3:ℝ)/2) * lam^((3:ℝ)/2))
          = (400 * 25000^((3:ℝ)/2)) * (lam^2 * lam^((3:ℝ)/2)) by ring]
      rw [h4]
      exact mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hl0 _)
    linarith
  have hbad : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
      (if 2 ≤ Nat.dist i k + Nat.dist j k then m i j else 0))
      ≤ 10^16 * (lam ^ (3:ℝ) + lam ^ ((7:ℝ)/2)) := by
    have hA' : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
        (if i ≠ k ∧ j ≠ k ∧ i ≠ j then m i j else 0)) ≤ 4*10^15 * lam ^ (3:ℝ) :=
      (le_of_eq hAeq2).trans (hT1b.trans hbound1)
    have hB' : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
        (if i = k ∧ 2 ≤ Nat.dist j k then m i j else 0)) ≤ 200 * lam^2 * g ^ ((3:ℝ)/5) :=
      (le_of_eq hBeq2').trans hT2s
    have hC' : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
        (if j = k ∧ 2 ≤ Nat.dist i k then m i j else 0)) ≤ 200 * lam^2 * g ^ ((3:ℝ)/5) :=
      (le_of_eq hCeq2').trans hT3s
    have hD' : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
        (if i = j ∧ i ≠ k then m i j else 0)) ≤ 4*10^15 * lam ^ (3:ℝ) :=
      (le_of_eq hDeq2).trans (hT1a.trans hbound2)
    have hBC : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
          (if i = k ∧ 2 ≤ Nat.dist j k then m i j else 0))
        + (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
          (if j = k ∧ 2 ≤ Nat.dist i k then m i j else 0))
        ≤ 10^16 * lam ^ ((7:ℝ)/2) := by
      have h1 := add_le_add hB' hC'
      have h2 : (200:ℝ) * lam^2 * g ^ ((3:ℝ)/5) + 200 * lam^2 * g ^ ((3:ℝ)/5)
          = 400 * lam^2 * g ^ ((3:ℝ)/5) := by ring
      rw [h2] at h1
      exact h1.trans hbound3
    have hAD : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
          (if i ≠ k ∧ j ≠ k ∧ i ≠ j then m i j else 0))
        + (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
          (if i = j ∧ i ≠ k then m i j else 0))
        ≤ 10^16 * lam ^ (3:ℝ) := by
      have h1 := add_le_add hA' hD'
      have h2 : (4:ℝ)*10^15 * lam ^ (3:ℝ) + 4*10^15 * lam ^ (3:ℝ)
          = 8*10^15 * lam ^ (3:ℝ) := by ring
      rw [h2] at h1
      have h3 : (8*10^15:ℝ) * lam ^ (3:ℝ) ≤ 10^16 * lam ^ (3:ℝ) :=
        mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg (le_of_lt hlam0) _)
      exact h1.trans h3
    have hs : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
        (if 2 ≤ Nat.dist i k + Nat.dist j k then m i j else 0))
        ≤ ((∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
              (if i ≠ k ∧ j ≠ k ∧ i ≠ j then m i j else 0))
            + (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
              (if i = j ∧ i ≠ k then m i j else 0)))
          + ((∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
              (if i = k ∧ 2 ≤ Nat.dist j k then m i j else 0))
            + (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
              (if j = k ∧ 2 ≤ Nat.dist i k then m i j else 0))) := by
      linarith [hsplitA]
    have hfin : ((∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
              (if i ≠ k ∧ j ≠ k ∧ i ≠ j then m i j else 0))
            + (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
              (if i = j ∧ i ≠ k then m i j else 0)))
          + ((∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
              (if i = k ∧ 2 ≤ Nat.dist j k then m i j else 0))
            + (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
              (if j = k ∧ 2 ≤ Nat.dist i k then m i j else 0)))
        ≤ 10^16 * (lam ^ (3:ℝ) + lam ^ ((7:ℝ)/2)) := by
      have h2 := add_le_add hAD hBC
      have h3 : (10:ℝ)^16 * lam ^ (3:ℝ) + 10^16 * lam ^ ((7:ℝ)/2)
          = 10^16 * (lam ^ (3:ℝ) + lam ^ ((7:ℝ)/2)) := by ring
      linarith [h2, h3]
    exact hs.trans hfin
  exact ⟨k, hk, hbad⟩


set_option autoImplicit true


-- =====================   from DS/t17.lean  =====================
/-! ## Stage 1: assembling the decay lemma (GW21 Lemma 2.1 / HWVS Lemma 3.2) -/

theorem decay_away_from_diagonal (N : ℕ) (lam c1 : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 29/31)
    (hc1 : 0 < c1) (hc1le : c1 ≤ 1)
    (m : ℕ → ℕ → ℝ) (x y : ℕ → ℝ)
    (hm0 : ∀ i j, 0 ≤ m i j) (hx0 : ∀ i, 0 ≤ x i) (hy0 : ∀ j, 0 ≤ y j)
    (hx1 : ∀ i, x i ≤ 1) (hy1 : ∀ j, y j ≤ 1)
    (hmsum : ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1), m i j = 1)
    (hxs : ∑ i ∈ Finset.range (N+1), x i ^ ((5:ℝ)/3) = 1)
    (hys : ∑ j ∈ Finset.range (N+1), y j ^ ((5:ℝ)/3) = 1)
    (hb : ∀ i j, m i j ≤ c1 * ((if i = j then 1 else Real.exp 1 * lam ^ (Nat.dist i j)) * x i * y j)) :
    ((1 - lam) / (1 - lam + 2 * Real.exp 1) ≤ c1) ∧
      ∃ k ∈ Finset.range (N+1), ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
        (if 2 ≤ Nat.dist i k + Nat.dist j k then m i j else 0)
        ≤ 10^16 * (lam^(3:ℝ) + lam^((7:ℝ)/2)) :=
  ⟨decay_part1 N lam c1 hlam0 (by linarith) hc1 m x y hm0 hx0 hy0 hx1 hy1 hmsum hxs hys hb,
   part2_core N lam c1 hlam0 hlam1 hc1 hc1le m x y hm0 hx0 hy0 hx1 hy1 hmsum hxs hys hb⟩

/-! ## Stage 2: the prime tail bound -/

/-- For any `ε > 0` there is `p₀` such that the sum of `p^{-6/5} + p^{-7/5}` over primes
`p > p₀` is `< ε`. -/
theorem exists_prime_tail_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ p₀ : ℕ, ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) → (∀ p ∈ s, p₀ < p) →
      ∑ p ∈ s, ((p:ℝ)^(-((6:ℝ)/5)) + (p:ℝ)^(-((7:ℝ)/5))) < ε := by
  set f : ℕ → ℝ := fun n => (n:ℝ)^(-((6:ℝ)/5)) + (n:ℝ)^(-((7:ℝ)/5)) with hf
  have hf0 : ∀ n, 0 ≤ f n := by
    intro n
    have h1 : (0:ℝ) ≤ (n:ℝ)^(-((6:ℝ)/5)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have h2 : (0:ℝ) ≤ (n:ℝ)^(-((7:ℝ)/5)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    simp only [hf]; linarith
  have hs1 : Summable (fun n : ℕ => (n:ℝ)^(-((6:ℝ)/5))) := by
    rw [show (fun n : ℕ => (n:ℝ)^(-((6:ℝ)/5))) = (fun n : ℕ => 1 / (n:ℝ)^((6:ℝ)/5)) from by
      funext n
      rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]]
    exact (Real.summable_one_div_nat_rpow (p := (6:ℝ)/5)).mpr (by norm_num)
  have hs2 : Summable (fun n : ℕ => (n:ℝ)^(-((7:ℝ)/5))) := by
    rw [show (fun n : ℕ => (n:ℝ)^(-((7:ℝ)/5))) = (fun n : ℕ => 1 / (n:ℝ)^((7:ℝ)/5)) from by
      funext n
      rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]]
    exact (Real.summable_one_div_nat_rpow (p := (7:ℝ)/5)).mpr (by norm_num)
  have hfs : Summable f := by simpa only [hf] using hs1.add hs2
  have hlim : Filter.Tendsto (fun N : ℕ => ∑' k : ℕ, f (k + N)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, f i) Filter.atTop
        (nhds (∑' i, f i)) := hfs.hasSum.tendsto_sum_nat
    have h2 : Filter.Tendsto (fun N : ℕ => (∑' i, f i) - ∑ i ∈ Finset.range N, f i)
        Filter.atTop (nhds ((∑' i, f i) - ∑' i, f i)) :=
      tendsto_const_nhds.sub h1
    rw [sub_self] at h2
    refine h2.congr' ?_
    filter_upwards with N
    have h3 := hfs.sum_add_tsum_nat_add N
    linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hlim.eventually_lt_const hε)
  refine ⟨N, ?_⟩
  intro s hsprime hsgt
  have hinj : Set.InjOn (fun n => n - N) ↑s := by
    intro a ha b hb hab
    have ha' : N < a := hsgt a (by simpa using ha)
    have hb' : N < b := hsgt b (by simpa using hb)
    have hab' : a - N = b - N := hab
    omega
  have h1 : ∑ n ∈ s, f n = ∑ k ∈ s.image (fun n => n - N), f (k + N) := by
    rw [Finset.sum_image (g := fun n => n - N) (f := fun k => f (k + N)) hinj]
    apply Finset.sum_congr rfl; intro n hn
    have : N < n := hsgt n hn
    congr 1; omega
  rw [h1]
  have hsNT : Summable (fun k : ℕ => f (k + N)) :=
    hfs.comp_injective (fun a b hab => by omega)
  exact lt_of_le_of_lt (hsNT.sum_le_tsum _ (fun k _ => hf0 (k+N))) (hN N le_rfl)

/-! ## Stage 3: definitions -/

/-- The set of primes dividing some element of `V`. -/
def pset (V : Finset ℕ) : Finset ℕ := V.biUnion (fun n => n.primeFactors)

/-- Total mass of a weight function on a finset. -/
def mass (a : ℕ → ℝ) (V : Finset ℕ) : ℝ := ∑ v ∈ V, a v

/-- Mass of a finite set of pairs, weighted by the product of the weights. -/
def pairMass (a b : ℕ → ℝ) (E : Finset (ℕ × ℕ)) : ℝ := ∑ e ∈ E, a e.1 * b e.2

/-- The primes `≥ t` dividing the "coprime part" of `(v,w)`. -/
def Qset (t : ℝ) (v w : ℕ) : Finset ℕ :=
  (Nat.primeFactors (v * w / (v.gcd w * v.gcd w))).filter (fun r => t ≤ (r:ℝ))

/-- The structural condition on a pair `(v,w)`. -/
def good (t C : ℝ) (a b : ℕ → ℝ) (v w : ℕ) : Prop :=
  (v.gcd w : ℝ) ≥ (v:ℝ)*(w:ℝ)*max (a v / (v.totient:ℝ)) (b w / (w.totient:ℝ)) ∧
  C ≤ ∑ r ∈ Qset t v w, 1/(r:ℝ)

/-- `p`-exact part of `V`. -/
def Vval (p i : ℕ) (V : Finset ℕ) : Finset ℕ := V.filter (fun v => p^i ∣ v ∧ ¬ p^(i+1) ∣ v)

/-- Reduced support. -/
def Vred (p i : ℕ) (V : Finset ℕ) : Finset ℕ := (Vval p i V).image (fun v => v / p^i)

/-- Reduced weight on the `v`-side. -/
def ared (p i j : ℕ) (a : ℕ → ℝ) : ℕ → ℝ :=
  fun u => if p ∣ u then 0 else (p:ℝ)^(i + j - min i j) * a (p^i * u) / ((p^i).totient : ℝ)

/-- Reduced weight on the `w`-side. -/
def bred (p i j : ℕ) (b : ℕ → ℝ) : ℕ → ℝ :=
  fun w => if p ∣ w then 0 else (p:ℝ)^(i + j - min i j) * b (p^j * w) / ((p^j).totient : ℝ)

/-- The pairs of `E` whose coordinates lie in `Vval p i V`, resp. `Vval p j W`. -/
def Eval (p i j : ℕ) (V W : Finset ℕ) (E : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  E.filter (fun e => e.1 ∈ Vval p i V ∧ e.2 ∈ Vval p j W)

/-- The reduced pair set. -/
def Ered (p i j : ℕ) (V W : Finset ℕ) (E : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (Eval p i j V W E).image (fun e => (e.1 / p^i, e.2 / p^j))

/-! ## Stage 5: the reduced instance is valid -/

section Reduced

variable {p i j : ℕ} {V W : Finset ℕ}

lemma mem_Vval_iff {v : ℕ} : v ∈ Vval p i V ↔ v ∈ V ∧ p^i ∣ v ∧ ¬ p^(i+1) ∣ v := by
  simp [Vval, Finset.mem_filter]

lemma Vval_unique {v i' : ℕ} (hp : p.Prime)
    (h1 : p^i ∣ v) (h1' : ¬ p^(i+1) ∣ v) (h2 : p^i' ∣ v) (h2' : ¬ p^(i'+1) ∣ v) : i = i' := by
  rcases lt_trichotomy i i' with h | h | h
  · exact absurd (dvd_trans (pow_dvd_pow p h : p^(i+1) ∣ p^i') h2) h1'
  · exact h
  · exact absurd (dvd_trans (pow_dvd_pow p h : p^(i'+1) ∣ p^i) h1) h2'

lemma Vred_ge_one (hp : p.Prime) {v : ℕ} (hv : v ∈ Vval p i V) : 1 ≤ v / p^i := by
  rw [mem_Vval_iff] at hv
  have hvpos : 0 < v := Nat.pos_of_ne_zero (by
    rintro rfl
    exact hv.2.2 ⟨0, by simp⟩)
  exact Nat.div_pos (Nat.le_of_dvd hvpos hv.2.1) (pow_pos hp.pos i)

lemma Vred_not_dvd (hp : p.Prime) {v : ℕ} (hv : v ∈ Vval p i V) : ¬ p ∣ v / p^i := by
  rw [mem_Vval_iff] at hv
  intro hcon
  exact hv.2.2 (by
    obtain ⟨k, hk⟩ := hcon
    refine ⟨k, ?_⟩
    rw [show i + 1 = i + 1 by rfl, pow_succ]
    calc v = p^i * (v / p^i) := (Nat.mul_div_cancel' hv.2.1).symm
      _ = p^i * (p * k) := by rw [hk]
      _ = (p^i * p) * k := by ring)

lemma ared_nonneg (ha0 : ∀ v, 0 ≤ a v) (u : ℕ) : 0 ≤ ared p i j a u := by
  unfold ared
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (mul_nonneg (by positivity) (ha0 _)) (by positivity)

end Reduced

/-! ## Stage 4a: gcd and coprimality helpers -/

/-- If `p` is a prime not dividing `u`, then `u.gcd (p^k w) = u.gcd w`. -/
lemma gcd_mul_coprime_pow (p k u w : ℕ) (hp : p.Prime) (hu : ¬ p ∣ u) :
    u.gcd (p^k * w) = u.gcd w := by
  set d := u.gcd (p^k * w) with hd
  apply Nat.dvd_antisymm
  · have hdu : d ∣ u := Nat.gcd_dvd_left _ _
    have hd2 : d ∣ p^k * w := Nat.gcd_dvd_right _ _
    have hpc : ¬ p ∣ d := fun h => hu (h.trans hdu)
    have hcop : d.Coprime (p^k) := by
      have h1 : p.Coprime d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpc
      exact (h1.pow_left k).symm
    have hdw : d ∣ w := by
      refine Nat.Coprime.dvd_of_dvd_mul_right hcop ?_
      rw [mul_comm]; exact hd2
    exact Nat.dvd_gcd hdu hdw
  · exact Nat.dvd_gcd (Nat.gcd_dvd_left u w) ((Nat.gcd_dvd_right u w).trans ⟨p^k, by ring⟩)

/-- The gcd of `p^i u` and `p^j w` for `p ∤ u w`. -/
lemma gcd_pow_mul (p i j u w : ℕ) (hp : p.Prime) (hu : ¬ p ∣ u) (hw : ¬ p ∣ w) :
    (p^i * u).gcd (p^j * w) = p^(min i j) * u.gcd w := by
  rcases le_total i j with hij | hji
  · have hmin : min i j = i := min_eq_left hij
    have h1 : p^j * w = p^i * (p^(j-i) * w) := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hij]
    rw [hmin, h1, Nat.gcd_mul_left]
    congr 1
    exact gcd_mul_coprime_pow p (j-i) u w hp hu
  · have hmin : min i j = j := min_eq_right hji
    have h1 : p^i * u = p^j * (p^(i-j) * u) := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hji]
    rw [hmin, h1, Nat.gcd_mul_left]
    rw [Nat.gcd_comm (p^(i-j)*u) w, gcd_mul_coprime_pow p (i-j) w u hp hw, Nat.gcd_comm w u]

/-- If `r` and `p` are primes and `r ∣ p^k` then `r = p`. -/
lemma prime_dvd_pow_eq (p r k : ℕ) (hp : p.Prime) (hr : r.Prime) (h : r ∣ p^k) : r = p := by
  rcases hp.eq_one_or_self_of_dvd r (hr.dvd_of_dvd_pow h) with h1 | h1
  · exact absurd h1 hr.ne_one
  · exact h1

/-- Transfer of the "large primes" set under the reduction. -/
lemma Qset_red_subset (t : ℝ) (p i j u w : ℕ) (hp : p.Prime) (hu : ¬ p ∣ u) (hw : ¬ p ∣ w)
    (hu0 : u ≠ 0) (hw0 : w ≠ 0) :
    Qset t (p^i*u) (p^j*w) ⊆ Qset t u w ∪ {p} := by
  intro r hr
  simp only [Qset, Finset.mem_filter, Finset.mem_union, Finset.mem_singleton] at hr ⊢
  obtain ⟨hrpf, hrt⟩ := hr
  rw [Nat.mem_primeFactors] at hrpf
  obtain ⟨hrp, hrdvd, -⟩ := hrpf
  by_cases hreq : r = p
  · exact Or.inr hreq
  refine Or.inl ⟨?_, hrt⟩
  rw [Nat.mem_primeFactors]
  set g := (p^i*u).gcd (p^j*w) with hg
  set g' := u.gcd w with hg'
  have hg_eq : g = p^(min i j) * g' := gcd_pow_mul p i j u w hp hu hw
  have h1 : g ∣ p^i*u := Nat.gcd_dvd_left _ _
  have h2 : g ∣ p^j*w := Nat.gcd_dvd_right _ _
  have hsplit : (p^i*u) * (p^j*w) / (g*g) = ((p^i*u)/g) * ((p^j*w)/g) :=
    (Nat.div_mul_div_comm h1 h2).symm
  rw [hsplit] at hrdvd
  have hvd : (p^i*u)/g = p^(i - min i j) * (u/g') := by
    have h3 : p^i / p^(min i j) * (u / g') = (p^i*u)/(p^(min i j) * g') :=
      Nat.div_mul_div_comm (pow_dvd_pow p (min_le_left i j)) (Nat.gcd_dvd_left u w)
    rw [← hg_eq] at h3
    rw [← h3, Nat.pow_div (min_le_left i j) hp.pos]
  have hwd : (p^j*w)/g = p^(j - min i j) * (w/g') := by
    have h4 : p^j / p^(min i j) * (w / g') = (p^j*w)/(p^(min i j) * g') :=
      Nat.div_mul_div_comm (pow_dvd_pow p (min_le_right i j)) (Nat.gcd_dvd_right u w)
    rw [← hg_eq] at h4
    rw [← h4, Nat.pow_div (min_le_right i j) hp.pos]
  rw [hvd, hwd] at hrdvd
  have hgoal : r ∣ (u/g') * (w/g') := by
    rcases (Nat.Prime.dvd_mul hrp).mp hrdvd with h | h
    · rcases (Nat.Prime.dvd_mul hrp).mp h with h' | h'
      · exact absurd (prime_dvd_pow_eq p r (i - min i j) hp hrp h') hreq
      · obtain ⟨k, hk⟩ := h'
        exact ⟨k * (w/g'), by rw [hk]; ring⟩
    · rcases (Nat.Prime.dvd_mul hrp).mp h with h' | h'
      · exact absurd (prime_dvd_pow_eq p r (j - min i j) hp hrp h') hreq
      · obtain ⟨k, hk⟩ := h'
        exact ⟨k * (u/g'), by rw [hk]; ring⟩
  rw [Nat.div_mul_div_comm (Nat.gcd_dvd_left u w) (Nat.gcd_dvd_right u w)] at hgoal
  have hg'pos : 0 < g' := Nat.gcd_pos_of_pos_left w (Nat.pos_of_ne_zero hu0)
  have hg'2dvd : g' * g' ∣ u * w := Nat.mul_dvd_mul (Nat.gcd_dvd_left u w) (Nat.gcd_dvd_right u w)
  have hpos : 0 < u * w := Nat.mul_pos (Nat.pos_of_ne_zero hu0) (Nat.pos_of_ne_zero hw0)
  have hle : g' * g' ≤ u * w := Nat.le_of_dvd hpos hg'2dvd
  exact ⟨hrp, hgoal, ne_of_gt (Nat.div_pos hle (by positivity))⟩

/-! ## Stage 4b: mass and pair-mass relations under the reduction -/

lemma mass_ared (p i j : ℕ) (hp : p.Prime) (a : ℕ → ℝ) (V : Finset ℕ) :
    mass (ared p i j a) (Vred p i V)
      = ((p:ℝ)^(i + j - min i j) / ((p^i).totient : ℝ)) * mass a (Vval p i V) := by
  unfold mass Vred
  rw [Finset.sum_image (g := fun v => v / p^i)
    (f := fun u => ared p i j a u) ?_]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    have hv' : v ∈ Vval p i V := by rwa [Vval] at hv
    unfold ared
    rw [if_neg (Vred_not_dvd hp hv'), Nat.mul_div_cancel' (mem_Vval_iff.mp hv').2.1]
    ring
  · intro x hx y hy hxy
    simp only [Vval, Finset.mem_filter, Finset.mem_coe] at hx hy
    have hxy' : x / p^i = y / p^i := hxy
    rw [← Nat.mul_div_cancel' hx.2.1, ← Nat.mul_div_cancel' hy.2.1, hxy']

lemma pairMass_ered (p i j : ℕ) (hp : p.Prime) (a b : ℕ → ℝ) (V W : Finset ℕ) (E : Finset (ℕ × ℕ)) :
    pairMass (ared p i j a) (bred p i j b) (Ered p i j V W E)
      = (((p:ℝ)^(i + j - min i j))^2 / (((p^i).totient:ℝ) * ((p^j).totient:ℝ)))
        * pairMass a b (Eval p i j V W E) := by
  unfold pairMass Ered
  rw [Finset.sum_image (g := fun e : ℕ × ℕ => (e.1 / p^i, e.2 / p^j))
    (f := fun u : ℕ × ℕ => ared p i j a u.1 * bred p i j b u.2) ?_]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Eval, Finset.mem_filter] at he
    obtain ⟨-, h1, h2⟩ := he
    have h1' : e.1 ∈ Vval p i V := by rwa [Vval] at h1
    have h2' : e.2 ∈ Vval p j W := by rwa [Vval] at h2
    unfold ared bred
    rw [if_neg (Vred_not_dvd hp h1'), if_neg (Vred_not_dvd hp h2'),
        Nat.mul_div_cancel' (mem_Vval_iff.mp h1').2.1, Nat.mul_div_cancel' (mem_Vval_iff.mp h2').2.1]
    ring
  · intro x hx y hy hxy
    simp only [Eval, Finset.mem_filter, Finset.mem_coe] at hx hy
    obtain ⟨-, hx1, hx2⟩ := hx
    obtain ⟨-, hy1, hy2⟩ := hy
    simp only [Vval, Finset.mem_filter] at hx1 hx2 hy1 hy2
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨hxy1, hxy2⟩ := hxy
    have e1 : x.1 = y.1 := by
      rw [← Nat.mul_div_cancel' hx1.2.1, ← Nat.mul_div_cancel' hy1.2.1, hxy1]
    have e2 : x.2 = y.2 := by
      rw [← Nat.mul_div_cancel' hx2.2.1, ← Nat.mul_div_cancel' hy2.2.1, hxy2]
    exact Prod.ext e1 e2

/-! ## Stage 4c: transfer of the structural condition -/

/-- `p` does not divide the coprime part of a reduced pair when `i = j`. -/
lemma not_dvd_coprime_part (p u w : ℕ) (hp : p.Prime) (hu : ¬ p ∣ u) (hw : ¬ p ∣ w) :
    ¬ p ∣ u * w / (u.gcd w * u.gcd w) := by
  set g' := u.gcd w with hg'
  have hgu : g' ∣ u := Nat.gcd_dvd_left u w
  have hgw : g' ∣ w := Nat.gcd_dvd_right u w
  have hsplit : u * w / (g' * g') = (u / g') * (w / g') :=
    (Nat.div_mul_div_comm hgu hgw).symm
  rw [hsplit]
  intro hcon
  rcases (Nat.Prime.dvd_mul hp).mp hcon with h | h
  · obtain ⟨k, hk⟩ := h
    refine hu ⟨g' * k, ?_⟩
    calc u = g' * (u / g') := (Nat.mul_div_cancel' hgu).symm
      _ = g' * (p * k) := by rw [hk]
      _ = p * (g' * k) := by ring
  · obtain ⟨k, hk⟩ := h
    refine hw ⟨g' * k, ?_⟩
    calc w = g' * (w / g') := (Nat.mul_div_cancel' hgw).symm
      _ = g' * (p * k) := by rw [hk]
      _ = p * (g' * k) := by ring

/-- The `Qset` sum over a reduced pair is at most the `Qset` sum of the reduced pair plus the
correction term. -/
lemma Qset_red_sum_le (t : ℝ) (p i j u w : ℕ) (hp : p.Prime) (ht : 0 < t)
    (hu : ¬ p ∣ u) (hw : ¬ p ∣ w) (hu0 : u ≠ 0) (hw0 : w ≠ 0) :
    ∑ r ∈ Qset t (p^i*u) (p^j*w), 1/(r:ℝ)
      ≤ (∑ r ∈ Qset t u w, 1/(r:ℝ)) + (if i = j then 0 else 1/t) := by
  set B := Qset t u w with hB
  set A := Qset t (p^i*u) (p^j*w) with hA
  have hsub := Qset_red_subset t p i j u w hp hu hw hu0 hw0
  by_cases hpA : p ∈ A
  · have htp : t ≤ (p:ℝ) := by
      have h := hpA; rw [hA, Qset, Finset.mem_filter] at h; exact h.2
    have hinj : i ≠ j := by
      rintro rfl
      have h1 : (p^i*u) * (p^i*w) / ((p^i*u).gcd (p^i*w) * (p^i*u).gcd (p^i*w))
          = u*w/(u.gcd w * u.gcd w) := by
        rw [gcd_pow_mul p i i u w hp hu hw, min_self]
        rw [show p^i * u.gcd w * (p^i * u.gcd w) = p^(2*i) * (u.gcd w * u.gcd w) by
              rw [show 2*i = i+i by ring, pow_add]; ring,
            show (p^i*u)*(p^i*w) = p^(2*i) * (u*w) by
              rw [show 2*i = i+i by ring, pow_add]; ring]
        exact Nat.mul_div_mul_left _ _ (pow_pos hp.pos _)
      have h2 := hpA
      rw [hA, Qset, Finset.mem_filter, Nat.mem_primeFactors, h1] at h2
      exact not_dvd_coprime_part p u w hp hu hw h2.1.2.1
    have h1 : ∑ r ∈ A, 1/(r:ℝ) ≤ ∑ r ∈ B ∪ {p}, 1/(r:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => by positivity)
    have h2 : ∑ r ∈ B ∪ {p}, 1/(r:ℝ) ≤ (∑ r ∈ B, 1/(r:ℝ)) + 1/(p:ℝ) := by
      rw [show B ∪ {p} = B ∪ ({p} \ B) by
        ext r; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]; tauto]
      rw [Finset.sum_union (Finset.disjoint_sdiff)]
      have h3 : ∑ r ∈ ({p} : Finset ℕ) \ B, 1/(r:ℝ) ≤ 1/(p:ℝ) := by
        calc ∑ r ∈ ({p} : Finset ℕ) \ B, 1/(r:ℝ)
            ≤ ∑ r ∈ ({p} : Finset ℕ), 1/(r:ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun r _ _ => by positivity)
          _ = 1/(p:ℝ) := Finset.sum_singleton _ _
      linarith
    have h3 : 1/(p:ℝ) ≤ 1/t := one_div_le_one_div_of_le ht htp
    have h4 : (if i = j then 0 else 1/t) = 1/t := if_neg hinj
    rw [h4]; linarith
  · have hsub' : A ⊆ B := by
      intro r hr
      rcases Finset.mem_union.mp (hsub hr) with h | h
      · exact h
      · rw [Finset.mem_singleton] at h
        exact absurd (h ▸ hr) hpA
    have h1 : ∑ r ∈ A, 1/(r:ℝ) ≤ ∑ r ∈ B, 1/(r:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub' (fun r _ _ => by positivity)
    have h2 : (0:ℝ) ≤ (if i = j then 0 else 1/t) := by
      split_ifs with h
      · exact le_rfl
      · exact div_nonneg zero_le_one ht.le
    linarith

/-- The reduced pair satisfies the structural condition (with the correction `-1_{i≠j}/t`). -/
lemma good_ered (p i j : ℕ) (a b : ℕ → ℝ) (t C : ℝ) (u w : ℕ)
    (hp : p.Prime) (ht : 0 < t) (hu : ¬ p ∣ u) (hw : ¬ p ∣ w)
    (hu0 : u ≠ 0) (hw0 : w ≠ 0)
    (hgood : good t C a b (p^i*u) (p^j*w)) :
    good t (C - (if i = j then 0 else 1/t)) (ared p i j a) (bred p i j b) u w := by
  obtain ⟨hD, hL⟩ := hgood
  have hppos : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hcop : (p^i).Coprime u := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu).pow_left i
  have hcop2 : (p^j).Coprime w := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hw).pow_left j
  have hphi : ((p^i*u).totient : ℝ) = ((p^i).totient : ℝ) * (u.totient : ℝ) := by
    rw [Nat.totient_mul hcop]; push_cast; ring
  have hphi2 : ((p^j*w).totient : ℝ) = ((p^j).totient : ℝ) * (w.totient : ℝ) := by
    rw [Nat.totient_mul hcop2]; push_cast; ring
  have hnei : ((p^i).totient : ℝ) ≠ 0 := by
    have : 0 < (p^i).totient := Nat.totient_pos.mpr (pow_pos hp.pos i); positivity
  have hnej : ((p^j).totient : ℝ) ≠ 0 := by
    have : 0 < (p^j).totient := Nat.totient_pos.mpr (pow_pos hp.pos j); positivity
  have hneu : (u.totient : ℝ) ≠ 0 := by
    have : 0 < u.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hu0); positivity
  have hnew : (w.totient : ℝ) ≠ 0 := by
    have : 0 < w.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hw0); positivity
  have heqA : ared p i j a u / (u.totient:ℝ)
      = (p:ℝ)^(i + j - min i j) * (a (p^i*u) / ((p^i*u).totient : ℝ)) := by
    unfold ared
    rw [if_neg hu, hphi]
    field_simp
  have heqB : bred p i j b w / (w.totient:ℝ)
      = (p:ℝ)^(i + j - min i j) * (b (p^j*w) / ((p^j*w).totient : ℝ)) := by
    unfold bred
    rw [if_neg hw, hphi2]
    field_simp
  constructor
  · have hmax : max (a (p^i*u) / ((p^i*u).totient:ℝ)) (b (p^j*w) / ((p^j*w).totient:ℝ))
        ≤ (↑((p^i*u).gcd (p^j*w))) / ((↑(p^i*u)) * (↑(p^j*w))) := by
      have hpos1 : (0:ℝ) < (↑(p^i*u) : ℝ) := by
        have h : 0 < p^i * u := Nat.mul_pos (pow_pos hp.pos i) (Nat.pos_of_ne_zero hu0)
        exact_mod_cast h
      have hpos2 : (0:ℝ) < (↑(p^j*w) : ℝ) := by
        have h : 0 < p^j * w := Nat.mul_pos (pow_pos hp.pos j) (Nat.pos_of_ne_zero hw0)
        exact_mod_cast h
      rw [le_div_iff₀ (mul_pos hpos1 hpos2)]
      linarith [hD]
    calc (u:ℝ)*(w:ℝ)*max (ared p i j a u/(u.totient:ℝ)) (bred p i j b w/(w.totient:ℝ))
        = (u:ℝ)*(w:ℝ)*(p:ℝ)^(i + j - min i j)
            * max (a (p^i*u) / ((p^i*u).totient:ℝ)) (b (p^j*w) / ((p^j*w).totient:ℝ)) := by
          rw [heqA, heqB]
          rcases le_total (a (p^i*u) / ((p^i*u).totient:ℝ)) (b (p^j*w) / ((p^j*w).totient:ℝ)) with h | h
          · rw [max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_left h (by positivity))]; ring
          · rw [max_eq_left h, max_eq_left (mul_le_mul_of_nonneg_left h (by positivity))]; ring
      _ ≤ (u:ℝ)*(w:ℝ)*(p:ℝ)^(i + j - min i j)
            * ((↑((p^i*u).gcd (p^j*w))) / ((↑(p^i*u)) * (↑(p^j*w)))) :=
          mul_le_mul_of_nonneg_left hmax
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg u) (Nat.cast_nonneg w))
              (pow_nonneg hppos.le _))
      _ = ↑(u.gcd w) := by
          rw [gcd_pow_mul p i j u w hp hu hw]
          push_cast
          rw [← mul_div_assoc, div_eq_iff (by positivity)]
          have hmin : min i j ≤ i + j := by omega
          have hpow : (p:ℝ)^(i + j - min i j) * (p:ℝ)^(min i j) = (p:ℝ)^(i+j) := by
            rw [← pow_add, Nat.sub_add_cancel hmin]
          have hLHS : (↑u * ↑w * (p:ℝ)^(i + j - min i j)) * ((p:ℝ)^(min i j) * ↑(u.gcd w))
              = ↑(u.gcd w) * (p:ℝ)^(i+j) * (↑u * ↑w) := by
            rw [show (↑u * ↑w * (p:ℝ)^(i + j - min i j)) * ((p:ℝ)^(min i j) * ↑(u.gcd w))
                = ↑(u.gcd w) * ((p:ℝ)^(i + j - min i j) * (p:ℝ)^(min i j)) * (↑u * ↑w) by ring,
              hpow]
          rw [hLHS, pow_add]; ring
  · have h := Qset_red_sum_le t p i j u w hp ht hu hw hu0 hw0
    linarith



/-! ## Stage 6: the bilinear bound -/

/-- The `good` condition transfers to the reduced instance. -/
lemma Ered_good (a b : ℕ → ℝ) (t C : ℝ) (E : Finset (ℕ × ℕ))
    (hp : p.Prime) (ht : 0 < t)
    (hgood : ∀ e ∈ E, good t C a b e.1 e.2) :
    ∀ e' ∈ Ered p i j V W E, good t (C - (if i = j then 0 else 1/t)) (ared p i j a) (bred p i j b) e'.1 e'.2 := by
  intro e' he'
  rw [Ered, Finset.mem_image] at he'
  obtain ⟨e, he, rfl⟩ := he'
  rw [Eval, Finset.mem_filter] at he
  obtain ⟨heE, he1, he2⟩ := he
  have hu : p^i * (e.1 / p^i) = e.1 := Nat.mul_div_cancel' (mem_Vval_iff.mp he1).2.1
  have hw : p^j * (e.2 / p^j) = e.2 := Nat.mul_div_cancel' (mem_Vval_iff.mp he2).2.1
  have hu0 : e.1 / p^i ≠ 0 := by
    have := Vred_ge_one hp he1; omega
  have hw0 : e.2 / p^j ≠ 0 := by
    have := Vred_ge_one hp he2; omega
  have h := good_ered p i j a b t C (e.1 / p^i) (e.2 / p^j) hp ht
    (Vred_not_dvd hp he1) (Vred_not_dvd hp he2) hu0 hw0
    (by rw [hu, hw]; exact hgood e heE)
  exact h
/-! ## Stage 7: partition lemmas -/

lemma Vval_biUnion (hp : p.Prime) (V : Finset ℕ) (hV : ∀ v ∈ V, 1 ≤ v) (N : ℕ)
    (hN : ∀ v ∈ V, v ≤ N) :
    V = (Finset.range (N+1)).biUnion (fun i => Vval p i V) := by
  haveI : Fact p.Prime := ⟨hp⟩
  ext v
  constructor
  · intro hv
    refine Finset.mem_biUnion.mpr ⟨padicValNat p v, ?_, ?_⟩
    · rw [Finset.mem_range]
      have hpos : 0 < v := lt_of_lt_of_le Nat.zero_lt_one (hV v hv)
      have h2 : 2 ^ padicValNat p v ≤ v := by
        calc 2 ^ padicValNat p v ≤ p ^ padicValNat p v := Nat.pow_le_pow_left hp.two_le _
          _ ≤ v := Nat.le_of_dvd hpos pow_padicValNat_dvd
      have h3 : padicValNat p v < 2 ^ padicValNat p v := Nat.lt_two_pow_self
      have hvN : v ≤ N := hN v hv
      omega
    · rw [mem_Vval_iff]
      refine ⟨hv, pow_padicValNat_dvd, fun h => ?_⟩
      have hpos : 0 < v := lt_of_lt_of_le Nat.zero_lt_one (hV v hv)
      have h2 := (padicValNat_dvd_iff_le (Nat.pos_iff_ne_zero.mp hpos)).mp h
      omega
  · intro hv
    obtain ⟨i, -, hvi⟩ := Finset.mem_biUnion.mp hv
    exact (mem_Vval_iff.mp hvi).1

lemma Vval_pairwiseDisjoint (hp : p.Prime) (V : Finset ℕ) (N : ℕ) :
    (↑(Finset.range (N+1)) : Set ℕ).PairwiseDisjoint (fun i => Vval p i V) := by
  intro x _ y _ hxy
  rw [Function.onFun, Finset.disjoint_left]
  intro v hvx hvy
  exact hxy (Vval_unique hp (mem_Vval_iff.mp hvx).2.1 (mem_Vval_iff.mp hvx).2.2
    (mem_Vval_iff.mp hvy).2.1 (mem_Vval_iff.mp hvy).2.2)

lemma mass_biUnion (hp : p.Prime) (a : ℕ → ℝ) (V : Finset ℕ) (hV : ∀ v ∈ V, 1 ≤ v) (N : ℕ)
    (hN : ∀ v ∈ V, v ≤ N) :
    mass a V = ∑ i ∈ Finset.range (N+1), mass a (Vval p i V) := by
  unfold mass
  conv_lhs => rw [Vval_biUnion hp V hV N hN]
  exact Finset.sum_biUnion (Vval_pairwiseDisjoint hp V N)

lemma Eval_biUnion (hp : p.Prime) (V W : Finset ℕ) (hV : ∀ v ∈ V, 1 ≤ v) (hW : ∀ w ∈ W, 1 ≤ w)
    (E : Finset (ℕ × ℕ)) (hE : E ⊆ V.product W) (N : ℕ)
    (hVN : ∀ v ∈ V, v ≤ N) (hWN : ∀ w ∈ W, w ≤ N) :
    E = ((Finset.range (N+1)).product (Finset.range (N+1))).biUnion
        (fun ij : ℕ × ℕ => Eval p ij.1 ij.2 V W E) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmem : ∀ (v : ℕ) (hpos : 0 < v), padicValNat p v < v := by
    intro v hpos
    have h2 : 2 ^ padicValNat p v ≤ v := by
      calc 2 ^ padicValNat p v ≤ p ^ padicValNat p v :=
            Nat.pow_le_pow_left hp.two_le _
        _ ≤ v := Nat.le_of_dvd hpos pow_padicValNat_dvd
    have h3 : padicValNat p v < 2 ^ padicValNat p v := Nat.lt_two_pow_self
    omega
  have hval : ∀ (S : Finset ℕ) (v : ℕ) (hpos : 0 < v), v ∈ Vval p (padicValNat p v) S ↔ v ∈ S := by
    intro S v hpos
    rw [mem_Vval_iff]
    constructor
    · exact fun h => h.1
    · intro hv
      refine ⟨hv, pow_padicValNat_dvd, fun h => ?_⟩
      have h2 := (padicValNat_dvd_iff_le (Nat.pos_iff_ne_zero.mp hpos)).mp h
      omega
  ext e
  constructor
  · intro he
    have heV : e.1 ∈ V := (Finset.mem_product.mp (hE he)).1
    have heW : e.2 ∈ W := (Finset.mem_product.mp (hE he)).2
    have hpos1 : 0 < e.1 := lt_of_lt_of_le Nat.zero_lt_one (hV e.1 heV)
    have hpos2 : 0 < e.2 := lt_of_lt_of_le Nat.zero_lt_one (hW e.2 heW)
    refine Finset.mem_biUnion.mpr ⟨(padicValNat p e.1, padicValNat p e.2), ?_, ?_⟩
    · refine Finset.mem_product.mpr ⟨?_, ?_⟩ <;> rw [Finset.mem_range]
      · have := hmem e.1 hpos1; have := hVN e.1 heV; omega
      · have := hmem e.2 hpos2; have := hWN e.2 heW; omega
    · rw [Eval, Finset.mem_filter]
      exact ⟨he, (hval V e.1 hpos1).mpr heV, (hval W e.2 hpos2).mpr heW⟩
  · intro he
    obtain ⟨ij, -, hij⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_filter.mp hij).1

lemma Eval_pairwiseDisjoint (hp : p.Prime) (V W : Finset ℕ) (E : Finset (ℕ × ℕ)) (N : ℕ) :
    (↑(((Finset.range (N+1)).product (Finset.range (N+1)))) : Set (ℕ × ℕ)).PairwiseDisjoint
      (fun ij : ℕ × ℕ => Eval p ij.1 ij.2 V W E) := by
  intro x _ y _ hxy
  rw [Function.onFun, Finset.disjoint_left]
  intro e hex hey
  rw [Eval, Finset.mem_filter] at hex hey
  have h1 := Vval_unique hp (mem_Vval_iff.mp hex.2.1).2.1 (mem_Vval_iff.mp hex.2.1).2.2
    (mem_Vval_iff.mp hey.2.1).2.1 (mem_Vval_iff.mp hey.2.1).2.2
  have h2 := Vval_unique hp (mem_Vval_iff.mp hex.2.2).2.1 (mem_Vval_iff.mp hex.2.2).2.2
    (mem_Vval_iff.mp hey.2.2).2.1 (mem_Vval_iff.mp hey.2.2).2.2
  exact hxy (Prod.ext h1 h2)

lemma pairMass_biUnion (hp : p.Prime) (a b : ℕ → ℝ) (V W : Finset ℕ)
    (hV : ∀ v ∈ V, 1 ≤ v) (hW : ∀ w ∈ W, 1 ≤ w)
    (E : Finset (ℕ × ℕ)) (hE : E ⊆ V.product W) (N : ℕ)
    (hVN : ∀ v ∈ V, v ≤ N) (hWN : ∀ w ∈ W, w ≤ N) :
    pairMass a b E = ∑ ij ∈ (Finset.range (N+1)).product (Finset.range (N+1)),
      pairMass a b (Eval p ij.1 ij.2 V W E) := by
  unfold pairMass
  conv_lhs => rw [Eval_biUnion hp V W hV hW E hE N hVN hWN]
  exact Finset.sum_biUnion (Eval_pairwiseDisjoint hp V W E N)

/-! ## Stage 9: the resolving proposition (HWVS §5) -/

/-- The "minus" part of `v` relative to `N`: primes where `v` is one power below `N`. -/
def vminus (N v : ℕ) : ℕ :=
  ∏ p ∈ (Nat.primeFactors N).filter (fun p => padicValNat p N = padicValNat p v + 1), p

/-- The "plus" part of `v` relative to `N`: primes where `v` is one power above `N`. -/
def vplus (N v : ℕ) : ℕ :=
  ∏ p ∈ (Nat.primeFactors v).filter (fun p => padicValNat p v = padicValNat p N + 1), p

/-- The `w`-neighbourhood of `v` in `E`. -/
def nhoodFst (E : Finset (ℕ × ℕ)) (v : ℕ) : Finset ℕ :=
  (E.filter (fun e => e.1 = v)).image Prod.snd

/-- The `v`-neighbourhood of `w` in `E`. -/
def nhoodSnd (E : Finset (ℕ × ℕ)) (w : ℕ) : Finset ℕ :=
  (E.filter (fun e => e.2 = w)).image Prod.fst

/-- The arithmetic structure of an edge set (HWVS property (3)). -/
def structured (E : Finset (ℕ × ℕ)) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ e ∈ E, ∀ p : ℕ, p.Prime →
    |((padicValNat p e.1 : ℤ) - (padicValNat p N : ℤ))|
      + |((padicValNat p e.2 : ℤ) - (padicValNat p N : ℤ))| ≤ 1

/-- The one-sided regularity of an edge set (HWVS property (2)). -/
def regular (a b : ℕ → ℝ) (E : Finset (ℕ × ℕ)) : Prop :=
  (∀ v ∈ E.image Prod.fst,
    (3/5) * pairMass a b E ≤ mass a (E.image Prod.fst) * ∑ w ∈ nhoodFst E v, b w) ∧
  (∀ w ∈ E.image Prod.snd,
    (3/5) * pairMass a b E ≤ mass b (E.image Prod.snd) * ∑ v ∈ nhoodSnd E w, a v)

/-- The fundamental bound on the weight `a v` coming from the `gcd` condition and the
arithmetic structure. -/
lemma good_le_phi (N : ℕ) (hN : 0 < N) (a b : ℕ → ℝ) (t C : ℝ) (v w : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (hstruct : ∀ p : ℕ, p.Prime →
      |((padicValNat p v : ℤ) - (padicValNat p N : ℤ))|
        + |((padicValNat p w : ℤ) - (padicValNat p N : ℤ))| ≤ 1)
    (hgood : good t C a b v w) :
    a v ≤ (v.totient : ℝ) / ((v:ℝ) * (vminus N v) * (vplus N w)) := by
  obtain ⟨hD, -⟩ := hgood
  have h1 : ((v.gcd w : ℕ) : ℝ) * (vminus N v) * (vplus N w) = (w : ℝ) := by
    exact_mod_cast gcd_ratio_decomp N v w hN hv hw hstruct
  have hphi : (0:ℝ) < (v.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hv
  have hvm : 0 < vminus N v := by
    unfold vminus
    exact Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr (fun p hp => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1.ne_zero))
  have hwp : 0 < vplus N w := by
    unfold vplus
    exact Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr (fun p hp => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1.ne_zero))
  have hD' : (v:ℝ) * (w:ℝ) * (a v / (v.totient : ℝ))
      ≤ (v.gcd w : ℕ) := by
    have := hD
    have h2 : (v:ℝ) * (w:ℝ) * max (a v / (v.totient:ℝ)) (b w / (w.totient:ℝ))
        ≥ (v:ℝ) * (w:ℝ) * (a v / (v.totient:ℝ)) := by
      apply mul_le_mul_of_nonneg_left (le_max_left _ _)
      positivity
    linarith [this, h2]
  have h2 : a v / (v.totient : ℝ) ≤ ((v.gcd w : ℕ) : ℝ) / ((v:ℝ) * (w:ℝ)) := by
    have h3 : a v * ((v:ℝ)*(w:ℝ)) ≤ ((v.gcd w:ℕ):ℝ) * (v.totient:ℝ) := by
      have h5 := hD'
      rw [← mul_div_assoc] at h5
      rw [div_le_iff₀ hphi] at h5
      linarith [h5]
    calc a v / (v.totient : ℝ)
        = a v * ((v:ℝ)*(w:ℝ)) / ((v.totient:ℝ) * ((v:ℝ)*(w:ℝ))) := by field_simp
      _ ≤ ((v.gcd w:ℕ):ℝ) * (v.totient:ℝ) / ((v.totient:ℝ) * ((v:ℝ)*(w:ℝ))) :=
          div_le_div_of_nonneg_right h3 (by positivity)
      _ = ((v.gcd w:ℕ):ℝ) / ((v:ℝ)*(w:ℝ)) := by field_simp
  calc a v = (v.totient : ℝ) * (a v / (v.totient : ℝ)) := by field_simp
    _ ≤ (v.totient : ℝ) * (((v.gcd w : ℕ) : ℝ) / ((v:ℝ) * (w:ℝ))) :=
        mul_le_mul_of_nonneg_left h2 hphi.le
    _ = (v.totient : ℝ) / ((v:ℝ) * (vminus N v) * (vplus N w)) := by
        rw [← h1]; field_simp

lemma mass_nonneg (a : ℕ → ℝ) (ha : ∀ v, 0 ≤ a v) (V : Finset ℕ) : 0 ≤ mass a V :=
  Finset.sum_nonneg (fun v _ => ha v)

lemma pairMass_nonneg (a b : ℕ → ℝ) (ha : ∀ v, 0 ≤ a v) (hb : ∀ w, 0 ≤ b w)
    (E : Finset (ℕ × ℕ)) : 0 ≤ pairMass a b E :=
  Finset.sum_nonneg (fun e _ => mul_nonneg (ha e.1) (hb e.2))

/-- The algebraic core of the half bound: the regularity (property (2)) turns the total mass
into a bound involving the neighbourhood sum at a single `w₀`. -/
lemma half_bound_algebra (a b : ℕ → ℝ) (E : Finset (ℕ × ℕ)) (w0 : ℕ)
    (ha0 : ∀ v, 0 ≤ a v) (hb0 : ∀ w, 0 ≤ b w)
    (hw0 : w0 ∈ E.image Prod.snd)
    (hreg : regular a b E) :
    (pairMass a b E)^2 ≤ (25/9) * (mass a (E.image Prod.fst)) * (mass b (E.image Prod.snd))
      * ∑ v ∈ nhoodSnd E w0, a v * ∑ w ∈ nhoodFst E v, b w := by
  obtain ⟨hreg1, hreg2⟩ := hreg
  have hV : (0:ℝ) ≤ mass a (E.image Prod.fst) := mass_nonneg a ha0 _
  have hW : (0:ℝ) ≤ mass b (E.image Prod.snd) := mass_nonneg b hb0 _
  have hmem : ∀ v ∈ nhoodSnd E w0, v ∈ E.image Prod.fst := by
    intro v hv
    rw [nhoodSnd, Finset.mem_image] at hv
    obtain ⟨e, he, rfl⟩ := hv
    exact Finset.mem_image.mpr ⟨e, (Finset.mem_filter.mp he).1, rfl⟩
  have step1 : (3/5) * pairMass a b E * (∑ v ∈ nhoodSnd E w0, a v)
      ≤ mass a (E.image Prod.fst)
        * (∑ v ∈ nhoodSnd E w0, a v * ∑ w ∈ nhoodFst E v, b w) := by
    calc (3/5) * pairMass a b E * (∑ v ∈ nhoodSnd E w0, a v)
        = ∑ v ∈ nhoodSnd E w0, ((3/5) * pairMass a b E) * a v := by
          rw [Finset.mul_sum]
      _ ≤ ∑ v ∈ nhoodSnd E w0, (mass a (E.image Prod.fst) * ∑ w ∈ nhoodFst E v, b w) * a v := by
          apply Finset.sum_le_sum; intro v hv
          exact mul_le_mul_of_nonneg_right (hreg1 v (hmem v hv)) (ha0 v)
      _ = mass a (E.image Prod.fst)
            * (∑ v ∈ nhoodSnd E w0, a v * ∑ w ∈ nhoodFst E v, b w) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro v _; ring
  have step2 : (3/5) * pairMass a b E
      ≤ mass b (E.image Prod.snd) * ∑ v ∈ nhoodSnd E w0, a v := hreg2 w0 hw0
  have h1 : (3/5) * pairMass a b E * ((3/5) * pairMass a b E)
      ≤ (3/5) * pairMass a b E
        * (mass b (E.image Prod.snd) * ∑ v ∈ nhoodSnd E w0, a v) :=
    mul_le_mul_of_nonneg_left step2 (by
      have := pairMass_nonneg a b ha0 hb0 E; linarith)
  have h2 : (3/5) * pairMass a b E * (mass b (E.image Prod.snd) * ∑ v ∈ nhoodSnd E w0, a v)
      = mass b (E.image Prod.snd)
        * ((3/5) * pairMass a b E * ∑ v ∈ nhoodSnd E w0, a v) := by ring
  rw [h2] at h1
  have h3 : mass b (E.image Prod.snd)
        * ((3/5) * pairMass a b E * ∑ v ∈ nhoodSnd E w0, a v)
      ≤ mass b (E.image Prod.snd)
        * (mass a (E.image Prod.fst)
          * (∑ v ∈ nhoodSnd E w0, a v * ∑ w ∈ nhoodFst E v, b w)) :=
    mul_le_mul_of_nonneg_left step1 hW
  have h4 : (3/5) * pairMass a b E * ((3/5) * pairMass a b E)
      = (9/25) * (pairMass a b E)^2 := by ring
  rw [h4] at h1
  nlinarith [h1.trans h3]

/-- `φ(am)/(am) ≤ φ(m)/m`, i.e. `φ(am) ≤ a·φ(m)`. -/
lemma totient_div_le (a m : ℕ) (ha : 0 < a) (hm : 0 < m) :
    ((a*m).totient : ℝ) / ((a*m : ℕ) : ℝ) ≤ (m.totient : ℝ) / (m : ℝ) := by
  have hfac2 : ∀ p ∈ a.primeFactors ∪ m.primeFactors, 2 ≤ p := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Nat.prime_of_mem_primeFactors hp).two_le
    · exact (Nat.prime_of_mem_primeFactors hp).two_le
  rw [totient_div_self_eq_prod_real (a*m) (by positivity),
      totient_div_self_eq_prod_real m hm.ne', Nat.primeFactors_mul ha.ne' hm.ne']
  have hsplit : ∏ p ∈ a.primeFactors ∪ m.primeFactors, (1 - 1 / (p:ℝ))
      = (∏ p ∈ (a.primeFactors ∪ m.primeFactors) \ m.primeFactors, (1 - 1 / (p:ℝ)))
        * ∏ p ∈ m.primeFactors, (1 - 1 / (p:ℝ)) := by
    rw [Finset.prod_sdiff (s₁ := m.primeFactors) (s₂ := a.primeFactors ∪ m.primeFactors)
      (Finset.subset_union_right (s₁ := a.primeFactors) (s₂ := m.primeFactors))]
  rw [hsplit]
  have hbnd : ∀ p ∈ a.primeFactors ∪ m.primeFactors,
      (0:ℝ) ≤ (1 - 1 / (p:ℝ)) ∧ (1 - 1 / (p:ℝ)) ≤ 1 := by
    intro p hp
    have hp2 : 2 ≤ p := hfac2 p hp
    have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hp2)
    have hpos : (0:ℝ) < (p:ℝ) := by linarith
    have hle : 1 / (p:ℝ) ≤ 1 := by
      rw [one_div]
      exact inv_le_one_of_one_le₀ hp1
    have h0 : (0:ℝ) ≤ 1 / (p:ℝ) := by positivity
    exact ⟨by linarith, by linarith⟩
  have h1 : ∏ p ∈ (a.primeFactors ∪ m.primeFactors) \ m.primeFactors, (1 - 1 / (p:ℝ)) ≤ 1 :=
    Finset.prod_le_one₀ (fun p hp => (hbnd p (Finset.mem_sdiff.mp hp).1).1)
      (fun p hp => (hbnd p (Finset.mem_sdiff.mp hp).1).2)
  have hnn2 : (0:ℝ) ≤ ∏ p ∈ m.primeFactors, (1 - 1 / (p:ℝ)) := by
    apply Finset.prod_nonneg
    intro p hp
    exact (hbnd p (Finset.mem_union_right _ hp)).1
  calc (∏ p ∈ (a.primeFactors ∪ m.primeFactors) \ m.primeFactors, (1 - 1 / (p:ℝ)))
        * ∏ p ∈ m.primeFactors, (1 - 1 / (p:ℝ))
      ≤ 1 * ∏ p ∈ m.primeFactors, (1 - 1 / (p:ℝ)) := mul_le_mul_of_nonneg_right h1 hnn2
    _ = ∏ p ∈ m.primeFactors, (1 - 1 / (p:ℝ)) := one_mul _

-- =====================   from DS/prelim.lean  =====================
lemma totient_le_mul_totient (a m : ℕ) (hm : 0 < m) :
    ((a * m).totient : ℝ) ≤ (a : ℝ) * (m.totient : ℝ) := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp [Nat.totient_zero]
  have h := totient_div_le a m ha hm
  have hpos : (0:ℝ) < ((a*m : ℕ) : ℝ) := by
    have : 0 < a * m := Nat.mul_pos ha hm
    exact_mod_cast this
  have h1 : ((a*m).totient : ℝ) ≤ ((m.totient : ℝ) / (m:ℝ)) * ((a*m : ℕ):ℝ) :=
    (div_le_iff₀ hpos).mp h
  have hm' : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  rw [Nat.cast_mul] at h1
  calc ((a * m).totient : ℝ)
      ≤ ((m.totient : ℝ) / (m:ℝ)) * ((a:ℝ)*(m:ℝ)) := h1
    _ = (a:ℝ) * (m.totient : ℝ) := by field_simp

lemma vminus_pos (N v : ℕ) : 0 < vminus N v := by
  unfold vminus
  exact Finset.prod_pos (fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)).pos)

lemma vplus_pos (N v : ℕ) : 0 < vplus N v := by
  unfold vplus
  exact Finset.prod_pos (fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)).pos)

lemma vminus_dvd (N v : ℕ) : vminus N v ∣ N := by
  unfold vminus
  exact (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans
    (Nat.prod_primeFactors_dvd N)

lemma phi_div_vminus_le (N v : ℕ) (hN : 0 < N) (hv : 0 < v)
    (hupper : ∀ p : ℕ, p.Prime → padicValNat p v ≤ padicValNat p N + 1)
    (hlower : ∀ p : ℕ, p.Prime → padicValNat p N ≤ padicValNat p v + 1) :
    (v.totient : ℝ) / ((v:ℝ) * (vminus N v)) ≤ ((N / vminus N v).totient : ℝ) / (N:ℝ) := by
  have hdvd : vminus N v ∣ N := vminus_dvd N v
  have hvpos : 0 < vminus N v := vminus_pos N v
  have h2 : v * vminus N v = vplus N v * N := padic_ratio_decomp N v hN hv hupper hlower
  have hdecomp : v = vplus N v * (N / vminus N v) := by
    have h2' : vplus N v * (N / vminus N v) * vminus N v = vplus N v * N := by
      rw [mul_assoc, Nat.div_mul_cancel hdvd]
    exact Nat.eq_of_mul_eq_mul_right hvpos (by rw [h2']; exact h2)
  have hdvpos : 0 < N / vminus N v := Nat.div_pos (Nat.le_of_dvd hN hdvd) hvpos
  have hv_eq : (v.totient : ℝ) = ((vplus N v * (N / vminus N v)).totient : ℝ) := by
    conv_lhs => rw [hdecomp]
  have h1 : ((vplus N v * (N / vminus N v)).totient : ℝ)
      ≤ (vplus N v : ℝ) * ((N / vminus N v).totient : ℝ) :=
    totient_le_mul_totient (vplus N v) (N / vminus N v) hdvpos
  have h6 : ((v:ℝ) * (vminus N v : ℝ)) = (vplus N v : ℝ) * (N:ℝ) := by
    conv_lhs => rw [← Nat.cast_mul]
    rw [h2, Nat.cast_mul]
  rw [hv_eq, h6]
  have hvppos : (0:ℝ) < (vplus N v : ℝ) := by
    have := vplus_pos N v; exact_mod_cast this
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast hN)]
  nlinarith [h1]


/-- The sum over the divisors `d` of `N` of `φ(N/d)` is `N`. -/
lemma sum_divisors_totient_div (N : ℕ) : ∑ d ∈ N.divisors, (N / d).totient = N := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hinj : Set.InjOn (fun d => N / d) ↑N.divisors := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Nat.mem_divisors] at ha hb
    change N / a = N / b at hab
    have h1 : a = N / (N / a) := (Nat.div_div_self ha.1 ha.2).symm
    have h2 : b = N / (N / b) := (Nat.div_div_self hb.1 hb.2).symm
    rw [h1, h2, hab]
  have himg : N.divisors.image (fun d => N / d) = N.divisors := by
    ext x
    constructor
    · intro hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨Nat.div_dvd_of_dvd hd.1, hd.2⟩
    · intro hx
      rw [Nat.mem_divisors] at hx
      exact Finset.mem_image.mpr ⟨N / x, by rw [Nat.mem_divisors]; exact ⟨Nat.div_dvd_of_dvd hx.1, hx.2⟩,
        Nat.div_div_self hx.1 hx.2⟩
  calc ∑ d ∈ N.divisors, (N / d).totient
      = ∑ x ∈ N.divisors.image (fun d => N / d), x.totient :=
        (Finset.sum_image (f := fun x => x.totient) hinj).symm
    _ = ∑ x ∈ N.divisors, x.totient := by rw [himg]
    _ = N := Nat.sum_totient N

/-- Sum over a union of two finsets. -/
lemma sum_union_le {α : Type*} [DecidableEq α] (s t : Finset α) {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  have hsub : s ∪ t = s ∪ (t \ s) := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  have hd : Disjoint s (t \ s) :=
    Finset.disjoint_left.mpr (fun a ha hb => (Finset.mem_sdiff.mp hb).2 ha)
  rw [hsub, Finset.sum_union hd]
  have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset (s := t) (t := s))
    (fun x hx _ => hf x)
  linarith

/-- Sum over a union of four finsets. -/
lemma sum_union4_le {α : Type*} [DecidableEq α] (s1 s2 s3 s4 : Finset α) {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s1 ∪ s2 ∪ s3 ∪ s4, f x
      ≤ ∑ x ∈ s1, f x + ∑ x ∈ s2, f x + ∑ x ∈ s3, f x + ∑ x ∈ s4, f x := by
  have h := sum_union_le (s1 ∪ s2 ∪ s3) s4 (f := f) hf
  have h2 := sum_union_le (s1 ∪ s2) s3 (f := f) hf
  have h3 := sum_union_le s1 s2 (f := f) hf
  linarith

/-- Sum over a union of four finsets, in the association `s1 ∪ s2 ∪ (s3 ∪ s4)`. -/
lemma sum_union4b_le {α : Type*} [DecidableEq α] (s1 s2 s3 s4 : Finset α) {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s1 ∪ s2 ∪ (s3 ∪ s4), f x
      ≤ ∑ x ∈ s1, f x + ∑ x ∈ s2, f x + ∑ x ∈ s3, f x + ∑ x ∈ s4, f x := by
  have h := sum_union_le (s1 ∪ s2) (s3 ∪ s4) (f := f) hf
  have h2 := sum_union_le s1 s2 (f := f) hf
  have h3 := sum_union_le s3 s4 (f := f) hf
  linarith

/-- Arithmetic structure of an edge set relative to a modulus `N`. -/
def isStruct (N : ℕ) (E : Finset (ℕ × ℕ)) : Prop :=
  ∀ e ∈ E, ∀ p : ℕ, p.Prime →
    |((padicValNat p e.1 : ℤ) - (padicValNat p N : ℤ))|
      + |((padicValNat p e.2 : ℤ) - (padicValNat p N : ℤ))| ≤ 1

lemma structured_iff (E : Finset (ℕ × ℕ)) :
    structured E ↔ ∃ N, 0 < N ∧ isStruct N E := Iff.rfl

/-- The structure gives the two `padicValNat` bounds needed for the decomposition. -/
lemma struct_bounds {N v w : ℕ}
    (h : ∀ p : ℕ, p.Prime →
      |((padicValNat p v : ℤ) - (padicValNat p N : ℤ))|
        + |((padicValNat p w : ℤ) - (padicValNat p N : ℤ))| ≤ 1) :
    (∀ p : ℕ, p.Prime → padicValNat p v ≤ padicValNat p N + 1) ∧
    (∀ p : ℕ, p.Prime → padicValNat p N ≤ padicValNat p v + 1) := by
  constructor
  · intro p hp
    have h1 : |((padicValNat p v : ℤ) - (padicValNat p N : ℤ))| ≤ 1 :=
      le_trans (le_add_of_nonneg_right (abs_nonneg _)) (h p hp)
    have := (abs_le.mp h1).2
    omega
  · intro p hp
    have h1 : |((padicValNat p v : ℤ) - (padicValNat p N : ℤ))| ≤ 1 :=
      le_trans (le_add_of_nonneg_right (abs_nonneg _)) (h p hp)
    have := (abs_le.mp h1).1
    omega

/-- Decomposition `v = v⁺ · (N / v⁻)`. -/
lemma v_eq_vplus_mul_div (N v : ℕ) (hN : 0 < N) (hv : 0 < v)
    (hupper : ∀ p : ℕ, p.Prime → padicValNat p v ≤ padicValNat p N + 1)
    (hlower : ∀ p : ℕ, p.Prime → padicValNat p N ≤ padicValNat p v + 1) :
    v = vplus N v * (N / vminus N v) := by
  have h : v * vminus N v = vplus N v * N := padic_ratio_decomp N v hN hv hupper hlower
  have hdvd : vminus N v ∣ N := vminus_dvd N v
  have hpos : 0 < vminus N v := vminus_pos N v
  have h2 : vplus N v * (N / vminus N v) * vminus N v = vplus N v * N := by
    rw [mul_assoc, Nat.div_mul_cancel hdvd]
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h2]; exact h)

/-- `(v : ℝ) * v⁻ = v⁺ * N`. -/
lemma cast_mul_vminus (N v : ℕ) (hN : 0 < N) (hv : 0 < v)
    (hupper : ∀ p : ℕ, p.Prime → padicValNat p v ≤ padicValNat p N + 1)
    (hlower : ∀ p : ℕ, p.Prime → padicValNat p N ≤ padicValNat p v + 1) :
    (v:ℝ) * (vminus N v : ℝ) = (vplus N v : ℝ) * (N:ℝ) := by
  have h2 : v * vminus N v = vplus N v * N := padic_ratio_decomp N v hN hv hupper hlower
  conv_lhs => rw [← Nat.cast_mul]
  rw [h2, Nat.cast_mul]

-- =====================   from DS/sbound.lean  =====================
/-! ## The `S`-estimates of the resolving proposition -/

/-- The anatomy predicate, phrased via `Lt`. -/
def anat (t c : ℝ) (n : ℕ) : Prop := c ≤ Lt t n

/-- For `1 ≤ t ≤ 2` the anatomy sums at threshold `t` and at threshold `2` coincide. -/
lemma Lt_max_eq (n : ℕ) (t : ℝ) (ht : 1 ≤ t) : Lt (max t 2) n = Lt t n := by
  unfold Lt
  by_cases h : 2 ≤ t
  · rw [max_eq_left h]
  · push_neg at h
    congr 1
    apply Finset.filter_congr
    intro p hp
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      exact_mod_cast this
    constructor
    · intro _; linarith
    · intro _; exact max_le (by linarith) hp2

/-- The two `padicValNat` bounds coming from the absolute-value form of the structure. -/
lemma padic_pair_of_abs {N n : ℕ}
    (h : ∀ p : ℕ, p.Prime → |((padicValNat p n : ℤ) - (padicValNat p N : ℤ))| ≤ 1) :
    ∀ p : ℕ, p.Prime → padicValNat p n ≤ padicValNat p N + 1 ∧
      padicValNat p N ≤ padicValNat p n + 1 := by
  intro p hp
  have h1 := abs_le.mp (h p hp)
  omega

/-- On a fibre of `n ↦ v⁻(n)` the map `n ↦ v⁺(n)` is injective. -/
lemma vplus_injOn_fiber (N : ℕ) (hN : 0 < N) (S : Finset ℕ) (d : ℕ)
    (hpos : ∀ n ∈ S, 0 < n)
    (hstr : ∀ n ∈ S, ∀ p : ℕ, p.Prime → padicValNat p n ≤ padicValNat p N + 1 ∧
      padicValNat p N ≤ padicValNat p n + 1) :
    Set.InjOn (fun n => vplus N n) ↑(S.filter (fun n => vminus N n = d)) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
  change vplus N a = vplus N b at hab
  have ea := v_eq_vplus_mul_div N a hN (hpos a ha.1)
    (fun p hp => (hstr a ha.1 p hp).1) (fun p hp => (hstr a ha.1 p hp).2)
  have eb := v_eq_vplus_mul_div N b hN (hpos b hb.1)
    (fun p hp => (hstr b hb.1 p hp).1) (fun p hp => (hstr b hb.1 p hp).2)
  have h1 : vplus N a * (N / vminus N a) = vplus N b * (N / vminus N b) := by
    rw [ha.2, hb.2, hab]
  rw [ea, eb, h1]

/-- The fibre of `n ↦ v⁻(n)` has cardinality at most `B` when `v⁺ ≤ B` throughout. -/
lemma vminus_fiber_card_le (N : ℕ) (hN : 0 < N) (S : Finset ℕ) (B d : ℕ)
    (hB : ∀ n ∈ S, vplus N n ≤ B) (hpos : ∀ n ∈ S, 0 < n)
    (hstr : ∀ n ∈ S, ∀ p : ℕ, p.Prime → padicValNat p n ≤ padicValNat p N + 1 ∧
      padicValNat p N ≤ padicValNat p n + 1) :
    (S.filter (fun n => vminus N n = d)).card ≤ B := by
  have hinj := vplus_injOn_fiber N hN S d hpos hstr
  have hsub : (S.filter (fun n => vminus N n = d)).image (fun n => vplus N n) ⊆ Finset.Icc 1 B := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_Icc]
    exact ⟨vplus_pos N n, hB n (Finset.mem_filter.mp hn).1⟩
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at h2
  have h3 : (Finset.Icc 1 B).card = B := by
    rw [Nat.card_Icc]; omega
  omega

/-- Sum of `φ(n)/(n·v⁻(n))` over a set of `n` with the anatomy condition on `v⁻`. -/
lemma sum_phi_div_vminus_le (N : ℕ) (hN : 0 < N) (S : Finset ℕ) (B : ℕ) (P : ℕ → Prop)
    [DecidablePred P]
    (hB : ∀ n ∈ S, vplus N n ≤ B) (hpos : ∀ n ∈ S, 0 < n)
    (hstr : ∀ n ∈ S, ∀ p : ℕ, p.Prime → padicValNat p n ≤ padicValNat p N + 1 ∧
      padicValNat p N ≤ padicValNat p n + 1) :
    ∑ n ∈ S, (if P (vminus N n) then (n.totient : ℝ) / ((n:ℝ) * (vminus N n)) else 0)
      ≤ (B : ℝ) * ((∑ d ∈ N.divisors, (if P d then ((N/d).totient : ℝ) else 0)) / (N:ℝ)) := by
  set T := S.filter (fun n => P (vminus N n)) with hT
  have hmem : ∀ n ∈ T, n ∈ S := fun n hn => (Finset.mem_filter.mp hn).1
  have hPT : ∀ n ∈ T, P (vminus N n) := fun n hn => (Finset.mem_filter.mp hn).2
  have hposT : ∀ n ∈ T, 0 < n := fun n hn => hpos n (hmem n hn)
  have hstrT : ∀ n ∈ T, ∀ p : ℕ, p.Prime → padicValNat p n ≤ padicValNat p N + 1 ∧
      padicValNat p N ≤ padicValNat p n + 1 := fun n hn => hstr n (hmem n hn)
  have hBT : ∀ n ∈ T, vplus N n ≤ B := fun n hn => hB n (hmem n hn)
  have hmain : ∑ n ∈ S, (if P (vminus N n) then (n.totient:ℝ)/((n:ℝ)*(vminus N n)) else 0)
      = ∑ n ∈ T, (n.totient:ℝ)/((n:ℝ)*(vminus N n)) := by
    rw [hT, Finset.sum_filter]
  rw [hmain]
  have hterm : ∀ n ∈ T, (n.totient:ℝ)/((n:ℝ)*(vminus N n))
      ≤ ((N / vminus N n).totient:ℝ)/(N:ℝ) := by
    intro n hn
    exact phi_div_vminus_le N n hN (hposT n hn) (fun p hp => (hstrT n hn p hp).1)
      (fun p hp => (hstrT n hn p hp).2)
  have hdouble : ∑ n ∈ T, ((N / vminus N n).totient : ℝ)
      = ∑ d ∈ N.divisors, ((N/d).totient : ℝ) * ((T.filter (fun n => vminus N n = d)).card : ℝ) := by
    have h1 : ∀ n ∈ T, ((N / vminus N n).totient : ℝ)
        = ∑ d ∈ N.divisors, (if vminus N n = d then ((N/d).totient : ℝ) else 0) := by
      intro n hn
      have hmemd : vminus N n ∈ N.divisors := by
        rw [Nat.mem_divisors]; exact ⟨vminus_dvd N n, hN.ne'⟩
      rw [Finset.sum_eq_single (vminus N n)]
      · simp
      · intro b hb hne
        rw [if_neg (Ne.symm hne)]
      · intro h; exact absurd hmemd h
    calc ∑ n ∈ T, ((N / vminus N n).totient : ℝ)
        = ∑ n ∈ T, ∑ d ∈ N.divisors, (if vminus N n = d then ((N/d).totient : ℝ) else 0) :=
          Finset.sum_congr rfl h1
      _ = ∑ d ∈ N.divisors, ∑ n ∈ T, (if vminus N n = d then ((N/d).totient : ℝ) else 0) :=
          Finset.sum_comm
      _ = ∑ d ∈ N.divisors, ((N/d).totient : ℝ) * ((T.filter (fun n => vminus N n = d)).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [← Finset.sum_filter]
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have hfinal : ∑ n ∈ T, ((N / vminus N n).totient : ℝ)
      ≤ (B : ℝ) * ∑ d ∈ N.divisors, (if P d then ((N/d).totient : ℝ) else 0) := by
    rw [hdouble]
    calc ∑ d ∈ N.divisors, ((N/d).totient : ℝ) * ((T.filter (fun n => vminus N n = d)).card : ℝ)
        ≤ ∑ d ∈ N.divisors, (if P d then ((N/d).totient : ℝ) else 0) * (B:ℝ) := by
          apply Finset.sum_le_sum
          intro d hd
          by_cases hPd : P d
          · rw [if_pos hPd]
            have hcard : ((T.filter (fun n => vminus N n = d)).card : ℝ) ≤ (B:ℝ) := by
              have := vminus_fiber_card_le N hN T B d hBT hposT hstrT
              exact_mod_cast this
            exact mul_le_mul_of_nonneg_left hcard (by positivity)
          · rw [if_neg hPd]
            have hemp : (T.filter (fun n => vminus N n = d)) = ∅ :=
              Finset.not_nonempty_iff_eq_empty.mp (by
                rintro ⟨n, hn⟩
                rw [Finset.mem_filter] at hn
                exact hPd (by rw [← hn.2]; exact hPT n hn.1))
            rw [hemp]; simp
      _ = (B : ℝ) * ∑ d ∈ N.divisors, (if P d then ((N/d).totient : ℝ) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d _
          ring
  calc ∑ n ∈ T, (n.totient:ℝ)/((n:ℝ)*(vminus N n))
      ≤ ∑ n ∈ T, ((N / vminus N n).totient:ℝ)/(N:ℝ) := Finset.sum_le_sum hterm
    _ = (1/(N:ℝ)) * ∑ n ∈ T, ((N / vminus N n).totient:ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
    _ ≤ (1/(N:ℝ)) * ((B:ℝ) * ∑ d ∈ N.divisors, (if P d then ((N/d).totient:ℝ) else 0)) :=
        mul_le_mul_of_nonneg_left hfinal (by positivity)
    _ = (B:ℝ) * ((∑ d ∈ N.divisors, (if P d then ((N/d).totient:ℝ) else 0))/(N:ℝ)) := by
        ring

/-- Sum of `φ(n)/(n·v⁻(n))` over a set of `n` with the anatomy condition on `v⁺`. -/
lemma sum_phi_div_vplus_le (N : ℕ) (hN : 0 < N) (S : Finset ℕ) (B : ℕ) (P : ℕ → Prop)
    [DecidablePred P]
    (hB : ∀ n ∈ S, vplus N n ≤ B) (hpos : ∀ n ∈ S, 0 < n)
    (hstr : ∀ n ∈ S, ∀ p : ℕ, p.Prime → padicValNat p n ≤ padicValNat p N + 1 ∧
      padicValNat p N ≤ padicValNat p n + 1) :
    ∑ n ∈ S, (if P (vplus N n) then (n.totient : ℝ) / ((n:ℝ) * (vminus N n)) else 0)
      ≤ (((Finset.Icc 1 B).filter P).card : ℝ) := by
  set T := S.filter (fun n => P (vplus N n)) with hT
  have hmem : ∀ n ∈ T, n ∈ S := fun n hn => (Finset.mem_filter.mp hn).1
  have hPT : ∀ n ∈ T, P (vplus N n) := fun n hn => (Finset.mem_filter.mp hn).2
  have hposT : ∀ n ∈ T, 0 < n := fun n hn => hpos n (hmem n hn)
  have hstrT : ∀ n ∈ T, ∀ p : ℕ, p.Prime → padicValNat p n ≤ padicValNat p N + 1 ∧
      padicValNat p N ≤ padicValNat p n + 1 := fun n hn => hstr n (hmem n hn)
  have hBT : ∀ n ∈ T, vplus N n ≤ B := fun n hn => hB n (hmem n hn)
  have hmain : ∑ n ∈ S, (if P (vplus N n) then (n.totient:ℝ)/((n:ℝ)*(vminus N n)) else 0)
      = ∑ n ∈ T, (n.totient:ℝ)/((n:ℝ)*(vminus N n)) := by
    rw [hT, Finset.sum_filter]
  rw [hmain]
  have hterm : ∀ n ∈ T, (n.totient:ℝ)/((n:ℝ)*(vminus N n))
      ≤ ((N / vminus N n).totient:ℝ)/(N:ℝ) := by
    intro n hn
    exact phi_div_vminus_le N n hN (hposT n hn) (fun p hp => (hstrT n hn p hp).1)
      (fun p hp => (hstrT n hn p hp).2)
  have hdouble : ∑ n ∈ T, ((N / vminus N n).totient : ℝ)
      = ∑ d ∈ N.divisors, ((N/d).totient : ℝ) * ((T.filter (fun n => vminus N n = d)).card : ℝ) := by
    have h1 : ∀ n ∈ T, ((N / vminus N n).totient : ℝ)
        = ∑ d ∈ N.divisors, (if vminus N n = d then ((N/d).totient : ℝ) else 0) := by
      intro n hn
      have hmemd : vminus N n ∈ N.divisors := by
        rw [Nat.mem_divisors]; exact ⟨vminus_dvd N n, hN.ne'⟩
      rw [Finset.sum_eq_single (vminus N n)]
      · simp
      · intro b hb hne
        rw [if_neg (Ne.symm hne)]
      · intro h; exact absurd hmemd h
    calc ∑ n ∈ T, ((N / vminus N n).totient : ℝ)
        = ∑ n ∈ T, ∑ d ∈ N.divisors, (if vminus N n = d then ((N/d).totient : ℝ) else 0) :=
          Finset.sum_congr rfl h1
      _ = ∑ d ∈ N.divisors, ∑ n ∈ T, (if vminus N n = d then ((N/d).totient : ℝ) else 0) :=
          Finset.sum_comm
      _ = ∑ d ∈ N.divisors, ((N/d).totient : ℝ) * ((T.filter (fun n => vminus N n = d)).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [← Finset.sum_filter]
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have hcardB : ∀ d, ((T.filter (fun n => vminus N n = d)).card : ℝ)
      ≤ (((Finset.Icc 1 B).filter P).card : ℝ) := by
    intro d
    have hinj := vplus_injOn_fiber N hN T d hposT hstrT
    have hsub : (T.filter (fun n => vminus N n = d)).image (fun n => vplus N n)
        ⊆ (Finset.Icc 1 B).filter P := by
      intro x hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨vplus_pos N n, hBT n (Finset.mem_filter.mp hn).1⟩,
        hPT n (Finset.mem_filter.mp hn).1⟩
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj] at h2
    exact_mod_cast h2
  calc ∑ n ∈ T, (n.totient:ℝ)/((n:ℝ)*(vminus N n))
      ≤ ∑ n ∈ T, ((N / vminus N n).totient:ℝ)/(N:ℝ) := Finset.sum_le_sum hterm
    _ = (1/(N:ℝ)) * ∑ n ∈ T, ((N / vminus N n).totient:ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
    _ = (1/(N:ℝ)) * ∑ d ∈ N.divisors, ((N/d).totient : ℝ) *
          ((T.filter (fun n => vminus N n = d)).card : ℝ) := by rw [hdouble]
    _ ≤ (1/(N:ℝ)) * ∑ d ∈ N.divisors, ((N/d).totient : ℝ) *
          ((((Finset.Icc 1 B).filter P).card : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left (hcardB d) (by positivity)
    _ = (1/(N:ℝ)) * (((Finset.Icc 1 B).filter P).card : ℝ) * ∑ d ∈ N.divisors, ((N/d).totient : ℝ) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
    _ = (1/(N:ℝ)) * (((Finset.Icc 1 B).filter P).card : ℝ) * (N:ℝ) := by
        have hdiv : (∑ d ∈ N.divisors, ((N/d).totient : ℝ)) = (N:ℝ) := by
          rw [← Nat.cast_sum, sum_divisors_totient_div]
        rw [hdiv]
    _ = (((Finset.Icc 1 B).filter P).card : ℝ) := by
        field_simp

-- =====================   from DS/qset.lean  =====================
/-! ## The four-way anatomy split of `Qset` -/

lemma padicValNat_gcd_eq_min (p v w : ℕ) (hp : p.Prime) (hv : v ≠ 0) (hw : w ≠ 0) :
    padicValNat p (v.gcd w) = min (padicValNat p v) (padicValNat p w) := by
  rw [← Nat.factorization_def _ hp, Nat.factorization_gcd hv hw, Finsupp.inf_apply,
    Nat.factorization_def v hp, Nat.factorization_def w hp]

/-- If `p` divides `v/gcd(v,w)` then `ν_p w < ν_p v`. -/
lemma padicValNat_lt_of_dvd (p v w : ℕ) (hp : p.Prime) (hv : 0 < v) (hw : 0 < w)
    (h : p ∣ v / v.gcd w) : padicValNat p w < padicValNat p v := by
  haveI : Fact p.Prime := ⟨hp⟩
  set g := v.gcd w with hg
  have hg0 : g ≠ 0 := (Nat.gcd_pos_of_pos_left w hv).ne'
  have hdv : g ∣ v := Nat.gcd_dvd_left v w
  have hdw : g ∣ w := Nat.gcd_dvd_right v w
  have hvg : g * (v / g) = v := Nat.mul_div_cancel' hdv
  have hwg : g * (w / g) = w := Nat.mul_div_cancel' hdw
  have hvg0 : v / g ≠ 0 := fun h0 => hv.ne' (by rw [← hvg, h0, mul_zero])
  have hwg0 : w / g ≠ 0 := fun h0 => hw.ne' (by rw [← hwg, h0, mul_zero])
  have e1 : padicValNat p v = padicValNat p g + padicValNat p (v/g) := by
    conv_lhs => rw [← hvg]
    rw [padicValNat.mul hg0 hvg0]
  have e2 : padicValNat p w = padicValNat p g + padicValNat p (w/g) := by
    conv_lhs => rw [← hwg]
    rw [padicValNat.mul hg0 hwg0]
  have e3 : padicValNat p g = min (padicValNat p v) (padicValNat p w) :=
    padicValNat_gcd_eq_min p v w hp hv.ne' hw.ne'
  have h1 : 1 ≤ padicValNat p (v/g) := by
    have h2 : p^1 ∣ v/g := by simpa using h
    have h3 := (padicValNat_dvd_iff_le hvg0).mp h2
    simpa using h3
  omega

lemma nat_eq_of_sub_eq_one {a n : ℕ} (h : ((a:ℤ) - (n:ℤ)) = 1) : a = n + 1 := by
  have : ((a:ℤ)) = ((n:ℤ)) + 1 := by omega
  exact_mod_cast this

lemma nat_succ_eq_of_sub_eq_neg_one {a n : ℕ} (h : ((a:ℤ) - (n:ℤ)) = -1) : a + 1 = n := by
  have : ((a:ℤ)) + 1 = ((n:ℤ)) := by omega
  exact_mod_cast this

lemma nat_eq_of_sub_eq_zero {a n : ℕ} (h : ((a:ℤ) - (n:ℤ)) = 0) : a = n := by
  have : ((a:ℤ)) = ((n:ℤ)) := by omega
  exact_mod_cast this

/-- Case analysis: if `ν_p w < ν_p v` then `p | v⁺` or `p | w⁻`. -/
lemma four_way_gt (N v w p : ℕ) (hN : 0 < N) (hv : 0 < v) (hw : 0 < w) (hp : p.Prime)
    (hstruct : |((padicValNat p v : ℤ) - (padicValNat p N : ℤ))|
      + |((padicValNat p w : ℤ) - (padicValNat p N : ℤ))| ≤ 1)
    (hgt : padicValNat p w < padicValNat p v) : p ∣ vplus N v ∨ p ∣ vminus N w := by
  haveI : Fact p.Prime := ⟨hp⟩
  set a := padicValNat p v with ha
  set b := padicValNat p w with hb
  set n := padicValNat p N with hn
  have hAB : |((a:ℤ) - (n:ℤ))| + |((b:ℤ) - (n:ℤ))| ≤ 1 := hstruct
  have hx1 : |((a:ℤ) - (n:ℤ))| ≤ 1 := le_trans (le_add_of_nonneg_right (abs_nonneg _)) hAB
  have hy1 : |((b:ℤ) - (n:ℤ))| ≤ 1 := le_trans (le_add_of_nonneg_left (abs_nonneg _)) hAB
  have hx : ((a:ℤ) - (n:ℤ)) = -1 ∨ ((a:ℤ) - (n:ℤ)) = 0 ∨ ((a:ℤ) - (n:ℤ)) = 1 := by
    have := abs_le.mp hx1; omega
  have hdvd_vplus : (n = 0 ∨ 1 ≤ n) → True := fun _ => trivial
  rcases hx with hx | hx | hx
  · exfalso
    have hyx : ((b:ℤ) - (n:ℤ)) ≤ -2 := by omega
    have h2 := abs_le.mp hy1
    omega
  · right
    have hbe : b + 1 = n := by
      have hyb : ((b:ℤ) - (n:ℤ)) ≤ -1 := by omega
      have h2 : ((b:ℤ) - (n:ℤ)) = -1 := by
        have h3 := abs_le.mp hy1
        omega
      exact nat_succ_eq_of_sub_eq_neg_one h2
    refine Finset.dvd_prod_of_mem (fun q => q) ?_
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Nat.mem_primeFactors]
      refine ⟨hp, ?_, hN.ne'⟩
      have h1 : 1 ≤ n := by omega
      have h2 : p^1 ∣ N := (padicValNat_dvd_iff_le hN.ne').mpr (by simpa using h1)
      rwa [pow_one] at h2
    · rw [← hn, ← hb]; exact hbe.symm
  · left
    have hae : a = n + 1 := nat_eq_of_sub_eq_one hx
    refine Finset.dvd_prod_of_mem (fun q => q) ?_
    rw [Finset.mem_filter]
    have habs : |((a:ℤ) - (n:ℤ))| = 1 := by rw [hx]; norm_num
    have hb0 : b = n := by
      have h3 : |((b:ℤ) - (n:ℤ))| ≤ 0 := by
        have h4 := hAB
        rw [habs] at h4
        omega
      exact nat_eq_of_sub_eq_zero (abs_eq_zero.mp (le_antisymm h3 (abs_nonneg _)))
    refine ⟨?_, ?_⟩
    · rw [Nat.mem_primeFactors]
      refine ⟨hp, ?_, hv.ne'⟩
      have h1 : 1 ≤ a := by omega
      have h2 : p^1 ∣ v := (padicValNat_dvd_iff_le hv.ne').mpr (by simpa using h1)
      rwa [pow_one] at h2
    · rw [← ha, ← hn]; exact hae

/-- Case analysis: if `ν_p v < ν_p w` then `p | v⁻` or `p | w⁺`. -/
lemma four_way_lt (N v w p : ℕ) (hN : 0 < N) (hv : 0 < v) (hw : 0 < w) (hp : p.Prime)
    (hstruct : |((padicValNat p v : ℤ) - (padicValNat p N : ℤ))|
      + |((padicValNat p w : ℤ) - (padicValNat p N : ℤ))| ≤ 1)
    (hlt : padicValNat p v < padicValNat p w) : p ∣ vminus N v ∨ p ∣ vplus N w := by
  haveI : Fact p.Prime := ⟨hp⟩
  set a := padicValNat p v with ha
  set b := padicValNat p w with hb
  set n := padicValNat p N with hn
  have hAB : |((a:ℤ) - (n:ℤ))| + |((b:ℤ) - (n:ℤ))| ≤ 1 := hstruct
  have hx1 : |((a:ℤ) - (n:ℤ))| ≤ 1 := le_trans (le_add_of_nonneg_right (abs_nonneg _)) hAB
  have hy1 : |((b:ℤ) - (n:ℤ))| ≤ 1 := le_trans (le_add_of_nonneg_left (abs_nonneg _)) hAB
  have hy : ((b:ℤ) - (n:ℤ)) = -1 ∨ ((b:ℤ) - (n:ℤ)) = 0 ∨ ((b:ℤ) - (n:ℤ)) = 1 := by
    have := abs_le.mp hy1; omega
  rcases hy with hy | hy | hy
  · exfalso
    have hxy : ((a:ℤ) - (n:ℤ)) ≤ -2 := by omega
    have h2 := abs_le.mp hx1
    omega
  · left
    have hae : a + 1 = n := by
      have hxa : ((a:ℤ) - (n:ℤ)) ≤ -1 := by omega
      have h2 : ((a:ℤ) - (n:ℤ)) = -1 := by
        have h3 := abs_le.mp hx1
        omega
      exact nat_succ_eq_of_sub_eq_neg_one h2
    refine Finset.dvd_prod_of_mem (fun q => q) ?_
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Nat.mem_primeFactors]
      refine ⟨hp, ?_, hN.ne'⟩
      have h1 : 1 ≤ n := by omega
      have h2 : p^1 ∣ N := (padicValNat_dvd_iff_le hN.ne').mpr (by simpa using h1)
      rwa [pow_one] at h2
    · rw [← ha, ← hn]; exact hae.symm
  · right
    have hbe : b = n + 1 := nat_eq_of_sub_eq_one hy
    refine Finset.dvd_prod_of_mem (fun q => q) ?_
    rw [Finset.mem_filter]
    have habs : |((b:ℤ) - (n:ℤ))| = 1 := by rw [hy]; norm_num
    have ha0 : a = n := by
      have h3 : |((a:ℤ) - (n:ℤ))| ≤ 0 := by
        have h4 := hAB
        rw [habs] at h4
        omega
      exact nat_eq_of_sub_eq_zero (abs_eq_zero.mp (le_antisymm h3 (abs_nonneg _)))
    refine ⟨?_, ?_⟩
    · rw [Nat.mem_primeFactors]
      refine ⟨hp, ?_, hw.ne'⟩
      have h1 : 1 ≤ b := by omega
      have h2 : p^1 ∣ w := (padicValNat_dvd_iff_le hw.ne').mpr (by simpa using h1)
      rwa [pow_one] at h2
    · rw [← hb, ← hn]; exact hbe

/-- A prime dividing the "coprime part" `vw/gcd(v,w)²` divides one of `v⁻, v⁺, w⁻, w⁺`. -/
lemma prime_dvd_four (N v w p : ℕ) (hN : 0 < N) (hv : 0 < v) (hw : 0 < w)
    (hp : p.Prime)
    (hstruct : |((padicValNat p v : ℤ) - (padicValNat p N : ℤ))|
      + |((padicValNat p w : ℤ) - (padicValNat p N : ℤ))| ≤ 1)
    (hdvd : p ∣ v * w / (v.gcd w * v.gcd w)) :
    p ∣ vminus N v ∨ p ∣ vplus N v ∨ p ∣ vminus N w ∨ p ∣ vplus N w := by
  have hcomm := Nat.div_mul_div_comm (Nat.gcd_dvd_left v w) (Nat.gcd_dvd_right v w)
  rw [← hcomm] at hdvd
  rcases hp.dvd_mul.mp hdvd with h | h
  · have hgt := padicValNat_lt_of_dvd p v w hp hv hw h
    rcases four_way_gt N v w p hN hv hw hp hstruct hgt with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl h'))
  · have h' : p ∣ w / w.gcd v := by rw [Nat.gcd_comm]; exact h
    have hlt := padicValNat_lt_of_dvd p w v hp hw hv h'
    rcases four_way_lt N v w p hN hv hw hp hstruct hlt with h'' | h''
    · exact Or.inl h''
    · exact Or.inr (Or.inr (Or.inr h''))

/-- The `Qset` sum is bounded by the four anatomy sums. -/
lemma Qset_sum_le_four (N v w : ℕ) (hN : 0 < N) (hv : 0 < v) (hw : 0 < w) (t : ℝ)
    (hstruct : ∀ p : ℕ, p.Prime → |((padicValNat p v : ℤ) - (padicValNat p N : ℤ))|
      + |((padicValNat p w : ℤ) - (padicValNat p N : ℤ))| ≤ 1) :
    ∑ r ∈ Qset t v w, 1/(r:ℝ)
      ≤ Lt t (vminus N v) + Lt t (vplus N v) + Lt t (vminus N w) + Lt t (vplus N w) := by
  set P := (vminus N v * vplus N v) * (vminus N w * vplus N w) with hP
  have hv1 : vminus N v ≠ 0 := (vminus_pos N v).ne'
  have hv2 : vplus N v ≠ 0 := (vplus_pos N v).ne'
  have hw1 : vminus N w ≠ 0 := (vminus_pos N w).ne'
  have hw2 : vplus N w ≠ 0 := (vplus_pos N w).ne'
  have hPfac : Nat.primeFactors P = (Nat.primeFactors (vminus N v) ∪ Nat.primeFactors (vplus N v))
      ∪ (Nat.primeFactors (vminus N w) ∪ Nat.primeFactors (vplus N w)) := by
    rw [hP, Nat.primeFactors_mul (mul_ne_zero hv1 hv2) (mul_ne_zero hw1 hw2),
      Nat.primeFactors_mul hv1 hv2, Nat.primeFactors_mul hw1 hw2]
  have hsub : Nat.primeFactors (v * w / (v.gcd w * v.gcd w)) ⊆ Nat.primeFactors P := by
    intro p hp'
    rw [Nat.mem_primeFactors] at hp' ⊢
    obtain ⟨hpp, hpd, -⟩ := hp'
    have hfour := prime_dvd_four N v w p hN hv hw hpp (hstruct p hpp) hpd
    refine ⟨hpp, ?_, (mul_ne_zero (mul_ne_zero hv1 hv2) (mul_ne_zero hw1 hw2))⟩
    rcases hfour with h | h | h | h
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _
    · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h _) _
    · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h _) _
  have hstep1 : ∑ r ∈ Qset t v w, 1/(r:ℝ) ≤ ∑ r ∈ (Nat.primeFactors P).filter
      (fun r : ℕ => t ≤ (r:ℝ)), 1/(r:ℝ) := by
    unfold Qset
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro r hr
      rw [Finset.mem_filter] at hr ⊢
      exact ⟨hsub hr.1, hr.2⟩
    · intro r hr _
      positivity
  have hstep2 : ∑ r ∈ (Nat.primeFactors P).filter (fun r : ℕ => t ≤ (r:ℝ)), 1/(r:ℝ)
      ≤ (∑ r ∈ (Nat.primeFactors (vminus N v)).filter (fun r : ℕ => t ≤ (r:ℝ)), 1/(r:ℝ))
        + (∑ r ∈ (Nat.primeFactors (vplus N v)).filter (fun r : ℕ => t ≤ (r:ℝ)), 1/(r:ℝ))
        + (∑ r ∈ (Nat.primeFactors (vminus N w)).filter (fun r : ℕ => t ≤ (r:ℝ)), 1/(r:ℝ))
        + (∑ r ∈ (Nat.primeFactors (vplus N w)).filter (fun r : ℕ => t ≤ (r:ℝ)), 1/(r:ℝ)) := by
    rw [hPfac]
    simp only [Finset.filter_union]
    exact sum_union4b_le _ _ _ _ (fun r => by positivity)
  have hLt : ∀ n : ℕ, Lt t n
      = ∑ r ∈ (Nat.primeFactors n).filter (fun r : ℕ => t ≤ (r:ℝ)), 1/(r:ℝ) := fun n => rfl
  rw [hLt, hLt, hLt, hLt]
  linarith

-- =====================   from DS/nhood.lean  =====================
/-! ## Neighbourhood bookkeeping -/

lemma mem_nhoodFst {E : Finset (ℕ × ℕ)} {v w : ℕ} : w ∈ nhoodFst E v ↔ (v,w) ∈ E := by
  constructor
  · intro h
    rw [nhoodFst, Finset.mem_image] at h
    obtain ⟨e, he, hwe⟩ := h
    rw [Finset.mem_filter] at he
    rw [← hwe, ← he.2]
    exact he.1
  · intro h
    rw [nhoodFst, Finset.mem_image]
    exact ⟨(v,w), by rw [Finset.mem_filter]; exact ⟨h, rfl⟩, rfl⟩

lemma mem_nhoodSnd {E : Finset (ℕ × ℕ)} {v w : ℕ} : v ∈ nhoodSnd E w ↔ (v,w) ∈ E := by
  constructor
  · intro h
    rw [nhoodSnd, Finset.mem_image] at h
    obtain ⟨e, he, hwe⟩ := h
    rw [Finset.mem_filter] at he
    rw [← hwe, ← he.2]
    exact he.1
  · intro h
    rw [nhoodSnd, Finset.mem_image]
    exact ⟨(v,w), by rw [Finset.mem_filter]; exact ⟨h, rfl⟩, rfl⟩

lemma nhoodFst_subset {E : Finset (ℕ × ℕ)} {V W : Finset ℕ} (hE : E ⊆ V.product W) (v : ℕ) :
    nhoodFst E v ⊆ W := by
  intro w hw
  exact (Finset.mem_product.mp (hE (mem_nhoodFst.mp hw))).2

lemma nhoodSnd_subset {E : Finset (ℕ × ℕ)} {V W : Finset ℕ} (hE : E ⊆ V.product W) (w : ℕ) :
    nhoodSnd E w ⊆ V := by
  intro v hv
  exact (Finset.mem_product.mp (hE (mem_nhoodSnd.mp hv))).1

/-- A sum over `nhoodFst` as a sum over `W` with an edge indicator. -/
lemma sum_nhoodFst_eq (E : Finset (ℕ × ℕ)) (W : Finset ℕ) {v : ℕ}
    (hW : nhoodFst E v ⊆ W) (f : ℕ → ℝ) :
    ∑ w ∈ nhoodFst E v, f w = ∑ w ∈ W, (if (v,w) ∈ E then f w else 0) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext w
    rw [Finset.mem_filter]
    exact ⟨fun h => ⟨hW h, mem_nhoodFst.mp h⟩, fun h => mem_nhoodFst.mpr h.2⟩
  · intro w _
    rfl

lemma sum_nhoodSnd_eq (E : Finset (ℕ × ℕ)) (V : Finset ℕ) {w : ℕ}
    (hV : nhoodSnd E w ⊆ V) (f : ℕ → ℝ) :
    ∑ v ∈ nhoodSnd E w, f v = ∑ v ∈ V, (if (v,w) ∈ E then f v else 0) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext v
    rw [Finset.mem_filter]
    exact ⟨fun h => ⟨hV h, mem_nhoodSnd.mp h⟩, fun h => mem_nhoodSnd.mpr h.2⟩
  · intro v _
    rfl

/-- The "one-sided" mass at `w₀` as a double sum with edge indicators. -/
lemma T_eq (E : Finset (ℕ × ℕ)) (V W : Finset ℕ) (hE : E ⊆ V.product W) (w0 : ℕ)
    (a b : ℕ → ℝ) :
    (∑ v ∈ nhoodSnd E w0, a v * ∑ w ∈ nhoodFst E v, b w)
      = ∑ v ∈ V, ∑ w ∈ W, (if (v,w0) ∈ E ∧ (v,w) ∈ E then a v * b w else 0) := by
  have h1 : ∀ v, a v * (∑ w ∈ nhoodFst E v, b w)
      = ∑ w ∈ W, (if (v,w) ∈ E then a v * b w else 0) := by
    intro v
    rw [Finset.mul_sum]
    exact sum_nhoodFst_eq E W (nhoodFst_subset hE v) (fun w => a v * b w)
  calc (∑ v ∈ nhoodSnd E w0, a v * ∑ w ∈ nhoodFst E v, b w)
      = ∑ v ∈ nhoodSnd E w0, ∑ w ∈ W, (if (v,w) ∈ E then a v * b w else 0) :=
        Finset.sum_congr rfl (fun v _ => h1 v)
    _ = ∑ v ∈ V, (if (v,w0) ∈ E then
          ∑ w ∈ W, (if (v,w) ∈ E then a v * b w else 0) else 0) :=
        (sum_nhoodSnd_eq E V (nhoodSnd_subset hE w0) _)
    _ = ∑ v ∈ V, ∑ w ∈ W, (if (v,w0) ∈ E ∧ (v,w) ∈ E then a v * b w else 0) := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases h : (v,w0) ∈ E
        · rw [if_pos h]
          apply Finset.sum_congr rfl
          intro w _
          by_cases h2 : (v,w) ∈ E
          · rw [if_pos h2, if_pos ⟨h, h2⟩]
          · rw [if_neg h2, if_neg (fun hc => h2 hc.2)]
        · rw [if_neg h]
          rw [Finset.sum_eq_zero]
          intro w _
          rw [if_neg (fun hc => h hc.1)]

-- =====================   from DS/half.lean  =====================
/-- The maximum of `v⁺` over the `v`-neighbours of `w`. -/
def v0p (E : Finset (ℕ × ℕ)) (N w : ℕ) : ℕ := (nhoodSnd E w).sup (vplus N)

/-- The weight `φ(n)/(n·n⁻)`. -/
def wgt (N n : ℕ) : ℝ := (n.totient : ℝ) / ((n:ℝ) * (vminus N n))

lemma wgt_nonneg (N n : ℕ) : 0 ≤ wgt N n := by
  unfold wgt; positivity

lemma str_fst {N : ℕ} {E : Finset (ℕ × ℕ)} (h : isStruct N E) {v w : ℕ} (he : (v,w) ∈ E) :
    ∀ p : ℕ, p.Prime → padicValNat p v ≤ padicValNat p N + 1 ∧
      padicValNat p N ≤ padicValNat p v + 1 :=
  fun p hp => ⟨(struct_bounds (h (v,w) he)).1 p hp, (struct_bounds (h (v,w) he)).2 p hp⟩

lemma str_snd {N : ℕ} {E : Finset (ℕ × ℕ)} (h : isStruct N E) {v w : ℕ} (he : (v,w) ∈ E) :
    ∀ p : ℕ, p.Prime → padicValNat p w ≤ padicValNat p N + 1 ∧
      padicValNat p N ≤ padicValNat p w + 1 := by
  intro p hp
  have hh := h (v,w) he
  have h1 : |((padicValNat p w : ℤ) - (padicValNat p N : ℤ))| ≤ 1 :=
    le_trans (le_add_of_nonneg_left (abs_nonneg _)) (hh p hp)
  have h2 := abs_le.mp h1
  constructor <;> omega

lemma exists_argmax_vplus (E : Finset (ℕ × ℕ)) (N w : ℕ) (hw : w ∈ E.image Prod.snd) :
    ∃ v ∈ nhoodSnd E w, vplus N v = v0p E N w := by
  obtain ⟨e, he, hwe⟩ := Finset.mem_image.mp hw
  have hne : (nhoodSnd E w).Nonempty := ⟨e.1, mem_nhoodSnd.mpr (by rw [← hwe]; exact he)⟩
  obtain ⟨v, hv, hveq⟩ := Finset.exists_mem_eq_sup _ hne (vplus N)
  exact ⟨v, hv, hveq.symm⟩

lemma v0p_pos (E : Finset (ℕ × ℕ)) (N w : ℕ) (hw : w ∈ E.image Prod.snd) : 1 ≤ v0p E N w := by
  obtain ⟨v, hv, hveq⟩ := exists_argmax_vplus E N w hw
  rw [← hveq]
  exact vplus_pos N v

lemma le_v0p (E : Finset (ℕ × ℕ)) (N v w : ℕ) (hv : (v,w) ∈ E) : vplus N v ≤ v0p E N w :=
  Finset.le_sup (mem_nhoodSnd.mpr hv)

/-- The four-way anatomy alternative for an edge of `E`. -/
lemma four_cases (N : ℕ) (hN : 0 < N) (V W : Finset ℕ) (a b : ℕ → ℝ) (t C : ℝ) (hC : 0 ≤ C)
    (hV : ∀ v ∈ V, 1 ≤ v) (hW : ∀ w ∈ W, 1 ≤ w) (E : Finset (ℕ × ℕ))
    (hE : E ⊆ V.product W) (hstr : isStruct N E)
    (hgood : ∀ e ∈ E, good t C a b e.1 e.2) :
    ∀ e ∈ E, anat t (C/4) (vminus N e.1) ∨ anat t (C/4) (vplus N e.1) ∨
      anat t (C/4) (vminus N e.2) ∨ anat t (C/4) (vplus N e.2) := by
  intro e he
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  have hmem := Finset.mem_product.mp (hE he)
  have hv0 : 0 < e.1 := lt_of_lt_of_le Nat.zero_lt_one (hV e.1 hmem.1)
  have hw0 : 0 < e.2 := lt_of_lt_of_le Nat.zero_lt_one (hW e.2 hmem.2)
  have hb := (hgood e he).2
  have hfour := Qset_sum_le_four N e.1 e.2 hN hv0 hw0 t (hstr e he)
  have hlt : ∀ m : ℕ, ¬ anat t (C/4) m → Lt t m < C/4 := fun m hm => lt_of_not_ge hm
  have hsum : Lt t (vminus N e.1) + Lt t (vplus N e.1) + Lt t (vminus N e.2)
      + Lt t (vplus N e.2) < C := by
    have h1' := hlt _ h1; have h2' := hlt _ h2
    have h3' := hlt _ h3; have h4' := hlt _ h4
    linarith
  linarith

lemma anat_max_iff (t c : ℝ) (ht : 1 ≤ t) (n : ℕ) : anat (max t 2) c n ↔ anat t c n := by
  unfold anat
  rw [Lt_max_eq n t ht]

lemma mass_mono (a : ℕ → ℝ) (ha : ∀ v, 0 ≤ a v) {s t : Finset ℕ} (h : s ⊆ t) :
    mass a s ≤ mass a t :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => ha i)


/-- The analogue of `good_le_phi` bounding the second weight. -/
lemma good_le_phi_b (N : ℕ) (hN : 0 < N) (a b : ℕ → ℝ) (t C : ℝ) (v w : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (hstruct : ∀ p : ℕ, p.Prime →
      |((padicValNat p v : ℤ) - (padicValNat p N : ℤ))|
        + |((padicValNat p w : ℤ) - (padicValNat p N : ℤ))| ≤ 1)
    (hgood : good t C a b v w) :
    b w ≤ (w.totient : ℝ) / ((w:ℝ) * (vminus N w) * (vplus N v)) := by
  obtain ⟨hD, -⟩ := hgood
  have hstruct' : ∀ p : ℕ, p.Prime →
      |((padicValNat p w : ℤ) - (padicValNat p N : ℤ))|
        + |((padicValNat p v : ℤ) - (padicValNat p N : ℤ))| ≤ 1 := by
    intro p hp; rw [add_comm]; exact hstruct p hp
  have h1 : ((v.gcd w : ℕ) : ℝ) * (vminus N w) * (vplus N v) = (v : ℝ) := by
    rw [Nat.gcd_comm]
    exact_mod_cast gcd_ratio_decomp N w v hN hw hv hstruct'
  have hphi : (0:ℝ) < (w.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hw
  have hD' : (v:ℝ) * (w:ℝ) * (b w / (w.totient : ℝ)) ≤ (v.gcd w : ℕ) := by
    have h2 : (v:ℝ) * (w:ℝ) * max (a v / (v.totient:ℝ)) (b w / (w.totient:ℝ))
        ≥ (v:ℝ) * (w:ℝ) * (b w / (w.totient:ℝ)) := by
      apply mul_le_mul_of_nonneg_left (le_max_right _ _)
      positivity
    linarith [hD, h2]
  have h2 : b w / (w.totient : ℝ) ≤ ((v.gcd w : ℕ) : ℝ) / ((v:ℝ) * (w:ℝ)) := by
    have h3 : b w * ((v:ℝ)*(w:ℝ)) ≤ ((v.gcd w:ℕ):ℝ) * (w.totient:ℝ) := by
      have h5 := hD'
      rw [← mul_div_assoc] at h5
      rw [div_le_iff₀ hphi] at h5
      linarith [h5]
    calc b w / (w.totient : ℝ)
        = b w * ((v:ℝ)*(w:ℝ)) / ((w.totient:ℝ) * ((v:ℝ)*(w:ℝ))) := by field_simp
      _ ≤ ((v.gcd w:ℕ):ℝ) * (w.totient:ℝ) / ((w.totient:ℝ) * ((v:ℝ)*(w:ℝ))) :=
          div_le_div_of_nonneg_right h3 (by positivity)
      _ = ((v.gcd w:ℕ):ℝ) / ((v:ℝ)*(w:ℝ)) := by field_simp
  calc b w = (w.totient : ℝ) * (b w / (w.totient : ℝ)) := by field_simp
    _ ≤ (w.totient : ℝ) * (((v.gcd w : ℕ) : ℝ) / ((v:ℝ) * (w:ℝ))) :=
        mul_le_mul_of_nonneg_left h2 hphi.le
    _ = (w.totient : ℝ) / ((w:ℝ) * (vminus N w) * (vplus N v)) := by
        rw [← h1]; field_simp

/-- The pointwise lower bound on `b`, using the maximiser of `v⁺` over the neighbours. -/
lemma b_le (N : ℕ) (hN : 0 < N) (V W : Finset ℕ) (a b : ℕ → ℝ) (t C : ℝ)
    (hV : ∀ v ∈ V, 1 ≤ v) (hW : ∀ w ∈ W, 1 ≤ w)
    (E : Finset (ℕ × ℕ)) (hE : E ⊆ V.product W) (hstr : isStruct N E)
    (hgood : ∀ e ∈ E, good t C a b e.1 e.2) {v w : ℕ} (hv : (v,w) ∈ E) :
    b w ≤ wgt N w / (v0p E N w) := by
  have hmem := Finset.mem_product.mp (hE hv)
  have hwW' : w ∈ E.image Prod.snd := Finset.mem_image.mpr ⟨(v,w), hv, rfl⟩
  obtain ⟨v', hv', hveq⟩ := exists_argmax_vplus E N w hwW'
  have hv'E : (v', w) ∈ E := mem_nhoodSnd.mp hv'
  have hp := good_le_phi_b N hN a b t C v' w (hV v' (Finset.mem_product.mp (hE hv'E)).1)
    (hW w hmem.2) (hstr (v',w) hv'E) (hgood (v',w) hv'E)
  rw [hveq] at hp
  unfold wgt
  rw [div_div]
  exact hp

instance anatDecidablePred (t c : ℝ) : DecidablePred (anat t c) :=
  fun n => inferInstanceAs (Decidable (c ≤ Lt t n))

/-- The anatomy constant. -/
def AA (C t : ℝ) : ℝ := Real.exp (21 * Real.exp 20) * Real.exp (-(20 * (C/4) * max t 2))

lemma AA_pos (C t : ℝ) : 0 < AA C t := by
  unfold AA; positivity

section SBounds

variable {N : ℕ} {V W : Finset ℕ} {a b : ℕ → ℝ} {t C : ℝ} {E : Finset (ℕ × ℕ)}

/-- Pointwise bound on `a`. -/
lemma a_le (hN : 0 < N) (hV : ∀ v ∈ V, 1 ≤ v) (hW : ∀ w ∈ W, 1 ≤ w)
    (hE : E ⊆ V.product W) (hstr : isStruct N E)
    (hgood : ∀ e ∈ E, good t C a b e.1 e.2) {v w0 : ℕ} (hv : (v,w0) ∈ E) :
    a v ≤ wgt N v / (vplus N w0) := by
  have hmem := Finset.mem_product.mp (hE hv)
  have hp := good_le_phi N hN a b t C v w0 (hV v hmem.1) (hW w0 hmem.2)
    (hstr (v,w0) hv) (hgood (v,w0) hv)
  unfold wgt
  rw [div_div]
  exact hp

/-- The divisor-anatomy sum is bounded. -/
lemma divisor_anat_le (hN : 0 < N) (ht : 1 ≤ t) (hC : 0 < C) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ d, P d → anat t (C/4) d) :
    (∑ d ∈ N.divisors, (if P d then ((N/d).totient : ℝ) else 0)) / (N:ℝ) ≤ AA C t := by
  have h5 : (∑ d ∈ N.divisors, (if P d then ((N/d).totient : ℝ) else 0))
      ≤ Real.exp (21 * Real.exp 20) * (N:ℝ) * Real.exp (-(20 * (C/4) * max t 2)) := by
    have h2 : ∀ d, P d → anat (max t 2) (C/4) d := fun d hd => (anat_max_iff t (C/4) ht d).mpr (hP d hd)
    have h6 : (∑ d ∈ N.divisors, (if P d then ((N/d).totient : ℝ) else 0))
        ≤ ∑ d ∈ N.divisors, (if anat (max t 2) (C/4) d then ((N/d).totient : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro d _
      by_cases h : P d
      · rw [if_pos h, if_pos (h2 d h)]
      · rw [if_neg h]; positivity
    refine h6.trans ?_
    exact anatomy_divisor_aux N (max t 2) (C/4) (le_max_right t 2) (by linarith)
  calc (∑ d ∈ N.divisors, (if P d then ((N/d).totient : ℝ) else 0)) / (N:ℝ)
      ≤ (Real.exp (21 * Real.exp 20) * (N:ℝ)
          * Real.exp (-(20 * (C/4) * max t 2))) / (N:ℝ) :=
        div_le_div_of_nonneg_right h5 (by positivity)
    _ = AA C t := by
        unfold AA
        field_simp

/-- Inner `v`-sum bound, no anatomy. -/
lemma bv_plain (hN : 0 < N) (hV : ∀ v ∈ V, 1 ≤ v)
    (hE : E ⊆ V.product W) (hstr : isStruct N E) (w : ℕ) :
    ∑ v ∈ nhoodSnd E w, wgt N v ≤ (v0p E N w : ℝ) := by
  have hpos : ∀ n ∈ nhoodSnd E w, 0 < n := fun n hn =>
    lt_of_lt_of_le Nat.zero_lt_one (hV n (nhoodSnd_subset hE w hn))
  have hstr' : ∀ n ∈ nhoodSnd E w, ∀ p : ℕ, p.Prime → padicValNat p n ≤ padicValNat p N + 1 ∧
      padicValNat p N ≤ padicValNat p n + 1 := fun n hn => str_fst hstr ((mem_nhoodSnd (E := E) (v := n) (w := w)).mp hn)
  have hB : ∀ n ∈ nhoodSnd E w, vplus N n ≤ v0p E N w := by
    intro n hn
    exact le_v0p E N n w ((mem_nhoodSnd (E := E) (v := n) (w := w)).mp hn)
  have h1 := sum_phi_div_vminus_le N hN (nhoodSnd E w) (v0p E N w) (fun _ => True) hB hpos hstr'
  have h2 : (∑ d ∈ N.divisors, (if (fun _ => True) d then ((N/d).totient : ℝ) else 0)) / (N:ℝ) = 1 := by
    have h3 : (∑ d ∈ N.divisors, ((N/d).totient : ℝ)) = (N:ℝ) := by
      rw [← Nat.cast_sum, sum_divisors_totient_div]
    rw [show (∑ d ∈ N.divisors, (if (fun _ => True) d then ((N/d).totient : ℝ) else 0))
        = ∑ d ∈ N.divisors, ((N/d).totient : ℝ) from by
      apply Finset.sum_congr rfl
      intro d _
      simp]
    rw [h3]
    field_simp
  calc ∑ v ∈ nhoodSnd E w, wgt N v
      ≤ (v0p E N w : ℝ) * ((∑ d ∈ N.divisors, (if (fun _ => True) d then ((N/d).totient : ℝ) else 0)) / (N:ℝ)) := by
        rw [show (∑ v ∈ nhoodSnd E w, wgt N v)
            = ∑ v ∈ nhoodSnd E w, (if (fun _ => True) (vminus N v) then wgt N v else 0) from by
          apply Finset.sum_congr rfl; intro v _; simp]
        exact h1
    _ = (v0p E N w : ℝ) := by rw [h2, mul_one]

/-- The `w`-sum, no anatomy. -/
lemma bw_plain (hN : 0 < N) (hW : ∀ w ∈ W, 1 ≤ w)
    (hE : E ⊆ V.product W) (hstr : isStruct N E)
    (w0 : ℕ) (hw0 : w0 ∈ E.image Prod.snd)
    (hwmax : ∀ w ∈ E.image Prod.snd, vplus N w ≤ vplus N w0) :
    ∑ w ∈ E.image Prod.snd, wgt N w ≤ (vplus N w0 : ℝ) := by
  have hpos : ∀ n ∈ E.image Prod.snd, 0 < n := by
    intro n hn
    obtain ⟨e, he, hne⟩ := Finset.mem_image.mp hn
    rw [← hne]
    exact lt_of_lt_of_le Nat.zero_lt_one (hW e.2 (Finset.mem_product.mp (hE he)).2)
  have hstr' : ∀ n ∈ E.image Prod.snd, ∀ p : ℕ, p.Prime → padicValNat p n ≤ padicValNat p N + 1 ∧
      padicValNat p N ≤ padicValNat p n + 1 := by
    intro n hn
    obtain ⟨e, he, hne⟩ := Finset.mem_image.mp hn
    rw [← hne]
    exact str_snd hstr he
  have hB : ∀ n ∈ E.image Prod.snd, vplus N n ≤ vplus N w0 := hwmax
  have h1 := sum_phi_div_vminus_le N hN (E.image Prod.snd) (vplus N w0) (fun _ => True) hB hpos hstr'
  have h2 : (∑ d ∈ N.divisors, (if (fun _ => True) d then ((N/d).totient : ℝ) else 0)) / (N:ℝ) = 1 := by
    have h3 : (∑ d ∈ N.divisors, ((N/d).totient : ℝ)) = (N:ℝ) := by
      rw [← Nat.cast_sum, sum_divisors_totient_div]
    rw [show (∑ d ∈ N.divisors, (if (fun _ => True) d then ((N/d).totient : ℝ) else 0))
        = ∑ d ∈ N.divisors, ((N/d).totient : ℝ) from by
      apply Finset.sum_congr rfl
      intro d _
      simp]
    rw [h3]
    field_simp
  calc ∑ w ∈ E.image Prod.snd, wgt N w
      ≤ (vplus N w0 : ℝ) * ((∑ d ∈ N.divisors, (if (fun _ => True) d then ((N/d).totient : ℝ) else 0)) / (N:ℝ)) := by
        rw [show (∑ w ∈ E.image Prod.snd, wgt N w)
            = ∑ w ∈ E.image Prod.snd, (if (fun _ => True) (vminus N w) then wgt N w else 0) from by
          apply Finset.sum_congr rfl; intro v _; simp]
        exact h1
    _ = (vplus N w0 : ℝ) := by rw [h2, mul_one]

/-- Inner `v`-sum bound, anatomy on `v⁻`. -/
lemma bv_anat_minus (hN : 0 < N) (ht : 1 ≤ t) (hC : 0 ≤ C)
    (hV : ∀ v ∈ V, 1 ≤ v) (hE : E ⊆ V.product W) (hstr : isStruct N E) (w : ℕ) :
    ∑ v ∈ nhoodSnd E w, (if anat t (C/4) (vminus N v) then wgt N v else 0)
      ≤ (v0p E N w : ℝ) * AA C t := by
  rcases eq_or_lt_of_le hC with h0 | hCpos
  · subst h0
    have hsum : (∑ v ∈ nhoodSnd E w, (if anat t ((0:ℝ)/4) (vminus N v) then wgt N v else 0))
        = ∑ v ∈ nhoodSnd E w, wgt N v := by
      apply Finset.sum_congr rfl; intro v _
      have h1 : anat t ((0:ℝ)/4) (vminus N v) := by
        unfold anat; norm_num; exact Lt_nonneg t _
      rw [if_pos h1]
    rw [hsum]
    have h1 := bv_plain hN hV hE hstr w
    have hAA : (1:ℝ) ≤ AA 0 t := by
      unfold AA
      rw [show (20 * ((0:ℝ)/4) * max t 2) = 0 by norm_num,
        show -((0:ℝ)) = 0 by norm_num, Real.exp_zero, mul_one]
      exact Real.one_le_exp (by positivity)
    nlinarith [h1, hAA]
  have hpos : ∀ n ∈ nhoodSnd E w, 0 < n := fun n hn =>
    lt_of_lt_of_le Nat.zero_lt_one (hV n (nhoodSnd_subset hE w hn))
  have hstr' : ∀ n ∈ nhoodSnd E w, ∀ p : ℕ, p.Prime → padicValNat p n ≤ padicValNat p N + 1 ∧
      padicValNat p N ≤ padicValNat p n + 1 := fun n hn => str_fst hstr ((mem_nhoodSnd (E := E) (v := n) (w := w)).mp hn)
  have hB : ∀ n ∈ nhoodSnd E w, vplus N n ≤ v0p E N w := by
    intro n hn
    exact le_v0p E N n w ((mem_nhoodSnd (E := E) (v := n) (w := w)).mp hn)
  have h1 := sum_phi_div_vminus_le N hN (nhoodSnd E w) (v0p E N w) (anat t (C/4)) hB hpos hstr'
  have h2 : (∑ d ∈ N.divisors, (if anat t (C/4) d then ((N/d).totient : ℝ) else 0)) / (N:ℝ)
      ≤ AA C t := divisor_anat_le hN ht hCpos (anat t (C/4)) (fun d hd => hd)
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))

/-- Inner `v`-sum bound, anatomy on `v⁺`. -/
lemma bv_anat_plus (hN : 0 < N) (ht : 1 ≤ t) (hC : 0 ≤ C)
    (hV : ∀ v ∈ V, 1 ≤ v) (hE : E ⊆ V.product W) (hstr : isStruct N E) (w : ℕ) :
    ∑ v ∈ nhoodSnd E w, (if anat t (C/4) (vplus N v) then wgt N v else 0)
      ≤ (v0p E N w : ℝ) * AA C t := by
  rcases eq_or_lt_of_le hC with h0 | hCpos
  · subst h0
    have hsum : (∑ v ∈ nhoodSnd E w, (if anat t ((0:ℝ)/4) (vplus N v) then wgt N v else 0))
        = ∑ v ∈ nhoodSnd E w, wgt N v := by
      apply Finset.sum_congr rfl; intro v _
      have h1 : anat t ((0:ℝ)/4) (vplus N v) := by
        unfold anat; norm_num; exact Lt_nonneg t _
      rw [if_pos h1]
    rw [hsum]
    have h1 := bv_plain hN hV hE hstr w
    have hAA : (1:ℝ) ≤ AA 0 t := by
      unfold AA
      rw [show (20 * ((0:ℝ)/4) * max t 2) = 0 by norm_num,
        show -((0:ℝ)) = 0 by norm_num, Real.exp_zero, mul_one]
      exact Real.one_le_exp (by positivity)
    nlinarith [h1, hAA]
  have hpos : ∀ n ∈ nhoodSnd E w, 0 < n := fun n hn =>
    lt_of_lt_of_le Nat.zero_lt_one (hV n (nhoodSnd_subset hE w hn))
  have hstr' : ∀ n ∈ nhoodSnd E w, ∀ p : ℕ, p.Prime → padicValNat p n ≤ padicValNat p N + 1 ∧
      padicValNat p N ≤ padicValNat p n + 1 := fun n hn => str_fst hstr ((mem_nhoodSnd (E := E) (v := n) (w := w)).mp hn)
  have hB : ∀ n ∈ nhoodSnd E w, vplus N n ≤ v0p E N w := by
    intro n hn
    exact le_v0p E N n w ((mem_nhoodSnd (E := E) (v := n) (w := w)).mp hn)
  have h1 := sum_phi_div_vplus_le N hN (nhoodSnd E w) (v0p E N w) (anat t (C/4)) hB hpos hstr'
  have h2 : (((Finset.Icc 1 (v0p E N w)).filter (anat t (C/4))).card : ℝ)
      ≤ (v0p E N w : ℝ) * AA C t := by
    have h3 : (((Finset.Icc 1 (v0p E N w)).filter (anat t (C/4))).card : ℝ)
        ≤ (((Finset.Icc 1 (v0p E N w)).filter (anat (max t 2) (C/4))).card : ℝ) := by
      have hsub : (Finset.Icc 1 (v0p E N w)).filter (anat t (C/4))
          ⊆ (Finset.Icc 1 (v0p E N w)).filter (anat (max t 2) (C/4)) := by
        intro n hn
        rw [Finset.mem_filter] at hn ⊢
        exact ⟨hn.1, (anat_max_iff t (C/4) ht n).mpr hn.2⟩
      exact_mod_cast Finset.card_le_card hsub
    refine h3.trans ?_
    have h4 := anatomy_unweighted_aux (v0p E N w) (max t 2) (C/4) (le_max_right t 2) (by linarith)
    refine h4.trans (le_of_eq ?_)
    unfold AA
    ring
  exact h1.trans h2

/-- The `w`-sum with anatomy on `w⁻`. -/
lemma bw_anat_minus (hN : 0 < N) (ht : 1 ≤ t) (hC : 0 ≤ C)
    (hW : ∀ w ∈ W, 1 ≤ w) (hE : E ⊆ V.product W) (hstr : isStruct N E)
    (w0 : ℕ) (hw0 : w0 ∈ E.image Prod.snd)
    (hwmax : ∀ w ∈ E.image Prod.snd, vplus N w ≤ vplus N w0) :
    ∑ w ∈ E.image Prod.snd, (if anat t (C/4) (vminus N w) then wgt N w else 0)
      ≤ (vplus N w0 : ℝ) * AA C t := by
  rcases eq_or_lt_of_le hC with h0 | hCpos
  · subst h0
    have hsum : (∑ w ∈ E.image Prod.snd,
        (if anat t ((0:ℝ)/4) (vminus N w) then wgt N w else 0))
        = ∑ w ∈ E.image Prod.snd, wgt N w := by
      apply Finset.sum_congr rfl; intro v _
      have h1 : anat t ((0:ℝ)/4) (vminus N v) := by
        unfold anat; norm_num; exact Lt_nonneg t _
      rw [if_pos h1]
    rw [hsum]
    have h1 := bw_plain hN hW hE hstr w0 hw0 hwmax
    have hAA : (1:ℝ) ≤ AA 0 t := by
      unfold AA
      rw [show (20 * ((0:ℝ)/4) * max t 2) = 0 by norm_num,
        show -((0:ℝ)) = 0 by norm_num, Real.exp_zero, mul_one]
      exact Real.one_le_exp (by positivity)
    nlinarith [h1, hAA]
  have hpos : ∀ n ∈ E.image Prod.snd, 0 < n := by
    intro n hn
    obtain ⟨e, he, hne⟩ := Finset.mem_image.mp hn
    rw [← hne]
    exact lt_of_lt_of_le Nat.zero_lt_one (hW e.2 (Finset.mem_product.mp (hE he)).2)
  have hstr' : ∀ n ∈ E.image Prod.snd, ∀ p : ℕ, p.Prime → padicValNat p n ≤ padicValNat p N + 1 ∧
      padicValNat p N ≤ padicValNat p n + 1 := by
    intro n hn
    obtain ⟨e, he, hne⟩ := Finset.mem_image.mp hn
    rw [← hne]
    exact str_snd hstr he
  have hB : ∀ n ∈ E.image Prod.snd, vplus N n ≤ vplus N w0 := hwmax
  have h1 := sum_phi_div_vminus_le N hN (E.image Prod.snd) (vplus N w0) (anat t (C/4)) hB hpos hstr'
  have h2 : (∑ d ∈ N.divisors, (if anat t (C/4) d then ((N/d).totient : ℝ) else 0)) / (N:ℝ)
      ≤ AA C t := divisor_anat_le hN ht hCpos (anat t (C/4)) (fun d hd => hd)
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))

/-- The `w`-sum with anatomy on `w⁺`. -/
lemma bw_anat_plus (hN : 0 < N) (ht : 1 ≤ t) (hC : 0 ≤ C)
    (hW : ∀ w ∈ W, 1 ≤ w) (hE : E ⊆ V.product W) (hstr : isStruct N E)
    (w0 : ℕ) (hw0 : w0 ∈ E.image Prod.snd)
    (hwmax : ∀ w ∈ E.image Prod.snd, vplus N w ≤ vplus N w0) :
    ∑ w ∈ E.image Prod.snd, (if anat t (C/4) (vplus N w) then wgt N w else 0)
      ≤ (vplus N w0 : ℝ) * AA C t := by
  rcases eq_or_lt_of_le hC with h0 | hCpos
  · subst h0
    have hsum : (∑ w ∈ E.image Prod.snd,
        (if anat t ((0:ℝ)/4) (vplus N w) then wgt N w else 0))
        = ∑ w ∈ E.image Prod.snd, wgt N w := by
      apply Finset.sum_congr rfl; intro v _
      have h1 : anat t ((0:ℝ)/4) (vplus N v) := by
        unfold anat; norm_num; exact Lt_nonneg t _
      rw [if_pos h1]
    rw [hsum]
    have h1 := bw_plain hN hW hE hstr w0 hw0 hwmax
    have hAA : (1:ℝ) ≤ AA 0 t := by
      unfold AA
      rw [show (20 * ((0:ℝ)/4) * max t 2) = 0 by norm_num,
        show -((0:ℝ)) = 0 by norm_num, Real.exp_zero, mul_one]
      exact Real.one_le_exp (by positivity)
    nlinarith [h1, hAA]
  have hpos : ∀ n ∈ E.image Prod.snd, 0 < n := by
    intro n hn
    obtain ⟨e, he, hne⟩ := Finset.mem_image.mp hn
    rw [← hne]
    exact lt_of_lt_of_le Nat.zero_lt_one (hW e.2 (Finset.mem_product.mp (hE he)).2)
  have hstr' : ∀ n ∈ E.image Prod.snd, ∀ p : ℕ, p.Prime → padicValNat p n ≤ padicValNat p N + 1 ∧
      padicValNat p N ≤ padicValNat p n + 1 := by
    intro n hn
    obtain ⟨e, he, hne⟩ := Finset.mem_image.mp hn
    rw [← hne]
    exact str_snd hstr he
  have hB : ∀ n ∈ E.image Prod.snd, vplus N n ≤ vplus N w0 := hwmax
  have h1 := sum_phi_div_vplus_le N hN (E.image Prod.snd) (vplus N w0) (anat t (C/4)) hB hpos hstr'
  have h2 : (((Finset.Icc 1 (vplus N w0)).filter (anat t (C/4))).card : ℝ)
      ≤ (vplus N w0 : ℝ) * AA C t := by
    have h3 : (((Finset.Icc 1 (vplus N w0)).filter (anat t (C/4))).card : ℝ)
        ≤ (((Finset.Icc 1 (vplus N w0)).filter (anat (max t 2) (C/4))).card : ℝ) := by
      have hsub : (Finset.Icc 1 (vplus N w0)).filter (anat t (C/4))
          ⊆ (Finset.Icc 1 (vplus N w0)).filter (anat (max t 2) (C/4)) := by
        intro n hn
        rw [Finset.mem_filter] at hn ⊢
        exact ⟨hn.1, (anat_max_iff t (C/4) ht n).mpr hn.2⟩
      exact_mod_cast Finset.card_le_card hsub
    refine h3.trans ?_
    have h4 := anatomy_unweighted_aux (vplus N w0) (max t 2) (C/4) (le_max_right t 2) (by linarith)
    refine h4.trans (le_of_eq ?_)
    unfold AA
    ring
  exact h1.trans h2

end SBounds

section Assemble

variable {N : ℕ} {V W : Finset ℕ} {a b : ℕ → ℝ} {t C : ℝ} {E : Finset (ℕ × ℕ)}

/-- Dropping a conjunct from an `if`, with nonnegative factors. -/
lemma ite_and_le (P Q : Prop) [Decidable P] [Decidable Q] {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (if P ∧ Q then x * y else 0) ≤ y * (if Q then x else 0) := by
  by_cases hQ : Q <;> by_cases hP : P
  · have h1 : (if P ∧ Q then x * y else (0:ℝ)) = x * y := if_pos ⟨hP, hQ⟩
    have h2 : (if Q then x else (0:ℝ)) = x := if_pos hQ
    rw [h1, h2]
    exact le_of_eq (mul_comm x y)
  · have h1 : (if P ∧ Q then x * y else (0:ℝ)) = 0 := if_neg (fun h => hP h.1)
    have h2 : (if Q then x else (0:ℝ)) = x := if_pos hQ
    rw [h1, h2]
    exact mul_nonneg hy hx
  · have h1 : (if P ∧ Q then x * y else (0:ℝ)) = 0 := if_neg (fun h => hQ h.2)
    have h2 : (if Q then x else (0:ℝ)) = 0 := if_neg hQ
    rw [h1, h2, mul_zero]
  · have h1 : (if P ∧ Q then x * y else (0:ℝ)) = 0 := if_neg (fun h => hQ h.2)
    have h2 : (if Q then x else (0:ℝ)) = 0 := if_neg hQ
    rw [h1, h2, mul_zero]

/-- Bound of the `v`-anatomy part of the one-sided mass. -/
lemma S_v_bound (hN : 0 < N) (ht : 1 ≤ t) (hC : 0 ≤ C)
    (hV : ∀ v ∈ V, 1 ≤ v) (hW : ∀ w ∈ W, 1 ≤ w)
    (ha0 : ∀ v, 0 ≤ a v) (hb0 : ∀ w, 0 ≤ b w)
    (hE : E ⊆ V.product W) (hstr : isStruct N E)
    (hgood : ∀ e ∈ E, good t C a b e.1 e.2) (w0 : ℕ) (hw0 : w0 ∈ E.image Prod.snd)
    (Q : ℕ → Prop) [DecidablePred Q]
    (hQ : ∀ w ∈ E.image Prod.snd,
      ∑ v ∈ nhoodSnd E w, (if Q v then wgt N v else 0) ≤ (v0p E N w : ℝ) * AA C t)
    (hwn : ∑ w ∈ E.image Prod.snd, wgt N w ≤ (vplus N w0 : ℝ)) :
    (∑ v ∈ V, ∑ w ∈ E.image Prod.snd,
        (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q v then a v * b w else 0)) ≤ AA C t := by
  have haa : ∀ v, (v,w0) ∈ E → a v ≤ wgt N v / (vplus N w0) :=
    fun v hv => a_le hN hV hW hE hstr hgood hv
  have hbb : ∀ v w, (v,w) ∈ E → b w ≤ wgt N w / (v0p E N w) :=
    fun v w hv => b_le N hN V W a b t C hV hW E hE hstr hgood hv
  have hw0p : (0:ℝ) < (vplus N w0 : ℝ) := by
    have := vplus_pos N w0; exact_mod_cast this
  have hpt : ∀ v w, (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q v then a v * b w else 0)
      ≤ (1/(vplus N w0 : ℝ)) * (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q v then
          wgt N v * (wgt N w / (v0p E N w)) else 0) := by
    intro v w
    by_cases hI : (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q v
    · rw [if_pos hI, if_pos hI]
      have h1 := haa v hI.1
      have h2 := hbb v w hI.2.1
      calc a v * b w
          ≤ (wgt N v / (vplus N w0)) * (wgt N w / (v0p E N w)) :=
            mul_le_mul h1 h2 (hb0 w) (div_nonneg (wgt_nonneg N v) hw0p.le)
        _ = (1/(vplus N w0 : ℝ)) * (wgt N v * (wgt N w / (v0p E N w))) := by
            field_simp
    · rw [if_neg hI, if_neg hI]
      rw [mul_zero]
  have hfac : ∀ w, (∑ v ∈ V, (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q v then
          wgt N v * (wgt N w / (v0p E N w)) else 0))
      = (wgt N w / (v0p E N w)) * ∑ v ∈ V, (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q v then wgt N v else 0) := by
    intro w
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro v _
    by_cases hI : (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q v
    · rw [if_pos hI, if_pos hI]; ring_nf
    · rw [if_neg hI, if_neg hI]; ring_nf
  have hdrop : ∀ w, (∑ v ∈ V, (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q v then wgt N v else 0))
      ≤ ∑ v ∈ V, (if (v,w) ∈ E ∧ Q v then wgt N v else 0) := by
    intro w
    apply Finset.sum_le_sum; intro v _
    by_cases hI : (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q v
    · rw [if_pos hI, if_pos ⟨hI.2.1, hI.2.2⟩]
    · rw [if_neg hI]
      by_cases h2 : (v,w) ∈ E ∧ Q v
      · rw [if_pos h2]
        exact wgt_nonneg N v
      · rw [if_neg h2]
  have hind : ∀ w, (∑ v ∈ V, (if (v,w) ∈ E ∧ Q v then wgt N v else 0))
      = ∑ v ∈ nhoodSnd E w, (if Q v then wgt N v else 0) := by
    intro w
    rw [show (∑ v ∈ V, (if (v,w) ∈ E ∧ Q v then wgt N v else 0))
        = ∑ v ∈ V, (if (v,w) ∈ E then (if Q v then wgt N v else 0) else 0) from by
      apply Finset.sum_congr rfl; intro v _
      by_cases h1 : (v,w) ∈ E <;> by_cases h2 : Q v <;> simp [h1, h2]]
    exact (sum_nhoodSnd_eq E V (nhoodSnd_subset hE w) (fun v => if Q v then wgt N v else 0)).symm
  have hfinal : (∑ v ∈ V, ∑ w ∈ E.image Prod.snd, (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q v then
          wgt N v * (wgt N w / (v0p E N w)) else 0)) ≤ (AA C t) * (vplus N w0 : ℝ) := by
    calc (∑ v ∈ V, ∑ w ∈ E.image Prod.snd, (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q v then
            wgt N v * (wgt N w / (v0p E N w)) else 0))
        = ∑ w ∈ E.image Prod.snd, (wgt N w / (v0p E N w)) *
            ∑ v ∈ V, (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q v then wgt N v else 0) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun w _ => hfac w)
      _ ≤ ∑ w ∈ E.image Prod.snd, (wgt N w / (v0p E N w)) *
            ∑ v ∈ V, (if (v,w) ∈ E ∧ Q v then wgt N v else 0) := by
          apply Finset.sum_le_sum; intro w _
          exact mul_le_mul_of_nonneg_left (hdrop w)
            (div_nonneg (wgt_nonneg N w) (by positivity))
      _ = ∑ w ∈ E.image Prod.snd, (wgt N w / (v0p E N w)) *
            ∑ v ∈ nhoodSnd E w, (if Q v then wgt N v else 0) := by
          exact Finset.sum_congr rfl (fun w _ => by rw [hind w])
      _ ≤ ∑ w ∈ E.image Prod.snd, (wgt N w / (v0p E N w)) * ((v0p E N w : ℝ) * AA C t) := by
          apply Finset.sum_le_sum; intro w hw
          exact mul_le_mul_of_nonneg_left (hQ w hw)
            (div_nonneg (wgt_nonneg N w) (by positivity))
      _ = ∑ w ∈ E.image Prod.snd, (AA C t) * wgt N w := by
          apply Finset.sum_congr rfl; intro w hw
          have hv0 : (v0p E N w : ℝ) ≠ 0 := by
            have := v0p_pos E N w hw; positivity
          field_simp
      _ = (AA C t) * ∑ w ∈ E.image Prod.snd, wgt N w := by rw [Finset.mul_sum]
      _ ≤ (AA C t) * (vplus N w0 : ℝ) :=
          mul_le_mul_of_nonneg_left hwn (AA_pos C t).le
  calc (∑ v ∈ V, ∑ w ∈ E.image Prod.snd,
        (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q v then a v * b w else 0))
      ≤ (1/(vplus N w0 : ℝ)) * (∑ v ∈ V, ∑ w ∈ E.image Prod.snd,
        (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q v then
          wgt N v * (wgt N w / (v0p E N w)) else 0)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum; intro v _
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum; intro w _
        exact hpt v w
    _ ≤ (1/(vplus N w0 : ℝ)) * ((AA C t) * (vplus N w0 : ℝ)) :=
        mul_le_mul_of_nonneg_left hfinal (by positivity)
    _ = AA C t := by field_simp

/-- Bound of the `w`-anatomy part of the one-sided mass. -/
lemma S_w_bound (hN : 0 < N) (ht : 1 ≤ t) (hC : 0 ≤ C)
    (hV : ∀ v ∈ V, 1 ≤ v) (hW : ∀ w ∈ W, 1 ≤ w)
    (ha0 : ∀ v, 0 ≤ a v) (hb0 : ∀ w, 0 ≤ b w)
    (hE : E ⊆ V.product W) (hstr : isStruct N E)
    (hgood : ∀ e ∈ E, good t C a b e.1 e.2) (w0 : ℕ) (hw0 : w0 ∈ E.image Prod.snd)
    (Q : ℕ → Prop) [DecidablePred Q]
    (hQ : ∀ w ∈ E.image Prod.snd, ∑ v ∈ nhoodSnd E w, wgt N v ≤ (v0p E N w : ℝ))
    (hwn : ∑ w ∈ E.image Prod.snd, (if Q w then wgt N w else 0) ≤ (vplus N w0 : ℝ) * AA C t) :
    (∑ v ∈ V, ∑ w ∈ E.image Prod.snd,
        (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q w then a v * b w else 0)) ≤ AA C t := by
  have haa : ∀ v, (v,w0) ∈ E → a v ≤ wgt N v / (vplus N w0) :=
    fun v hv => a_le hN hV hW hE hstr hgood hv
  have hbb : ∀ v w, (v,w) ∈ E → b w ≤ wgt N w / (v0p E N w) :=
    fun v w hv => b_le N hN V W a b t C hV hW E hE hstr hgood hv
  have hw0p : (0:ℝ) < (vplus N w0 : ℝ) := by
    have := vplus_pos N w0; exact_mod_cast this
  have hpt : ∀ v w, (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q w then a v * b w else 0)
      ≤ (1/(vplus N w0 : ℝ)) * (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q w then
          wgt N v * (wgt N w / (v0p E N w)) else 0) := by
    intro v w
    by_cases hI : (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q w
    · rw [if_pos hI, if_pos hI]
      have h1 := haa v hI.1
      have h2 := hbb v w hI.2.1
      calc a v * b w
          ≤ (wgt N v / (vplus N w0)) * (wgt N w / (v0p E N w)) :=
            mul_le_mul h1 h2 (hb0 w) (div_nonneg (wgt_nonneg N v) hw0p.le)
        _ = (1/(vplus N w0 : ℝ)) * (wgt N v * (wgt N w / (v0p E N w))) := by
            field_simp
    · rw [if_neg hI, if_neg hI]
      rw [mul_zero]
  have hfac : ∀ w, (∑ v ∈ V, (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q w then
          wgt N v * (wgt N w / (v0p E N w)) else 0))
      = (wgt N w / (v0p E N w)) * ∑ v ∈ V, (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q w then wgt N v else 0) := by
    intro w
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro v _
    by_cases hI : (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q w
    · rw [if_pos hI, if_pos hI]; ring_nf
    · rw [if_neg hI, if_neg hI]; ring_nf
  have hdrop : ∀ w, (∑ v ∈ V, (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q w then wgt N v else 0))
      ≤ ∑ v ∈ V, (if (v,w) ∈ E then wgt N v else 0) := by
    intro w
    apply Finset.sum_le_sum; intro v _
    by_cases hI : (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q w
    · rw [if_pos hI, if_pos hI.2.1]
    · rw [if_neg hI]
      by_cases h2 : (v,w) ∈ E
      · rw [if_pos h2]
        exact wgt_nonneg N v
      · rw [if_neg h2]
  have hinn : ∀ w, (∑ v ∈ V, (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q w then
        wgt N v * (wgt N w / (v0p E N w)) else 0))
      = (if Q w then (wgt N w / (v0p E N w)) *
            (∑ v ∈ V, (if (v,w0) ∈ E ∧ (v,w) ∈ E then wgt N v else 0)) else 0) := by
    intro w
    by_cases hQw : Q w
    · rw [if_pos hQw]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro v _
      by_cases hI : (v,w0) ∈ E ∧ (v,w) ∈ E
      · rw [if_pos ⟨hI.1, hI.2, hQw⟩, if_pos hI]; ring
      · rw [if_neg (fun h => hI ⟨h.1, h.2.1⟩), if_neg hI]; ring
    · rw [if_neg hQw]
      rw [Finset.sum_eq_zero]
      intro v _
      rw [if_neg (fun h => hQw h.2.2)]
  have hswap : (∑ v ∈ V, ∑ w ∈ E.image Prod.snd, (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q w then
          wgt N v * (wgt N w / (v0p E N w)) else 0))
      = ∑ w ∈ E.image Prod.snd, (if Q w then (wgt N w / (v0p E N w)) *
            (∑ v ∈ V, (if (v,w0) ∈ E ∧ (v,w) ∈ E then wgt N v else 0)) else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun w _ => hinn w)
  have hfinal : (∑ v ∈ V, ∑ w ∈ E.image Prod.snd, (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q w then
          wgt N v * (wgt N w / (v0p E N w)) else 0)) ≤ (AA C t) * (vplus N w0 : ℝ) := by
    rw [hswap]
    calc ∑ w ∈ E.image Prod.snd, (if Q w then (wgt N w / (v0p E N w)) *
            (∑ v ∈ V, (if (v,w0) ∈ E ∧ (v,w) ∈ E then wgt N v else 0)) else 0)
        ≤ ∑ w ∈ E.image Prod.snd, (if Q w then (wgt N w / (v0p E N w)) *
            (∑ v ∈ V, (if (v,w) ∈ E then wgt N v else 0)) else 0) := by
          apply Finset.sum_le_sum; intro w _
          by_cases hQw : Q w
          · rw [if_pos hQw, if_pos hQw]
            refine mul_le_mul_of_nonneg_left ?_
              (div_nonneg (wgt_nonneg N w) (by positivity))
            apply Finset.sum_le_sum; intro v _
            by_cases h2 : (v,w) ∈ E
            · rw [if_pos h2]
              by_cases h1 : (v,w0) ∈ E
              · rw [if_pos ⟨h1, h2⟩]
              · rw [if_neg (fun h => h1 h.1)]
                exact wgt_nonneg N v
            · rw [if_neg h2]
              by_cases h1 : (v,w0) ∈ E ∧ (v,w) ∈ E
              · exact absurd h1.2 h2
              · rw [if_neg h1]
          · have h1 : (if Q w then (wgt N w / (v0p E N w)) *
                (∑ v ∈ V, (if (v,w0) ∈ E ∧ (v,w) ∈ E then wgt N v else 0)) else (0:ℝ)) = 0 :=
              if_neg hQw
            have h2 : (if Q w then (wgt N w / (v0p E N w)) *
                (∑ v ∈ V, (if (v,w) ∈ E then wgt N v else 0)) else (0:ℝ)) = 0 :=
              if_neg hQw
            rw [h1, h2]
      _ = ∑ w ∈ E.image Prod.snd, (if Q w then (wgt N w / (v0p E N w)) *
            (∑ v ∈ nhoodSnd E w, wgt N v) else 0) := by
          apply Finset.sum_congr rfl; intro w _
          by_cases hQw : Q w
          · rw [if_pos hQw, if_pos hQw]
            congr 1
            exact (sum_nhoodSnd_eq E V (nhoodSnd_subset hE w) (fun v => wgt N v)).symm
          · rw [if_neg hQw]
            try rw [if_neg hQw]
            try exact le_refl 0
      _ ≤ ∑ w ∈ E.image Prod.snd, (if Q w then (wgt N w / (v0p E N w)) * (v0p E N w : ℝ) else 0) := by
          apply Finset.sum_le_sum; intro w hw
          by_cases hQw : Q w
          · rw [if_pos hQw, if_pos hQw]
            exact mul_le_mul_of_nonneg_left (hQ w hw)
              (div_nonneg (wgt_nonneg N w) (by positivity))
          · rw [if_neg hQw]
            try rw [if_neg hQw]
            try exact le_refl 0
      _ = ∑ w ∈ E.image Prod.snd, (if Q w then wgt N w else 0) := by
          apply Finset.sum_congr rfl; intro w hw
          by_cases hQw : Q w
          · rw [if_pos hQw, if_pos hQw]
            have hv0 : (v0p E N w : ℝ) ≠ 0 := by
              have := v0p_pos E N w hw; positivity
            field_simp
          · rw [if_neg hQw]
            try rw [if_neg hQw]
            try exact le_refl 0
      _ ≤ (vplus N w0 : ℝ) * AA C t := hwn
      _ = (AA C t) * (vplus N w0 : ℝ) := by ring
  calc (∑ v ∈ V, ∑ w ∈ E.image Prod.snd,
        (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q w then a v * b w else 0))
      ≤ (1/(vplus N w0 : ℝ)) * (∑ v ∈ V, ∑ w ∈ E.image Prod.snd,
        (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ Q w then
          wgt N v * (wgt N w / (v0p E N w)) else 0)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum; intro v _
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum; intro w _
        exact hpt v w
    _ ≤ (1/(vplus N w0 : ℝ)) * ((AA C t) * (vplus N w0 : ℝ)) :=
        mul_le_mul_of_nonneg_left hfinal (by positivity)
    _ = AA C t := by field_simp

end Assemble

/-- `T_eq` with arbitrary bounding finsets. -/
lemma T_eq' (E : Finset (ℕ × ℕ)) (V W' : Finset ℕ) (w0 : ℕ) (a b : ℕ → ℝ)
    (hV : nhoodSnd E w0 ⊆ V) (hW : ∀ v, nhoodFst E v ⊆ W') :
    (∑ v ∈ nhoodSnd E w0, a v * ∑ w ∈ nhoodFst E v, b w)
      = ∑ v ∈ V, ∑ w ∈ W', (if (v,w0) ∈ E ∧ (v,w) ∈ E then a v * b w else 0) := by
  have h1 : ∀ v, a v * (∑ w ∈ nhoodFst E v, b w)
      = ∑ w ∈ W', (if (v,w) ∈ E then a v * b w else 0) := by
    intro v
    rw [Finset.mul_sum]
    exact sum_nhoodFst_eq E W' (hW v) (fun w => a v * b w)
  calc (∑ v ∈ nhoodSnd E w0, a v * ∑ w ∈ nhoodFst E v, b w)
      = ∑ v ∈ nhoodSnd E w0, ∑ w ∈ W', (if (v,w) ∈ E then a v * b w else 0) :=
        Finset.sum_congr rfl (fun v _ => h1 v)
    _ = ∑ v ∈ V, (if (v,w0) ∈ E then
          ∑ w ∈ W', (if (v,w) ∈ E then a v * b w else 0) else 0) :=
        (sum_nhoodSnd_eq E V hV _)
    _ = ∑ v ∈ V, ∑ w ∈ W', (if (v,w0) ∈ E ∧ (v,w) ∈ E then a v * b w else 0) := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases h : (v,w0) ∈ E
        · rw [if_pos h]
          apply Finset.sum_congr rfl
          intro w _
          by_cases h2 : (v,w) ∈ E
          · rw [if_pos h2, if_pos ⟨h, h2⟩]
          · rw [if_neg h2, if_neg (fun hc => h2 hc.2)]
        · rw [if_neg h]
          rw [Finset.sum_eq_zero]
          intro w _
          rw [if_neg (fun hc => h hc.1)]

/-- At least one of four `if`s carries the value. -/
lemma ite_c_le_sum_four (I Q P1 P2 P3 P4 : Prop) [Decidable I] [Decidable Q] [Decidable P1]
    [Decidable P2] [Decidable P3] [Decidable P4] (h : I → Q → P1 ∨ P2 ∨ P3 ∨ P4) {c : ℝ}
    (hc : 0 ≤ c) :
    (if I ∧ Q then c else 0) ≤ (if I ∧ Q ∧ P1 then c else 0) + (if I ∧ Q ∧ P2 then c else 0)
      + (if I ∧ Q ∧ P3 then c else 0) + (if I ∧ Q ∧ P4 then c else 0) := by
  have h1 : 0 ≤ (if I ∧ Q ∧ P1 then c else 0) := by
    by_cases h' : I ∧ Q ∧ P1
    · rw [if_pos h']; exact hc
    · rw [if_neg h']
  have h2 : 0 ≤ (if I ∧ Q ∧ P2 then c else 0) := by
    by_cases h' : I ∧ Q ∧ P2
    · rw [if_pos h']; exact hc
    · rw [if_neg h']
  have h3 : 0 ≤ (if I ∧ Q ∧ P3 then c else 0) := by
    by_cases h' : I ∧ Q ∧ P3
    · rw [if_pos h']; exact hc
    · rw [if_neg h']
  have h4 : 0 ≤ (if I ∧ Q ∧ P4 then c else 0) := by
    by_cases h' : I ∧ Q ∧ P4
    · rw [if_pos h']; exact hc
    · rw [if_neg h']
  by_cases hI : I
  · by_cases hQ : Q
    · rw [if_pos ⟨hI, hQ⟩]
      rcases h hI hQ with hp | hp | hp | hp
      · have e1 : (if I ∧ Q ∧ P1 then c else 0) = c := if_pos ⟨hI, hQ, hp⟩
        rw [e1]; linarith
      · have e1 : (if I ∧ Q ∧ P2 then c else 0) = c := if_pos ⟨hI, hQ, hp⟩
        rw [e1]; linarith
      · have e1 : (if I ∧ Q ∧ P3 then c else 0) = c := if_pos ⟨hI, hQ, hp⟩
        rw [e1]; linarith
      · have e1 : (if I ∧ Q ∧ P4 then c else 0) = c := if_pos ⟨hI, hQ, hp⟩
        rw [e1]; linarith
    · rw [if_neg (fun h' => hQ h'.2)]
      have e1 : (if I ∧ Q ∧ P1 then c else 0) = 0 := if_neg (fun h' => hQ h'.2.1)
      have e2 : (if I ∧ Q ∧ P2 then c else 0) = 0 := if_neg (fun h' => hQ h'.2.1)
      have e3 : (if I ∧ Q ∧ P3 then c else 0) = 0 := if_neg (fun h' => hQ h'.2.1)
      have e4 : (if I ∧ Q ∧ P4 then c else 0) = 0 := if_neg (fun h' => hQ h'.2.1)
      rw [e1, e2, e3, e4]; norm_num
  · rw [if_neg (fun h' => hI h'.1)]
    have e1 : (if I ∧ Q ∧ P1 then c else 0) = 0 := if_neg (fun h' => hI h'.1)
    have e2 : (if I ∧ Q ∧ P2 then c else 0) = 0 := if_neg (fun h' => hI h'.1)
    have e3 : (if I ∧ Q ∧ P3 then c else 0) = 0 := if_neg (fun h' => hI h'.1)
    have e4 : (if I ∧ Q ∧ P4 then c else 0) = 0 := if_neg (fun h' => hI h'.1)
    rw [e1, e2, e3, e4]; norm_num

/-- The half bound of the resolving proposition. -/
lemma half_bound (N : ℕ) (hN : 0 < N) (V W : Finset ℕ) (a b : ℕ → ℝ) (t C : ℝ)
    (hC : 0 ≤ C) (ht : 1 ≤ t) (hV : ∀ v ∈ V, 1 ≤ v) (hW : ∀ w ∈ W, 1 ≤ w)
    (ha0 : ∀ v, 0 ≤ a v) (hb0 : ∀ w, 0 ≤ b w)
    (E : Finset (ℕ × ℕ)) (hE : E ⊆ V.product W) (hstr : isStruct N E)
    (hgood : ∀ e ∈ E, good t C a b e.1 e.2) (hreg : regular a b E) :
    (pairMass a b E)^2 ≤ (100/9) * Real.exp (21 * Real.exp 20) * Real.exp (-(5 * C * t))
      * (mass a V * mass b W) := by
  rcases eq_empty_or_nonempty E with h0 | hne
  · subst h0
    have hp0 : pairMass a b (∅ : Finset (ℕ × ℕ)) = 0 := by simp [pairMass]
    rw [hp0]
    have h1 : 0 ≤ mass a V := mass_nonneg a ha0 V
    have h2 : 0 ≤ mass b W := mass_nonneg b hb0 W
    have h3 : (0:ℝ) ≤ Real.exp (21 * Real.exp 20) := (Real.exp_pos _).le
    have h4 : (0:ℝ) ≤ Real.exp (-(5*C*t)) := (Real.exp_pos _).le
    have hp0 : pairMass a b (∅ : Finset (ℕ × ℕ)) = 0 := by simp [pairMass]
    rw [zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    positivity
  · obtain ⟨w0, hw0, hw0max⟩ := Finset.exists_max_image (E.image Prod.snd) (fun w => vplus N w)
      (hne.image Prod.snd)
    have hVsub : nhoodSnd E w0 ⊆ V := nhoodSnd_subset hE w0
    have hVsub2 : E.image Prod.fst ⊆ V := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_product.mp (hE he)).1
    have hWsub2 : E.image Prod.snd ⊆ W := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_product.mp (hE he)).2
    have hW'sub : ∀ v, nhoodFst E v ⊆ E.image Prod.snd := by
      intro v w hw
      exact Finset.mem_image.mpr ⟨(v,w), mem_nhoodFst.mp hw, rfl⟩
    -- the four sums
    set S1 : ℝ := ∑ v ∈ V, ∑ w ∈ E.image Prod.snd,
      (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ anat t (C/4) (vminus N v) then a v * b w else 0) with hS1
    set S2 : ℝ := ∑ v ∈ V, ∑ w ∈ E.image Prod.snd,
      (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ anat t (C/4) (vplus N v) then a v * b w else 0) with hS2
    set S3 : ℝ := ∑ v ∈ V, ∑ w ∈ E.image Prod.snd,
      (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ anat t (C/4) (vminus N w) then a v * b w else 0) with hS3
    set S4 : ℝ := ∑ v ∈ V, ∑ w ∈ E.image Prod.snd,
      (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ anat t (C/4) (vplus N w) then a v * b w else 0) with hS4
    have hcases := four_cases N hN V W a b t C hC hV hW E hE hstr hgood
    have hT4 : (∑ v ∈ V, ∑ w ∈ E.image Prod.snd,
        (if (v,w0) ∈ E ∧ (v,w) ∈ E then a v * b w else 0)) ≤ S1 + S2 + S3 + S4 := by
      rw [hS1, hS2, hS3, hS4]
      have hTL : (∑ v ∈ V, ∑ w ∈ E.image Prod.snd,
            (if (v,w0) ∈ E ∧ (v,w) ∈ E then a v * b w else 0))
          ≤ ∑ v ∈ V, ∑ w ∈ E.image Prod.snd,
              ((if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ anat t (C/4) (vminus N v) then a v * b w else 0)
              + (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ anat t (C/4) (vplus N v) then a v * b w else 0)
              + (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ anat t (C/4) (vminus N w) then a v * b w else 0)
              + (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ anat t (C/4) (vplus N w) then a v * b w else 0)) := by
        apply Finset.sum_le_sum; intro v _
        apply Finset.sum_le_sum; intro w _
        exact ite_c_le_sum_four ((v,w0) ∈ E) ((v,w) ∈ E)
          (anat t (C/4) (vminus N v)) (anat t (C/4) (vplus N v))
          (anat t (C/4) (vminus N w)) (anat t (C/4) (vplus N w))
          (fun _ hQ => (show anat t (C/4) (vminus N v) ∨ anat t (C/4) (vplus N v) ∨
              anat t (C/4) (vminus N w) ∨ anat t (C/4) (vplus N w) from
            hcases (v,w) hQ)) (mul_nonneg (ha0 v) (hb0 w))
      have hdist : (∑ v ∈ V, ∑ w ∈ E.image Prod.snd,
              ((if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ anat t (C/4) (vminus N v) then a v * b w else 0)
              + (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ anat t (C/4) (vplus N v) then a v * b w else 0)
              + (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ anat t (C/4) (vminus N w) then a v * b w else 0)
              + (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ anat t (C/4) (vplus N w) then a v * b w else 0)))
          = (∑ v ∈ V, ∑ w ∈ E.image Prod.snd,
                (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ anat t (C/4) (vminus N v) then a v * b w else 0))
            + (∑ v ∈ V, ∑ w ∈ E.image Prod.snd,
                (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ anat t (C/4) (vplus N v) then a v * b w else 0))
            + (∑ v ∈ V, ∑ w ∈ E.image Prod.snd,
                (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ anat t (C/4) (vminus N w) then a v * b w else 0))
            + (∑ v ∈ V, ∑ w ∈ E.image Prod.snd,
                (if (v,w0) ∈ E ∧ (v,w) ∈ E ∧ anat t (C/4) (vplus N w) then a v * b w else 0)) := by
        simp only [Finset.sum_add_distrib]
        try ring
      refine le_trans hTL ?_
      rw [hdist]
    have hb1 : S1 ≤ AA C t :=
      S_v_bound hN ht hC hV hW ha0 hb0 hE hstr hgood w0 hw0
        (fun v => anat t (C/4) (vminus N v))
        (fun w hw => bv_anat_minus hN ht hC hV hE hstr w) (bw_plain hN hW hE hstr w0 hw0 hw0max)
    have hb2 : S2 ≤ AA C t :=
      S_v_bound hN ht hC hV hW ha0 hb0 hE hstr hgood w0 hw0
        (fun v => anat t (C/4) (vplus N v))
        (fun w hw => bv_anat_plus hN ht hC hV hE hstr w) (bw_plain hN hW hE hstr w0 hw0 hw0max)
    have hb3 : S3 ≤ AA C t :=
      S_w_bound hN ht hC hV hW ha0 hb0 hE hstr hgood w0 hw0
        (fun w => anat t (C/4) (vminus N w))
        (fun w hw => bv_plain hN hV hE hstr w)
        (bw_anat_minus hN ht hC hW hE hstr w0 hw0 hw0max)
    have hb4 : S4 ≤ AA C t :=
      S_w_bound hN ht hC hV hW ha0 hb0 hE hstr hgood w0 hw0
        (fun w => anat t (C/4) (vplus N w))
        (fun w hw => bv_plain hN hV hE hstr w)
        (bw_anat_plus hN ht hC hW hE hstr w0 hw0 hw0max)
    have hT : (∑ v ∈ nhoodSnd E w0, a v * ∑ w ∈ nhoodFst E v, b w) ≤ 4 * AA C t := by
      rw [T_eq' E V (E.image Prod.snd) w0 a b hVsub hW'sub]
      linarith [hT4, hb1, hb2, hb3, hb4]
    have halg := half_bound_algebra a b E w0 ha0 hb0 hw0 hreg
    have hm1 : mass a (E.image Prod.fst) ≤ mass a V := mass_mono a ha0 hVsub2
    have hm2 : mass b (E.image Prod.snd) ≤ mass b W := mass_mono b hb0 hWsub2
    have hm0a : 0 ≤ mass a (E.image Prod.fst) := mass_nonneg a ha0 _
    have hm0b : 0 ≤ mass b (E.image Prod.snd) := mass_nonneg b hb0 _
    have hAA : AA C t ≤ Real.exp (21 * Real.exp 20) * Real.exp (-(5 * C * t)) := by
      unfold AA
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply Real.exp_le_exp.mpr
      nlinarith [le_max_right t 2, le_max_left t 2, hC]
    have hT0 : 0 ≤ (∑ v ∈ nhoodSnd E w0, a v * ∑ w ∈ nhoodFst E v, b w) :=
      Finset.sum_nonneg (fun v _ => mul_nonneg (ha0 v)
        (Finset.sum_nonneg (fun w _ => hb0 w)))
    have hμab : 0 ≤ mass a V * mass b W :=
      mul_nonneg (mass_nonneg a ha0 V) (mass_nonneg b hb0 W)
    have hstep : mass a (E.image Prod.fst) * mass b (E.image Prod.snd)
          * (∑ v ∈ nhoodSnd E w0, a v * ∑ w ∈ nhoodFst E v, b w)
        ≤ mass a V * mass b W * (4 * AA C t) := by
      have hμ' : mass a (E.image Prod.fst) * mass b (E.image Prod.snd) ≤ mass a V * mass b W :=
        mul_le_mul hm1 hm2 hm0b (mass_nonneg a ha0 V)
      exact mul_le_mul hμ' hT hT0 (by positivity)
    calc (pairMass a b E)^2
        ≤ (25/9) * (mass a (E.image Prod.fst) * mass b (E.image Prod.snd)
            * (∑ v ∈ nhoodSnd E w0, a v * ∑ w ∈ nhoodFst E v, b w)) := by
          nlinarith [halg]
      _ ≤ (25/9) * (mass a V * mass b W * (4 * AA C t)) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ ≤ (25/9) * (mass a V * mass b W
            * (4 * (Real.exp (21 * Real.exp 20) * Real.exp (-(5 * C * t))))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_left _ hμab
          exact mul_le_mul_of_nonneg_left hAA (by norm_num)
      _ = (100/9) * Real.exp (21 * Real.exp 20) * Real.exp (-(5 * C * t))
            * (mass a V * mass b W) := by ring

-- =====================   from DS/resolve.lean  =====================
/-- `pairMass` is at most the product of the two masses. -/
lemma pairMass_le_mass_mul (a b : ℕ → ℝ) (ha0 : ∀ v, 0 ≤ a v) (hb0 : ∀ w, 0 ≤ b w)
    (V W : Finset ℕ) (E : Finset (ℕ × ℕ)) (hE : E ⊆ V.product W) :
    pairMass a b E ≤ mass a V * mass b W := by
  have h1 : pairMass a b E ≤ ∑ e ∈ V.product W, a e.1 * b e.2 := by
    unfold pairMass
    exact Finset.sum_le_sum_of_subset_of_nonneg hE
      (fun e _ _ => mul_nonneg (ha0 e.1) (hb0 e.2))
  refine h1.trans (le_of_eq ?_)
  rw [show V.product W = V ×ˢ W from rfl, Finset.sum_product]
  unfold mass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum]

/-- The resolving step: the half bound contradicts property (1).
This is the two-case argument of HWVS §5: if the two masses are small we use the trivial bound
`pairMass ≤ mass a V * mass b W`, and otherwise the mass of the support pays for the missing
exponential decay. -/
theorem resolve_bound (N : ℕ) (hN : 0 < N) (V W : Finset ℕ) (a b : ℕ → ℝ) (t C : ℝ)
    (hC : 0 ≤ C) (ht : 1 ≤ t) (hV : ∀ v ∈ V, 1 ≤ v) (hW : ∀ w ∈ W, 1 ≤ w)
    (ha0 : ∀ v, 0 ≤ a v) (hb0 : ∀ w, 0 ≤ b w)
    (E : Finset (ℕ × ℕ)) (hE : E ⊆ V.product W) (hstr : isStruct N E)
    (hgood : ∀ e ∈ E, good t C a b e.1 e.2) (hreg : regular a b E)
    (P : ℕ)
    (hP : 32 * ((100/9 : ℝ) * Real.exp (21 * Real.exp 20))^2 ≤ (1000:ℝ)^(5*P)) :
    pairMass a b E ≤ (1/2) * 1000^P * (mass a V * mass b W)^((3:ℝ)/5)
      * Real.exp (-(3 * C * t / 5)) := by
  set ι := Real.exp (21 * Real.exp 20) with hι
  set μ := mass a V * mass b W with hμ
  set K := (1000:ℝ)^P with hK
  set E1 := Real.exp (-(C*t)) with hE1
  have hμ0 : 0 ≤ μ := by
    rw [hμ]
    exact mul_nonneg (mass_nonneg a ha0 V) (mass_nonneg b hb0 W)
  have hKpos : 0 < K := by rw [hK]; positivity
  have hE1pos : 0 < E1 := by rw [hE1]; exact Real.exp_pos _
  have hE1le : E1 ≤ 1 := by
    rw [hE1, Real.exp_le_one_iff]
    nlinarith [hC, ht]
  have hι0 : 0 ≤ ι := by rw [hι]; positivity
  have hexp5 : Real.exp (-(5 * C * t)) = E1^5 := by
    rw [hE1, ← Real.exp_nat_mul]
    congr 1
    ring
  have hexp3 : Real.exp (-(3 * C * t / 5)) = E1^((3:ℝ)/5) := by
    rw [hE1, ← Real.exp_mul]
    congr 1
    ring
  have hhalf := half_bound N hN V W a b t C hC ht hV hW ha0 hb0 E hE hstr hgood hreg
  rw [hexp5] at hhalf
  have hgoal : (1/2) * K * μ^((3:ℝ)/5) * E1^((3:ℝ)/5)
      = (1/2) * 1000^P * (mass a V * mass b W)^((3:ℝ)/5) * Real.exp (-(3 * C * t / 5)) := by
    rw [hK, hμ, hexp3]
  rw [← hgoal]
  set T := (K/2)^((5:ℝ)/2) * E1^((3:ℝ)/2) with hT
  have hTpos : 0 < T := by
    rw [hT]
    exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos hE1pos _)
  by_cases hcase : μ ≤ T
  · -- Case A: the total mass is small
    by_cases hμzero : μ = 0
    · rw [hμzero, Real.zero_rpow (by norm_num : (3:ℝ)/5 ≠ 0)]
      have hM0 : pairMass a b E ≤ 0 := by
        rw [← hμzero]
        exact pairMass_le_mass_mul a b ha0 hb0 V W E hE
      simpa using hM0
    · have hμpos : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hμzero)
      have hT25 : T^((2:ℝ)/5) = (K/2) * E1^((3:ℝ)/5) := by
        rw [hT, Real.mul_rpow (by positivity) (Real.rpow_nonneg hE1pos.le _),
          ← Real.rpow_mul (by positivity), ← Real.rpow_mul hE1pos.le,
          show (5:ℝ)/2 * (2/5) = 1 by norm_num, show (3:ℝ)/2 * (2/5) = 3/5 by norm_num,
          Real.rpow_one]
      have h2 : μ^((2:ℝ)/5) ≤ (K/2) * E1^((3:ℝ)/5) := by
        rw [← hT25]
        exact Real.rpow_le_rpow hμ0 hcase (by norm_num)
      have h3 : μ^((3:ℝ)/5) * μ^((2:ℝ)/5) = μ := by
        rw [← Real.rpow_add hμpos, show (3:ℝ)/5 + 2/5 = 1 by norm_num, Real.rpow_one]
      calc pairMass a b E ≤ μ := pairMass_le_mass_mul a b ha0 hb0 V W E hE
        _ = μ^((3:ℝ)/5) * μ^((2:ℝ)/5) := h3.symm
        _ ≤ μ^((3:ℝ)/5) * ((K/2) * E1^((3:ℝ)/5)) :=
            mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hμ0 _)
        _ = (1/2) * K * μ^((3:ℝ)/5) * E1^((3:ℝ)/5) := by ring
  · -- Case B: the total mass is large
    have hTle : T ≤ μ := le_of_lt (not_le.mp hcase)
    have hμpos : 0 < μ := lt_of_lt_of_le hTpos hTle
    have hA0 : 0 ≤ Real.sqrt ((100/9) * ι) := Real.sqrt_nonneg _
    have hMle : pairMass a b E ≤ Real.sqrt ((100/9) * ι) * E1^((5:ℝ)/2) * μ^((1:ℝ)/2) := by
      have h1 : pairMass a b E ≤ Real.sqrt ((100/9) * ι * E1^5 * μ) :=
        (Real.le_sqrt (pairMass_nonneg a b ha0 hb0 E) (by positivity)).mpr hhalf
      have hsqrtE1 : Real.sqrt (E1^5) = E1^((5:ℝ)/2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast E1 5, ← Real.rpow_mul hE1pos.le]
        norm_num
      have hsqrtμ : Real.sqrt μ = μ^((1:ℝ)/2) := Real.sqrt_eq_rpow μ
      have hsqrtprod : Real.sqrt ((100/9) * ι * E1^5 * μ)
          = Real.sqrt ((100/9) * ι) * E1^((5:ℝ)/2) * μ^((1:ℝ)/2) := by
        rw [show ((100/9) * ι * E1^5 * μ) = ((100/9) * ι * E1^5) * μ by ring,
          Real.sqrt_mul (by positivity),
          show ((100/9) * ι * E1^5) = ((100/9) * ι) * E1^5 by ring,
          Real.sqrt_mul (by positivity), hsqrtE1, hsqrtμ]
      rw [hsqrtprod] at h1
      exact h1
    have h4 : K^((5:ℝ)/4) * K^(-((1:ℝ)/4)) = K := by
      rw [← Real.rpow_add hKpos]; norm_num
    have hE1a : E1^((5:ℝ)/2) * E1^(-((3:ℝ)/20)) = E1^((47:ℝ)/20) := by
      rw [← Real.rpow_add hE1pos]
      norm_num
    have hμneg : μ^(-((1:ℝ)/10))
        ≤ 2^((1:ℝ)/4) * K^(-((1:ℝ)/4)) * E1^(-((3:ℝ)/20)) := by
      have h1 : T^(-((1:ℝ)/10)) = (K/2)^(-((1:ℝ)/4)) * E1^(-((3:ℝ)/20)) := by
        rw [hT, Real.mul_rpow (by positivity) (Real.rpow_nonneg hE1pos.le _),
          ← Real.rpow_mul (by positivity), ← Real.rpow_mul hE1pos.le,
          show (5:ℝ)/2 * (-(1/10)) = -(1/4) by norm_num,
          show (3:ℝ)/2 * (-(1/10)) = -(3/20) by norm_num]
      have h3 : (K/2)^(-((1:ℝ)/4)) = 2^((1:ℝ)/4) * K^(-((1:ℝ)/4)) := by
        rw [show (K/2 : ℝ) = K * 2⁻¹ by ring,
          Real.mul_rpow hKpos.le (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
        have h5 : (2:ℝ)⁻¹ ^ (-((1:ℝ)/4)) = 2^((1:ℝ)/4) := by
          rw [Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
            inv_inv]
        rw [h5]
        ring
      have h6 := Real.rpow_le_rpow_of_nonpos hTpos hTle (by norm_num : (-((1:ℝ)/10)) ≤ 0)
      rw [h1, h3] at h6
      exact h6
    have h4 : K^((5:ℝ)/4) * K^(-((1:ℝ)/4)) = K := by
      rw [← Real.rpow_add hKpos]; norm_num
    have hE1id : E1^((47:ℝ)/20) = E1^((7:ℝ)/4) * E1^((3:ℝ)/5) := by
      rw [← Real.rpow_add hE1pos]; norm_num
    have hP' : 32 * ((100/9) * ι)^2 ≤ K^5 := by
      rw [hK, ← pow_mul, show P * 5 = 5 * P by ring]
      exact hP
    have hA4 : (Real.sqrt ((100/9) * ι))^4 = ((100/9) * ι)^2 := by
      rw [show (4:ℕ) = 2*2 by norm_num, pow_mul, Real.sq_sqrt (by positivity)]
    have hA2 : Real.sqrt ((100/9) * ι) * 2^((1:ℝ)/4) ≤ (1/2) * K^((5:ℝ)/4) := by
      rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (4:ℕ) ≠ 0)]
      have h1 : (Real.sqrt ((100/9) * ι) * 2^((1:ℝ)/4))^4 = ((100/9) * ι)^2 * 2 := by
        rw [mul_pow, hA4, ← Real.rpow_natCast (2^((1:ℝ)/4)) 4,
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        norm_num
      have h2 : ((1/2) * K^((5:ℝ)/4))^4 = (1/16) * K^5 := by
        rw [mul_pow, ← Real.rpow_natCast (K^((5:ℝ)/4)) 4, ← Real.rpow_mul hKpos.le]
        norm_num
      rw [h1, h2]
      nlinarith [hP']
    have hE1small : E1^((7:ℝ)/4) ≤ 1 := Real.rpow_le_one hE1pos.le hE1le (by norm_num)
    have hconst2 : Real.sqrt ((100/9) * ι) * 2^((1:ℝ)/4) * E1^((7:ℝ)/4)
        ≤ (1/2) * K^((5:ℝ)/4) := by
      calc Real.sqrt ((100/9) * ι) * 2^((1:ℝ)/4) * E1^((7:ℝ)/4)
          ≤ Real.sqrt ((100/9) * ι) * 2^((1:ℝ)/4) * 1 :=
            mul_le_mul_of_nonneg_left hE1small (by positivity)
        _ ≤ (1/2) * K^((5:ℝ)/4) := by simpa using hA2
    have hconst : Real.sqrt ((100/9) * ι) * 2^((1:ℝ)/4) * K^(-((1:ℝ)/4)) * E1^((47:ℝ)/20)
        ≤ (1/2) * K * E1^((3:ℝ)/5) := by
      have heq : Real.sqrt ((100/9) * ι) * 2^((1:ℝ)/4) * K^(-((1:ℝ)/4)) * E1^((47:ℝ)/20)
          = (Real.sqrt ((100/9) * ι) * 2^((1:ℝ)/4) * E1^((7:ℝ)/4))
            * (K^(-((1:ℝ)/4)) * E1^((3:ℝ)/5)) := by
        rw [hE1id]; ring
      rw [heq]
      calc (Real.sqrt ((100/9) * ι) * 2^((1:ℝ)/4) * E1^((7:ℝ)/4))
            * (K^(-((1:ℝ)/4)) * E1^((3:ℝ)/5))
          ≤ ((1/2) * K^((5:ℝ)/4)) * (K^(-((1:ℝ)/4)) * E1^((3:ℝ)/5)) :=
            mul_le_mul_of_nonneg_right hconst2
              (mul_nonneg (Real.rpow_nonneg hKpos.le _) (Real.rpow_nonneg hE1pos.le _))
        _ = (1/2) * K * E1^((3:ℝ)/5) := by
            rw [show ((1/2) * K^((5:ℝ)/4)) * (K^(-((1:ℝ)/4)) * E1^((3:ℝ)/5))
                = (1/2) * (K^((5:ℝ)/4) * K^(-((1:ℝ)/4))) * E1^((3:ℝ)/5) by ring, h4]
    calc pairMass a b E ≤ Real.sqrt ((100/9) * ι) * E1^((5:ℝ)/2) * μ^((1:ℝ)/2) := hMle
      _ = Real.sqrt ((100/9) * ι) * E1^((5:ℝ)/2) * (μ^((3:ℝ)/5) * μ^(-((1:ℝ)/10))) := by
          rw [← Real.rpow_add hμpos]; norm_num
      _ ≤ Real.sqrt ((100/9) * ι) * E1^((5:ℝ)/2)
            * (μ^((3:ℝ)/5) * (2^((1:ℝ)/4) * K^(-((1:ℝ)/4)) * E1^(-((3:ℝ)/20)))) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.sqrt_nonneg _)
            (Real.rpow_nonneg hE1pos.le _))
          exact mul_le_mul_of_nonneg_left hμneg (Real.rpow_nonneg hμ0 _)
      _ = (Real.sqrt ((100/9) * ι) * 2^((1:ℝ)/4) * K^(-((1:ℝ)/4))) * E1^((47:ℝ)/20)
            * μ^((3:ℝ)/5) := by
          have heq : Real.sqrt ((100/9) * ι) * E1^((5:ℝ)/2) * (μ^((3:ℝ)/5)
                * (2^((1:ℝ)/4) * K^(-((1:ℝ)/4)) * E1^(-((3:ℝ)/20))))
              = (Real.sqrt ((100/9) * ι) * 2^((1:ℝ)/4) * K^(-((1:ℝ)/4)))
                * (E1^((5:ℝ)/2) * E1^(-((3:ℝ)/20))) * μ^((3:ℝ)/5) := by ring
          rw [heq, hE1a]
      _ ≤ ((1/2) * K * E1^((3:ℝ)/5)) * μ^((3:ℝ)/5) :=
          mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hμ0 _)
      _ = (1/2) * K * μ^((3:ℝ)/5) * E1^((3:ℝ)/5) := by ring

-- =====================   from DS/structure.lean  =====================
/-! ## Structure of a minimal counterexample -/

lemma rpow_35_pow5 (z : ℝ) (hz : 0 ≤ z) : (z^((3:ℝ)/5))^5 = z^3 := by
  rw [← Real.rpow_natCast (z^((3:ℝ)/5)) 5, ← Real.rpow_mul hz]
  norm_num

lemma exp_neg_pow5 (x : ℝ) : (Real.exp (-(x/5)))^5 = Real.exp (-x) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Power form to `3/5`-power form. -/
lemma pow5_to_rpow {A K U : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) (hU : 0 ≤ U) {Ct : ℝ}
    (h : A^5 ≤ K^5 * U^3 * Real.exp (-(3*Ct))) :
    A ≤ K * U^((3:ℝ)/5) * Real.exp (-(3*Ct/5)) := by
  have hB0 : 0 ≤ K * U^((3:ℝ)/5) * Real.exp (-(3*Ct/5)) := by
    have := Real.rpow_nonneg hU ((3:ℝ)/5)
    positivity
  rw [← pow_le_pow_iff_left₀ hA hB0 (by norm_num : (5:ℕ) ≠ 0)]
  have hB5 : (K * U^((3:ℝ)/5) * Real.exp (-(3*Ct/5)))^5
      = K^5 * U^3 * Real.exp (-(3*Ct)) := by
    rw [mul_pow, mul_pow, rpow_35_pow5 U hU]
    rw [show Real.exp (-(3*Ct/5)) = Real.exp (-((3*Ct)/5)) by ring_nf]
    rw [exp_neg_pow5]
  rw [hB5]
  exact h

/-- The primes of the reduced support are primes of the original one, shorn of `p`. -/
lemma pset_Vred_subset {p i : ℕ} (hp : p.Prime) (V : Finset ℕ) (hV : ∀ v ∈ V, 1 ≤ v) :
    pset (Vred p i V) ⊆ pset V ∧ p ∉ pset (Vred p i V) := by
  constructor
  · intro u hu
    rw [pset, Finset.mem_biUnion] at hu
    obtain ⟨u', hu', hpu⟩ := hu
    have hdvd : u ∣ u' := (Nat.mem_primeFactors.mp hpu).2.1
    rw [pset, Finset.mem_biUnion]
    rw [Vred, Finset.mem_image] at hu'
    obtain ⟨v, hv, rfl⟩ := hu'
    refine ⟨v, (mem_Vval_iff.mp hv).1,
      Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hpu).1,
        dvd_trans hdvd (Nat.div_dvd_of_dvd (mem_Vval_iff.mp hv).2.1), ?_⟩⟩
    have := hV v (mem_Vval_iff.mp hv).1
    omega
  · intro hp'
    rw [pset, Finset.mem_biUnion] at hp'
    obtain ⟨u', hu', hpu⟩ := hp'
    have hdvd : p ∣ u' := (Nat.mem_primeFactors.mp hpu).2.1
    rw [Vred, Finset.mem_image] at hu'
    obtain ⟨v, hv, rfl⟩ := hu'
    exact Vred_not_dvd hp hv hdvd

lemma pset_union_Vred_ssub {p i j : ℕ} (hp : p.Prime) (V W : Finset ℕ)
    (hV : ∀ v ∈ V, 1 ≤ v) (hW : ∀ w ∈ W, 1 ≤ w) (hpmem : p ∈ pset V ∪ pset W) :
    (pset (Vred p i V) ∪ pset (Vred p j W)).card < (pset V ∪ pset W).card := by
  have h1 := pset_Vred_subset (i := i) hp V hV
  have h2 := pset_Vred_subset (i := j) hp W hW
  have hsub : pset (Vred p i V) ∪ pset (Vred p j W) ⊆ (pset V ∪ pset W) \ {p} := by
    intro u hu
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    rcases Finset.mem_union.mp hu with h | h
    · exact ⟨Finset.mem_union_left _ (h1.1 h), fun hc => h1.2 (hc ▸ h)⟩
    · exact ⟨Finset.mem_union_right _ (h2.1 h), fun hc => h2.2 (hc ▸ h)⟩
  have h3 : ((pset V ∪ pset W) \ {p}).card < (pset V ∪ pset W).card := by
    rw [Finset.card_sdiff, Finset.inter_comm, Finset.inter_singleton_of_mem hpmem]
    have hne : 0 < (pset V ∪ pset W).card := Finset.card_pos.mpr ⟨p, hpmem⟩
    simp only [Finset.card_singleton]
    omega
  exact lt_of_le_of_lt (Finset.card_le_card hsub) h3

/-- The `p`-adic bilinear decomposition of a counterexample. -/
lemma bilinear_bound
    (p₀ Nmax p : ℕ) (V W : Finset ℕ) (a b : ℕ → ℝ) (t C : ℝ) (E : Finset (ℕ × ℕ))
    (hp : p.Prime) (hpmem : p ∈ pset V ∪ pset W)
    (hV : ∀ v ∈ V, 1 ≤ v) (hW : ∀ w ∈ W, 1 ≤ w)
    (ha0 : ∀ v, 0 ≤ a v) (hb0 : ∀ w, 0 ≤ b w)
    (hE : E ⊆ V.product W) (ht : 1 ≤ t) (hC : 0 ≤ C)
    (hgood : ∀ e ∈ E, good t C a b e.1 e.2)
    (hNmaxV : ∀ v ∈ V, v ≤ Nmax) (hNmaxW : ∀ w ∈ W, w ≤ Nmax)
    (hctr : (1000:ℝ)^((p₀ + ((pset V ∪ pset W).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card))
        * (mass a V * mass b W)^((3:ℝ)/5) * Real.exp (-(3*C*t/5)) < pairMass a b E)
    (IH : ∀ (VM WM : Finset ℕ) (aM bM : ℕ → ℝ) (tM CM : ℝ) (EM : Finset (ℕ × ℕ)),
        (pset VM ∪ pset WM).card < (pset V ∪ pset W).card →
        (∀ v ∈ VM, 1 ≤ v) → (∀ w ∈ WM, 1 ≤ w) → (∀ v, 0 ≤ aM v) → (∀ w, 0 ≤ bM w) →
        1 ≤ tM → 0 ≤ CM → EM ⊆ VM.product WM →
        (∀ e ∈ EM, good tM CM aM bM e.1 e.2) →
        pairMass aM bM EM ≤ (1000:ℝ)^((p₀ + ((pset VM ∪ pset WM).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card))
          * (mass aM VM * mass bM WM)^((3:ℝ)/5) * Real.exp (-(3*CM*tM/5))) :
    ∀ i ∈ Finset.range (Nmax+1), ∀ j ∈ Finset.range (Nmax+1),
      pairMass a b (Eval p i j V W E) / pairMass a b E
        ≤ (if p ≤ p₀ then (1/1000:ℝ) else 1) *
          ((if i = j then (1:ℝ) else Real.exp 1 * ((p:ℝ)^(-(2:ℝ)/5))^(Nat.dist i j))
          * (mass a (Vval p i V) / mass a V)^((3:ℝ)/5)
          * (mass b (Vval p j W) / mass b W)^((3:ℝ)/5)) := by
  intro i hi j hj
  -- positivity of the masses
  have hPEpos : 0 < pairMass a b E := by
    have h0 : 0 ≤ (1000:ℝ)^((p₀ + ((pset V ∪ pset W).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card))
        * (mass a V * mass b W)^((3:ℝ)/5) * Real.exp (-(3*C*t/5)) := by
      have h1 : (0:ℝ) ≤ (mass a V * mass b W)^((3:ℝ)/5) :=
        Real.rpow_nonneg (mul_nonneg (mass_nonneg a ha0 V) (mass_nonneg b hb0 W)) _
      have h2 : (0:ℝ) ≤ (1000:ℝ)^((p₀ + ((pset V ∪ pset W).filter
          (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card)) := pow_nonneg (by norm_num) _
      have h3 : (0:ℝ) ≤ Real.exp (-(3*C*t/5)) := (Real.exp_pos _).le
      exact mul_nonneg (mul_nonneg h2 h1) h3
    linarith [hctr, h0]
  have hApos : 0 < mass a V := by
    by_contra hcon
    push_neg at hcon
    have h0 : mass a V = 0 := le_antisymm hcon (mass_nonneg a ha0 V)
    have hz : ∀ v ∈ V, a v = 0 := fun v hv =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha0 i)).mp h0 v hv
    have hp0 : pairMass a b E = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      rw [hz e.1 (Finset.mem_product.mp (hE he)).1, zero_mul]
    linarith [hPEpos]
  have hBpos : 0 < mass b W := by
    by_contra hcon
    push_neg at hcon
    have h0 : mass b W = 0 := le_antisymm hcon (mass_nonneg b hb0 W)
    have hz : ∀ w ∈ W, b w = 0 := fun w hw =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hb0 i)).mp h0 w hw
    have hp0 : pairMass a b E = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      rw [hz e.2 (Finset.mem_product.mp (hE he)).2, mul_zero]
    linarith [hPEpos]
  -- the reduced instance
  set CR : ℝ := max (C - (if i = j then 0 else 1/t)) 0 with hCRdef
  have hCR : 0 ≤ CR := le_max_right _ _
  have hgoodR : ∀ e ∈ Ered p i j V W E, good t CR (ared p i j a) (bred p i j b) e.1 e.2 := by
    intro e he
    have h1 := Ered_good a b t C E hp (by linarith : 0 < t) hgood e he
    have hle : C - (if i = j then 0 else 1/t) ≤ CR := le_max_left _ _
    obtain ⟨hD, hQ⟩ := h1
    refine ⟨hD, ?_⟩
    have h2 : (0:ℝ) ≤ ∑ r ∈ Qset t e.1 e.2, 1/(r:ℝ) :=
      Finset.sum_nonneg (fun r _ => by positivity)
    exact max_le hQ h2
  have hcard : (pset (Vred p i V) ∪ pset (Vred p j W)).card < (pset V ∪ pset W).card :=
    pset_union_Vred_ssub hp V W hV hW hpmem
  have hEred : Ered p i j V W E ⊆ (Vred p i V).product (Vred p j W) := by
    intro e he
    rw [Ered, Finset.mem_image] at he
    obtain ⟨e0, he0, rfl⟩ := he
    rw [Eval, Finset.mem_filter] at he0
    obtain ⟨he0E, he1, he2⟩ := he0
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨e0.1, he1, rfl⟩
    · exact Finset.mem_image.mpr ⟨e0.2, he2, rfl⟩
  have hVred : ∀ v ∈ Vred p i V, 1 ≤ v := fun v hv => by
    rw [Vred, Finset.mem_image] at hv
    obtain ⟨v0, hv0, rfl⟩ := hv
    exact Vred_ge_one hp hv0
  have hWred : ∀ w ∈ Vred p j W, 1 ≤ w := fun v hv => by
    rw [Vred, Finset.mem_image] at hv
    obtain ⟨v0, hv0, rfl⟩ := hv
    exact Vred_ge_one hp hv0
  have hared0 : ∀ v, 0 ≤ ared p i j a v := by
    intro v
    unfold ared
    by_cases h : p ∣ v
    · rw [if_pos h]
    · rw [if_neg h]
      have h3 : (0:ℝ) < ((p^i).totient : ℝ) := by
        have := Nat.totient_pos.mpr (pow_pos hp.pos i)
        exact_mod_cast this
      have h1 : (0:ℝ) ≤ (p:ℝ)^(i + j - min i j) := pow_nonneg (Nat.cast_nonneg p) _
      have h2 : (0:ℝ) ≤ a (p^i * v) := ha0 _
      exact div_nonneg (mul_nonneg h1 h2) h3.le
  have hbred0 : ∀ w, 0 ≤ bred p i j b w := by
    intro v
    unfold bred
    by_cases h : p ∣ v
    · rw [if_pos h]
    · rw [if_neg h]
      have h3 : (0:ℝ) < ((p^j).totient : ℝ) := by
        have := Nat.totient_pos.mpr (pow_pos hp.pos j)
        exact_mod_cast this
      have h1 : (0:ℝ) ≤ (p:ℝ)^(i + j - min i j) := pow_nonneg (Nat.cast_nonneg p) _
      have h2 : (0:ℝ) ≤ b (p^j * v) := hb0 _
      exact div_nonneg (mul_nonneg h1 h2) h3.le
  have hIH := IH (Vred p i V) (Vred p j W) (ared p i j a) (bred p i j b) t CR
    (Ered p i j V W E) hcard hVred hWred hared0 hbred0 ht hCR hEred hgoodR

  -- notation
  set P1 : ℝ := (p:ℝ)^(i + j - min i j) with hP1
  set TP1 : ℝ := ((p^i).totient : ℝ) with hTP1
  set TP2 : ℝ := ((p^j).totient : ℝ) with hTP2
  set X : ℝ := P1^2/(TP1*TP2) with hX
  set PE : ℝ := pairMass a b (Eval p i j V W E) with hPEe
  set PR : ℝ := pairMass (ared p i j a) (bred p i j b) (Ered p i j V W E) with hPRe
  set Ai : ℝ := mass a (Vval p i V) with hAi
  set Bj : ℝ := mass b (Vval p j W) with hBj
  set Knew : ℝ := (1000:ℝ)^((p₀ + ((pset (Vred p i V) ∪ pset (Vred p j W)).filter
      (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card)) with hKnew
  set K0 : ℝ := (1000:ℝ)^((p₀ + ((pset V ∪ pset W).filter
      (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card)) with hK0
  have hP1pos : 0 < P1 := by
    rw [hP1]; exact pow_pos (by exact_mod_cast hp.pos) _
  have hTP1pos : 0 < TP1 := by
    rw [hTP1]
    have := Nat.totient_pos.mpr (pow_pos hp.pos i); exact_mod_cast this
  have hTP2pos : 0 < TP2 := by
    rw [hTP2]
    have := Nat.totient_pos.mpr (pow_pos hp.pos j); exact_mod_cast this
  have hXpos : 0 < X := by rw [hX]; positivity
  have hAi0 : 0 ≤ Ai := mass_nonneg a ha0 _
  have hBj0 : 0 ≤ Bj := mass_nonneg b hb0 _
  have hF1 : PR = X * PE := by
    rw [hPRe, hPEe, hX, hP1, hTP1, hTP2]
    exact pairMass_ered p i j hp a b V W E
  have hAR : mass (ared p i j a) (Vred p i V) = (P1/TP1) * Ai := by
    rw [hAi, hP1, hTP1]
    exact mass_ared p i j hp a V
  have hBR : mass (bred p i j b) (Vred p j W) = (P1/TP2) * Bj := by
    rw [hBj, hP1, hTP2]
    have hfun : bred p i j b = ared p j i b := by
      funext u
      unfold bred ared
      by_cases h : p ∣ u
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
        rw [show i + j - min i j = j + i - min j i by omega]
    rw [hfun]
    have h := mass_ared p j i hp b W
    rw [show j + i - min j i = i + j - min i j by omega] at h
    exact h
  have hABeq : mass (ared p i j a) (Vred p i V) * mass (bred p i j b) (Vred p j W) = X * (Ai * Bj) := by
    rw [hAR, hBR, hX]
    field_simp
    try ring
  -- the IH conclusion
  have hIHb : PR ≤ Knew * (X * (Ai*Bj))^((3:ℝ)/5) * Real.exp (-(3*CR*t/5)) := by
    rw [hPRe, hKnew] at hIH ⊢
    rw [hABeq] at hIH
    exact hIH
  -- remove the X^{-2/5}
  have hPEbound : PE ≤ Knew * X^(-(2:ℝ)/5) * (Ai*Bj)^((3:ℝ)/5) * Real.exp (-(3*CR*t/5)) := by
    have h2 : Knew * (X * (Ai*Bj))^((3:ℝ)/5) * Real.exp (-(3*CR*t/5))
        = Knew * X^((3:ℝ)/5) * (Ai*Bj)^((3:ℝ)/5) * Real.exp (-(3*CR*t/5)) := by
      rw [Real.mul_rpow hXpos.le (mul_nonneg hAi0 hBj0)]
      ring
    have h3 : PE = PR / X := by
      rw [hF1]
      field_simp
    rw [h3]
    calc PR / X ≤ (Knew * X^((3:ℝ)/5) * (Ai*Bj)^((3:ℝ)/5) * Real.exp (-(3*CR*t/5))) / X := by
          apply div_le_div_of_nonneg_right
          · rw [← h2]; exact hIHb
          · exact hXpos.le
      _ = Knew * X^(-(2:ℝ)/5) * (Ai*Bj)^((3:ℝ)/5) * Real.exp (-(3*CR*t/5)) := by
          rw [show (-(2:ℝ)/5) = (3:ℝ)/5 - 1 by norm_num, Real.rpow_sub hXpos, Real.rpow_one]
          field_simp
  -- bound X^{-2/5} by p^{-2 dist/5}
  have hTP1le : TP1 ≤ (p:ℝ)^i := by
    rw [hTP1]
    have := Nat.totient_le (p^i)
    exact_mod_cast this
  have hTP2le : TP2 ≤ (p:ℝ)^j := by
    rw [hTP2]
    have := Nat.totient_le (p^j)
    exact_mod_cast this
  have hXge : (p:ℝ)^(Nat.dist i j) ≤ X := by
    rw [hX, hP1]
    have hden : TP1*TP2 ≤ (p:ℝ)^i * (p:ℝ)^j :=
      mul_le_mul hTP1le hTP2le (by positivity) (by positivity)
    have hdenpos : 0 < TP1*TP2 := mul_pos hTP1pos hTP2pos
    have hden2 : 0 < (p:ℝ)^i * (p:ℝ)^j := by
      have hp1 : (0:ℝ) < p := by exact_mod_cast hp.pos
      positivity
    have h1 : ((p:ℝ)^(i + j - min i j))^2 / ((p:ℝ)^i * (p:ℝ)^j)
        ≤ ((p:ℝ)^(i + j - min i j))^2 / (TP1*TP2) :=
      div_le_div_of_nonneg_left (by positivity) hdenpos hden
    have h2 : ((p:ℝ)^(i + j - min i j))^2 / ((p:ℝ)^i * (p:ℝ)^j)
        = (p:ℝ)^(Nat.dist i j) := by
      have hp1 : (0:ℝ) < p := by exact_mod_cast hp.pos
      rw [← pow_add, ← pow_mul, div_eq_mul_inv,
        ← pow_sub₀ _ hp1.ne'
          (by have h1 : min i j ≤ i := min_le_left _ _; have h2 : min i j ≤ j := min_le_right _ _; omega)]
      congr 1
      rw [Nat.dist_eq_max_sub_min]
      have h1 : min i j ≤ i := min_le_left _ _
      have h2 : min i j ≤ j := min_le_right _ _
      omega
    rw [← h2]
    exact h1
  have hXpow : X^(-(2:ℝ)/5) ≤ ((p:ℝ)^(Nat.dist i j))^(-(2:ℝ)/5) := by
    apply Real.rpow_le_rpow_of_nonpos
    · exact pow_pos (by exact_mod_cast hp.pos) _
    · exact hXge
    · norm_num
  have hpd : ((p:ℝ)^(Nat.dist i j))^(-(2:ℝ)/5) = ((p:ℝ)^(-(2:ℝ)/5))^(Nat.dist i j) := by
    rw [show (p:ℝ)^(Nat.dist i j) = (p:ℝ)^((Nat.dist i j : ℕ) : ℝ) from
      (Real.rpow_natCast (p:ℝ) (Nat.dist i j)).symm]
    rw [show ((p:ℝ)^(-(2:ℝ)/5))^(Nat.dist i j)
        = ((p:ℝ)^(-(2:ℝ)/5))^((Nat.dist i j : ℕ) : ℝ) from
      (Real.rpow_natCast ((p:ℝ)^(-(2:ℝ)/5)) (Nat.dist i j)).symm]
    rw [← Real.rpow_mul (Nat.cast_nonneg p), ← Real.rpow_mul (Nat.cast_nonneg p)]
    congr 1
    ring
  have hPEfin : PE ≤ Knew * ((p:ℝ)^(-(2:ℝ)/5))^(Nat.dist i j) * (Ai*Bj)^((3:ℝ)/5)
      * Real.exp (-(3*CR*t/5)) := by
    refine hPEbound.trans ?_
    rw [hpd] at hXpow
    have hK0' : 0 ≤ Knew := by
      rw [hKnew]; positivity
    have hPj : 0 ≤ ((p:ℝ)^(-(2:ℝ)/5))^(Nat.dist i j) := by
      apply pow_nonneg
      exact Real.rpow_nonneg (Nat.cast_nonneg p) _
    have hABj : 0 ≤ (Ai*Bj)^((3:ℝ)/5) := Real.rpow_nonneg (mul_nonneg hAi0 hBj0) _
    have hstep : Knew * X^(-(2:ℝ)/5) * (Ai*Bj)^((3:ℝ)/5) * Real.exp (-(3*CR*t/5))
        ≤ Knew * ((p:ℝ)^(-(2:ℝ)/5))^(Nat.dist i j) * (Ai*Bj)^((3:ℝ)/5)
          * Real.exp (-(3*CR*t/5)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_right _ hABj
      exact mul_le_mul_of_nonneg_left hXpow hK0'
    exact hstep
  -- constant comparison: the reduced support has lost the prime `p`
  have hKle : Knew ≤ (if p ≤ p₀ then (1/1000:ℝ) else 1) * K0 := by
    have hsub : pset (Vred p i V) ∪ pset (Vred p j W) ⊆ (pset V ∪ pset W) \ {p} := by
      intro u hu
      rw [Finset.mem_sdiff, Finset.mem_singleton]
      have h1 := pset_Vred_subset (i := i) hp V hV
      have h2 := pset_Vred_subset (i := j) hp W hW
      refine ⟨?_, ?_⟩
      · rcases Finset.mem_union.mp hu with h | h
        · exact Finset.mem_union_left _ (h1.1 h)
        · exact Finset.mem_union_right _ (h2.1 h)
      · rintro rfl
        rcases Finset.mem_union.mp hu with h | h
        · exact h1.2 h
        · exact h2.2 h
    have hcard_le : ((pset (Vred p i V) ∪ pset (Vred p j W)).filter
          (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card
        ≤ (((pset V ∪ pset W) \ {p}).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ hsub)
    have hEq : ((pset V ∪ pset W) \ {p}).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)
        = ((pset V ∪ pset W).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)) \ {p} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton]
      tauto
    by_cases hple : p ≤ p₀
    · rw [if_pos hple]
      have hpin : p ∈ (pset V ∪ pset W).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀) := by
        rw [Finset.mem_filter]; exact ⟨hpmem, hp, hple⟩
      have hN1 : 1 ≤ ((pset V ∪ pset W).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card :=
        Finset.card_pos.mpr ⟨p, hpin⟩
      have hcn : ((pset (Vred p i V) ∪ pset (Vred p j W)).filter
            (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card
          ≤ ((pset V ∪ pset W).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card - 1 := by
        refine hcard_le.trans_eq ?_
        rw [hEq, Finset.card_sdiff, Finset.inter_comm,
          Finset.inter_singleton_of_mem hpin, Finset.card_singleton]
      rw [hKnew, hK0]
      have hpown : (1000:ℝ)^((p₀ + ((pset (Vred p i V) ∪ pset (Vred p j W)).filter
            (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card))
          ≤ (1000:ℝ)^(((p₀ + ((pset V ∪ pset W).filter
            (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card)) - 1) := by
        apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 1000)
        omega
      refine hpown.trans ?_
      have hstep : (1000:ℝ)^(((p₀ + ((pset V ∪ pset W).filter
            (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card)) - 1)
          = (1/1000) * (1000:ℝ)^(p₀ + ((pset V ∪ pset W).filter
            (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card) := by
        rw [pow_sub₀ (1000:ℝ) (m := p₀ + ((pset V ∪ pset W).filter
            (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card) (n := 1) (by norm_num) (by omega),
          pow_one]
        ring
      rw [hstep]
    · rw [if_neg hple, one_mul]
      rw [hKnew, hK0]
      apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 1000)
      have : ((pset (Vred p i V) ∪ pset (Vred p j W)).filter
            (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card
          ≤ ((pset V ∪ pset W).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card := by
        refine hcard_le.trans ?_
        rw [hEq]
        exact Finset.card_le_card (Finset.sdiff_subset)
      omega
  -- divide the bilinear bound by the lower bound for pairMass E
  set MA : ℝ := mass a V with hMAdef
  set MB : ℝ := mass b W with hMBdef
  set PE0 : ℝ := pairMass a b E with hPE0def
  set LL : ℝ := Knew * ((p:ℝ)^(-(2:ℝ)/5))^(Nat.dist i j) * (Ai*Bj)^((3:ℝ)/5)
      * Real.exp (-(3*CR*t/5)) with hLLdef
  set XD : ℝ := K0 * (MA*MB)^((3:ℝ)/5) * Real.exp (-(3*C*t/5)) with hXDdef
  set c1 : ℝ := (if p ≤ p₀ then (1/1000:ℝ) else 1) with hc1def
  have hK0pos : 0 < K0 := by rw [hK0]; positivity
  have hXDpos : 0 < XD := by
    rw [hXDdef]
    exact mul_pos (mul_pos hK0pos (Real.rpow_pos_of_pos (mul_pos hApos hBpos) _))
      (Real.exp_pos _)
  have hc1nonneg : 0 ≤ c1 := by
    rw [hc1def]
    by_cases h : p ≤ p₀ <;> simp [h]
  have hLLnonneg : 0 ≤ LL := by
    rw [hLLdef]
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) (Real.exp_pos _).le
    · rw [hKnew]; positivity
    · exact pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) _
    · exact Real.rpow_nonneg (mul_nonneg hAi0 hBj0) _
  have h3 : PE / PE0 ≤ LL / XD := by
    rw [div_le_iff₀ hPEpos]
    have hpx : 1 ≤ PE0 / XD := by
      rw [le_div_iff₀ hXDpos]; linarith [hctr]
    calc PE ≤ LL := hPEfin
      _ = LL * 1 := by ring
      _ ≤ LL * (PE0 / XD) := mul_le_mul_of_nonneg_left hpx hLLnonneg
      _ = LL / XD * PE0 := by ring
  have hABr : (Ai*Bj)^((3:ℝ)/5) / (MA*MB)^((3:ℝ)/5)
      = (Ai/MA)^((3:ℝ)/5) * (Bj/MB)^((3:ℝ)/5) := by
    have h1 : ((Ai*Bj)/(MA*MB))^((3:ℝ)/5) = ((Ai/MA)*(Bj/MB))^((3:ℝ)/5) := by
      congr 1
      field_simp
    rw [← Real.div_rpow (mul_nonneg hAi0 hBj0) (mul_pos hApos hBpos).le, h1,
      Real.mul_rpow (div_nonneg hAi0 hApos.le) (div_nonneg hBj0 hBpos.le)]
  have hexpdiv : Real.exp (-(3*CR*t/5)) / Real.exp (-(3*C*t/5))
      = Real.exp (3*(C-CR)*t/5) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hc1le : Knew / K0 ≤ c1 := by
    rw [hc1def, div_le_iff₀ hK0pos]
    exact hKle
  have hld0 : 0 ≤ ((p:ℝ)^(-(2:ℝ)/5))^(Nat.dist i j) :=
    pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) _
  have hfac : (Knew / K0) * ((p:ℝ)^(-(2:ℝ)/5))^(Nat.dist i j)
        * Real.exp (3*(C-CR)*t/5)
      ≤ c1 * (if i = j then (1:ℝ)
          else Real.exp 1 * ((p:ℝ)^(-(2:ℝ)/5))^(Nat.dist i j)) := by
    by_cases hij : i = j
    · have hCRi : CR = C := by
        rw [hCRdef, if_pos hij, sub_zero]
        exact max_eq_left hC
      have hdist0 : Nat.dist i j = 0 := by rw [hij, Nat.dist_self]
      have hexp0 : Real.exp (3*(C-CR)*t/5) = 1 := by
        rw [hCRi, show 3*(C-C)*t/5 = 0 by ring, Real.exp_zero]
      rw [if_pos hij, hdist0, pow_zero, hexp0]
      simp only [mul_one]
      exact hc1le
    · rw [if_neg hij]
      have hCRle : C - CR ≤ 1/t := by
        have h2 : C - 1/t ≤ CR := by
          rw [hCRdef]
          have h3 : (if i = j then (0:ℝ) else 1/t) = 1/t := if_neg hij
          rw [h3]
          exact le_max_left _ _
        linarith
      have ht0 : (0:ℝ) < t := by linarith
      have hexp1 : Real.exp (3*(C-CR)*t/5) ≤ Real.exp 1 := by
        apply Real.exp_le_exp.mpr
        have h1 : 3*(C-CR)*t ≤ 3*(1/t)*t :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hCRle (by norm_num : (0:ℝ) ≤ 3)) ht0.le
        have h2 : 3*(1/t)*t = 3 := by field_simp
        linarith [h1, h2]
      calc (Knew / K0) * ((p:ℝ)^(-(2:ℝ)/5))^(Nat.dist i j)
            * Real.exp (3*(C-CR)*t/5)
          = ((Knew / K0) * ((p:ℝ)^(-(2:ℝ)/5))^(Nat.dist i j))
            * Real.exp (3*(C-CR)*t/5) := by ring
        _ ≤ (c1 * ((p:ℝ)^(-(2:ℝ)/5))^(Nat.dist i j)) * Real.exp 1 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right hc1le hld0) hexp1
              (Real.exp_pos _).le ?_
            exact mul_nonneg hc1nonneg hld0
        _ = c1 * (Real.exp 1 * ((p:ℝ)^(-(2:ℝ)/5))^(Nat.dist i j)) := by ring
  have hLXeq : LL / XD = (Knew / K0) * ((p:ℝ)^(-(2:ℝ)/5))^(Nat.dist i j)
      * ((Ai*Bj)^((3:ℝ)/5) / (MA*MB)^((3:ℝ)/5))
      * (Real.exp (-(3*CR*t/5)) / Real.exp (-(3*C*t/5))) := by
    rw [hLLdef, hXDdef]
    field_simp
  have hXD2 : LL / XD ≤ c1 * ((if i = j then (1:ℝ)
      else Real.exp 1 * ((p:ℝ)^(-(2:ℝ)/5))^(Nat.dist i j))
      * (Ai/MA)^((3:ℝ)/5) * (Bj/MB)^((3:ℝ)/5)) := by
    rw [hLXeq, hABr, hexpdiv]
    have hX12 : 0 ≤ (Ai/MA)^((3:ℝ)/5) * (Bj/MB)^((3:ℝ)/5) :=
      mul_nonneg (Real.rpow_nonneg (div_nonneg hAi0 hApos.le) _)
        (Real.rpow_nonneg (div_nonneg hBj0 hBpos.le) _)
    calc (Knew / K0) * ((p:ℝ)^(-(2:ℝ)/5))^(Nat.dist i j)
          * ((Ai/MA)^((3:ℝ)/5) * (Bj/MB)^((3:ℝ)/5)) * Real.exp (3*(C-CR)*t/5)
        = ((Knew / K0) * ((p:ℝ)^(-(2:ℝ)/5))^(Nat.dist i j)
            * Real.exp (3*(C-CR)*t/5)) * ((Ai/MA)^((3:ℝ)/5) * (Bj/MB)^((3:ℝ)/5)) := by
          ring
      _ ≤ (c1 * (if i = j then (1:ℝ)
            else Real.exp 1 * ((p:ℝ)^(-(2:ℝ)/5))^(Nat.dist i j)))
            * ((Ai/MA)^((3:ℝ)/5) * (Bj/MB)^((3:ℝ)/5)) :=
          mul_le_mul_of_nonneg_right hfac hX12
      _ = c1 * ((if i = j then (1:ℝ)
            else Real.exp 1 * ((p:ℝ)^(-(2:ℝ)/5))^(Nat.dist i j))
            * (Ai/MA)^((3:ℝ)/5) * (Bj/MB)^((3:ℝ)/5)) := by ring
  exact h3.trans hXD2

-- =====================   from DS/struct2.lean  =====================
/-! ## Step 1 of the structure proposition: decay away from the diagonal -/

/-- `Vval p i V` is empty when `i` exceeds all elements of `V`. -/
lemma Vval_eq_empty_of_lt {p N i : ℕ} (hp : p.Prime) {V : Finset ℕ}
    (hV : ∀ v ∈ V, 1 ≤ v) (hVN : ∀ v ∈ V, v ≤ N) (hi : N < i) : Vval p i V = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro v hv
  rw [mem_Vval_iff] at hv
  obtain ⟨hvV, hdvd, -⟩ := hv
  have h1 : p ^ i ≤ v := Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one (hV v hvV)) hdvd
  have h2 : i < 2 ^ i := Nat.lt_two_pow_self
  have h3 : 2 ^ i ≤ p ^ i := Nat.pow_le_pow_left hp.two_le i
  have h4 : v ≤ N := hVN v hvV
  omega

/-- Removing all edges through a single first-coordinate vertex. -/
lemma pairMass_filter_ne (a b : ℕ → ℝ) (E : Finset (ℕ × ℕ)) (v : ℕ) :
    pairMass a b (E.filter (fun e => e.1 ≠ v))
      = pairMass a b E - a v * ∑ w ∈ nhoodFst E v, b w := by
  have h1 : E.filter (fun e => e.1 ≠ v) = E \ E.filter (fun e => e.1 = v) := by
    ext e
    by_cases h : e.1 = v <;> simp [h]
  have h2 := Finset.sum_sdiff (f := fun e : ℕ × ℕ => a e.1 * b e.2)
    (Finset.filter_subset (fun e : ℕ × ℕ => e.1 = v) E)
  have h3 : ∑ e ∈ E.filter (fun e => e.1 = v), a e.1 * b e.2
      = a v * ∑ e ∈ E.filter (fun e => e.1 = v), b e.2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [(Finset.mem_filter.mp he).2]
  have h4 : ∑ e ∈ E.filter (fun e => e.1 = v), b e.2 = ∑ w ∈ nhoodFst E v, b w := by
    rw [nhoodFst]
    exact (Finset.sum_image (f := b) (g := Prod.snd) (s := E.filter (fun e => e.1 = v))
      (fun x hx y hy hxy => Prod.ext (by rw [(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2]) hxy)).symm
  rw [h1, pairMass, pairMass, ← h2, h3, h4]
  ring

/-- `p^{-2/5} ≤ 4/5` for `p ≥ 2`. -/
lemma prime_rpow_neg_two_fifths (p : ℕ) (hp : 2 ≤ p) :
    (p : ℝ) ^ (-(2 : ℝ) / 5) ≤ 4/5 := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have h2 : (5:ℝ)/4 ≤ (p:ℝ)^((2:ℝ)/5) := by
    rw [← pow_le_pow_iff_left₀ (by norm_num : (0:ℝ) ≤ 5/4)
      (Real.rpow_nonneg hp0.le _) (by norm_num : (5:ℕ) ≠ 0)]
    have hpq : ((p:ℝ)^((2:ℝ)/5))^5 = (p:ℝ)^2 := by
      calc ((p:ℝ)^((2:ℝ)/5))^5
          = (p:ℝ)^((2:ℝ)/5 * ((5:ℕ):ℝ)) := (Real.rpow_mul_natCast hp0.le ((2:ℝ)/5) 5).symm
        _ = (p:ℝ)^(2:ℝ) := by rw [show (2:ℝ)/5 * ((5:ℕ):ℝ) = 2 by norm_num]
        _ = (p:ℝ)^2 := Real.rpow_natCast (p:ℝ) 2
    rw [hpq]
    have h3 : ((2:ℝ))^2 ≤ (p:ℝ)^2 :=
      pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hp) 2
    norm_num at h3 ⊢
    linarith
  have h3 : ((p:ℝ)^((2:ℝ)/5))⁻¹ ≤ ((5:ℝ)/4)⁻¹ :=
    (inv_le_inv₀ (Real.rpow_pos_of_pos hp0 _) (by norm_num)).mpr h2
  have h4 : (p:ℝ)^(-((2:ℝ)/5)) = ((p:ℝ)^((2:ℝ)/5))⁻¹ := Real.rpow_neg hp0.le _
  have h5 : (p:ℝ)^(-(2:ℝ)/5) = (p:ℝ)^(-((2:ℝ)/5)) := by
    rw [show (-(2:ℝ)/5) = -((2:ℝ)/5) by ring]
  rw [h5, h4]
  norm_num at h3 ⊢
  exact h3

/-- A numerical form of the decay contradiction. -/
lemma decay_ratio_gt_one_thousand (lam : ℝ) (_h0 : 0 ≤ lam) (h1 : lam ≤ 4/5) :
    (1/1000 : ℝ) < (1 - lam) / (1 - lam + 2 * Real.exp 1) := by
  have hden : 0 < 1 - lam + 2 * Real.exp 1 := by
    have := Real.exp_pos 1; linarith
  rw [lt_div_iff₀ hden]
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  nlinarith [he, h1]

/-- **Decay step**: applied to a counterexample, the bilinear bound forces the prime `p` to be
larger than `p₀` and concentrates the mass on a diagonal neighbourhood. -/
lemma decay_step
    (p₀ Nmax p : ℕ) (V W : Finset ℕ) (a b : ℕ → ℝ) (t C : ℝ) (E : Finset (ℕ × ℕ))
    (hp : p.Prime) (hpmem : p ∈ pset V ∪ pset W)
    (hV : ∀ v ∈ V, 1 ≤ v) (hW : ∀ w ∈ W, 1 ≤ w)
    (ha0 : ∀ v, 0 ≤ a v) (hb0 : ∀ w, 0 ≤ b w)
    (hE : E ⊆ V.product W) (ht : 1 ≤ t) (hC : 0 ≤ C)
    (hgood : ∀ e ∈ E, good t C a b e.1 e.2)
    (hNmaxV : ∀ v ∈ V, v ≤ Nmax) (hNmaxW : ∀ w ∈ W, w ≤ Nmax)
    (hctr : (1000:ℝ)^((p₀ + ((pset V ∪ pset W).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card))
        * (mass a V * mass b W)^((3:ℝ)/5) * Real.exp (-(3*C*t/5)) < pairMass a b E)
    (IH : ∀ (VM WM : Finset ℕ) (aM bM : ℕ → ℝ) (tM CM : ℝ) (EM : Finset (ℕ × ℕ)),
        (pset VM ∪ pset WM).card < (pset V ∪ pset W).card →
        (∀ v ∈ VM, 1 ≤ v) → (∀ w ∈ WM, 1 ≤ w) → (∀ v, 0 ≤ aM v) → (∀ w, 0 ≤ bM w) →
        1 ≤ tM → 0 ≤ CM → EM ⊆ VM.product WM →
        (∀ e ∈ EM, good tM CM aM bM e.1 e.2) →
        pairMass aM bM EM ≤ (1000:ℝ)^((p₀ + ((pset VM ∪ pset WM).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card))
          * (mass aM VM * mass bM WM)^((3:ℝ)/5) * Real.exp (-(3*CM*tM/5))) :
    p₀ < p ∧ ∃ k ∈ Finset.range (Nmax+1),
      pairMass a b (E.filter (fun e => 2 ≤ Nat.dist (padicValNat p e.1) k
          + Nat.dist (padicValNat p e.2) k))
        ≤ (10:ℝ)^16 * (((p:ℝ)^(-((6:ℝ)/5))) + ((p:ℝ)^(-((7:ℝ)/5)))) * pairMass a b E := by
  have hPEpos : 0 < pairMass a b E := by
    have h0 : 0 ≤ (1000:ℝ)^((p₀ + ((pset V ∪ pset W).filter
          (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card))
        * (mass a V * mass b W)^((3:ℝ)/5) * Real.exp (-(3*C*t/5)) := by
      have h1 : (0:ℝ) ≤ (mass a V * mass b W)^((3:ℝ)/5) :=
        Real.rpow_nonneg (mul_nonneg (mass_nonneg a ha0 V) (mass_nonneg b hb0 W)) _
      have h2 : (0:ℝ) ≤ (1000:ℝ)^((p₀ + ((pset V ∪ pset W).filter
          (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card)) := pow_nonneg (by norm_num) _
      have h3 : (0:ℝ) ≤ Real.exp (-(3*C*t/5)) := (Real.exp_pos _).le
      exact mul_nonneg (mul_nonneg h2 h1) h3
    linarith [hctr, h0]
  have hApos : 0 < mass a V := by
    by_contra hcon
    push_neg at hcon
    have h0 : mass a V = 0 := le_antisymm hcon (mass_nonneg a ha0 V)
    have hz : ∀ v ∈ V, a v = 0 := fun v hv =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha0 i)).mp h0 v hv
    have hp0 : pairMass a b E = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      rw [hz e.1 (Finset.mem_product.mp (hE he)).1, zero_mul]
    linarith [hPEpos]
  have hBpos : 0 < mass b W := by
    by_contra hcon
    push_neg at hcon
    have h0 : mass b W = 0 := le_antisymm hcon (mass_nonneg b hb0 W)
    have hz : ∀ w ∈ W, b w = 0 := fun w hw =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hb0 i)).mp h0 w hw
    have hp0 : pairMass a b E = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      rw [hz e.2 (Finset.mem_product.mp (hE he)).2, mul_zero]
    linarith [hPEpos]
  haveI : Fact p.Prime := ⟨hp⟩
  set lam : ℝ := (p:ℝ)^(-(2:ℝ)/5) with hlamdef
  set c1 : ℝ := (if p ≤ p₀ then (1/1000:ℝ) else 1) with hc1def
  set m : ℕ → ℕ → ℝ := fun i j => pairMass a b (Eval p i j V W E) / pairMass a b E with hmdef
  set xx : ℕ → ℝ := fun i => (mass a (Vval p i V) / mass a V)^((3:ℝ)/5) with hxxdef
  set yy : ℕ → ℝ := fun j => (mass b (Vval p j W) / mass b W)^((3:ℝ)/5) with hyydef
  have hp2 : 2 ≤ p := hp.two_le
  have hp0' : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hA0 : 0 ≤ mass a V := hApos.le
  have hB0 : 0 ≤ mass b W := hBpos.le
  have hlam0 : 0 < lam := by rw [hlamdef]; exact Real.rpow_pos_of_pos hp0' _
  have hlam45 : lam ≤ 4/5 := by rw [hlamdef]; exact prime_rpow_neg_two_fifths p hp2
  have hlam31 : lam ≤ 29/31 := by linarith
  have hc1pos : 0 < c1 := by rw [hc1def]; split <;> norm_num
  have hc1le : c1 ≤ 1 := by rw [hc1def]; split <;> norm_num
  have hm0 : ∀ i j, 0 ≤ m i j := by
    intro i j; rw [hmdef]
    exact div_nonneg (pairMass_nonneg a b ha0 hb0 _) hPEpos.le
  have hxx0 : ∀ i, 0 ≤ xx i := by
    intro i; rw [hxxdef]
    exact Real.rpow_nonneg (div_nonneg (mass_nonneg a ha0 _) hA0) _
  have hyy0 : ∀ j, 0 ≤ yy j := by
    intro j; rw [hyydef]
    exact Real.rpow_nonneg (div_nonneg (mass_nonneg b hb0 _) hB0) _
  have hxx1 : ∀ i, xx i ≤ 1 := by
    intro i; rw [hxxdef]
    refine Real.rpow_le_one (div_nonneg (mass_nonneg a ha0 _) hA0) ?_ (by norm_num)
    rw [div_le_one hApos]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun v => p^i ∣ v ∧ ¬ p^(i+1) ∣ v) V) (fun v _ _ => ha0 v)
  have hyy1 : ∀ j, yy j ≤ 1 := by
    intro j; rw [hyydef]
    refine Real.rpow_le_one (div_nonneg (mass_nonneg b hb0 _) hB0) ?_ (by norm_num)
    rw [div_le_one hBpos]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun w => p^j ∣ w ∧ ¬ p^(j+1) ∣ w) W) (fun w _ _ => hb0 w)
  have hmsum : ∑ i ∈ Finset.range (Nmax+1), ∑ j ∈ Finset.range (Nmax+1), m i j = 1 := by
    have h1 : ∑ i ∈ Finset.range (Nmax+1), ∑ j ∈ Finset.range (Nmax+1),
        pairMass a b (Eval p i j V W E) = pairMass a b E := by
      rw [← Finset.sum_product (f := fun ij : ℕ × ℕ => pairMass a b (Eval p ij.1 ij.2 V W E))]
      exact (pairMass_biUnion hp a b V W hV hW E hE Nmax hNmaxV hNmaxW).symm
    calc ∑ i ∈ Finset.range (Nmax+1), ∑ j ∈ Finset.range (Nmax+1), m i j
        = ∑ i ∈ Finset.range (Nmax+1), ∑ j ∈ Finset.range (Nmax+1),
            pairMass a b (Eval p i j V W E) / pairMass a b E := by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [hmdef]
      _ = (∑ i ∈ Finset.range (Nmax+1), ∑ j ∈ Finset.range (Nmax+1),
            pairMass a b (Eval p i j V W E)) / pairMass a b E := by
          simp_rw [Finset.sum_div]
      _ = 1 := by rw [h1, div_self hPEpos.ne']
  have hxs : ∑ i ∈ Finset.range (Nmax+1), xx i ^ ((5:ℝ)/3) = 1 := by
    have h1 : ∀ i, xx i ^ ((5:ℝ)/3) = mass a (Vval p i V) / mass a V := by
      intro i
      simp only [hxxdef]
      rw [← Real.rpow_mul (div_nonneg (mass_nonneg a ha0 _) hA0),
        show (3:ℝ)/5 * (5/3) = 1 by norm_num, Real.rpow_one]
    have hnum : ∑ i ∈ Finset.range (Nmax+1), mass a (Vval p i V) = mass a V :=
      (mass_biUnion hp a V hV Nmax hNmaxV).symm
    rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.sum_div, hnum, div_self hApos.ne']
  have hys : ∑ j ∈ Finset.range (Nmax+1), yy j ^ ((5:ℝ)/3) = 1 := by
    have h1 : ∀ j, yy j ^ ((5:ℝ)/3) = mass b (Vval p j W) / mass b W := by
      intro j
      simp only [hyydef]
      rw [← Real.rpow_mul (div_nonneg (mass_nonneg b hb0 _) hB0),
        show (3:ℝ)/5 * (5/3) = 1 by norm_num, Real.rpow_one]
    have hnum : ∑ j ∈ Finset.range (Nmax+1), mass b (Vval p j W) = mass b W :=
      (mass_biUnion hp b W hW Nmax hNmaxW).symm
    rw [Finset.sum_congr rfl (fun j _ => h1 j), ← Finset.sum_div, hnum, div_self hBpos.ne']
  have hb : ∀ i j, m i j ≤ c1 * ((if i = j then (1:ℝ)
      else Real.exp 1 * lam ^ (Nat.dist i j)) * xx i * yy j) := by
    intro i j
    have hbracket : 0 ≤ (if i = j then (1:ℝ) else Real.exp 1 * lam ^ (Nat.dist i j)) := by
      by_cases h : i = j
      · rw [if_pos h]; norm_num
      · rw [if_neg h]; exact mul_nonneg (Real.exp_pos 1).le (pow_nonneg hlam0.le _)
    have hz0 : 0 ≤ c1 * ((if i = j then (1:ℝ)
        else Real.exp 1 * lam ^ (Nat.dist i j)) * xx i * yy j) :=
      mul_nonneg hc1pos.le (mul_nonneg (mul_nonneg hbracket (hxx0 i)) (hyy0 j))
    by_cases hi : i ≤ Nmax
    · by_cases hj : j ≤ Nmax
      · have hbil := bilinear_bound p₀ Nmax p V W a b t C E hp hpmem hV hW ha0 hb0 hE ht hC
          hgood hNmaxV hNmaxW hctr IH i (Finset.mem_range.mpr (by omega)) j
          (Finset.mem_range.mpr (by omega))
        simp only [hmdef, hxxdef, hyydef, hlamdef, hc1def]
        exact hbil
      · have hz : pairMass a b (Eval p i j V W E) = 0 := by
          have h0 : Eval p i j V W E = ∅ := by
            rw [Eval, Finset.filter_eq_empty_iff]
            intro e _ hcon
            have hmem : e.2 ∈ Vval p j W := hcon.2
            rw [Vval_eq_empty_of_lt (p := p) (N := Nmax) (i := j) hp hW hNmaxW
              (by omega)] at hmem
            exact Finset.notMem_empty _ hmem
          rw [h0]; simp [pairMass]
        simp only [hmdef]
        rw [hz, zero_div]
        exact hz0
    · have hz : pairMass a b (Eval p i j V W E) = 0 := by
        have h0 : Eval p i j V W E = ∅ := by
          rw [Eval, Finset.filter_eq_empty_iff]
          intro e _ hcon
          have hmem : e.1 ∈ Vval p i V := hcon.1
          rw [Vval_eq_empty_of_lt (p := p) (N := Nmax) (i := i) hp hV hNmaxV
            (by omega)] at hmem
          exact Finset.notMem_empty _ hmem
        rw [h0]; simp [pairMass]
      simp only [hmdef]
      rw [hz, zero_div]
      exact hz0
  have hdec := decay_away_from_diagonal Nmax lam c1 hlam0 hlam31 hc1pos hc1le m xx yy hm0
    hxx0 hyy0 hxx1 hyy1 hmsum hxs hys hb
  obtain ⟨hcle, k, hk, hsum⟩ := hdec
  have hpgt : p₀ < p := by
    by_contra hcon
    push_neg at hcon
    have hlt : (1/1000:ℝ) < c1 :=
      lt_of_lt_of_le (decay_ratio_gt_one_thousand lam hlam0.le hlam45) hcle
    rw [hc1def, if_pos hcon] at hlt
    exact lt_irrefl _ hlt
  refine ⟨hpgt, k, hk, ?_⟩
  have hkey : pairMass a b (E.filter (fun e => 2 ≤ Nat.dist (padicValNat p e.1) k
        + Nat.dist (padicValNat p e.2) k))
      ≤ (10:ℝ)^16 * (lam^((3:ℝ)) + lam^((7:ℝ)/2)) * pairMass a b E := by
    set Sidx : Finset (ℕ × ℕ) := ((Finset.range (Nmax+1)).product
        (Finset.range (Nmax+1))).filter
        (fun ij : ℕ × ℕ => 2 ≤ Nat.dist ij.1 k + Nat.dist ij.2 k) with hSidx
    have hsub : E.filter (fun e => 2 ≤ Nat.dist (padicValNat p e.1) k
          + Nat.dist (padicValNat p e.2) k) ⊆ Sidx.biUnion (fun ij => Eval p ij.1 ij.2 V W E) := by
      intro e he
      rw [Finset.mem_filter] at he
      obtain ⟨heE, hec⟩ := he
      have he1V : e.1 ∈ V := (Finset.mem_product.mp (hE heE)).1
      have he2W : e.2 ∈ W := (Finset.mem_product.mp (hE heE)).2
      have hpos1 : 0 < e.1 := lt_of_lt_of_le Nat.zero_lt_one (hV e.1 he1V)
      have hpos2 : 0 < e.2 := lt_of_lt_of_le Nat.zero_lt_one (hW e.2 he2W)
      have hmem1 : e.1 ∈ Vval p (padicValNat p e.1) V := by
        rw [mem_Vval_iff]
        refine ⟨he1V, pow_padicValNat_dvd, fun h => ?_⟩
        have h' := (padicValNat_dvd_iff_le (Nat.pos_iff_ne_zero.mp hpos1)).mp h
        omega
      have hmem2 : e.2 ∈ Vval p (padicValNat p e.2) W := by
        rw [mem_Vval_iff]
        refine ⟨he2W, pow_padicValNat_dvd, fun h => ?_⟩
        have h' := (padicValNat_dvd_iff_le (Nat.pos_iff_ne_zero.mp hpos2)).mp h
        omega
      have hbU := Eval_biUnion hp V W hV hW E hE Nmax hNmaxV hNmaxW
      rw [hbU] at heE
      obtain ⟨ij, hij, heij⟩ := Finset.mem_biUnion.mp heE
      have hij1 : ij.1 = padicValNat p e.1 :=
        Vval_unique hp (mem_Vval_iff.mp (Finset.mem_filter.mp heij).2.1).2.1
          (mem_Vval_iff.mp (Finset.mem_filter.mp heij).2.1).2.2
          (mem_Vval_iff.mp hmem1).2.1 (mem_Vval_iff.mp hmem1).2.2
      have hij2 : ij.2 = padicValNat p e.2 :=
        Vval_unique hp (mem_Vval_iff.mp (Finset.mem_filter.mp heij).2.2).2.1
          (mem_Vval_iff.mp (Finset.mem_filter.mp heij).2.2).2.2
          (mem_Vval_iff.mp hmem2).2.1 (mem_Vval_iff.mp hmem2).2.2
      refine Finset.mem_biUnion.mpr ⟨ij, ?_, heij⟩
      rw [hSidx, Finset.mem_filter]
      exact ⟨hij, by rw [hij1, hij2]; exact hec⟩
    have hdisj : (↑Sidx : Set (ℕ × ℕ)).PairwiseDisjoint (fun ij => Eval p ij.1 ij.2 V W E) := by
      intro u hu v hv huv
      exact Eval_pairwiseDisjoint hp V W E Nmax (x := u) (Finset.mem_filter.mp hu).1
        (y := v) (Finset.mem_filter.mp hv).1 huv
    have h1 : pairMass a b (E.filter (fun e => 2 ≤ Nat.dist (padicValNat p e.1) k
          + Nat.dist (padicValNat p e.2) k))
        ≤ ∑ ij ∈ Sidx, pairMass a b (Eval p ij.1 ij.2 V W E) := by
      unfold pairMass
      refine (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun e _ _ => mul_nonneg (ha0 e.1) (hb0 e.2))).trans ?_
      rw [Finset.sum_biUnion (f := fun e : ℕ × ℕ => a e.1 * b e.2) hdisj]
    have h2 : ∑ ij ∈ Sidx, pairMass a b (Eval p ij.1 ij.2 V W E)
        = (∑ i ∈ Finset.range (Nmax+1), ∑ j ∈ Finset.range (Nmax+1),
            (if 2 ≤ Nat.dist i k + Nat.dist j k then m i j else 0)) * pairMass a b E := by
      rw [hSidx, Finset.sum_filter]
      change (∑ x ∈ (Finset.range (Nmax+1)) ×ˢ (Finset.range (Nmax+1)),
          (if 2 ≤ Nat.dist x.1 k + Nat.dist x.2 k then pairMass a b (Eval p x.1 x.2 V W E)
            else 0)) = _
      rw [Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _
      by_cases hc : 2 ≤ Nat.dist i k + Nat.dist j k
      · rw [if_pos hc, if_pos hc, hmdef]
        field_simp
      · rw [if_neg hc, if_neg hc, zero_mul]
    calc pairMass a b (E.filter (fun e => 2 ≤ Nat.dist (padicValNat p e.1) k
            + Nat.dist (padicValNat p e.2) k))
        ≤ ∑ ij ∈ Sidx, pairMass a b (Eval p ij.1 ij.2 V W E) := h1
      _ = (∑ i ∈ Finset.range (Nmax+1), ∑ j ∈ Finset.range (Nmax+1),
            (if 2 ≤ Nat.dist i k + Nat.dist j k then m i j else 0)) * pairMass a b E := h2
      _ ≤ (10:ℝ)^16 * (lam^((3:ℝ)) + lam^((7:ℝ)/2)) * pairMass a b E :=
          mul_le_mul_of_nonneg_right hsum hPEpos.le
  refine hkey.trans ?_
  have hlam3 : lam^((3:ℝ)) = (p:ℝ)^(-((6:ℝ)/5)) := by
    rw [hlamdef]
    rw [← Real.rpow_mul (Nat.cast_nonneg p) (-(2:ℝ)/5) 3]
    rw [show (-(2:ℝ)/5) * 3 = -((6:ℝ)/5) by norm_num]
  have hlam7 : lam^((7:ℝ)/2) = (p:ℝ)^(-((7:ℝ)/5)) := by
    rw [hlamdef]
    rw [← Real.rpow_mul (Nat.cast_nonneg p) (-(2:ℝ)/5) ((7:ℝ)/2)]
    rw [show (-(2:ℝ)/5) * ((7:ℝ)/2) = -((7:ℝ)/5) by norm_num]
  rw [hlam3, hlam7]

-- =====================   from DS/struct3.lean  =====================
/-! ## Step 2: the structured subgraph -/

lemma mem_pset_iff {p : ℕ} {V : Finset ℕ} :
    p ∈ pset V ↔ ∃ v ∈ V, p.Prime ∧ p ∣ v ∧ v ≠ 0 := by
  rw [pset, Finset.mem_biUnion]
  constructor
  · rintro ⟨v, hv, hpv⟩
    obtain ⟨hp, hdvd, hne⟩ := Nat.mem_primeFactors.mp hpv
    exact ⟨v, hv, hp, hdvd, hne⟩
  · rintro ⟨v, hv, hprime, hdvd, hne⟩
    exact ⟨v, hv, Nat.mem_primeFactors.mpr ⟨hprime, hdvd, hne⟩⟩

lemma not_dvd_of_not_mem_pset {p v : ℕ} (hp : p.Prime) {V : Finset ℕ} (hv : v ∈ V)
    (hv0 : v ≠ 0) (hpmem : p ∉ pset V) : ¬ p ∣ v := by
  intro h
  exact hpmem (mem_pset_iff.mpr ⟨v, hv, hp, h, hv0⟩)

lemma pset_primes {V : Finset ℕ} {p : ℕ} (hp : p ∈ pset V) : p.Prime := by
  rw [pset, Finset.mem_biUnion] at hp
  obtain ⟨v, -, hpv⟩ := hp
  exact (Nat.mem_primeFactors.mp hpv).1

/-- The `p`-adic valuation of a product of prime powers. -/
lemma padicValNat_prod_prime_pow_eq_zero {p : ℕ} (hp : p.Prime) (s : Finset ℕ)
    (f : ℕ → ℕ) (hsp : ∀ q ∈ s, q.Prime) (hps : p ∉ s) :
    padicValNat p (∏ q ∈ s, q ^ f q) = 0 := by
  classical
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  induction s using Finset.induction_on with
  | empty => simp
  | insert q s hqs ih =>
      have hqprime : q.Prime := hsp q (Finset.mem_insert_self q s)
      have hsp' : ∀ r ∈ s, r.Prime := fun r hr => hsp r (Finset.mem_insert_of_mem hr)
      have hqs' : p ∉ s := fun h => hps (Finset.mem_insert_of_mem h)
      have h1 : q ^ f q ≠ 0 := pow_ne_zero _ hqprime.ne_zero
      have h2 : (∏ r ∈ s, r ^ f r) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun r hr => pow_ne_zero _ (hsp' r hr).ne_zero)
      have h3 : padicValNat p (q ^ f q) = 0 := by
        by_cases hf : f q = 0
        · rw [hf, pow_zero]; exact padicValNat.one
        · haveI : Fact q.Prime := ⟨hqprime⟩
          have hne : p ≠ q := fun h => hps (h ▸ Finset.mem_insert_self q s)
          exact padicValNat_prime_prime_pow (f q) hne
      rw [Finset.prod_insert hqs, padicValNat.mul h1 h2, ih hsp' hqs', h3, add_zero]

lemma padicValNat_prod_prime_pow (p : ℕ) (hp : p.Prime) (s : Finset ℕ) (f : ℕ → ℕ)
    (hsp : ∀ q ∈ s, q.Prime) :
    padicValNat p (∏ q ∈ s, q ^ f q) = if p ∈ s then f p else 0 := by
  classical
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  by_cases hps : p ∈ s
  · rw [if_pos hps, ← Finset.prod_erase_mul s (fun q => q ^ f q) hps]
    have h1 : (∏ q ∈ s.erase p, q ^ f q) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr
        (fun r hr => pow_ne_zero _ (hsp r (Finset.mem_of_mem_erase hr)).ne_zero)
    have h2 : p ^ f p ≠ 0 := pow_ne_zero _ hp.ne_zero
    rw [padicValNat.mul h1 h2, padicValNat.prime_pow (p := p) (f p)]
    have h3 : padicValNat p (∏ q ∈ s.erase p, q ^ f q) = 0 :=
      padicValNat_prod_prime_pow_eq_zero hp (s.erase p) f
        (fun r hr => hsp r (Finset.mem_of_mem_erase hr)) (Finset.notMem_erase p s)
    rw [h3, zero_add]
  · rw [if_neg hps]
    exact padicValNat_prod_prime_pow_eq_zero hp s f hsp hps

/-! ### Union bounds for sums of non-negative weights -/

lemma sum_le_sum_biUnion {γ ι : Type*} [DecidableEq γ] [DecidableEq ι] {f : γ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (s : Finset ι) (B : ι → Finset γ) :
    ∑ x ∈ s.biUnion B, f x ≤ ∑ i ∈ s, ∑ x ∈ B i, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      refine (sum_union_le (B i) (s.biUnion B) hf).trans ?_
      linarith [ih]

lemma sum_filter_forall_not_mem {γ ι : Type*} [DecidableEq γ] [DecidableEq ι]
    (E : Finset γ) (B : ι → Finset γ) (s : Finset ι) (m : γ → ℝ) (hm : ∀ x, 0 ≤ m x) :
    Finset.sum (E.filter (fun x => ∀ i ∈ s, x ∉ B i)) m
      ≥ Finset.sum E m - Finset.sum s (fun i => Finset.sum (B i) m) := by
  classical
  set F := E.filter (fun x => ∀ i ∈ s, x ∉ B i) with hF
  have hsub : F ⊆ E := Finset.filter_subset _ _
  have h2 : ∑ x ∈ E \ F, m x ≤ ∑ i ∈ s, ∑ x ∈ B i, m x := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => hm x)).trans
      (sum_le_sum_biUnion hm s B)
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hxE, hxF⟩ := hx
    rw [hF, Finset.mem_filter] at hxF
    have hcon : ¬ (∀ i ∈ s, x ∉ B i) := fun h => hxF ⟨hxE, h⟩
    push_neg at hcon
    exact Finset.mem_biUnion.mpr hcon
  have h3 : ∑ x ∈ E, m x = ∑ x ∈ F, m x + ∑ x ∈ E \ F, m x := by
    have := Finset.sum_sdiff (f := m) hsub
    linarith
  linarith

lemma int_natCast_dist (a b : ℕ) : ((Nat.dist a b : ℕ) : ℤ) = |((a:ℤ) - (b:ℤ))| := by
  rcases le_total a b with h | h
  · have h1 : ((b - a : ℕ) : ℤ) = (b:ℤ) - (a:ℤ) := Nat.cast_sub h
    have h2 : Nat.dist a b = b - a := by simp only [Nat.dist]; omega
    rw [h2, h1, abs_sub_comm, abs_of_nonneg (by omega)]
  · have h1 : ((a - b : ℕ) : ℤ) = (a:ℤ) - (b:ℤ) := Nat.cast_sub h
    have h2 : Nat.dist a b = a - b := by simp only [Nat.dist]; omega
    rw [h2, h1, abs_of_nonneg (by omega)]

/-- **Step 2**: the counterexample contains a large subgraph whose coordinates are all within one
`p`-adic step of the `k_p` for every prime `p` of the support. -/
lemma exists_structured_subset
    (p₀ Nmax : ℕ) (V W : Finset ℕ) (a b : ℕ → ℝ) (t C : ℝ) (E : Finset (ℕ × ℕ))
    (hp₀ : 1 ≤ p₀)
    (hV : ∀ v ∈ V, 1 ≤ v) (hW : ∀ w ∈ W, 1 ≤ w)
    (ha0 : ∀ v, 0 ≤ a v) (hb0 : ∀ w, 0 ≤ b w)
    (hE : E ⊆ V.product W) (ht : 1 ≤ t) (hC : 0 ≤ C)
    (hgood : ∀ e ∈ E, good t C a b e.1 e.2)
    (hNmaxV : ∀ v ∈ V, v ≤ Nmax) (hNmaxW : ∀ w ∈ W, w ≤ Nmax)
    (htail : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → (∀ p ∈ s, p₀ < p) →
        ∑ p ∈ s, ((p:ℝ)^(-((6:ℝ)/5)) + (p:ℝ)^(-((7:ℝ)/5))) < 1/(2*(10:ℝ)^16))
    (hctr : (1000:ℝ)^((p₀ + ((pset V ∪ pset W).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card))
        * (mass a V * mass b W)^((3:ℝ)/5) * Real.exp (-(3*C*t/5)) < pairMass a b E)
    (IH : ∀ (VM WM : Finset ℕ) (aM bM : ℕ → ℝ) (tM CM : ℝ) (EM : Finset (ℕ × ℕ)),
        (pset VM ∪ pset WM).card < (pset V ∪ pset W).card →
        (∀ v ∈ VM, 1 ≤ v) → (∀ w ∈ WM, 1 ≤ w) → (∀ v, 0 ≤ aM v) → (∀ w, 0 ≤ bM w) →
        1 ≤ tM → 0 ≤ CM → EM ⊆ VM.product WM →
        (∀ e ∈ EM, good tM CM aM bM e.1 e.2) →
        pairMass aM bM EM ≤ (1000:ℝ)^((p₀ + ((pset VM ∪ pset WM).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card))
          * (mass aM VM * mass bM WM)^((3:ℝ)/5) * Real.exp (-(3*CM*tM/5))) :
    ∃ (Nstar : ℕ) (Estar : Finset (ℕ × ℕ)),
      0 < Nstar ∧ Estar ⊆ E ∧ isStruct Nstar Estar ∧ (1/2) * pairMass a b E ≤ pairMass a b Estar := by
  classical
  have hPEpos : 0 < pairMass a b E := by
    have h0 : 0 ≤ (1000:ℝ)^((p₀ + ((pset V ∪ pset W).filter
          (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card))
        * (mass a V * mass b W)^((3:ℝ)/5) * Real.exp (-(3*C*t/5)) := by
      have h1 : (0:ℝ) ≤ (mass a V * mass b W)^((3:ℝ)/5) :=
        Real.rpow_nonneg (mul_nonneg (mass_nonneg a ha0 V) (mass_nonneg b hb0 W)) _
      have h2 : (0:ℝ) ≤ (1000:ℝ)^((p₀ + ((pset V ∪ pset W).filter
          (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card)) := pow_nonneg (by norm_num) _
      have h3 : (0:ℝ) ≤ Real.exp (-(3*C*t/5)) := (Real.exp_pos _).le
      exact mul_nonneg (mul_nonneg h2 h1) h3
    linarith [hctr, h0]
  have hprime_mem : ∀ p ∈ pset V ∪ pset W, p.Prime :=
    fun p hp => (Finset.mem_union.mp hp).elim pset_primes pset_primes
  have hdec : ∀ p : ℕ, ∃ k : ℕ, p ∈ pset V ∪ pset W →
      k ∈ Finset.range (Nmax+1) ∧ p₀ < p ∧
      pairMass a b (E.filter (fun e => 2 ≤ Nat.dist (padicValNat p e.1) k
          + Nat.dist (padicValNat p e.2) k))
        ≤ (10:ℝ)^16 * ((p:ℝ)^(-((6:ℝ)/5)) + (p:ℝ)^(-((7:ℝ)/5))) * pairMass a b E := by
    intro p
    by_cases hp : p ∈ pset V ∪ pset W
    · obtain ⟨hgt, k, hk, hb⟩ := decay_step p₀ Nmax p V W a b t C E (hprime_mem p hp) hp
        hV hW ha0 hb0 hE ht hC hgood hNmaxV hNmaxW hctr IH
      exact ⟨k, fun _ => ⟨hk, hgt, hb⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  let kf : ℕ → ℕ := fun p => Classical.choose (hdec p)
  have hkf : ∀ p ∈ pset V ∪ pset W, kf p ∈ Finset.range (Nmax+1) ∧ p₀ < p ∧
      pairMass a b (E.filter (fun e => 2 ≤ Nat.dist (padicValNat p e.1) (kf p)
          + Nat.dist (padicValNat p e.2) (kf p)))
        ≤ (10:ℝ)^16 * ((p:ℝ)^(-((6:ℝ)/5)) + (p:ℝ)^(-((7:ℝ)/5))) * pairMass a b E :=
    fun p hp => Classical.choose_spec (hdec p) hp
  set B : ℕ → Finset (ℕ × ℕ) := fun p => E.filter (fun e => 2 ≤ Nat.dist (padicValNat p e.1) (kf p)
      + Nat.dist (padicValNat p e.2) (kf p)) with hB
  set Pset : Finset ℕ := pset V ∪ pset W with hPset
  set Estar : Finset (ℕ × ℕ) := E.filter (fun e => ∀ p ∈ Pset, e ∉ B p) with hEstar
  -- the tail bound
  have hsum_tail : ∑ p ∈ Pset, ((p:ℝ)^(-((6:ℝ)/5)) + (p:ℝ)^(-((7:ℝ)/5)))
      < 1/(2*(10:ℝ)^16) :=
    htail Pset (fun p hp => hprime_mem p (by rw [hPset] at hp; exact hp))
      (fun p hp => (hkf p (by rw [hPset] at hp; exact hp)).2.1)
  have hBs : ∑ p ∈ Pset, pairMass a b (B p) ≤ (10:ℝ)^16 *
      (∑ p ∈ Pset, ((p:ℝ)^(-((6:ℝ)/5)) + (p:ℝ)^(-((7:ℝ)/5)))) * pairMass a b E := by
    calc ∑ p ∈ Pset, pairMass a b (B p)
        ≤ ∑ p ∈ Pset, (10:ℝ)^16 * ((p:ℝ)^(-((6:ℝ)/5)) + (p:ℝ)^(-((7:ℝ)/5))) * pairMass a b E := by
          apply Finset.sum_le_sum
          intro p hp
          rw [hB]
          exact (hkf p (by rw [hPset] at hp; exact hp)).2.2
      _ = (10:ℝ)^16 * (∑ p ∈ Pset, ((p:ℝ)^(-((6:ℝ)/5)) + (p:ℝ)^(-((7:ℝ)/5))))
            * pairMass a b E := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hBsmall : ∑ p ∈ Pset, pairMass a b (B p) < (1/2) * pairMass a b E := by
    have h2 : (10:ℝ)^16 * (∑ p ∈ Pset, ((p:ℝ)^(-((6:ℝ)/5)) + (p:ℝ)^(-((7:ℝ)/5))))
        < (10:ℝ)^16 * (1/(2*(10:ℝ)^16)) :=
      mul_lt_mul_of_pos_left hsum_tail (by norm_num)
    calc ∑ p ∈ Pset, pairMass a b (B p)
        ≤ (10:ℝ)^16 * (∑ p ∈ Pset, ((p:ℝ)^(-((6:ℝ)/5)) + (p:ℝ)^(-((7:ℝ)/5))))
            * pairMass a b E := hBs
      _ < (10:ℝ)^16 * (1/(2*(10:ℝ)^16)) * pairMass a b E :=
          mul_lt_mul_of_pos_right h2 hPEpos
      _ = (1/2) * pairMass a b E := by norm_num
  have hEstar_big : (1/2) * pairMass a b E ≤ pairMass a b Estar := by
    have hunion : pairMass a b E - ∑ p ∈ Pset, pairMass a b (B p) ≤ pairMass a b Estar := by
      rw [hEstar, hPset, pairMass, pairMass]
      exact sum_filter_forall_not_mem E B (pset V ∪ pset W) (fun e => a e.1 * b e.2)
        (fun e => mul_nonneg (ha0 e.1) (hb0 e.2))
    linarith [hunion, hBsmall]
  -- the arithmetic structure
  refine ⟨∏ p ∈ Pset, p ^ (kf p), Estar, ?_, ?_, ?_, hEstar_big⟩
  · exact Finset.prod_pos (fun p hp => pow_pos (hprime_mem p (by rw [hPset] at hp; exact hp)).pos _)
  · rw [hEstar]; exact Finset.filter_subset _ _
  · intro e he q hq
    rw [hEstar, Finset.mem_filter] at he
    obtain ⟨heE, hse⟩ := he
    have he1V : e.1 ∈ V := (Finset.mem_product.mp (hE heE)).1
    have he2W : e.2 ∈ W := (Finset.mem_product.mp (hE heE)).2
    by_cases hqs : q ∈ Pset
    · have hν : padicValNat q (∏ p ∈ Pset, p ^ (kf p)) = kf q := by
        rw [padicValNat_prod_prime_pow q hq Pset (fun p => kf p)
          (fun p hp => hprime_mem p (by rw [hPset] at hp; exact hp)), if_pos hqs]
      rw [hν, ← int_natCast_dist, ← int_natCast_dist]
      have hb : ¬ (2 ≤ Nat.dist (padicValNat q e.1) (kf q)
          + Nat.dist (padicValNat q e.2) (kf q)) := fun hcon =>
        hse q hqs (by rw [hB]; exact Finset.mem_filter.mpr ⟨heE, hcon⟩)
      have hb1 : Nat.dist (padicValNat q e.1) (kf q)
          + Nat.dist (padicValNat q e.2) (kf q) ≤ 1 := by omega
      exact_mod_cast hb1
    · have hν : padicValNat q (∏ p ∈ Pset, p ^ (kf p)) = 0 := by
        rw [padicValNat_prod_prime_pow q hq Pset (fun p => kf p)
          (fun p hp => hprime_mem p (by rw [hPset] at hp; exact hp)), if_neg hqs]
      have he1 : padicValNat q e.1 = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        exact not_dvd_of_not_mem_pset hq he1V (by have := hV e.1 he1V; omega)
          (fun h => hqs (by rw [hPset]; exact Finset.mem_union_left _ h))
      have he2 : padicValNat q e.2 = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        exact not_dvd_of_not_mem_pset hq he2W (by have := hW e.2 he2W; omega)
          (fun h => hqs (by rw [hPset]; exact Finset.mem_union_right _ h))
      rw [hν, he1, he2]
      norm_num

-- =====================   from DS/struct4.lean  =====================
/-! ## Step 3: a minimal counterexample is regular -/

/-- Property (1) of the structure proposition: `E` is a near-counterexample. -/
def prop1 (P : ℕ) (a b : ℕ → ℝ) (t C : ℝ) (E : Finset (ℕ × ℕ)) : Prop :=
  ((1/2:ℝ) * 1000^P)^5 * (mass a (E.image Prod.fst) * mass b (E.image Prod.snd))^3
    * Real.exp (-(3*C*t)) < (pairMass a b E)^5

/-- The convexity step: `x^{3/5}(x+y)^{2/5} ≤ x + (2/5) y` for `x, y ≥ 0`. -/
lemma rpow_mul_le_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x^((3:ℝ)/5) * (x+y)^((2:ℝ)/5) ≤ x + (2/5)*y := by
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · rw [← hx0]
    simp only [Real.zero_rpow (by norm_num : (3:ℝ)/5 ≠ 0), zero_mul]
    linarith
  · have hyx : (0:ℝ) ≤ y/x := div_nonneg hy hxpos.le
    have h1 : (1 + y/x)^((2:ℝ)/5) ≤ 1 + (2/5)*(y/x) :=
      rpow_one_add_le_one_add_mul_self (s := y/x) (by linarith) (by norm_num) (by norm_num)
    have h2 : (x+y)^((2:ℝ)/5) = x^((2:ℝ)/5) * (1 + y/x)^((2:ℝ)/5) := by
      rw [show x + y = x * (1 + y/x) by field_simp]
      rw [Real.mul_rpow hx (by positivity : (0:ℝ) ≤ 1 + y/x)]
    have h3 : x^((3:ℝ)/5) * x^((2:ℝ)/5) = x := by
      rw [← Real.rpow_add hxpos]; norm_num
    calc x^((3:ℝ)/5) * (x+y)^((2:ℝ)/5)
        = (x^((3:ℝ)/5) * x^((2:ℝ)/5)) * (1 + y/x)^((2:ℝ)/5) := by rw [h2]; ring
      _ = x * (1 + y/x)^((2:ℝ)/5) := by rw [h3]
      _ ≤ x * (1 + (2/5)*(y/x)) := mul_le_mul_of_nonneg_left h1 hx
      _ = x + (2/5)*y := by field_simp

lemma image_fst_filter_ne (E : Finset (ℕ × ℕ)) (v : ℕ) :
    (E.filter (fun e => e.1 ≠ v)).image Prod.fst = (E.image Prod.fst).erase v := by
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨e, ⟨he, hne⟩, rfl⟩
    exact ⟨hne, e, he, rfl⟩
  · rintro ⟨hne, e, he, rfl⟩
    exact ⟨e, ⟨he, hne⟩, rfl⟩

/-- Removing the neighbourhood of a vertex decreases the mass by precisely the weight of the
vertex times the `b`-mass of its neighbourhood. -/
lemma pairMass_new_gt
    (a b : ℕ → ℝ) (ha0 : ∀ v, 0 ≤ a v) (hb0 : ∀ w, 0 ≤ b w)
    (E : Finset (ℕ × ℕ)) (v : ℕ) (hv : v ∈ E.image Prod.fst) (hav : 0 < a v)
    (hPM : 0 < pairMass a b E) (hVM : 0 < mass a (E.image Prod.fst))
    (hfail : mass a (E.image Prod.fst) * ∑ w ∈ nhoodFst E v, b w < (3/5) * pairMass a b E) :
    pairMass a b E * (mass a ((E.filter (fun e => e.1 ≠ v)).image Prod.fst)
        / mass a (E.image Prod.fst))^((3:ℝ)/5)
      < pairMass a b (E.filter (fun e => e.1 ≠ v)) := by
  set PM := pairMass a b E with hPMdef
  set VM := mass a (E.image Prod.fst) with hVMdef
  set VMn := mass a ((E.filter (fun e => e.1 ≠ v)).image Prod.fst) with hVMndef
  set Γ := ∑ w ∈ nhoodFst E v, b w with hΓdef
  have hVMn0 : 0 ≤ VMn := mass_nonneg a ha0 _
  have hVMsum : VM = VMn + a v := by
    have h1 : VMn = mass a ((E.image Prod.fst).erase v) := by
      rw [hVMndef, image_fst_filter_ne E v]
    have h2 : mass a ((E.image Prod.fst).erase v) = mass a (E.image Prod.fst) - a v := by
      simp only [mass, Finset.sum_erase_eq_sub hv]
    rw [h1, h2, hVMdef]
    ring
  have hPMn : pairMass a b (E.filter (fun e => e.1 ≠ v)) = PM - a v * Γ := by
    rw [hPMdef, hΓdef]
    exact pairMass_filter_ne a b E v
  have hΓle : a v * Γ < a v * ((3/5) * PM / VM) := by
    apply mul_lt_mul_of_pos_left _ hav
    rw [lt_div_iff₀ hVM]
    linarith [hfail]
  have hkey : VMn^((3:ℝ)/5) * VM^((2:ℝ)/5) ≤ VMn + (2/5) * a v := by
    have h := rpow_mul_le_add hVMn0 (le_of_lt hav)
    rwa [← hVMsum] at h
  have hVMprod : VM * (VMn / VM)^((3:ℝ)/5) = VMn^((3:ℝ)/5) * VM^((2:ℝ)/5) := by
    rw [Real.div_rpow hVMn0 hVM.le]
    have h35 : VM / VM^((3:ℝ)/5) = VM^((2:ℝ)/5) := by
      have h := Real.rpow_sub hVM (1:ℝ) ((3:ℝ)/5)
      rw [show (1:ℝ) - 3/5 = 2/5 by norm_num, Real.rpow_one] at h
      exact h.symm
    rw [show VM * (VMn ^ ((3:ℝ)/5) / VM ^ ((3:ℝ)/5))
        = VMn^((3:ℝ)/5) * (VM / VM^((3:ℝ)/5)) by ring, h35]
  calc pairMass a b E * (VMn / VM)^((3:ℝ)/5)
      = (PM / VM) * (VM * (VMn / VM)^((3:ℝ)/5)) := by
        rw [← hPMdef]; field_simp
    _ = (PM / VM) * (VMn^((3:ℝ)/5) * VM^((2:ℝ)/5)) := by rw [hVMprod]
    _ ≤ (PM / VM) * (VMn + (2/5) * a v) :=
        mul_le_mul_of_nonneg_left hkey (div_nonneg hPM.le hVM.le)
    _ = PM - a v * ((3/5) * PM / VM) := by
        rw [hVMsum]; field_simp; ring
    _ < PM - a v * Γ := by linarith [hΓle]
    _ = pairMass a b (E.filter (fun e => e.1 ≠ v)) := hPMn.symm


lemma image_snd_filter_ne (E : Finset (ℕ × ℕ)) (w : ℕ) :
    (E.filter (fun e => e.2 ≠ w)).image Prod.snd = (E.image Prod.snd).erase w := by
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨e, ⟨he, hne⟩, rfl⟩
    exact ⟨hne, e, he, rfl⟩
  · rintro ⟨hne, e, he, rfl⟩
    exact ⟨e, ⟨he, hne⟩, rfl⟩

lemma pairMass_filter_ne_snd (a b : ℕ → ℝ) (E : Finset (ℕ × ℕ)) (w : ℕ) :
    pairMass a b (E.filter (fun e => e.2 ≠ w))
      = pairMass a b E - b w * ∑ v ∈ nhoodSnd E w, a v := by
  have h1 : E.filter (fun e => e.2 ≠ w) = E \ E.filter (fun e => e.2 = w) := by
    ext e
    by_cases h : e.2 = w <;> simp [h]
  have h2 := Finset.sum_sdiff (f := fun e : ℕ × ℕ => a e.1 * b e.2)
    (Finset.filter_subset (fun e : ℕ × ℕ => e.2 = w) E)
  have h3 : ∑ e ∈ E.filter (fun e => e.2 = w), a e.1 * b e.2
      = (∑ e ∈ E.filter (fun e => e.2 = w), a e.1) * b w := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    rw [(Finset.mem_filter.mp he).2]
  have h4 : ∑ e ∈ E.filter (fun e => e.2 = w), a e.1 = ∑ v ∈ nhoodSnd E w, a v := by
    rw [nhoodSnd]
    exact (Finset.sum_image (f := a) (g := Prod.fst) (s := E.filter (fun e => e.2 = w))
      (fun x hx y hy hxy => Prod.ext hxy
        (by rw [(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2]))).symm
  rw [h1, pairMass, pairMass, ← h2, h3, h4]
  ring

/-- The symmetric form of `pairMass_new_gt`, removing the neighbourhood of `w`. -/
lemma pairMass_new_gt_snd
    (a b : ℕ → ℝ) (ha0 : ∀ v, 0 ≤ a v) (hb0 : ∀ w, 0 ≤ b w)
    (E : Finset (ℕ × ℕ)) (w : ℕ) (hw : w ∈ E.image Prod.snd) (hbw : 0 < b w)
    (hPM : 0 < pairMass a b E) (hWM : 0 < mass b (E.image Prod.snd))
    (hfail : mass b (E.image Prod.snd) * ∑ v ∈ nhoodSnd E w, a v < (3/5) * pairMass a b E) :
    pairMass a b E * (mass b ((E.filter (fun e => e.2 ≠ w)).image Prod.snd)
        / mass b (E.image Prod.snd))^((3:ℝ)/5)
      < pairMass a b (E.filter (fun e => e.2 ≠ w)) := by
  set PM := pairMass a b E with hPMdef
  set WM := mass b (E.image Prod.snd) with hWMdef
  set WMn := mass b ((E.filter (fun e => e.2 ≠ w)).image Prod.snd) with hWMndef
  set Γ := ∑ v ∈ nhoodSnd E w, a v with hΓdef
  have hWMn0 : 0 ≤ WMn := mass_nonneg b hb0 _
  have hWMsum : WM = WMn + b w := by
    have h1 : WMn = mass b ((E.image Prod.snd).erase w) := by
      rw [hWMndef, image_snd_filter_ne E w]
    have h2 : mass b ((E.image Prod.snd).erase w) = mass b (E.image Prod.snd) - b w := by
      simp only [mass, Finset.sum_erase_eq_sub hw]
    rw [h1, h2, hWMdef]
    ring
  have hPMn : pairMass a b (E.filter (fun e => e.2 ≠ w)) = PM - b w * Γ := by
    rw [hPMdef, hΓdef]
    exact pairMass_filter_ne_snd a b E w
  have hΓle : b w * Γ < b w * ((3/5) * PM / WM) := by
    apply mul_lt_mul_of_pos_left _ hbw
    rw [lt_div_iff₀ hWM]
    linarith [hfail]
  have hkey : WMn^((3:ℝ)/5) * WM^((2:ℝ)/5) ≤ WMn + (2/5) * b w := by
    have h := rpow_mul_le_add hWMn0 (le_of_lt hbw)
    rwa [← hWMsum] at h
  have hWMprod : WM * (WMn / WM)^((3:ℝ)/5) = WMn^((3:ℝ)/5) * WM^((2:ℝ)/5) := by
    rw [Real.div_rpow hWMn0 hWM.le]
    have h35 : WM / WM^((3:ℝ)/5) = WM^((2:ℝ)/5) := by
      have h := Real.rpow_sub hWM (1:ℝ) ((3:ℝ)/5)
      rw [show (1:ℝ) - 3/5 = 2/5 by norm_num, Real.rpow_one] at h
      exact h.symm
    rw [show WM * (WMn ^ ((3:ℝ)/5) / WM ^ ((3:ℝ)/5))
        = WMn^((3:ℝ)/5) * (WM / WM^((3:ℝ)/5)) by ring, h35]
  calc pairMass a b E * (WMn / WM)^((3:ℝ)/5)
      = (PM / WM) * (WM * (WMn / WM)^((3:ℝ)/5)) := by
        rw [← hPMdef]; field_simp
    _ = (PM / WM) * (WMn^((3:ℝ)/5) * WM^((2:ℝ)/5)) := by rw [hWMprod]
    _ ≤ (PM / WM) * (WMn + (2/5) * b w) :=
        mul_le_mul_of_nonneg_left hkey (div_nonneg hPM.le hWM.le)
    _ = PM - b w * ((3/5) * PM / WM) := by
        rw [hWMsum]; field_simp; ring
    _ < PM - b w * Γ := by linarith [hΓle]
    _ = pairMass a b (E.filter (fun e => e.2 ≠ w)) := hPMn.symm

/-- **Step 3**: a subgraph of `Estar` of minimal cardinality satisfying property (1) satisfies the
one-sided regularity condition (2). -/
theorem minimal_regular (P : ℕ) (a b : ℕ → ℝ) (t C : ℝ) (Estar : Finset (ℕ × ℕ))
    (ha0 : ∀ v, 0 ≤ a v) (hb0 : ∀ w, 0 ≤ b w)
    (hstar : prop1 P a b t C Estar) :
    ∃ E' : Finset (ℕ × ℕ), E' ⊆ Estar ∧ prop1 P a b t C E' ∧ regular a b E' := by
  classical
  obtain ⟨E', hE'mem, hE'min⟩ := Finset.exists_min_image
    (Estar.powerset.filter (fun E'' => prop1 P a b t C E'')) Finset.card
    ⟨Estar, by rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨Finset.Subset.refl _, hstar⟩⟩
  have hE'sub : E' ⊆ Estar := Finset.mem_powerset.mp (Finset.mem_filter.mp hE'mem).1
  have hE'prop : prop1 P a b t C E' := (Finset.mem_filter.mp hE'mem).2
  have hbase : 0 ≤ ((1/2:ℝ) * 1000^P)^5
      * (mass a (E'.image Prod.fst) * mass b (E'.image Prod.snd))^3 * Real.exp (-(3*C*t)) := by
    apply mul_nonneg _ (Real.exp_pos _).le
    exact mul_nonneg (by positivity)
      (pow_nonneg (mul_nonneg (mass_nonneg a ha0 _) (mass_nonneg b hb0 _)) _)
  have hPM : 0 < pairMass a b E' := by
    rw [prop1] at hE'prop
    by_contra hcon
    push_neg at hcon
    have h0 : pairMass a b E' = 0 := le_antisymm hcon (pairMass_nonneg a b ha0 hb0 E')
    have h5 : (pairMass a b E')^5 ≤ 0 := by rw [h0]; norm_num
    linarith [hE'prop, hbase, h5]
  have hVM : 0 < mass a (E'.image Prod.fst) := by
    by_contra hcon
    push_neg at hcon
    have h0 : mass a (E'.image Prod.fst) = 0 := le_antisymm hcon (mass_nonneg a ha0 _)
    have hz : ∀ x ∈ E'.image Prod.fst, a x = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha0 i)).mp h0
    have hpz : pairMass a b E' = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      rw [hz e.1 (Finset.mem_image.mpr ⟨e, he, rfl⟩), zero_mul]
    linarith [hPM]
  have hWM : 0 < mass b (E'.image Prod.snd) := by
    by_contra hcon
    push_neg at hcon
    have h0 : mass b (E'.image Prod.snd) = 0 := le_antisymm hcon (mass_nonneg b hb0 _)
    have hz : ∀ x ∈ E'.image Prod.snd, b x = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hb0 i)).mp h0
    have hpz : pairMass a b E' = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      rw [hz e.2 (Finset.mem_image.mpr ⟨e, he, rfl⟩), mul_zero]
    linarith [hPM]
  refine ⟨E', hE'sub, hE'prop, ?_⟩
  constructor
  · by_contra hcon
    push_neg at hcon
    obtain ⟨v, hv, hfailure⟩ := hcon
    set Enew : Finset (ℕ × ℕ) := E'.filter (fun e => e.1 ≠ v) with hEnew
    have hEnew_sub : Enew ⊆ Estar := fun x hx => hE'sub (Finset.mem_of_mem_filter x hx)
    have hne : Enew ≠ E' := by
      intro heq
      obtain ⟨e0, he0, hve0⟩ := Finset.mem_image.mp hv
      have hmem : e0 ∈ Enew := heq ▸ he0
      rw [hEnew, Finset.mem_filter] at hmem
      exact hmem.2 hve0
    have hssub : Enew ⊂ E' := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, hne⟩
    have hcard : Enew.card < E'.card := Finset.card_lt_card hssub
    have hprop_new : prop1 P a b t C Enew := by
      by_cases hav : 0 < a v
      · have hnew := pairMass_new_gt a b ha0 hb0 E' v hv hav hPM hVM hfailure
        rw [prop1] at hE'prop ⊢
        set ρ : ℝ := (mass a (Enew.image Prod.fst) / mass a (E'.image Prod.fst))^((3:ℝ)/5)
          with hρdef
        have hVMn0 : 0 ≤ mass a (Enew.image Prod.fst) := mass_nonneg a ha0 _
        have hρ0 : 0 ≤ ρ := by
          rw [hρdef]; exact Real.rpow_nonneg (div_nonneg hVMn0 hVM.le) _
        have hρ5 : ρ^5 = (mass a (Enew.image Prod.fst) / mass a (E'.image Prod.fst))^3 := by
          rw [hρdef]; exact rpow_35_pow5 _ (div_nonneg hVMn0 hVM.le)
        have hnew' : pairMass a b E' * ρ < pairMass a b Enew := by rw [hρdef]; exact hnew
        have h5 : (pairMass a b E' * ρ)^5 < (pairMass a b Enew)^5 :=
          pow_lt_pow_left₀ hnew' (mul_nonneg hPM.le hρ0) (by norm_num)
        have hWMn : mass b (Enew.image Prod.snd) ≤ mass b (E'.image Prod.snd) :=
          mass_mono b hb0 (Finset.image_subset_image (Finset.filter_subset _ _))
        calc ((1/2:ℝ) * 1000^P)^5 * (mass a (Enew.image Prod.fst) * mass b (Enew.image Prod.snd))^3
              * Real.exp (-(3*C*t))
            ≤ ((1/2:ℝ) * 1000^P)^5 * (mass a (Enew.image Prod.fst) * mass b (E'.image Prod.snd))^3
              * Real.exp (-(3*C*t)) := by
              apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact pow_le_pow_left₀ (mul_nonneg hVMn0 (mass_nonneg b hb0 _))
                (mul_le_mul_of_nonneg_left hWMn hVMn0) 3
          _ = ((1/2:ℝ) * 1000^P)^5 * (mass a (E'.image Prod.fst) * mass b (E'.image Prod.snd))^3
              * Real.exp (-(3*C*t)) * ρ^5 := by
              rw [hρ5]; field_simp
          _ ≤ (pairMass a b E')^5 * ρ^5 :=
              mul_le_mul_of_nonneg_right hE'prop.le (pow_nonneg hρ0 5)
          _ = (pairMass a b E' * ρ)^5 := by rw [mul_pow]
          _ < (pairMass a b Enew)^5 := h5
      · have hav0 : a v = 0 := le_antisymm (not_lt.mp hav) (ha0 v)
        rw [prop1] at hE'prop ⊢
        have hPMn : pairMass a b Enew = pairMass a b E' := by
          rw [hEnew, pairMass_filter_ne a b E' v, hav0]
          ring
        have hVMn_eq : mass a (Enew.image Prod.fst) = mass a (E'.image Prod.fst) := by
          rw [hEnew, image_fst_filter_ne E' v]
          have h2 : mass a ((E'.image Prod.fst).erase v) = mass a (E'.image Prod.fst) - a v := by
            simp only [mass, Finset.sum_erase_eq_sub hv]
          rw [h2, hav0, sub_zero]
        have hWMn : mass b (Enew.image Prod.snd) ≤ mass b (E'.image Prod.snd) :=
          mass_mono b hb0 (Finset.image_subset_image (Finset.filter_subset _ _))
        rw [hPMn, hVMn_eq]
        refine lt_of_le_of_lt ?_ hE'prop
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (mul_nonneg (mass_nonneg a ha0 _) (mass_nonneg b hb0 _))
          (mul_le_mul_of_nonneg_left hWMn (mass_nonneg a ha0 _)) 3
    have := hE'min Enew
      (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hEnew_sub, hprop_new⟩)
    omega
  · by_contra hcon
    push_neg at hcon
    obtain ⟨w, hw, hfailure⟩ := hcon
    set Enew : Finset (ℕ × ℕ) := E'.filter (fun e => e.2 ≠ w) with hEnew
    have hEnew_sub : Enew ⊆ Estar := fun x hx => hE'sub (Finset.mem_of_mem_filter x hx)
    have hne : Enew ≠ E' := by
      intro heq
      obtain ⟨e0, he0, hwe0⟩ := Finset.mem_image.mp hw
      have hmem : e0 ∈ Enew := heq ▸ he0
      rw [hEnew, Finset.mem_filter] at hmem
      exact hmem.2 hwe0
    have hssub : Enew ⊂ E' := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, hne⟩
    have hcard : Enew.card < E'.card := Finset.card_lt_card hssub
    have hprop_new : prop1 P a b t C Enew := by
      by_cases hbw : 0 < b w
      · have hnew := pairMass_new_gt_snd a b ha0 hb0 E' w hw hbw hPM hWM hfailure
        rw [prop1] at hE'prop ⊢
        set ρ : ℝ := (mass b (Enew.image Prod.snd) / mass b (E'.image Prod.snd))^((3:ℝ)/5)
          with hρdef
        have hWMn0 : 0 ≤ mass b (Enew.image Prod.snd) := mass_nonneg b hb0 _
        have hρ0 : 0 ≤ ρ := by
          rw [hρdef]; exact Real.rpow_nonneg (div_nonneg hWMn0 hWM.le) _
        have hρ5 : ρ^5 = (mass b (Enew.image Prod.snd) / mass b (E'.image Prod.snd))^3 := by
          rw [hρdef]; exact rpow_35_pow5 _ (div_nonneg hWMn0 hWM.le)
        have hnew' : pairMass a b E' * ρ < pairMass a b Enew := by rw [hρdef]; exact hnew
        have h5 : (pairMass a b E' * ρ)^5 < (pairMass a b Enew)^5 :=
          pow_lt_pow_left₀ hnew' (mul_nonneg hPM.le hρ0) (by norm_num)
        have hVMn : mass a (Enew.image Prod.fst) ≤ mass a (E'.image Prod.fst) :=
          mass_mono a ha0 (Finset.image_subset_image (Finset.filter_subset _ _))
        calc ((1/2:ℝ) * 1000^P)^5 * (mass a (Enew.image Prod.fst) * mass b (Enew.image Prod.snd))^3
              * Real.exp (-(3*C*t))
            ≤ ((1/2:ℝ) * 1000^P)^5 * (mass a (E'.image Prod.fst) * mass b (Enew.image Prod.snd))^3
              * Real.exp (-(3*C*t)) := by
              apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact pow_le_pow_left₀ (mul_nonneg (mass_nonneg a ha0 _) hWMn0)
                (mul_le_mul_of_nonneg_right hVMn hWMn0) 3
          _ = ((1/2:ℝ) * 1000^P)^5 * (mass a (E'.image Prod.fst) * mass b (E'.image Prod.snd))^3
              * Real.exp (-(3*C*t)) * ρ^5 := by
              rw [hρ5]; field_simp
          _ ≤ (pairMass a b E')^5 * ρ^5 :=
              mul_le_mul_of_nonneg_right hE'prop.le (pow_nonneg hρ0 5)
          _ = (pairMass a b E' * ρ)^5 := by rw [mul_pow]
          _ < (pairMass a b Enew)^5 := h5
      · have hbw0 : b w = 0 := le_antisymm (not_lt.mp hbw) (hb0 w)
        rw [prop1] at hE'prop ⊢
        have hPMn : pairMass a b Enew = pairMass a b E' := by
          rw [hEnew, pairMass_filter_ne_snd a b E' w, hbw0]
          ring
        have hWMn_eq : mass b (Enew.image Prod.snd) = mass b (E'.image Prod.snd) := by
          rw [hEnew, image_snd_filter_ne E' w]
          have h2 : mass b ((E'.image Prod.snd).erase w) = mass b (E'.image Prod.snd) - b w := by
            simp only [mass, Finset.sum_erase_eq_sub hw]
          rw [h2, hbw0, sub_zero]
        have hVMn : mass a (Enew.image Prod.fst) ≤ mass a (E'.image Prod.fst) :=
          mass_mono a ha0 (Finset.image_subset_image (Finset.filter_subset _ _))
        rw [hPMn, hWMn_eq]
        refine lt_of_le_of_lt ?_ hE'prop
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (mul_nonneg (mass_nonneg a ha0 _) (mass_nonneg b hb0 _))
          (mul_le_mul_of_nonneg_right hVMn (mass_nonneg b hb0 _)) 3
    have := hE'min Enew
      (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hEnew_sub, hprop_new⟩)
    omega

lemma isStruct.mono {N : ℕ} {E E' : Finset (ℕ × ℕ)} (h : isStruct N E) (hsub : E' ⊆ E) :
    isStruct N E' :=
  fun e he p hp => h e (hsub he) p hp

/-- The rpow-form counterexample upgrades to property (1) for a subgraph of at least half mass. -/
lemma prop1_of_rpow_counter {P : ℕ} {a b : ℕ → ℝ} {t C : ℝ} {E Estar : Finset (ℕ × ℕ)}
    (ha0 : ∀ v, 0 ≤ a v) (hb0 : ∀ w, 0 ≤ b w)
    (hsub : Estar ⊆ E) (hbig : (1/2) * pairMass a b E ≤ pairMass a b Estar)
    (hctr : (1000:ℝ)^P
        * (mass a (E.image Prod.fst) * mass b (E.image Prod.snd))^((3:ℝ)/5)
        * Real.exp (-(3*C*t/5)) < pairMass a b E) :
    prop1 P a b t C Estar := by
  rw [prop1]
  have hμ : mass a (Estar.image Prod.fst) * mass b (Estar.image Prod.snd)
      ≤ mass a (E.image Prod.fst) * mass b (E.image Prod.snd) :=
    mul_le_mul (mass_mono a ha0 (Finset.image_subset_image hsub))
      (mass_mono b hb0 (Finset.image_subset_image hsub))
      (mass_nonneg b hb0 _) (mass_nonneg a ha0 _)
  have h1 : ((1/2:ℝ) * 1000^P)
        * (mass a (E.image Prod.fst) * mass b (E.image Prod.snd))^((3:ℝ)/5)
        * Real.exp (-(3*C*t/5)) < pairMass a b Estar := by
    have h2 : (1/2:ℝ) * ((1000:ℝ)^P
          * (mass a (E.image Prod.fst) * mass b (E.image Prod.snd))^((3:ℝ)/5)
          * Real.exp (-(3*C*t/5))) < (1/2) * pairMass a b E :=
      mul_lt_mul_of_pos_left hctr (by norm_num)
    have h3 : (1/2:ℝ) * ((1000:ℝ)^P
          * (mass a (E.image Prod.fst) * mass b (E.image Prod.snd))^((3:ℝ)/5)
          * Real.exp (-(3*C*t/5)))
        = ((1/2:ℝ) * 1000^P)
          * (mass a (E.image Prod.fst) * mass b (E.image Prod.snd))^((3:ℝ)/5)
          * Real.exp (-(3*C*t/5)) := by ring
    rw [h3] at h2
    linarith
  have h2' : (0:ℝ) ≤ ((1/2:ℝ) * 1000^P)
      * (mass a (E.image Prod.fst) * mass b (E.image Prod.snd))^((3:ℝ)/5)
      * Real.exp (-(3*C*t/5)) := by
    have hμ0 := Real.rpow_nonneg (mul_nonneg (mass_nonneg a ha0 (E.image Prod.fst))
      (mass_nonneg b hb0 (E.image Prod.snd))) ((3:ℝ)/5)
    have hK : (0:ℝ) ≤ (1/2:ℝ) * 1000^P := by positivity
    exact mul_nonneg (mul_nonneg hK hμ0) (Real.exp_pos _).le
  have h5 : (((1/2:ℝ) * 1000^P) * (mass a (E.image Prod.fst) * mass b (E.image Prod.snd))^((3:ℝ)/5)
      * Real.exp (-(3*C*t/5)))^5 < (pairMass a b Estar)^5 :=
    pow_lt_pow_left₀ h1 h2' (by norm_num)
  have hpow : (((1/2:ℝ) * 1000^P) * (mass a (E.image Prod.fst) * mass b (E.image Prod.snd))^((3:ℝ)/5)
      * Real.exp (-(3*C*t/5)))^5
      = ((1/2:ℝ) * 1000^P)^5 * (mass a (E.image Prod.fst) * mass b (E.image Prod.snd))^3
        * Real.exp (-(3*C*t)) := by
    rw [mul_pow, mul_pow, rpow_35_pow5 _ (mul_nonneg (mass_nonneg a ha0 _) (mass_nonneg b hb0 _))]
    rw [show Real.exp (-(3*C*t/5)) = Real.exp (-((3*C*t)/5)) by ring_nf, exp_neg_pow5]
  calc ((1/2:ℝ) * 1000^P)^5 * (mass a (Estar.image Prod.fst) * mass b (Estar.image Prod.snd))^3
        * Real.exp (-(3*C*t))
      ≤ ((1/2:ℝ) * 1000^P)^5 * (mass a (E.image Prod.fst) * mass b (E.image Prod.snd))^3
        * Real.exp (-(3*C*t)) := by
        have hA0 : (0:ℝ) ≤ ((1/2:ℝ) * 1000^P)^5 := by positivity
        have hBC : (mass a (Estar.image Prod.fst) * mass b (Estar.image Prod.snd))^3
            ≤ (mass a (E.image Prod.fst) * mass b (E.image Prod.snd))^3 :=
          pow_le_pow_left₀ (mul_nonneg (mass_nonneg a ha0 _) (mass_nonneg b hb0 _)) hμ 3
        exact mul_le_mul (mul_le_mul_of_nonneg_left hBC hA0) (le_refl _) (Real.exp_pos _).le
          (mul_nonneg hA0 (pow_nonneg (mul_nonneg (mass_nonneg a ha0 _) (mass_nonneg b hb0 _)) 3))
    _ = (((1/2:ℝ) * 1000^P) * (mass a (E.image Prod.fst) * mass b (E.image Prod.snd))^((3:ℝ)/5)
        * Real.exp (-(3*C*t/5)))^5 := hpow.symm
    _ < (pairMass a b Estar)^5 := h5

/-- **The structure of a minimal counterexample** (HWVS Proposition 3.4, specialised). -/
theorem structure_step
    (p₀ Nmax : ℕ) (V W : Finset ℕ) (a b : ℕ → ℝ) (t C : ℝ) (E : Finset (ℕ × ℕ))
    (hp₀ : 1 ≤ p₀)
    (hV : ∀ v ∈ V, 1 ≤ v) (hW : ∀ w ∈ W, 1 ≤ w)
    (ha0 : ∀ v, 0 ≤ a v) (hb0 : ∀ w, 0 ≤ b w)
    (hE : E ⊆ V.product W) (ht : 1 ≤ t) (hC : 0 ≤ C)
    (hgood : ∀ e ∈ E, good t C a b e.1 e.2)
    (hNmaxV : ∀ v ∈ V, v ≤ Nmax) (hNmaxW : ∀ w ∈ W, w ≤ Nmax)
    (htail : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → (∀ p ∈ s, p₀ < p) →
        ∑ p ∈ s, ((p:ℝ)^(-((6:ℝ)/5)) + (p:ℝ)^(-((7:ℝ)/5))) < 1/(2*(10:ℝ)^16))
    (hctr : (1000:ℝ)^((p₀ + ((pset V ∪ pset W).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card))
        * (mass a V * mass b W)^((3:ℝ)/5) * Real.exp (-(3*C*t/5)) < pairMass a b E)
    (IH : ∀ (VM WM : Finset ℕ) (aM bM : ℕ → ℝ) (tM CM : ℝ) (EM : Finset (ℕ × ℕ)),
        (pset VM ∪ pset WM).card < (pset V ∪ pset W).card →
        (∀ v ∈ VM, 1 ≤ v) → (∀ w ∈ WM, 1 ≤ w) → (∀ v, 0 ≤ aM v) → (∀ w, 0 ≤ bM w) →
        1 ≤ tM → 0 ≤ CM → EM ⊆ VM.product WM →
        (∀ e ∈ EM, good tM CM aM bM e.1 e.2) →
        pairMass aM bM EM ≤ (1000:ℝ)^((p₀ + ((pset VM ∪ pset WM).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card))
          * (mass aM VM * mass bM WM)^((3:ℝ)/5) * Real.exp (-(3*CM*tM/5))) :
    ∃ (Nstar : ℕ) (E' : Finset (ℕ × ℕ)),
      0 < Nstar ∧ E' ⊆ E ∧ isStruct Nstar E' ∧ regular a b E' ∧
      prop1 (p₀ + ((pset V ∪ pset W).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card) a b t C E' := by
  obtain ⟨Nstar, Estar, hN, hsub, hstr, hbig⟩ := exists_structured_subset p₀ Nmax V W a b t C E
    hp₀ hV hW ha0 hb0 hE ht hC hgood hNmaxV hNmaxW htail hctr IH
  have hctr' : (1000:ℝ)^((p₀ + ((pset V ∪ pset W).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card))
      * (mass a (E.image Prod.fst) * mass b (E.image Prod.snd))^((3:ℝ)/5)
      * Real.exp (-(3*C*t/5)) < pairMass a b E := by
    have himgV : E.image Prod.fst ⊆ V := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_product.mp (hE he)).1
    have himgW : E.image Prod.snd ⊆ W := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_product.mp (hE he)).2
    have hμ : mass a (E.image Prod.fst) * mass b (E.image Prod.snd) ≤ mass a V * mass b W :=
      mul_le_mul (mass_mono a ha0 himgV) (mass_mono b hb0 himgW)
        (mass_nonneg b hb0 _) (mass_nonneg a ha0 _)
    have hK : (0:ℝ) ≤ (1000:ℝ)^((p₀ + ((pset V ∪ pset W).filter
        (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card)) := by positivity
    have hr : (mass a (E.image Prod.fst) * mass b (E.image Prod.snd))^((3:ℝ)/5)
        ≤ (mass a V * mass b W)^((3:ℝ)/5) :=
      Real.rpow_le_rpow (mul_nonneg (mass_nonneg a ha0 _) (mass_nonneg b hb0 _)) hμ (by norm_num)
    refine lt_of_le_of_lt ?_ hctr
    refine mul_le_mul (mul_le_mul_of_nonneg_left hr hK) (le_refl _) (Real.exp_pos _).le ?_
    exact mul_nonneg hK (Real.rpow_nonneg (mul_nonneg (mass_nonneg a ha0 _) (mass_nonneg b hb0 _)) _)
  have hstar : prop1 (p₀ + ((pset V ∪ pset W).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card)
      a b t C Estar :=
    prop1_of_rpow_counter ha0 hb0 hsub hbig hctr'
  obtain ⟨E', hE'sub, hE'prop, hE'reg⟩ :=
    minimal_regular _ a b t C Estar ha0 hb0 hstar
  exact ⟨Nstar, E', hN, hE'sub.trans hsub, hstr.mono hE'sub, hE'reg, hE'prop⟩

-- =====================   from DS/main.lean  =====================
/-! ## Step 4: the induction (HWVS Theorem 1.7) -/

/-- The degenerate case where no prime divides any element of the support. -/
lemma main_bound_empty (p₀ : ℕ) (hp₀ : 1 ≤ p₀) (V W : Finset ℕ) (a b : ℕ → ℝ)
    (t C : ℝ) (E : Finset (ℕ × ℕ)) (hPset : pset V ∪ pset W = ∅)
    (hV : ∀ v ∈ V, 1 ≤ v) (hW : ∀ w ∈ W, 1 ≤ w)
    (ha0 : ∀ v, 0 ≤ a v) (hb0 : ∀ w, 0 ≤ b w)
    (hE : E ⊆ V.product W) (hC : 0 ≤ C) (hgood : ∀ e ∈ E, good t C a b e.1 e.2) :
    pairMass a b E ≤ (1000:ℝ)^((p₀ + ((pset V ∪ pset W).filter
        (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card))
      * (mass a V * mass b W)^((3:ℝ)/5) * Real.exp (-(3*C*t/5)) := by
  have hV1 : ∀ v ∈ V, v = 1 := by
    intro v hv
    by_contra hne
    obtain ⟨q, hq, hdvd⟩ := Nat.exists_prime_and_dvd hne
    have hmem : q ∈ pset V := mem_pset_iff.mpr ⟨v, hv, hq, hdvd, by have := hV v hv; omega⟩
    have hmem2 : q ∈ pset V ∪ pset W := Finset.mem_union_left _ hmem
    rw [hPset] at hmem2
    exact Finset.notMem_empty _ hmem2
  have hW1 : ∀ w ∈ W, w = 1 := by
    intro w hw
    by_contra hne
    obtain ⟨q, hq, hdvd⟩ := Nat.exists_prime_and_dvd hne
    have hmem : q ∈ pset W := mem_pset_iff.mpr ⟨w, hw, hq, hdvd, by have := hW w hw; omega⟩
    have hmem2 : q ∈ pset V ∪ pset W := Finset.mem_union_right _ hmem
    rw [hPset] at hmem2
    exact Finset.notMem_empty _ hmem2
  have hEsub : E ⊆ {(1, 1)} := by
    intro e he
    rw [Finset.mem_singleton]
    exact Prod.ext (hV1 e.1 (Finset.mem_product.mp (hE he)).1)
      (hW1 e.2 (Finset.mem_product.mp (hE he)).2)
  rcases Finset.eq_empty_or_nonempty E with hE0 | ⟨e0, he0⟩
  · rw [hE0, pairMass, Finset.sum_empty]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg
      (mul_nonneg (mass_nonneg a ha0 V) (mass_nonneg b hb0 W)) _)) (Real.exp_pos _).le
  have he1 : e0 = (1, 1) := by
    have h := hEsub he0
    rwa [Finset.mem_singleton] at h
  have hEeq : E = {(1, 1)} := by
    refine Finset.Subset.antisymm hEsub ?_
    rw [Finset.singleton_subset_iff]
    rw [← he1]
    exact he0
  have h1V : (1:ℕ) ∈ V := by
    have h := (Finset.mem_product.mp (hE he0)).1
    rwa [he1] at h
  have h1W : (1:ℕ) ∈ W := by
    have h := (Finset.mem_product.mp (hE he0)).2
    rwa [he1] at h
  have hmassV : mass a V = a 1 := by
    rw [mass, Finset.eq_singleton_iff_unique_mem.mpr ⟨h1V, fun x hx => hV1 x hx⟩]
    simp
  have hmassW : mass b W = b 1 := by
    rw [mass, Finset.eq_singleton_iff_unique_mem.mpr ⟨h1W, fun x hx => hW1 x hx⟩]
    simp
  have hg := hgood (1, 1) (hEeq ▸ Finset.mem_singleton_self _)
  obtain ⟨hg1, hg2⟩ := hg
  simp only [Nat.gcd_one_right, Nat.cast_one, Nat.totient_one, div_one, one_mul] at hg1
  have ha1 : a 1 ≤ 1 := le_trans (le_max_left _ _) hg1
  have hb1 : b 1 ≤ 1 := le_trans (le_max_right _ _) hg1
  have hQ : Qset t 1 1 = ∅ := by
    unfold Qset
    simp [Nat.primeFactors_one]
  have hC0 : C = 0 := by
    have h2 := hg2
    have hQ' : Qset t (1,1).1 (1,1).2 = ∅ := hQ
    rw [hQ'] at h2
    simp at h2
    linarith
  rw [hEeq, hmassV, hmassW]
  have hsingle : pairMass a b {(1,1)} = a 1 * b 1 := by
    simp [pairMass]
  rw [hsingle]
  have h1le : a 1 * b 1 ≤ 1 := by nlinarith [ha1, hb1, ha0 1, hb0 1]
  have hkey : a 1 * b 1 ≤ (a 1 * b 1)^((3:ℝ)/5) := by
    have h0 : 0 < a 1 * b 1 ∨ a 1 * b 1 = 0 := by
      rcases eq_or_lt_of_le (mul_nonneg (ha0 1) (hb0 1)) with h | h
      · exact Or.inr h.symm
      · exact Or.inl h
    rcases h0 with h0 | h0
    · have := Real.rpow_le_rpow_of_exponent_ge h0 h1le (by norm_num : (3:ℝ)/5 ≤ 1)
      rwa [Real.rpow_one] at this
    · rw [h0, Real.zero_rpow (by norm_num : (3:ℝ)/5 ≠ 0)]
  have hK1 : (1:ℝ) ≤ (1000:ℝ)^((p₀ + ((pset V ∪ pset W).filter
      (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card)) := one_le_pow₀ (by norm_num)
  calc a 1 * b 1 ≤ (a 1 * b 1)^((3:ℝ)/5) := hkey
    _ ≤ (1000:ℝ)^((p₀ + ((pset V ∪ pset W).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card))
          * (a 1 * b 1)^((3:ℝ)/5) * 1 := by
        have hX0 : (0:ℝ) ≤ (a 1 * b 1)^((3:ℝ)/5) :=
          Real.rpow_nonneg (mul_nonneg (ha0 1) (hb0 1)) _
        nlinarith [hK1, hX0]
    _ = (1000:ℝ)^((p₀ + ((pset V ∪ pset W).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card))
          * (a 1 * b 1)^((3:ℝ)/5) * Real.exp (-(3*C*t/5)) := by
        have hCt : Real.exp (-(3*C*t/5)) = 1 := by
          rw [hC0]
          norm_num
        rw [hCt, mul_one]

/-- **Step 4**: the induction of HWVS Theorem 1.7 (specialised to `f = g = φ`, `ε = 1/10`). -/
theorem main_bound (p₀ : ℕ) (hp₀ : 1 ≤ p₀)
    (htail : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → (∀ p ∈ s, p₀ < p) →
        ∑ p ∈ s, ((p:ℝ)^(-((6:ℝ)/5)) + (p:ℝ)^(-((7:ℝ)/5))) < 1/(2*(10:ℝ)^16))
    (hPbig : 32 * ((100/9 : ℝ) * Real.exp (21 * Real.exp 20))^2 ≤ (1000:ℝ)^(5*p₀)) :
    ∀ n : ℕ, ∀ (V W : Finset ℕ) (a b : ℕ → ℝ) (t C : ℝ) (E : Finset (ℕ × ℕ)),
      (pset V ∪ pset W).card = n →
      (∀ v ∈ V, 1 ≤ v) → (∀ w ∈ W, 1 ≤ w) → (∀ v, 0 ≤ a v) → (∀ w, 0 ≤ b w) →
      1 ≤ t → 0 ≤ C → E ⊆ V.product W → (∀ e ∈ E, good t C a b e.1 e.2) →
      pairMass a b E ≤ (1000:ℝ)^((p₀ + ((pset V ∪ pset W).filter
          (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card))
        * (mass a V * mass b W)^((3:ℝ)/5) * Real.exp (-(3*C*t/5)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V W a b t C E hcard hV hW ha0 hb0 ht hC hE hgood
    by_cases hPset : pset V ∪ pset W = ∅
    · exact main_bound_empty p₀ hp₀ V W a b t C E hPset hV hW ha0 hb0 hE hC hgood
    · by_contra hcon
      push_neg at hcon
      have IH : ∀ (VM WM : Finset ℕ) (aM bM : ℕ → ℝ) (tM CM : ℝ) (EM : Finset (ℕ × ℕ)),
          (pset VM ∪ pset WM).card < (pset V ∪ pset W).card →
          (∀ v ∈ VM, 1 ≤ v) → (∀ w ∈ WM, 1 ≤ w) → (∀ v, 0 ≤ aM v) → (∀ w, 0 ≤ bM w) →
          1 ≤ tM → 0 ≤ CM → EM ⊆ VM.product WM →
          (∀ e ∈ EM, good tM CM aM bM e.1 e.2) →
          pairMass aM bM EM ≤ (1000:ℝ)^((p₀ + ((pset VM ∪ pset WM).filter
              (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card))
            * (mass aM VM * mass bM WM)^((3:ℝ)/5) * Real.exp (-(3*CM*tM/5)) := by
        intro VM WM aM bM tM CM EM hlt hVM hWM haM hbM htM hCM hEM hgM
        exact ih (pset VM ∪ pset WM).card (by omega) VM WM aM bM tM CM EM rfl
          hVM hWM haM hbM htM hCM hEM hgM
      have hNmaxV : ∀ v ∈ V, v ≤ (V ∪ W).sup id := fun v hv =>
        Finset.le_sup (f := id) (Finset.mem_union_left W hv)
      have hNmaxW : ∀ w ∈ W, w ≤ (V ∪ W).sup id := fun w hw =>
        Finset.le_sup (f := id) (Finset.mem_union_right V hw)
      obtain ⟨Nstar, E', hNpos, hE'sub, hstr, hreg, hprop⟩ :=
        structure_step p₀ ((V ∪ W).sup id) V W a b t C E hp₀ hV hW ha0 hb0 hE ht hC hgood
          hNmaxV hNmaxW htail hcon IH
      set Pex : ℕ := p₀ + ((pset V ∪ pset W).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card
        with hPexdef
      have hV' : ∀ v ∈ E'.image Prod.fst, 1 ≤ v := by
        intro v hv
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
        exact hV e.1 (Finset.mem_product.mp (hE (hE'sub he))).1
      have hW' : ∀ w ∈ E'.image Prod.snd, 1 ≤ w := by
        intro w hw
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hw
        exact hW e.2 (Finset.mem_product.mp (hE (hE'sub he))).2
      have hE' : E' ⊆ (E'.image Prod.fst).product (E'.image Prod.snd) := by
        intro e he
        exact Finset.mem_product.mpr
          ⟨Finset.mem_image.mpr ⟨e, he, rfl⟩, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
      have hgood' : ∀ e ∈ E', good t C a b e.1 e.2 := fun e he => hgood e (hE'sub he)
      have hPex : 32 * ((100/9 : ℝ) * Real.exp (21 * Real.exp 20))^2 ≤ (1000:ℝ)^(5*Pex) := by
        refine hPbig.trans (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 1000) ?_)
        rw [hPexdef]
        omega
      have hres := resolve_bound Nstar hNpos (E'.image Prod.fst) (E'.image Prod.snd) a b t C
        hC ht hV' hW' ha0 hb0 E' hE' hstr hgood' hreg Pex hPex
      have hprop' : (1/2) * 1000^Pex
            * (mass a (E'.image Prod.fst) * mass b (E'.image Prod.snd))^((3:ℝ)/5)
            * Real.exp (-(3*C*t/5)) < pairMass a b E' := by
        have hA0 : (0:ℝ) ≤ (1/2) * 1000^Pex
            * (mass a (E'.image Prod.fst) * mass b (E'.image Prod.snd))^((3:ℝ)/5)
            * Real.exp (-(3*C*t/5)) := by
          refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
            (Real.rpow_nonneg (mul_nonneg (mass_nonneg a ha0 _) (mass_nonneg b hb0 _)) _))
            (Real.exp_pos _).le
        rw [← pow_lt_pow_iff_left₀ hA0 (pairMass_nonneg a b ha0 hb0 E')
          (by norm_num : (5:ℕ) ≠ 0)]
        have h5 : ((1/2) * 1000^Pex
              * (mass a (E'.image Prod.fst) * mass b (E'.image Prod.snd))^((3:ℝ)/5)
              * Real.exp (-(3*C*t/5)))^5
            = ((1/2:ℝ) * 1000^Pex)^5
              * (mass a (E'.image Prod.fst) * mass b (E'.image Prod.snd))^3
              * Real.exp (-(3*C*t)) := by
          rw [mul_pow, mul_pow, mul_pow, rpow_35_pow5 _
            (mul_nonneg (mass_nonneg a ha0 _) (mass_nonneg b hb0 _)), exp_neg_pow5]
        rw [h5]
        rw [prop1] at hprop
        rw [hPexdef] at hprop ⊢
        exact hprop
      linarith [hres, hprop']

-- =====================   from DS/final.lean  =====================
/-! ## Step 5: the numerical constants and the final application -/

lemma t_pow_le_exp (t : ℝ) (ht : 1 ≤ t) : t^((9:ℝ)/5) * Real.exp (-(6*t)) ≤ 1 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have h1 : t^((9:ℝ)/5) ≤ Real.exp (6*t) := by
    rw [Real.rpow_def_of_pos ht0]
    apply Real.exp_le_exp.mpr
    have hlog : Real.log t ≤ t := Real.log_le_self ht0.le
    nlinarith
  calc t^((9:ℝ)/5) * Real.exp (-(6*t)) ≤ Real.exp (6*t) * Real.exp (-(6*t)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 1 := by
        rw [← Real.exp_add, show 6*t + -(6*t) = 0 by ring, Real.exp_zero]

lemma p0_numeric_bound :
    32 * ((100/9 : ℝ) * Real.exp (21 * Real.exp 20))^2 ≤ (1000:ℝ)^(5*(10:ℕ)^10) := by
  have hlog1000 : (6:ℝ) ≤ Real.log 1000 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 1000)]
    calc Real.exp 6 = (Real.exp 1)^6 := by
          rw [show (6:ℝ) = (6:ℕ) * 1 by norm_num, Real.exp_nat_mul]
      _ ≤ 3^6 := pow_le_pow_left₀ (Real.exp_pos 1).le (le_of_lt Real.exp_one_lt_three) 6
      _ ≤ 1000 := by norm_num
  have hexp20 : Real.exp 20 ≤ (4:ℝ) * 10^9 := by
    have h1 : Real.exp 20 = (Real.exp 1)^20 := by
      rw [show (20:ℝ) = (20:ℕ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h1]
    calc (Real.exp 1)^20 ≤ 3^20 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le (le_of_lt Real.exp_one_lt_three) 20
      _ ≤ 4 * 10^9 := by norm_num
  have hexp21 : Real.exp (21 * Real.exp 20) ≤ (1000:ℝ)^((2:ℕ) * ((10:ℕ)^10)) := by
    have h2 : 21 * Real.exp 20 ≤ ((2:ℝ) * 10^10) * Real.log 1000 := by
      have h2' : (21:ℝ) * ((4:ℝ) * 10^9) ≤ ((2:ℝ) * 10^10) * 6 := by norm_num
      nlinarith [hexp20, hlog1000]
    have h3 : (1000:ℝ)^((2:ℕ) * ((10:ℕ)^10))
        = Real.exp (((2:ℝ) * 10^10) * Real.log 1000) := by
      rw [← Real.rpow_natCast (1000:ℝ) ((2:ℕ) * ((10:ℕ)^10)),
        Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 1000), mul_comm (Real.log 1000)]
      push_cast
      ring
    rw [h3]
    exact Real.exp_le_exp.mpr h2
  have hsquare : (Real.exp (21 * Real.exp 20))^2 ≤ (1000:ℝ)^((4:ℕ) * ((10:ℕ)^10)) := by
    calc (Real.exp (21 * Real.exp 20))^2
        ≤ ((1000:ℝ)^((2:ℕ) * ((10:ℕ)^10)))^2 :=
          pow_le_pow_left₀ (Real.exp_pos _).le hexp21 2
      _ = (1000:ℝ)^((4:ℕ) * ((10:ℕ)^10)) := by
          rw [← pow_mul]
          norm_num
  have hsmall : 32 * ((100/9 : ℝ))^2 * (1000:ℝ)^((4:ℕ)*((10:ℕ)^10))
      ≤ (1000:ℝ)^(5*((10:ℕ)^10)) := by
    have h2 : 32 * ((100/9 : ℝ))^2 ≤ (1000:ℝ)^((1:ℕ) * ((10:ℕ)^10)) := by
      have h3 : (32 * ((100/9:ℝ))^2 : ℝ) ≤ 1000^2 := by norm_num
      have h4 : (1000:ℝ)^(2:ℕ) ≤ (1000:ℝ)^((1:ℕ) * ((10:ℕ)^10)) :=
        pow_le_pow_right₀ (by norm_num)
          (by norm_num : (2:ℕ) ≤ 1 * (10:ℕ)^10)
      exact le_trans h3 h4
    calc 32 * ((100/9 : ℝ))^2 * (1000:ℝ)^((4:ℕ)*((10:ℕ)^10))
        ≤ (1000:ℝ)^((1:ℕ) * ((10:ℕ)^10)) * (1000:ℝ)^((4:ℕ)*((10:ℕ)^10)) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (1000:ℝ)^(5*((10:ℕ)^10)) := by
          rw [← pow_add]
          norm_num
  calc 32 * ((100/9 : ℝ) * Real.exp (21 * Real.exp 20))^2
      = 32 * ((100/9 : ℝ))^2 * (Real.exp (21 * Real.exp 20))^2 := by ring
    _ ≤ 32 * ((100/9 : ℝ))^2 * (1000:ℝ)^((4:ℕ)*((10:ℕ)^10)) :=
        mul_le_mul_of_nonneg_left hsquare (by norm_num)
    _ ≤ (1000:ℝ)^(5*((10:ℕ)^10)) := hsmall

/-- The Duffin--Schaeffer conjecture: Koukoulopoulos--Maynard, Proposition 5.4. -/
theorem km_prop_gcd_aux :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ψ : ℕ → ℝ) (hψ0 : ∀ n, 0 ≤ ψ n) (hψhalf : ∀ n, ψ n ≤ 1 / 2)
        (X Y : ℕ) (hX : 1 ≤ X) (hY : X ≤ Y)
        (hblock : 1 ≤ ∑ q ∈ Finset.Icc X Y, (q.totient : ℝ) * ψ q / q ∧
                  ∑ q ∈ Finset.Icc X Y, (q.totient : ℝ) * ψ q / q ≤ 2)
        (t : ℝ) (ht : 1 ≤ t),
      ∑ p ∈ (Finset.Icc X Y).product (Finset.Icc X Y),
          (if (p.1.gcd p.2 : ℝ) ≥ max ((p.2 : ℝ) * ψ p.1) ((p.1 : ℝ) * ψ p.2) / t ∧
              10 ≤ ∑ r ∈ (Nat.primeFactors (p.1 * p.2 / (p.1.gcd p.2 * p.1.gcd p.2))).filter
                     (fun r : ℕ => t ≤ (r : ℝ)), 1 / (r : ℝ)
           then (p.1.totient : ℝ) * ψ p.1 / p.1 * ((p.2.totient : ℝ) * ψ p.2 / p.2) else 0)
        ≤ C / t := by
  classical
  obtain ⟨p₁, hp₁⟩ := exists_prime_tail_bound (1/(2*(10:ℝ)^16)) (by norm_num)
  set p₀ : ℕ := max p₁ ((10:ℕ)^10) with hp₀def
  have htail : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → (∀ p ∈ s, p₀ < p) →
      ∑ p ∈ s, ((p:ℝ)^(-((6:ℝ)/5)) + (p:ℝ)^(-((7:ℝ)/5))) < 1/(2*(10:ℝ)^16) := by
    intro s hs hps
    exact hp₁ s hs (fun p hp => lt_of_le_of_lt (le_max_left _ _) (hps p hp))
  have hPbig : 32 * ((100/9 : ℝ) * Real.exp (21 * Real.exp 20))^2 ≤ (1000:ℝ)^(5*p₀) := by
    refine le_trans p0_numeric_bound (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 1000) ?_)
    rw [hp₀def]
    omega
  refine ⟨(1000:ℝ)^(3*p₀) * 4^((3:ℝ)/5), by positivity, ?_⟩
  intro ψ hψ0 hψhalf X Y hX hY hblock t ht
  set V : Finset ℕ := Finset.Icc X Y with hVdef
  set a : ℕ → ℝ := fun q => (q.totient : ℝ) * ψ q / ((q:ℝ) * t) with hadef
  have hV1 : ∀ v ∈ V, 1 ≤ v := by
    intro v hv
    rw [hVdef] at hv
    exact le_trans hX (Finset.mem_Icc.mp hv).1
  have ha0 : ∀ q, 0 ≤ a q := by
    intro q
    rw [hadef]
    refine div_nonneg (mul_nonneg (by positivity) (hψ0 q)) ?_
    exact mul_nonneg (Nat.cast_nonneg q) (by linarith)
  -- the equivalence of the two conditions on `V × V`
  have hcondiff : ∀ e ∈ V.product V,
      (((e.1.gcd e.2 : ℝ) ≥ max ((e.2 : ℝ) * ψ e.1) ((e.1 : ℝ) * ψ e.2) / t ∧
          10 ≤ ∑ r ∈ (Nat.primeFactors (e.1 * e.2 / (e.1.gcd e.2 * e.1.gcd e.2))).filter
                 (fun r : ℕ => t ≤ (r : ℝ)), 1 / (r : ℝ))
        ↔ good t 10 a a e.1 e.2) := by
    intro e he
    obtain ⟨he1, he2⟩ := Finset.mem_product.mp he
    have hv1 : 1 ≤ e.1 := hV1 e.1 he1
    have hv2 : 1 ≤ e.2 := hV1 e.2 he2
    have hdiv : ∀ u : ℕ, 1 ≤ u → a u / (u.totient : ℝ) = ψ u / ((u:ℝ)*t) := by
      intro u hu
      have hφ : ((u.totient : ℝ)) ≠ 0 := by
        have h := Nat.totient_pos.mpr (by omega : 0 < u)
        exact_mod_cast h.ne'
      change (u.totient : ℝ) * ψ u / ((u:ℝ) * t) / (u.totient : ℝ) = ψ u / ((u:ℝ) * t)
      field_simp
    have hmul : (e.1:ℝ)*(e.2:ℝ)*max (ψ e.1/((e.1:ℝ)*t)) (ψ e.2/((e.2:ℝ)*t))
        = max ((e.2:ℝ)*ψ e.1) ((e.1:ℝ)*ψ e.2)/t := by
      have h1 : (e.1:ℝ)*(e.2:ℝ)*(ψ e.1/((e.1:ℝ)*t)) = (e.2:ℝ)*ψ e.1/t := by
        field_simp
      have h2 : (e.1:ℝ)*(e.2:ℝ)*(ψ e.2/((e.2:ℝ)*t)) = (e.1:ℝ)*ψ e.2/t := by
        field_simp
      rw [mul_max_of_nonneg _ _ (by positivity), h1, h2,
        max_div_div_right (by linarith : (0:ℝ) ≤ t)]
    rw [good]
    simp only [Qset]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rw [hdiv e.1 hv1, hdiv e.2 hv2, hmul]
      exact h1
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rw [hdiv e.1 hv1, hdiv e.2 hv2, hmul] at h1
      exact h1
  -- the target sum is `t^2` times the pair mass of the good pairs
  set E : Finset (ℕ × ℕ) := (V.product V).filter (fun e => good t 10 a a e.1 e.2) with hEdef
  have hsum_eq : (∑ p ∈ V.product V,
        (if (p.1.gcd p.2 : ℝ) ≥ max ((p.2 : ℝ) * ψ p.1) ((p.1 : ℝ) * ψ p.2) / t ∧
              10 ≤ ∑ r ∈ (Nat.primeFactors (p.1 * p.2 / (p.1.gcd p.2 * p.1.gcd p.2))).filter
                     (fun r : ℕ => t ≤ (r : ℝ)), 1 / (r : ℝ)
           then (p.1.totient : ℝ) * ψ p.1 / p.1 * ((p.2.totient : ℝ) * ψ p.2 / p.2) else 0))
      = t^2 * pairMass a a E := by
    rw [hEdef, pairMass, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have hv1 : 1 ≤ e.1 := hV1 e.1 (Finset.mem_product.mp he).1
    have hv2 : 1 ≤ e.2 := hV1 e.2 (Finset.mem_product.mp he).2
    have haeq : ∀ u : ℕ, 1 ≤ u → a u = (u.totient : ℝ) * ψ u / u / t := by
      intro u _
      change (u.totient : ℝ) * ψ u / ((u:ℝ) * t) = (u.totient : ℝ) * ψ u / u / t
      rw [div_mul_eq_div_div]
    rw [hVdef] at he
    by_cases hg : good t 10 a a e.1 e.2
    · rw [if_pos ((hcondiff e he).mpr hg), if_pos hg, haeq e.1 hv1, haeq e.2 hv2]
      field_simp
    · rw [if_neg (fun h => hg ((hcondiff e he).mp h)), if_neg hg, mul_zero]
  rw [hsum_eq]
  -- the main bound
  have hEsub : E ⊆ V.product V := by rw [hEdef]; exact Finset.filter_subset _ _
  have hgoodE : ∀ e ∈ E, good t 10 a a e.1 e.2 := fun e he => (Finset.mem_filter.mp he).2
  have hmb := main_bound p₀ (by omega) htail hPbig (pset V ∪ pset V).card V V a a t 10 E rfl
    hV1 hV1 ha0 ha0 ht (by norm_num) hEsub hgoodE
  have hS : pairMass a a E ≤ (1000:ℝ)^(p₀ + ((pset V ∪ pset V).filter
        (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card) * (mass a V * mass a V)^((3:ℝ)/5)
      * Real.exp (-(6*t)) := by
    rwa [show -(3*(10:ℝ)*t/5) = -(6*t) by ring] at hmb
  have hmass : mass a V = (∑ q ∈ V, (q.totient : ℝ) * ψ q / q) / t := by
    rw [mass]
    rw [show (∑ q ∈ V, a q) = ∑ q ∈ V, ((q.totient : ℝ) * ψ q / q) / t from by
      apply Finset.sum_congr rfl
      intro q _
      change (q.totient : ℝ) * ψ q / ((q:ℝ) * t) = (q.totient : ℝ) * ψ q / q / t
      rw [div_mul_eq_div_div]]
    rw [Finset.sum_div]
  have hmass_le : mass a V ≤ 2/t := by
    rw [hmass]
    exact div_le_div_of_nonneg_right hblock.2 (by linarith)
  have hmass0 : 0 ≤ mass a V := mass_nonneg a ha0 V
  have ht0 : (0:ℝ) < t := by linarith
  have hfour : (mass a V * mass a V)^((3:ℝ)/5) ≤ 4^((3:ℝ)/5) * t^(-((6:ℝ)/5)) := by
    have h2t : (0:ℝ) ≤ 2/t := by positivity
    have hmul : mass a V * mass a V ≤ (2/t) * (2/t) :=
      mul_le_mul hmass_le hmass_le hmass0 h2t
    have hr := Real.rpow_le_rpow (mul_nonneg hmass0 hmass0) hmul (by norm_num : (0:ℝ) ≤ (3:ℝ)/5)
    have heq : (2/t) * (2/t) = 4/t^2 := by ring
    rw [heq] at hr
    calc (mass a V * mass a V)^((3:ℝ)/5) ≤ (4/t^2)^((3:ℝ)/5) := hr
      _ = 4^((3:ℝ)/5) * t^(-((6:ℝ)/5)) := by
          rw [Real.div_rpow (by norm_num : (0:ℝ) ≤ 4) (by positivity : (0:ℝ) ≤ t^2)]
          rw [show (t^2)^((3:ℝ)/5) = t^((6:ℝ)/5) by
            rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le]
            norm_num]
          rw [Real.rpow_neg ht0.le, div_eq_mul_inv]
  have hK : (1000:ℝ)^(p₀ + ((pset V ∪ pset V).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card)
      ≤ (1000:ℝ)^(3*p₀) := by
    apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 1000)
    have hc : ((pset V ∪ pset V).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card ≤ 2*p₀ := by
      have h1 : ((pset V ∪ pset V).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card
          ≤ (Finset.range (p₀+1)).card := by
        apply Finset.card_le_card
        intro q hq
        rw [Finset.mem_filter] at hq
        rw [Finset.mem_range]
        omega
      refine le_trans h1 ?_
      simp only [Finset.card_range]
      have hp1 : 1 ≤ p₀ := by
        rw [hp₀def]
        exact le_trans (by norm_num : 1 ≤ (10:ℕ)^10) (le_max_right _ _)
      omega
    omega
  have hstep1 : t^2 * pairMass a a E
      ≤ t^2 * ((1000:ℝ)^(p₀ + ((pset V ∪ pset V).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card)
          * (4^((3:ℝ)/5) * t^(-((6:ℝ)/5))) * Real.exp (-(6*t))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc pairMass a a E
        ≤ (1000:ℝ)^(p₀ + ((pset V ∪ pset V).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card)
          * (mass a V * mass a V)^((3:ℝ)/5) * Real.exp (-(6*t)) := hS
      _ ≤ (1000:ℝ)^(p₀ + ((pset V ∪ pset V).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card)
          * (4^((3:ℝ)/5) * t^(-((6:ℝ)/5))) * Real.exp (-(6*t)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left hfour (by positivity)
  have htexp : t^2 * t^(-((6:ℝ)/5)) = t^((9:ℝ)/5)/t := by
    have h1 : t^2 * t^(-((6:ℝ)/5)) = t^((4:ℝ)/5) := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht0,
        show ((2:ℕ):ℝ) + (-((6:ℝ)/5)) = (4:ℝ)/5 by norm_num]
    rw [h1]
    rw [show ((9:ℝ)/5) = (4:ℝ)/5 + 1 by norm_num, Real.rpow_add ht0, Real.rpow_one]
    rw [mul_div_assoc, div_self ht0.ne', mul_one]
  have hfin : t^2 * pairMass a a E ≤ (1000:ℝ)^(3*p₀) * 4^((3:ℝ)/5) / t := by
    refine hstep1.trans ?_
    have h1 : t^((9:ℝ)/5) * Real.exp (-(6*t)) ≤ 1 := t_pow_le_exp t ht
    have hA0 : (0:ℝ) ≤ (1000:ℝ)^(p₀ + ((pset V ∪ pset V).filter
        (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card) * 4^((3:ℝ)/5) := by positivity
    have h2 : (1000:ℝ)^(p₀ + ((pset V ∪ pset V).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card)
          * 4^((3:ℝ)/5) * (t^((9:ℝ)/5) * Real.exp (-(6*t)))
        ≤ (1000:ℝ)^(p₀ + ((pset V ∪ pset V).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card)
          * 4^((3:ℝ)/5) := by
      simpa using mul_le_mul_of_nonneg_left h1 hA0
    calc t^2 * ((1000:ℝ)^(p₀ + ((pset V ∪ pset V).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card)
          * (4^((3:ℝ)/5) * t^(-((6:ℝ)/5))) * Real.exp (-(6*t)))
        = (1000:ℝ)^(p₀ + ((pset V ∪ pset V).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card)
          * 4^((3:ℝ)/5) * (t^2 * t^(-((6:ℝ)/5))) * Real.exp (-(6*t)) := by ring
      _ = (1000:ℝ)^(p₀ + ((pset V ∪ pset V).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card)
          * 4^((3:ℝ)/5) * (t^((9:ℝ)/5) * Real.exp (-(6*t)))/t := by
          rw [htexp]; ring
      _ ≤ (1000:ℝ)^(p₀ + ((pset V ∪ pset V).filter (fun q : ℕ => q.Prime ∧ q ≤ p₀)).card)
          * 4^((3:ℝ)/5) / t :=
          div_le_div_of_nonneg_right h2 ht0.le
      _ ≤ (1000:ℝ)^(3*p₀) * 4^((3:ℝ)/5) / t := by
          apply div_le_div_of_nonneg_right _ ht0.le
          exact mul_le_mul_of_nonneg_right hK (by positivity)
  exact hfin

-- =====================   Target lemma (KM Proposition 5.4)  =====================

theorem km_prop_gcd :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ψ : ℕ → ℝ) (hψ0 : ∀ n, 0 ≤ ψ n) (hψhalf : ∀ n, ψ n ≤ 1 / 2)
        (X Y : ℕ) (hX : 1 ≤ X) (hY : X ≤ Y)
        (hblock : 1 ≤ ∑ q ∈ Finset.Icc X Y, (q.totient : ℝ) * ψ q / q ∧
                  ∑ q ∈ Finset.Icc X Y, (q.totient : ℝ) * ψ q / q ≤ 2)
        (t : ℝ) (ht : 1 ≤ t),
      ∑ p ∈ (Finset.Icc X Y).product (Finset.Icc X Y),
          (if (p.1.gcd p.2 : ℝ) ≥ max ((p.2 : ℝ) * ψ p.1) ((p.1 : ℝ) * ψ p.2) / t ∧
              10 ≤ ∑ r ∈ (Nat.primeFactors (p.1 * p.2 / (p.1.gcd p.2 * p.1.gcd p.2))).filter
                     (fun r : ℕ => t ≤ (r : ℝ)), 1 / (r : ℝ)
           then (p.1.totient : ℝ) * ψ p.1 / p.1 * ((p.2.totient : ℝ) * ψ p.2 / p.2) else 0)
        ≤ C / t := km_prop_gcd_aux

end

end Commons.NumberTheory.DuffinSchaeffer
