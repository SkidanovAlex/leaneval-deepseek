/-
Foundation for: primes `≡ 1 (mod 3)` with a logarithmic size bound.

This file sets up the basic objects used in the proof that there are many primes
congruent to `1` modulo `3` below a bound of shape `C * ℓ * log ℓ`.

Main objects:

* `LambdaOne`, the von Mangoldt function `Λ` restricted to the residue class `1` mod `3`;
* `IsGoodPrime p`, the predicate `p.Prime ∧ p % 3 = 1`;
* `goodPrimeCount N`, the number of good primes below `N`;
* `goodPrimeSum N = ∑_{p < N, p good} log p`, the Chebyshev `θ`-function of the progression.
-/
import Mathlib

open scoped BigOperators
open Finset

namespace Work.Tower

/-! ## Definitions -/

/-- The von Mangoldt function `Λ` restricted to the residue class `1` modulo `3`:
`Λ n` if `n ≡ 1 (mod 3)` and `0` otherwise. -/
noncomputable abbrev LambdaOne (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 3) n

/-- A prime congruent to `1` modulo `3`. -/
def IsGoodPrime (p : ℕ) : Prop := p.Prime ∧ p % 3 = 1

instance : DecidablePred IsGoodPrime := fun p => by unfold IsGoodPrime; infer_instance

/-- The number of good primes below `N`. -/
def goodPrimeCount (N : ℕ) : ℕ := ((Finset.range N).filter IsGoodPrime).card

/-- The sum of `log p` over good primes `p < N`; cf. `Chebyshev.theta` for all primes. -/
noncomputable def goodPrimeSum (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range N).filter IsGoodPrime, Real.log (p : ℝ)

/-! ## The von Mangoldt function on the class `1 mod 3` -/

lemma lambdaOne_apply (n : ℕ) :
    LambdaOne n = if n % 3 = 1 then ArithmeticFunction.vonMangoldt n else 0 := by
  rw [LambdaOne, ArithmeticFunction.vonMangoldt.residueClass]
  by_cases h : (n : ZMod 3) = 1
  · rw [Set.indicator_of_mem (show n ∈ {m : ℕ | (m : ZMod 3) = 1} from h),
      ite_eq_left (by simpa using (ZMod.natCast_eq_natCast_iff' n 1 3).mp h)]
  · rw [Set.indicator_of_notMem (show n ∉ {m : ℕ | (m : ZMod 3) = 1} from h),
      ite_eq_right (fun hh => h (by simpa using (ZMod.natCast_eq_natCast_iff' n 1 3).mpr hh))]

lemma lambdaOne_apply_prime {p : ℕ} (hp : p.Prime) :
    LambdaOne p = if p % 3 = 1 then Real.log (p : ℝ) else 0 := by
  rw [lambdaOne_apply, ArithmeticFunction.vonMangoldt_apply_prime hp]

lemma lambdaOne_nonneg (n : ℕ) : 0 ≤ LambdaOne n :=
  ArithmeticFunction.vonMangoldt.residueClass_nonneg _ n

lemma lambdaOne_le_vonMangoldt (n : ℕ) :
    LambdaOne n ≤ ArithmeticFunction.vonMangoldt n :=
  ArithmeticFunction.vonMangoldt.residueClass_le _ n

lemma lambdaOne_eq_zero_of_ne {n : ℕ} (h : n % 3 ≠ 1) : LambdaOne n = 0 := by
  rw [lambdaOne_apply, ite_eq_right h]

/-- The prime part of `LambdaOne`. -/
lemma primePart_apply (n : ℕ) :
    (if n.Prime then LambdaOne n else 0) = if IsGoodPrime n then Real.log (n : ℝ) else 0 := by
  by_cases hp : n.Prime
  · rw [ite_eq_left hp, lambdaOne_apply_prime hp]
    by_cases h3 : n % 3 = 1
    · rw [ite_eq_left h3, ite_eq_left ⟨hp, h3⟩]
    · rw [ite_eq_right h3, ite_eq_right (fun h => h3 h.2)]
  · rw [ite_eq_right hp, ite_eq_right (fun h => hp h.1)]

/-! ## Summability of the relevant Dirichlet series -/

lemma summable_lambdaOne_div_rpow {x : ℝ} (hx : 1 < x) :
    Summable fun n : ℕ => LambdaOne n / (n : ℝ) ^ x :=
  LSeries.summable_real_of_abscissaOfAbsConv_lt <|
    (ArithmeticFunction.vonMangoldt.abscissaOfAbsConv_residueClass_le_one
      (1 : ZMod 3)).trans_lt (by exact_mod_cast hx)

lemma summable_primePart_div_rpow {x : ℝ} (hx : 1 < x) :
    Summable fun n : ℕ => (if n.Prime then LambdaOne n else 0) / (n : ℝ) ^ x := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (summable_lambdaOne_div_rpow hx)
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnn : 0 ≤ (if n.Prime then LambdaOne n else 0) := by
        split_ifs with h
        · exact lambdaOne_nonneg n
        · exact le_rfl
      exact div_nonneg hnn (Real.rpow_nonneg hnpos.le x)
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [div_le_div_iff_of_pos_right (Real.rpow_pos_of_pos hnpos x)]
      split_ifs with h
      · exact le_rfl
      · exact lambdaOne_nonneg n

lemma summable_nonprimePart_div_rpow {x : ℝ} (hx : 1 < x) :
    Summable fun n : ℕ => (if n.Prime then 0 else LambdaOne n) / (n : ℝ) ^ x := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (summable_lambdaOne_div_rpow hx)
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnn : 0 ≤ (if n.Prime then 0 else LambdaOne n) := by
        split_ifs with h
        · exact le_rfl
        · exact lambdaOne_nonneg n
      exact div_nonneg hnn (Real.rpow_nonneg hnpos.le x)
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [div_le_div_iff_of_pos_right (Real.rpow_pos_of_pos hnpos x)]
      split_ifs with h
      · exact lambdaOne_nonneg n
      · exact le_rfl

/-! ## `goodPrimeSum` vs `θ` and vs the count -/

lemma goodPrimeSum_nonneg (N : ℕ) : 0 ≤ goodPrimeSum N :=
  Finset.sum_nonneg fun p hp => Real.log_nonneg (by
    rw [Finset.mem_filter, Finset.mem_range] at hp
    exact_mod_cast hp.2.1.one_lt.le)

lemma goodPrimeSum_mono : Monotone goodPrimeSum := by
  intro a b hab
  rw [goodPrimeSum, goodPrimeSum]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 hab, hp.2⟩
  · intro p hp _
    rw [Finset.mem_filter, Finset.mem_range] at hp
    exact Real.log_nonneg (by exact_mod_cast hp.2.1.one_lt.le)

lemma goodPrimeSum_le_theta (N : ℕ) : goodPrimeSum N ≤ Chebyshev.theta (N : ℝ) := by
  rw [goodPrimeSum, Chebyshev.theta_eq_sum_primesLE_log]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    rw [Nat.mem_primesLE]
    exact ⟨hp.1.le, hp.2.1⟩
  · intro p hp _
    rw [Nat.mem_primesLE] at hp
    exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)

lemma goodPrimeSum_le_card_mul_log (N : ℕ) :
    goodPrimeSum N ≤ (goodPrimeCount N : ℝ) * Real.log (N : ℝ) := by
  rw [goodPrimeSum, goodPrimeCount]
  refine (Finset.sum_le_card_nsmul _ _ (Real.log (N : ℝ)) ?_).trans_eq (nsmul_eq_mul _ _)
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp
  exact Real.log_le_log (by exact_mod_cast hp.2.1.pos) (by exact_mod_cast hp.1.le)

/-! ## Dyadic blocks -/

/-- The sum of `LambdaOne` over the dyadic block `[2 ^ k, 2 ^ (k + 1))`. -/
noncomputable def primeBlock (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), (if n.Prime then LambdaOne n else 0)

lemma primeBlock_eq_logSum (k : ℕ) :
    primeBlock k = ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
      (if IsGoodPrime n then Real.log (n : ℝ) else 0) := by
  rw [primeBlock]
  exact Finset.sum_congr rfl fun n _ => primePart_apply n

lemma primeBlock_le_goodPrimeSum (k : ℕ) : primeBlock k ≤ goodPrimeSum (2 ^ (k + 1)) := by
  rw [primeBlock_eq_logSum, goodPrimeSum, ← Finset.sum_filter]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_Ico] at hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp.1.2, hp.2⟩
  · intro p hp _
    rw [Finset.mem_filter, Finset.mem_range] at hp
    exact Real.log_nonneg (by exact_mod_cast hp.2.1.one_lt.le)

lemma primeBlock_le_theta (k : ℕ) : primeBlock k ≤ Chebyshev.theta ((2 ^ (k + 1) : ℕ) : ℝ) := by
  rw [primeBlock_eq_logSum, ← Finset.sum_filter, Chebyshev.theta_eq_sum_primesLE_log]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_Ico] at hp
    rw [Nat.mem_primesLE]
    exact ⟨hp.1.2.le, hp.2.1⟩
  · intro p hp _
    rw [Nat.mem_primesLE] at hp
    exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)

/-- The decomposition of `∑_{n < 2 ^ L} f n` into dyadic blocks (for `f` vanishing at `0`,
which is the case for all the summands we use). -/
lemma sum_Ico_one_two_pow_eq_sum_blocks (f : ℕ → ℝ) (L : ℕ) :
    ∑ n ∈ Finset.Ico 1 (2 ^ L), f n
      = ∑ k ∈ Finset.range L, ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), f n := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ← ih]
    have h1 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    have h2 : 2 ^ L ≤ 2 ^ (L + 1) := by
      rw [pow_succ]; exact Nat.le_mul_of_pos_right _ (by norm_num)
    have hdisj : Disjoint (Finset.Ico 1 (2 ^ L)) (Finset.Ico (2 ^ L) (2 ^ (L + 1))) :=
      Finset.disjoint_left.mpr fun x hx hx' => by
        rw [Finset.mem_Ico] at hx hx'; omega
    rw [← Finset.Ico_union_Ico_eq_Ico h1 h2, Finset.sum_union hdisj]

/-- On a dyadic block, `n ^ (-x)` is bounded by `2 ^ (-(x * k))`. -/
lemma rpow_neg_le_of_mem_Ico_two_pow {n k : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (hn : n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1))) :
    (n : ℝ) ^ (-x) ≤ (2 : ℝ) ^ (-(x * (k : ℝ))) := by
  have hk : ((2 : ℝ) ^ k) ≤ (n : ℝ) := by
    exact_mod_cast (Finset.mem_Ico.mp hn).1
  have hnpos : 0 < (n : ℝ) := by
    have h2k : 0 < (2 : ℕ) ^ k := by positivity
    exact_mod_cast lt_of_lt_of_le h2k (Finset.mem_Ico.mp hn).1
  have hmain : (2 : ℝ) ^ ((k : ℝ) * x) ≤ (n : ℝ) ^ x := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k) hk hx
    rw [← Real.rpow_natCast] at h
    rwa [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
  rw [Real.rpow_neg hnpos.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hnpos x)
    (Real.rpow_pos_of_pos (by norm_num) ((k : ℝ) * x))).mpr hmain

/-! ## Elementary estimates -/

lemma two_rpow_neg_eq_exp (y : ℝ) : (2 : ℝ) ^ (-y) = Real.exp (-(y * Real.log 2)) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

lemma two_rpow_neg_mul_nat (y : ℝ) (k : ℕ) :
    (2 : ℝ) ^ (-(y * (k : ℝ))) = ((2 : ℝ) ^ (-y)) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

lemma two_rpow_neg_le_one {δ : ℝ} (hδ : 0 ≤ δ) : (2 : ℝ) ^ (-δ) ≤ 1 := by
  rw [two_rpow_neg_eq_exp, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by
    nlinarith [hδ, Real.log_pos (by norm_num : (1 : ℝ) < 2)])

lemma one_sub_two_rpow_neg_ge {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ * Real.log 2 ≤ 1) :
    δ * Real.log 2 / 2 ≤ 1 - (2 : ℝ) ^ (-δ) := by
  rw [two_rpow_neg_eq_exp, Real.exp_neg]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hy0 : 0 ≤ δ * Real.log 2 := mul_nonneg hδ hlog2.le
  have hexp : (0 : ℝ) < Real.exp (δ * Real.log 2) := Real.exp_pos _
  have hle : (Real.exp (δ * Real.log 2))⁻¹ ≤ (1 + δ * Real.log 2)⁻¹ := by
    rw [inv_le_inv₀ hexp (by linarith)]
    linarith [Real.add_one_le_exp (δ * Real.log 2)]
  have heq : (1 : ℝ) - (1 + δ * Real.log 2)⁻¹
      = (δ * Real.log 2) / (1 + δ * Real.log 2) := by
    field_simp
    ring
  have hhalf : (δ * Real.log 2) / 2 ≤ (δ * Real.log 2) / (1 + δ * Real.log 2) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith [hy0, hδ1]
  linarith [hle, heq.le, heq.ge, hhalf]

lemma div_one_sub_two_rpow_neg_le_mul {δ c : ℝ} (hδ : 0 < δ)
    (hδ1 : δ * Real.log 2 ≤ 1) (hc : 0 ≤ c) :
    c / (1 - (2 : ℝ) ^ (-δ)) ≤ 2 * c / (δ * Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := one_sub_two_rpow_neg_ge hδ.le hδ1
  have hpos : 0 < 1 - (2 : ℝ) ^ (-δ) := by linarith [h, mul_pos hδ hlog2]
  rw [div_le_div_iff₀ hpos (by positivity)]
  nlinarith [h, hc, mul_pos hδ hlog2]

lemma geom_sum_range_le_inv {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (K : ℕ) :
    ∑ k ∈ Finset.range K, r ^ k ≤ (1 - r)⁻¹ :=
  (Summable.sum_le_tsum _ (fun _ _ => pow_nonneg h0 _)
    (summable_geometric_of_lt_one h0 h1)).trans_eq (tsum_geometric_of_lt_one h0 h1)

lemma geom_sum_Ico_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (K L : ℕ) :
    ∑ k ∈ Finset.Ico K L, r ^ k ≤ r ^ K / (1 - r) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h : ∑ k ∈ Finset.range (L - K), r ^ (K + k)
      = r ^ K * ∑ k ∈ Finset.range (L - K), r ^ k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => pow_add r K k
  rw [h, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (geom_sum_range_le_inv h0 h1 _) (pow_nonneg h0 K)

lemma log_two_floor_le_log_div {M : ℝ} (hM : 1 ≤ M) :
    (Nat.log 2 ⌊M⌋₊ : ℝ) ≤ Real.log M / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM0 : 0 < M := by linarith
  have hne : ⌊M⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊M⌋₊ := Nat.le_floor_iff hM0.le |>.mpr (by exact_mod_cast hM)
    omega
  have h1 : (2 : ℕ) ^ Nat.log 2 ⌊M⌋₊ ≤ ⌊M⌋₊ := Nat.pow_log_le_self 2 hne
  have h2 : (2 : ℝ) ^ Nat.log 2 ⌊M⌋₊ ≤ M := by
    have h2a : ((2 : ℕ) ^ Nat.log 2 ⌊M⌋₊ : ℝ) ≤ (⌊M⌋₊ : ℝ) := by exact_mod_cast h1
    have h2b : ((2 : ℕ) ^ Nat.log 2 ⌊M⌋₊ : ℝ) ≤ M :=
      h2a.trans (Nat.floor_le (a := M) hM0.le)
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h2b
  have h3 : ((Nat.log 2 ⌊M⌋₊ : ℕ) : ℝ) * Real.log 2 ≤ Real.log M := by
    have := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 ⌊M⌋₊) h2
    rwa [Real.log_pow] at this
  rw [le_div_iff₀ hlog2]
  exact h3

lemma log_le_two_mul_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  rcases le_or_gt x 1 with h | h
  · have h1 : Real.log x ≤ 0 := Real.log_nonpos hx h
    have h2 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    linarith
  · have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
      rw [Real.log_sqrt hx]
      ring
    rw [h1]
    have h2 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hsqrt
    linarith [Real.sqrt_nonneg x]

end Work.Tower
