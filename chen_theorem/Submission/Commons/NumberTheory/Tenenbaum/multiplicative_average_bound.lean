import Mathlib
import Submission.Commons.NumberTheory.Nat.sum_indicator_dvd_Icc_le
import Submission.Commons.NumberTheory.Nat.prod_pm1_pm2_eq_divisor_sum

open scoped BigOperators
open Finset

noncomputable section

namespace Commons.NumberTheory.Tenenbaum

/-- `u t a p` is the additive increment `e^{a/p} - 1` when the prime `p` is at
least `t`, and `0` otherwise. -/
def u (t a : ℝ) (p : ℕ) : ℝ :=
  if t ≤ (p : ℝ) then Real.exp (a / (p : ℝ)) - 1 else 0

/-- The weight with which a squarefree integer contributes: `0` unless it is
squarefree, in which case the product over its prime factors of `u t a p`. -/
def hfun (t a : ℝ) (d : ℕ) : ℝ :=
  if Squarefree d then ∏ p ∈ d.primeFactors, u t a p else 0

lemma u_eq_sub (t a : ℝ) (p : ℕ) (hp : t ≤ (p : ℝ)) :
    u t a p = Real.exp (a / (p : ℝ)) - 1 := by
  simp [u, hp]

lemma u_eq_zero_of_not (t a : ℝ) (p : ℕ) (hp : ¬ t ≤ (p : ℝ)) :
    u t a p = 0 := by
  simp [u, hp]

lemma u_nonneg (t a : ℝ) (ha0 : 0 ≤ a) (p : ℕ) : 0 ≤ u t a p := by
  by_cases hp : t ≤ (p : ℝ)
  · rw [u_eq_sub t a p hp]
    exact sub_nonneg.mpr (Real.one_le_exp (div_nonneg ha0 (by exact_mod_cast (Nat.zero_le p))))
  · rw [u_eq_zero_of_not t a p hp]

/-- For a product over the prime factors of `n` of `e^{a/p}` with the large
primes, rewriting via `1 + u` gives the same product over all prime factors. -/
lemma prod_filter_exp_eq_prod_one_add_u (t a : ℝ) (n : ℕ) :
    (∏ p ∈ (Nat.primeFactors n).filter (fun p : ℕ => t ≤ (p : ℝ)),
        Real.exp (a / (p : ℝ))) =
      ∏ p ∈ Nat.primeFactors n, (1 + u t a p) := by
  let F : Finset ℕ := (Nat.primeFactors n).filter (fun p : ℕ => t ≤ (p : ℝ))
  let G : Finset ℕ := (Nat.primeFactors n).filter (fun p : ℕ => ¬ t ≤ (p : ℝ))
  have hprod1 : (∏ p ∈ G, (1 + u t a p)) = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    have hp' : ¬ t ≤ (p : ℝ) := (Finset.mem_filter.mp hp).2
    have hu : u t a p = 0 := u_eq_zero_of_not t a p hp'
    simp [hu]
  calc
    (∏ p ∈ F, Real.exp (a / (p : ℝ)))
        = ∏ p ∈ F, (1 + u t a p) := by
          apply Finset.prod_congr rfl
          intro p hp
          have hp' : t ≤ (p : ℝ) := (Finset.mem_filter.mp hp).2
          rw [u_eq_sub t a p hp']
          ring
    _ = (∏ p ∈ F, (1 + u t a p)) * 1 := by rw [mul_one]
    _ = (∏ p ∈ F, (1 + u t a p)) * (∏ p ∈ G, (1 + u t a p)) := by rw [hprod1, mul_one]
    _ = ∏ p ∈ Nat.primeFactors n, (1 + u t a p) := by
          exact (Finset.prod_filter_mul_prod_filter_not (Nat.primeFactors n)
            (fun p : ℕ => t ≤ (p : ℝ)) (fun p => 1 + u t a p))

/-- The divisor sum of `hfun` expands to the product over the prime factors. -/
lemma sum_divisors_hfun_eq_prod_primeFactors_one_add_u (t a : ℝ) (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, hfun t a d) = ∏ p ∈ Nat.primeFactors n, (1 + u t a p) := by
  classical
  calc
    (∑ d ∈ n.divisors, hfun t a d)
        = ∑ d ∈ n.divisors with Squarefree d, ∏ p ∈ d.primeFactors, u t a p := by
          rw [Finset.sum_filter]
          rfl
    _ = ∑ T ∈ (Nat.primeFactors n).powerset, ∏ p ∈ T, u t a p := by
          exact Commons.NumberTheory.Nat.sum_squarefree_divisors_eq_sum_powerset_primeFactors
            n hn (fun p : ℕ => u t a p)
    _ = ∏ p ∈ Nat.primeFactors n, (1 + u t a p) := by
          exact (Finset.prod_one_add (s := Nat.primeFactors n) (f := fun p : ℕ => u t a p)).symm

lemma divisors_eq_Icc_filter_dvd (N n : ℕ) (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    n.divisors = (Finset.Icc 1 N).filter (fun d : ℕ => d ∣ n) := by
  ext d
  constructor
  · intro hd
    have hdv : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hn0 : n ≠ 0 := by omega
    have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn0 hdv
    have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdv
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, le_trans hdle hnN⟩, hdv⟩
  · intro hd
    have h1 : d ∈ Finset.Icc 1 N := (Finset.mem_filter.mp hd).1
    have hdv : d ∣ n := (Finset.mem_filter.mp hd).2
    exact Nat.mem_divisors.mpr ⟨hdv, by omega⟩

lemma sum_divisors_hfun_eq_sum_Icc_indicator (t a : ℝ) (N n : ℕ) (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    (∑ d ∈ n.divisors, hfun t a d) =
      ∑ d ∈ Finset.Icc 1 N, (if d ∣ n then hfun t a d else 0) := by
  rw [divisors_eq_Icc_filter_dvd N n hn1 hnN]
  rw [Finset.sum_filter]

/-- The left hand side equals the double sum over pairs `(n,d)` with `d ∣ n`. -/
lemma LHS_eq_doubleSum (t a : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        ∏ p ∈ (Nat.primeFactors n).filter (fun p : ℕ => t ≤ (p : ℝ)),
          Real.exp (a / (p : ℝ))) =
      (∑ n ∈ Finset.Icc 1 N,
        ∑ d ∈ Finset.Icc 1 N, (if d ∣ n then hfun t a d else 0)) := by
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
  calc
    (∏ p ∈ (Nat.primeFactors n).filter (fun p : ℕ => t ≤ (p : ℝ)), Real.exp (a / (p : ℝ)))
        = ∏ p ∈ Nat.primeFactors n, (1 + u t a p) := prod_filter_exp_eq_prod_one_add_u t a n
    _ = ∑ d ∈ n.divisors, hfun t a d := by
          exact (sum_divisors_hfun_eq_prod_primeFactors_one_add_u t a n (by omega)).symm
    _ = ∑ d ∈ Finset.Icc 1 N, (if d ∣ n then hfun t a d else 0) :=
          sum_divisors_hfun_eq_sum_Icc_indicator t a N n hn1 hnN

/-- Reordering the double sum over `(n,d)` and extracting `hfun d`. -/
lemma doubleSum_eq_sum_mul (t a : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        ∑ d ∈ Finset.Icc 1 N, (if d ∣ n then hfun t a d else 0)) =
      (∑ d ∈ Finset.Icc 1 N,
        (∑ n ∈ Finset.Icc 1 N, if d ∣ n then (1 : ℝ) else 0) * hfun t a d) := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, (if d ∣ n then hfun t a d else 0))
        = ∑ n ∈ Finset.Icc 1 N,
            ∑ d ∈ Finset.Icc 1 N, (if d ∣ n then (1 : ℝ) else 0) * hfun t a d := by
          apply Finset.sum_congr rfl
          intro n hn
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hdn : d ∣ n
          · simp [hdn]
          · simp [hdn]
    _ = ∑ d ∈ Finset.Icc 1 N,
          ∑ n ∈ Finset.Icc 1 N, (if d ∣ n then (1 : ℝ) else 0) * hfun t a d := by
          exact Finset.sum_comm
    _ = ∑ d ∈ Finset.Icc 1 N,
          (∑ n ∈ Finset.Icc 1 N, if d ∣ n then (1 : ℝ) else 0) * hfun t a d := by
          apply Finset.sum_congr rfl
          intro d hd
          exact (Finset.sum_mul (Finset.Icc 1 N)
            (fun n : ℕ => if d ∣ n then (1 : ℝ) else 0) (hfun t a d)).symm

lemma hfun_nonneg (t a : ℝ) (ha0 : 0 ≤ a) (d : ℕ) : 0 ≤ hfun t a d := by
  classical
  by_cases hsq : Squarefree d
  · have hu : ∀ p ∈ d.primeFactors, 0 ≤ u t a p := fun p hp => u_nonneg t a ha0 p
    rw [hfun, if_pos hsq]
    exact Finset.prod_nonneg hu
  · rw [hfun, if_neg hsq]

/-- The number of multiples of `d` in `[1,N]` is at most `N / d`; multiplying
by the nonnegative weight `hfun d` and summing bounds the reordered sum. -/
lemma sum_mul_le_sum_mul (t a : ℝ) (N : ℕ) (ha0 : 0 ≤ a) :
    (∑ d ∈ Finset.Icc 1 N,
        (∑ n ∈ Finset.Icc 1 N, if d ∣ n then (1 : ℝ) else 0) * hfun t a d) ≤
      (∑ d ∈ Finset.Icc 1 N, ((N : ℝ) / (d : ℝ)) * hfun t a d) := by
  refine Finset.sum_le_sum ?_
  intro d hd
  have hA : (∑ n ∈ Finset.Icc 1 N, if d ∣ n then (1 : ℝ) else 0) ≤ (N : ℝ) / (d : ℝ) :=
    Commons.NumberTheory.Nat.sum_indicator_dvd_Icc_le N d
  exact mul_le_mul_of_nonneg_right hA (hfun_nonneg t a ha0 d)

lemma sqfree_div_prod_eq_prod_div (t a : ℝ) (d : ℕ) (hsq : Squarefree d) :
    (∏ p ∈ d.primeFactors, u t a p) / (d : ℝ) =
      ∏ p ∈ d.primeFactors, (u t a p / (p : ℝ)) := by
  have hnat : (∏ p ∈ d.primeFactors, p) = d := Nat.prod_primeFactors_of_squarefree hsq
  have hden : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod (fun p : ℕ => p) d.primeFactors]
    rw [hnat]
  calc
    (∏ p ∈ d.primeFactors, u t a p) / (d : ℝ)
        = (∏ p ∈ d.primeFactors, u t a p) / (∏ p ∈ d.primeFactors, (p : ℝ)) := by
          rw [hden]
    _ = ∏ p ∈ d.primeFactors, (u t a p / (p : ℝ)) := by
          rw [Finset.prod_div_distrib]

lemma sum_hfun_div_eq_sqfree_sum (t a : ℝ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, hfun t a d / (d : ℝ)) =
      (∑ d ∈ (Finset.Icc 1 N).filter Squarefree,
        ∏ p ∈ d.primeFactors, (u t a p / (p : ℝ))) := by
  classical
  calc
    (∑ d ∈ Finset.Icc 1 N, hfun t a d / (d : ℝ))
        = ∑ d ∈ Finset.Icc 1 N,
            (if Squarefree d then (∏ p ∈ d.primeFactors, u t a p) / (d : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hsq : Squarefree d
          · simp [hfun, hsq]
          · simp [hfun, hsq]
    _ = (∑ d ∈ (Finset.Icc 1 N).filter Squarefree,
            (∏ p ∈ d.primeFactors, u t a p) / (d : ℝ)) := by
          rw [Finset.sum_filter]
    _ = (∑ d ∈ (Finset.Icc 1 N).filter Squarefree,
            ∏ p ∈ d.primeFactors, (u t a p / (p : ℝ))) := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          exact sqfree_div_prod_eq_prod_div t a d (Finset.mem_filter.mp hd).2

/-- Summing the products over the squarefree integers `d ≤ N` is bounded by the
full product over the primes `≤ N`. -/
lemma sqfree_sum_prod_le_prod_prime_one_add (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ p ∈ Nat.primesLE N, 0 ≤ w p) :
    (∑ d ∈ (Finset.Icc 1 N).filter Squarefree, ∏ p ∈ d.primeFactors, w p) ≤
      ∏ q ∈ Nat.primesLE N, (1 + w q) := by
  classical
  let s : Finset ℕ := Finset.Icc 1 N
  let P : Finset ℕ := Nat.primesLE N
  have him : Set.InjOn (fun d : ℕ => d.primeFactors) ↑(s.filter Squarefree) := by
    intro d₁ hd₁ d₂ hd₂ heq
    have hsq₁ : Squarefree d₁ := (Finset.mem_filter.mp hd₁).2
    have hsq₂ : Squarefree d₂ := (Finset.mem_filter.mp hd₂).2
    have heq' : d₁.primeFactors = d₂.primeFactors := by simpa using heq
    calc
      d₁ = ∏ p ∈ d₁.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsq₁).symm
      _ = ∏ p ∈ d₂.primeFactors, p := by rw [heq']
      _ = d₂ := Nat.prod_primeFactors_of_squarefree hsq₂
  have him_sub : Finset.image (fun d : ℕ => d.primeFactors) (s.filter Squarefree) ⊆
      P.powerset := by
    intro T hT
    rcases Finset.mem_image.mp hT with ⟨d, hd, hTd⟩
    rw [← hTd]
    apply Finset.mem_powerset.mpr
    intro p hp
    have hdmem : d ∈ s := (Finset.mem_filter.mp hd).1
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdmem).1
    have hdle : d ≤ N := (Finset.mem_Icc.mp hdmem).2
    have hd0 : d ≠ 0 := by omega
    have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ d := (Nat.mem_primeFactors.mp hp).2.1
    have hple : p ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hpdvd
    exact Nat.mem_primesLE.mpr ⟨le_trans hple hdle, hpprime⟩
  have hnonneg : ∀ T ∈ P.powerset, T ∉ Finset.image (fun d : ℕ => d.primeFactors)
      (s.filter Squarefree) → 0 ≤ ∏ p ∈ T, w p := by
    intro T hT hTnot
    apply Finset.prod_nonneg
    intro p hp
    exact hw p ((Finset.mem_powerset.mp hT) hp)
  calc
    (∑ d ∈ s.filter Squarefree, ∏ p ∈ d.primeFactors, w p)
        = ∑ T ∈ Finset.image (fun d : ℕ => d.primeFactors) (s.filter Squarefree),
            ∏ p ∈ T, w p := by
          exact (Finset.sum_image (f := fun T : Finset ℕ => ∏ p ∈ T, w p)
            (s := s.filter Squarefree) (g := fun d : ℕ => d.primeFactors) him).symm
    _ ≤ ∑ T ∈ P.powerset, ∏ p ∈ T, w p := by
          exact Finset.sum_le_sum_of_subset_of_nonneg him_sub hnonneg
    _ = ∏ q ∈ P, (1 + w q) := by
          exact (Finset.prod_one_add (s := P) (f := w)).symm

/-- The product over all primes `≤ N` can be restricted to primes at least `t`. -/
lemma prod_prime_one_add_eq_prod_filter (t a : ℝ) (N : ℕ) :
    (∏ q ∈ Nat.primesLE N, (1 + u t a q / (q : ℝ))) =
      (∏ q ∈ (Nat.primesLE N).filter (fun q : ℕ => t ≤ (q : ℝ)),
        (1 + u t a q / (q : ℝ))) := by
  classical
  let P' : Finset ℕ := Nat.primesLE N
  let P : Finset ℕ := (Nat.primesLE N).filter (fun q : ℕ => t ≤ (q : ℝ))
  have hprod1 : (∏ q ∈ P'.filter (fun q : ℕ => ¬ t ≤ (q : ℝ)), (1 + u t a q / (q : ℝ))) = 1 := by
    apply Finset.prod_eq_one
    intro q hq
    have hq' : ¬ t ≤ (q : ℝ) := (Finset.mem_filter.mp hq).2
    have hu : u t a q = 0 := u_eq_zero_of_not t a q hq'
    simp [hu]
  calc
    (∏ q ∈ Nat.primesLE N, (1 + u t a q / (q : ℝ)))
        = (∏ q ∈ P, (1 + u t a q / (q : ℝ))) *
          (∏ q ∈ P'.filter (fun q : ℕ => ¬ t ≤ (q : ℝ)), (1 + u t a q / (q : ℝ))) := by
          exact (Finset.prod_filter_mul_prod_filter_not P' (fun q : ℕ => t ≤ (q : ℝ))
            (fun q : ℕ => 1 + u t a q / (q : ℝ))).symm
    _ = ∏ q ∈ P, (1 + u t a q / (q : ℝ)) := by rw [hprod1, mul_one]

/-- For `q ≥ t`, `u t a q / q = (e^{a/q} - 1) / q`. -/
lemma sum_filter_u_div_eq_exp (t a : ℝ) (N : ℕ) :
    (∑ q ∈ (Nat.primesLE N).filter (fun q : ℕ => t ≤ (q : ℝ)), u t a q / (q : ℝ)) =
      (∑ q ∈ (Nat.primesLE N).filter (fun q : ℕ => t ≤ (q : ℝ)),
        (Real.exp (a / (q : ℝ)) - 1) / (q : ℝ)) := by
  refine Finset.sum_congr rfl ?_
  intro q hq
  have hq' : t ≤ (q : ℝ) := (Finset.mem_filter.mp hq).2
  rw [u_eq_sub t a q hq']

/-- Product inequality `∏ (1 + w p) ≤ exp (∑ w p)`. -/
lemma prod_one_add_le_exp_sum (w : ℕ → ℝ) (s : Finset ℕ) (h0 : ∀ p ∈ s, 0 ≤ w p) :
    (∏ p ∈ s, (1 + w p)) ≤ Real.exp (∑ p ∈ s, w p) := by
  calc
    (∏ p ∈ s, (1 + w p)) ≤ ∏ p ∈ s, Real.exp (w p) := by
          refine Finset.prod_le_prod₀ ?_ ?_
          · intro p hp
            exact add_nonneg zero_le_one (h0 p hp)
          · intro p hp
            simpa [add_comm] using (Real.add_one_le_exp (w p))
    _ = Real.exp (∑ p ∈ s, w p) := by
          exact (Real.exp_sum s w).symm

lemma sum_mul_N_div_eq_mul_sum_div (t a : ℝ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, ((N : ℝ) / (d : ℝ)) * hfun t a d) =
      (N : ℝ) * (∑ d ∈ Finset.Icc 1 N, hfun t a d / (d : ℝ)) := by
  classical
  calc
    (∑ d ∈ Finset.Icc 1 N, ((N : ℝ) / (d : ℝ)) * hfun t a d)
        = ∑ d ∈ Finset.Icc 1 N, (N : ℝ) * (hfun t a d / (d : ℝ)) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hd0 : (d : ℝ) ≠ 0 := by
            have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
            have hdp : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hd1)
            exact ne_of_gt hdp
          field_simp [hd0]
    _ = (N : ℝ) * (∑ d ∈ Finset.Icc 1 N, hfun t a d / (d : ℝ)) := by
          exact (Finset.mul_sum (Finset.Icc 1 N) (fun d : ℕ => hfun t a d / (d : ℝ)) (N : ℝ)).symm

/-- The main multiplicative average estimate. -/
lemma multiplicative_average_bound_core (t a : ℝ) (N : ℕ) (ha0 : 0 ≤ a) :
    (∑ n ∈ Finset.Icc 1 N,
        ∏ p ∈ (Nat.primeFactors n).filter (fun p : ℕ => t ≤ (p : ℝ)),
          Real.exp (a / (p : ℝ))) ≤
      (N : ℝ) * Real.exp (
        ∑ q ∈ (Nat.primesLE N).filter (fun q : ℕ => t ≤ (q : ℝ)),
          (Real.exp (a / (q : ℝ)) - 1) / (q : ℝ)) := by
  classical
  let s : Finset ℕ := Finset.Icc 1 N
  let P : Finset ℕ := (Nat.primesLE N).filter (fun q : ℕ => t ≤ (q : ℝ))
  have hw : ∀ p ∈ Nat.primesLE N, 0 ≤ u t a p / (p : ℝ) := by
    intro p hp
    exact div_nonneg (u_nonneg t a ha0 p) (by exact_mod_cast (Nat.zero_le p))
  have hwP : ∀ q ∈ P, 0 ≤ u t a q / (q : ℝ) := by
    intro q hq
    exact hw q ((Finset.mem_filter.mp hq).1)
  have hN : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  calc
    (∑ n ∈ Finset.Icc 1 N,
        ∏ p ∈ (Nat.primeFactors n).filter (fun p : ℕ => t ≤ (p : ℝ)),
          Real.exp (a / (p : ℝ)))
        = ∑ n ∈ s, ∑ d ∈ s, (if d ∣ n then hfun t a d else 0) := by
          simpa [s] using (LHS_eq_doubleSum t a N)
    _ = ∑ d ∈ s, (∑ n ∈ s, if d ∣ n then (1 : ℝ) else 0) * hfun t a d := by
          simpa [s] using (doubleSum_eq_sum_mul t a N)
    _ ≤ ∑ d ∈ s, ((N : ℝ) / (d : ℝ)) * hfun t a d := by
          simpa [s] using (sum_mul_le_sum_mul t a N ha0)
    _ = (N : ℝ) * (∑ d ∈ s, hfun t a d / (d : ℝ)) := by
          simpa [s] using (sum_mul_N_div_eq_mul_sum_div t a N)
    _ = (N : ℝ) * (∑ d ∈ s.filter Squarefree, ∏ p ∈ d.primeFactors, (u t a p / (p : ℝ))) := by
          rw [sum_hfun_div_eq_sqfree_sum t a N]
    _ ≤ (N : ℝ) * (∏ q ∈ Nat.primesLE N, (1 + u t a q / (q : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ hN
          exact sqfree_sum_prod_le_prod_prime_one_add (fun p : ℕ => u t a p / (p : ℝ)) N hw
    _ = (N : ℝ) * (∏ q ∈ P, (1 + u t a q / (q : ℝ))) := by
          rw [prod_prime_one_add_eq_prod_filter t a N]
    _ ≤ (N : ℝ) * Real.exp (∑ q ∈ P, u t a q / (q : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hN
          exact prod_one_add_le_exp_sum (fun q : ℕ => u t a q / (q : ℝ)) P hwP
    _ = (N : ℝ) * Real.exp (∑ q ∈ P, (Real.exp (a / (q : ℝ)) - 1) / (q : ℝ)) := by
          rw [sum_filter_u_div_eq_exp t a N]

theorem multiplicative_average_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (t a : ℝ) (N : ℕ), 2 ≤ t → 0 ≤ a → a ≤ t →
      (∑ n ∈ Finset.Icc 1 N,
          ∏ p ∈ (Nat.primeFactors n).filter (fun p : ℕ => t ≤ (p : ℝ)),
            Real.exp (a / (p : ℝ)))
        ≤ C * (N : ℝ) * Real.exp (
            ∑ q ∈ (Nat.primesLE N).filter (fun q : ℕ => t ≤ (q : ℝ)),
              (Real.exp (a / (q : ℝ)) - 1) / (q : ℝ)) := by
  refine ⟨1, by norm_num, ?_⟩
  intro t a N ht2 ha0 hat
  have hc := multiplicative_average_bound_core t a N ha0
  simpa [mul_assoc] using hc

end Commons.NumberTheory.Tenenbaum
