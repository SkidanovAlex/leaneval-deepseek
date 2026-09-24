import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Submission.Commons.NumberTheory.Chebyshev.lcmUpto_table2500

open scoped BigOperators
open Finset

namespace Commons.NumberTheory.Chebyshev

/-!
# Hanson's theorem: `lcm(1..n) ≤ 3^n`

The finite table (`lcmUpto_table2500`) covers `n ≤ 2500`.  For the tail we use
Hanson's multinomial coefficient argument: with the Sylvester sequence
`Syl 0 = 2, Syl (i+1) = Syl i * (Syl i - 1) + 1` (2, 3, 7, 43, 1807, ...),
for `k = idxNat n` (least `k` with `n < Syl k`) we have `∑_{i<k} n / Syl i ≤ n - 1`,
so `Dn n := ∏_{i<k} (n / Syl i)!` divides `n!` and hence
`Cn n := n! / Dn n` is a positive integer with `Nat.lcmUpto n ∣ Cn n`.

The tail estimate `Cn n ≤ 3 ^ n` for `n ≥ 2500` is proved by real logarithm
estimates: Stirling's formula bounds `log n!` from above and each `log q!`
from below, which gives `log (Cn n) ≤ U n` for a computable expression `U`.
One checks `U (n+1) - U n ≤ 109/100 < log 3` at every step `n ≥ 2500`
(except the rare Sylvester-activation steps, which lose at most `1`), while
`U 2500 ≤ 2500 * log 3 - 1`.  Since activations are separated by enormous
gaps (they occur at `2 * Syl i`), the slack `(n:ℝ) * log 3 - U n` never
drops below `0` for `n ≥ 2500`.
-/

def Syl : ℕ → ℕ
  | 0 => 2
  | n + 1 => Syl n * (Syl n - 1) + 1

theorem Syl_two_le (n : ℕ) : 2 ≤ Syl n := by
  induction n with
  | zero => norm_num [Syl]
  | succ n ih =>
      change 2 ≤ Syl n * (Syl n - 1) + 1
      have hp : 0 < Syl n - 1 := by omega
      have hm : Syl n ≤ Syl n * (Syl n - 1) := Nat.le_mul_of_pos_right _ hp
      omega

theorem Syl_one_le (n : ℕ) : 1 ≤ Syl n := by
  have := Syl_two_le n
  omega

theorem Syl_pos (n : ℕ) : 0 < Syl n := by
  have := Syl_two_le n
  omega

theorem Syl_lt_succ (n : ℕ) : Syl n < Syl (n + 1) := by
  change Syl n < Syl n * (Syl n - 1) + 1
  have hb : 2 ≤ Syl n := Syl_two_le n
  have hp : 0 < Syl n - 1 := by omega
  have hm : Syl n ≤ Syl n * (Syl n - 1) := Nat.le_mul_of_pos_right _ hp
  omega

theorem Syl_strictMono : StrictMono Syl := by
  intro a b h
  induction h with
  | refl => exact Syl_lt_succ a
  | step h ih => exact lt_trans ih (Syl_lt_succ _)

theorem Syl_injective {a b : ℕ} (h : Syl a = Syl b) : a = b :=
  Syl_strictMono.injective h

theorem Syl_ge_two_pow (n : ℕ) : n + 2 ≤ Syl n := by
  induction n with
  | zero => norm_num [Syl]
  | succ n ih =>
      change n + 3 ≤ Syl n * (Syl n - 1) + 1
      have hb2 : 2 ≤ Syl n := Syl_two_le n
      have hp : 0 < Syl n - 1 := by omega
      have hm : Syl n ≤ Syl n * (Syl n - 1) := Nat.le_mul_of_pos_right _ hp
      omega

theorem Syl_unbounded : ∀ n : ℕ, ∃ m, n < Syl m := by
  intro n
  refine ⟨n + 2, ?_⟩
  have := Syl_ge_two_pow (n + 2)
  omega

theorem prod_range_Syl (n : ℕ) : (∏ j ∈ range n, Syl j) = Syl n - 1 := by
  induction n with
  | zero => norm_num [Syl]
  | succ n ih =>
      rw [prod_range_succ, ih]
      have hS : Syl (n+1) = Syl n * (Syl n - 1) + 1 := rfl
      rw [hS]
      have : Syl n * (Syl n - 1) + 1 - 1 = Syl n * (Syl n - 1) := by
        exact Nat.add_sub_cancel _ _
      rw [this]
      rw [mul_comm]

/-- 1 - 1/a_n = sum_{j<n} 1/a_j : cast to ℝ -/
theorem sum_inv_Syl (n : ℕ) :
    (∑ j ∈ range n, (1 : ℝ) / (Syl j : ℝ)) = 1 - 1 / ((Syl n - 1 : ℕ) : ℝ) := by
  induction n with
  | zero => simp [Syl]
  | succ n ih =>
      rw [sum_range_succ, ih]
      have ha0 : (Syl n : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (Syl_pos n))
      have hb2 : 2 ≤ Syl n := Syl_two_le n
      have hp1n : 0 < Syl n - 1 := by omega
      have ha1 : ((Syl n - 1 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hp1n)
      have hsub : ((Syl n - 1 : ℕ) : ℝ) = (Syl n : ℝ) - 1 := by
        have hle : 1 ≤ Syl n := Syl_one_le n
        rw [Nat.cast_sub hle]
        norm_num
      have hprod : ((Syl n : ℝ) * ((Syl n - 1 : ℕ) : ℝ)) = ((Syl (n+1) - 1 : ℕ) : ℝ) := by
        have hS : Syl (n + 1) = Syl n * (Syl n - 1) + 1 := rfl
        rw [hS]
        have hnat : Syl n * (Syl n - 1) + 1 - 1 = Syl n * (Syl n - 1) := Nat.add_sub_cancel _ _
        rw [hnat]
        rw [hsub, Nat.cast_mul]
        rw [← hsub]
      calc
        (1 - 1 / ((Syl n - 1 : ℕ) : ℝ)) + 1 / (Syl n : ℝ)
            = 1 + (1 / (Syl n : ℝ) - 1 / ((Syl n - 1 : ℕ) : ℝ)) := by ring
        _ = 1 - 1 / (((Syl n : ℝ) * ((Syl n - 1 : ℕ) : ℝ))) := by
            congr 1
            rw [hsub]
            field_simp [ha0]
            have hA : (Syl n : ℝ) - 1 ≠ 0 := by
              rw [← hsub]
              exact ha1
            field_simp [hA]
            ring
        _ = 1 - 1 / ((Syl (n+1) - 1 : ℕ) : ℝ) := by rw [hprod]

/-- least index k with m < Syl k (all ℕ).  Exists since Syl is unbounded. -/
def idxNat (m : ℕ) : ℕ :=
  Nat.find (Syl_unbounded m)

theorem idxNat_spec (m : ℕ) : m < Syl (idxNat m) := by
  unfold idxNat
  exact Nat.find_spec (Syl_unbounded m)

theorem idxNat_min (m k : ℕ) (hk : k < idxNat m) : Syl k ≤ m := by
  unfold idxNat at hk
  have hmin := Nat.find_min (Syl_unbounded m) hk
  omega

/-- Key bound (Hanson Lemma 1): for m ≥ 1, sum of integer quotients is < m. -/
theorem sum_div_Syl_lt (m : ℕ) (hm : 1 ≤ m) :
    (∑ i ∈ range (idxNat m), ((m / Syl i : ℕ) : ℝ)) < (m : ℝ) := by
  have hsum := sum_inv_Syl (idxNat m)
  calc
    (∑ i ∈ range (idxNat m), ((m / Syl i : ℕ) : ℝ))
        ≤ (∑ i ∈ range (idxNat m), (m : ℝ) / (Syl i : ℝ)) := by
          refine sum_le_sum ?_
          intro i hi
          have hpos : (0:ℝ) < (Syl i : ℝ) := by exact_mod_cast (Syl_pos i)
          have hq : (m / Syl i : ℕ) * Syl i ≤ m := Nat.div_mul_le_self m (Syl i)
          have hq' : ((m / Syl i : ℕ) : ℝ) * (Syl i : ℝ) ≤ (m : ℝ) := by
            exact_mod_cast hq
          exact (le_div_iff₀ hpos).2 hq'
    _ = (m : ℝ) * (∑ i ∈ range (idxNat m), 1 / (Syl i : ℝ)) := by
          rw [mul_sum]
          refine sum_congr rfl ?_
          intro i hi
          ring
    _ = (m : ℝ) * (1 - 1 / ((Syl (idxNat m) - 1 : ℕ) : ℝ)) := by rw [hsum]
    _ < (m : ℝ) := by
          have hden : (0:ℝ) < ((Syl (idxNat m) - 1 : ℕ) : ℝ) := by
            have hk := idxNat_spec m
            have : 0 < Syl (idxNat m) - 1 := by omega
            exact_mod_cast this
          have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
          have hlt : 1 - 1 / ((Syl (idxNat m) - 1 : ℕ) : ℝ) < 1 := by
            rw [sub_lt_self_iff]
            positivity
          nlinarith

/-- integer form: sum of quotients is at most m - 1 -/
theorem sum_div_Syl_le_sub_one (m : ℕ) (hm : 1 ≤ m) :
    (∑ i ∈ range (idxNat m), m / Syl i) ≤ m - 1 := by
  have hlt := sum_div_Syl_lt m hm
  have hlt' : (∑ i ∈ range (idxNat m), m / Syl i) < m := by
    exact_mod_cast hlt
  omega

theorem Syl_dvd_mul_dvd (n : ℕ) (i : ℕ) : (n / Syl i) * Syl i ≤ n :=
  Nat.div_mul_le_self n (Syl i)

/-- quotient q_i := n / a_i is at least 1 when i < idxNat n (i.e. a_i ≤ n) -/
theorem quot_pos (n : ℕ) (i : ℕ) (hi : i < idxNat n) : 1 ≤ n / Syl i := by
  have h1 : Syl i ≤ n := idxNat_min n i hi
  exact (Nat.le_div_iff_mul_le (Syl_pos i)).2 (by simpa using h1)

/-- q_i = n / a_i -/
noncomputable def quot (n i : ℕ) : ℕ := n / Syl i

/-- D(n) = product of q_i! -/
noncomputable def Dn (n : ℕ) : ℕ := ∏ i ∈ range (idxNat n), (quot n i).factorial

/-- C(n) = n! / D(n) -/
noncomputable def Cn (n : ℕ) : ℕ := n.factorial / Dn n

theorem sum_quot_le_sub_one (n : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ range (idxNat n), quot n i) ≤ n - 1 := by
  simpa [quot] using sum_div_Syl_le_sub_one n hn

theorem Dn_dvd_factorial (n : ℕ) : Dn n ∣ n.factorial := by
  by_cases hn : 1 ≤ n
  · have ht := sum_quot_le_sub_one n hn
    have h1 : Dn n ∣ (∑ i ∈ range (idxNat n), quot n i).factorial := by
      simpa [Dn] using Nat.prod_factorial_dvd_factorial_sum (range (idxNat n)) (quot n)
    have h2 : (∑ i ∈ range (idxNat n), quot n i).factorial ∣ n.factorial :=
      Nat.factorial_dvd_factorial (by omega)
    exact dvd_trans h1 h2
  · have hn0 : n = 0 := by omega
    subst n
    have h0 : idxNat 0 = 0 := by
      unfold idxNat
      by_contra h
      have hpos : 0 < Nat.find (Syl_unbounded 0) := Nat.pos_of_ne_zero h
      have hmin := Nat.find_min (Syl_unbounded 0) hpos
      exact hmin (by have := Syl_pos 0; omega)
    simp [Dn, quot, h0]

theorem Dn_pos (n : ℕ) : 0 < Dn n := by
  exact prod_pos (fun i hi => (by positivity : 0 < (quot n i).factorial))

theorem Cn_pos (n : ℕ) : 0 < Cn n := by
  unfold Cn
  have hdvd : Dn n ∣ n.factorial := Dn_dvd_factorial n
  have hle : Dn n ≤ n.factorial := Nat.le_of_dvd (Nat.factorial_pos n) hdvd
  exact Nat.div_pos hle (Dn_pos n)


theorem sum_factorization_apply (s : Finset ℕ) (f : ℕ → ℕ →₀ ℕ) (p : ℕ) :
    (∑ j ∈ s, f j) p = ∑ j ∈ s, (f j) p := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s has ih
    simp [has, ih, Finsupp.add_apply]

theorem Cn_factorization_sub (n : ℕ) (p : ℕ) :
    (Cn n).factorization p = (n.factorial).factorization p - (Dn n).factorization p := by
  unfold Cn
  rw [Nat.factorization_div (Dn_dvd_factorial n)]
  rfl

theorem factorial_factorization_Ico (n p : ℕ) (hp : p.Prime) :
    (n.factorial).factorization p = ∑ i ∈ Ico 1 (n + 1), n / p ^ i := by
  exact Nat.factorization_factorial hp (Nat.lt_succ_of_le (Nat.log_le_self p n))

theorem Dn_factorization_sum (n p : ℕ) (hp : p.Prime) :
    (Dn n).factorization p =
      ∑ j ∈ range (idxNat n), (∑ i ∈ Ico 1 ((quot n j) + 1), (quot n j) / p ^ i : ℕ) := by
  calc
    (Dn n).factorization p
        = (∑ j ∈ range (idxNat n), ((quot n j).factorial).factorization) p := by
          rw [Dn, Nat.factorization_prod (fun j hj => Nat.factorial_ne_zero _)]
    _ = ∑ j ∈ range (idxNat n), (((quot n j).factorial).factorization p) := by
          rw [sum_factorization_apply]
    _ = ∑ j ∈ range (idxNat n), (∑ i ∈ Ico 1 ((quot n j) + 1), (quot n j) / p ^ i) := by
          refine sum_congr rfl ?_
          intro j hj
          rw [Nat.factorization_factorial hp
            (Nat.lt_succ_of_le (Nat.log_le_self p (quot n j)))]

/-- q_j / p^i = m / Syl j where m = n / p^i -/
theorem quot_div_pow_eq (n p i j : ℕ) :
    (quot n j) / p ^ i = (n / p ^ i) / Syl j := by
  unfold quot
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  congr 1
  rw [mul_comm]



theorem idxNat_mono {m n : ℕ} (h : m ≤ n) : idxNat m ≤ idxNat n := by
  by_contra hc
  have hlt : idxNat n < idxNat m := by omega
  have hs := idxNat_min m (idxNat n) hlt
  have hn : n < Syl (idxNat n) := idxNat_spec n
  omega

theorem Syl_gt_of_idxNat_le {m j : ℕ} (h : idxNat m ≤ j) : m < Syl j := by
  have h1 := idxNat_spec m
  exact lt_of_lt_of_le h1 (Syl_strictMono.monotone h)

theorem sum_div_zero_extend (m N : ℕ) (hN : idxNat m ≤ N) :
    (∑ j ∈ range (idxNat m), m / Syl j) = ∑ j ∈ range N, m / Syl j := by
  classical
  refine Finset.sum_subset ?subset ?zero
  · intro j hj
    exact Finset.mem_range.mpr (by
      have hj' : j < idxNat m := Finset.mem_range.mp hj
      omega)
  · intro j hj hnot
    have hnot' : ¬ j < idxNat m := by simpa using hnot
    have hjm : idxNat m ≤ j := by omega
    exact Nat.div_eq_of_lt (Syl_gt_of_idxNat_le hjm)

theorem legendre_term_ge (n p i : ℕ) (hp : p.Prime) (hpn : p ^ i ≤ n) :
    1 ≤ n / p ^ i - (∑ j ∈ range (idxNat n), (n / p ^ i) / Syl j) := by
  let m := n / p ^ i
  have hm : 1 ≤ m := by
    have hpipos : 0 < p ^ i := pow_pos hp.pos i
    exact (Nat.le_div_iff_mul_le hpipos).2 (by simpa using hpn)
  have hsum : (∑ j ∈ range (idxNat n), m / Syl j) ≤ m - 1 := by
    have hle : n / p ^ i ≤ n := Nat.div_le_self n (p ^ i)
    have heq := sum_div_zero_extend m (idxNat n) (idxNat_mono hle)
    rw [← heq]
    exact sum_div_Syl_le_sub_one m hm
  change 1 ≤ m - (∑ j ∈ range (idxNat n), m / Syl j)
  omega

theorem quot_div_sum_eq (n p i : ℕ) :
    (∑ j ∈ range (idxNat n), (quot n j) / p ^ i) =
      ∑ j ∈ range (idxNat n), (n / p ^ i) / Syl j := by
  refine sum_congr rfl ?_
  intro j hj
  exact quot_div_pow_eq n p i j


theorem nat_add_sub_add_sub (x y u v : ℕ) (hu : u ≤ x) (hv : v ≤ y) :
    (x + y) - (u + v) = (x - u) + (y - v) := by
  rw [← Nat.sub_sub]
  rw [add_comm x y]
  rw [Nat.add_sub_assoc hu y]
  rw [add_comm y (x - u)]
  rw [Nat.add_sub_assoc hv (x - u)]

theorem sum_sub_sum {ι : Type*} (s : Finset ι) (f g : ι → ℕ)
    (h : ∀ i ∈ s, g i ≤ f i) :
    (∑ i ∈ s, f i) - (∑ i ∈ s, g i) = ∑ i ∈ s, (f i - g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
      have h' : ∀ i ∈ s, g i ≤ f i := fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hga : g a ≤ f a := h a (Finset.mem_insert_self a s)
      have hG : (∑ i ∈ s, g i) ≤ (∑ i ∈ s, f i) := sum_le_sum h'
      rw [sum_insert has, sum_insert has, sum_insert has]
      rw [nat_add_sub_add_sub (f a) (∑ i ∈ s, f i) (g a) (∑ i ∈ s, g i) hga hG]
      rw [ih h']

theorem pow_ge_add_one (p i : ℕ) (hp : 2 ≤ p) : i + 1 ≤ p ^ i := by
  induction i with
  | zero => norm_num
  | succ i ih =>
      rw [pow_succ]
      calc
        i + 1 + 1 ≤ (i + 1) * p := by
          have h1 : (i + 1) * 2 ≤ (i + 1) * p := Nat.mul_le_mul_left (i + 1) (by omega)
          omega
        _ ≤ p ^ i * p := Nat.mul_le_mul_right p ih

theorem pow_gt_of_add_le (p q i : ℕ) (hp : 2 ≤ p) (hi : q + 1 ≤ i) : q < p ^ i := by
  have h1 : i + 1 ≤ p ^ i := pow_ge_add_one p i hp
  have h2 : q + 1 < p ^ i := by omega
  omega

theorem div_pow_eq_zero_of_ge (q p i : ℕ) (hp : 2 ≤ p) (hi : q + 1 ≤ i) :
    q / p ^ i = 0 :=
  Nat.div_eq_of_lt (pow_gt_of_add_le p q i hp hi)

/-- for q ≤ N the inner Legendre sum can be extended to the longer range (extra terms vanish) -/
theorem inner_extend (q N p : ℕ) (hp : 2 ≤ p) (hq : q ≤ N) :
    (∑ i ∈ Ico 1 (q + 1), q / p ^ i) = (∑ i ∈ Ico 1 (N + 1), q / p ^ i) := by
  classical
  have hsub : Ico 1 (q + 1) ⊆ Ico 1 (N + 1) := by
    exact Finset.Ico_subset_Ico_right (by omega)
  refine Finset.sum_subset hsub ?_
  intro i hi hnot
  have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
  have hnot' : ¬ i < q + 1 := by
    intro hic
    exact hnot (by exact Finset.mem_Ico.mpr ⟨hi1, hic⟩)
  have hiq : q + 1 ≤ i := by omega
  exact div_pow_eq_zero_of_ge q p i hp hiq


theorem quot_le (n i : ℕ) : quot n i ≤ n := by
  unfold quot
  exact Nat.div_le_self n (Syl i)

theorem Dn_factorization_reassoc (n p : ℕ) (hp : p.Prime) :
    (Dn n).factorization p =
      ∑ i ∈ Ico 1 (n + 1), (∑ j ∈ range (idxNat n), (quot n j) / p ^ i) := by
  calc
    (Dn n).factorization p
        = ∑ j ∈ range (idxNat n), (∑ i ∈ Ico 1 ((quot n j) + 1), (quot n j) / p ^ i) :=
          Dn_factorization_sum n p hp
    _ = ∑ j ∈ range (idxNat n), (∑ i ∈ Ico 1 (n + 1), (quot n j) / p ^ i) := by
          refine sum_congr rfl ?_
          intro j hj
          exact inner_extend (quot n j) n p (by have := hp.two_le; omega) (quot_le n j)
    _ = ∑ i ∈ Ico 1 (n + 1), (∑ j ∈ range (idxNat n), (quot n j) / p ^ i) := by
          exact Finset.sum_comm


theorem idxNat_zero : idxNat 0 = 0 := by
  unfold idxNat
  by_contra h
  have hpos : 0 < Nat.find (Syl_unbounded 0) := Nat.pos_of_ne_zero h
  have hmin := Nat.find_min (Syl_unbounded 0) hpos
  exact hmin (by have := Syl_pos 0; omega)

theorem lcmUpto_dvd_Cn (n : ℕ) : Nat.lcmUpto n ∣ Cn n := by
  by_cases hn0 : n = 0
  · subst n
    simp [Nat.lcmUpto, Cn, Dn, quot, idxNat_zero]
  · rw [← Nat.factorization_prime_le_iff_dvd (Nat.lcmUpto_ne_zero n) (Cn_pos n).ne']
    intro p hp
    rw [Nat.factorization_lcmUpto n hp]
    rw [Cn_factorization_sub n p]
    rw [factorial_factorization_Ico n p hp]
    rw [Dn_factorization_reassoc n p hp]
    let I := Ico 1 (n + 1)
    let c := fun i : ℕ => ∑ j ∈ range (idxNat n), (quot n j) / p ^ i
    have hc : ∀ i ∈ I, c i ≤ n / p ^ i := by
      intro i hi
      by_cases hpn : p ^ i ≤ n
      · have h1 := legendre_term_ge n p i hp hpn
        -- 1 ≤ m − Σ_j (n/p^i)/Syl j ; c i = Σ_j quot/p^i = Σ_j (n/p^i)/Syl j
        have hrewrite : c i = ∑ j ∈ range (idxNat n), (n / p ^ i) / Syl j := by
          unfold c
          exact quot_div_sum_eq n p i
        rw [hrewrite]
        have hm : 1 ≤ n / p ^ i := by
          have hpipos : 0 < p ^ i := pow_pos hp.pos i
          exact (Nat.le_div_iff_mul_le hpipos).2 (by simpa using hpn)
        omega
      · -- p^i > n : then n/p^i = 0 and every term zero
        have hnot : n < p ^ i := by omega
        have hm : n / p ^ i = 0 := Nat.div_eq_of_lt hnot
        unfold c
        calc
          (∑ j ∈ range (idxNat n), quot n j / p ^ i) = 0 := by
            apply sum_eq_zero
            intro j hj
            exact Nat.div_eq_of_lt (lt_of_le_of_lt (quot_le n j) hnot)
          _ ≤ n / p ^ i := by rw [hm]
    have hdiff :
        (∑ i ∈ I, n / p ^ i) - (∑ i ∈ I, c i) = ∑ i ∈ I, (n / p ^ i - c i) :=
      sum_sub_sum I (fun i => n / p ^ i) c hc
    rw [hdiff]
    -- now: goal Nat.log p n ≤ Σ_{i∈I} (a_i − c_i)
    let t := fun i : ℕ => n / p ^ i - c i
    have hnonneg : ∀ i ∈ I, 0 ≤ t i := by
      intro i hi
      exact Nat.le_sub_of_add_le (by
        have hc' := hc i hi
        omega)
    have hterm : ∀ j ∈ range (Nat.log p n), 1 ≤ t (j + 1) := by
      intro j hj
      have hjlog : j + 1 ≤ Nat.log p n := by
        have : j < Nat.log p n := Finset.mem_range.mp hj
        omega
      have hpil : p ^ (j + 1) ≤ p ^ Nat.log p n := Nat.pow_le_pow_right (by have := hp.pos; omega) hjlog
      have hpn : p ^ (j + 1) ≤ n := le_trans hpil (Nat.pow_log_le_self p (by omega : n ≠ 0))
      have h1 := legendre_term_ge n p (j + 1) hp hpn
      have hrewrite : c (j + 1) = ∑ k ∈ range (idxNat n), (n / p ^ (j + 1)) / Syl k := by
        unfold c
        exact quot_div_sum_eq n p (j + 1)
      dsimp [t]
      rw [hrewrite]
      simpa using h1
    let J := (range (Nat.log p n)).image (fun j => j + 1)
    have hJsub : J ⊆ I := by
      intro i hi
      rw [Finset.mem_image] at hi
      rcases hi with ⟨j, hj, rfl⟩
      have hjlog : j + 1 ≤ Nat.log p n := by
        have : j < Nat.log p n := Finset.mem_range.mp hj
        omega
      have hle : Nat.log p n ≤ n := Nat.log_le_self p n
      rw [Finset.mem_Ico]
      omega
    have hsub : (∑ i ∈ J, t i) ≤ ∑ i ∈ I, t i := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hJsub (by
        intro i hi hnot
        exact hnonneg i hi)
    have hJt : (∑ j ∈ range (Nat.log p n), 1) ≤ ∑ j ∈ range (Nat.log p n), t (j + 1) := by
      refine sum_le_sum ?_
      intro j hj
      exact hterm j hj
    have hJsum : (∑ i ∈ J, t i) = ∑ j ∈ range (Nat.log p n), t (j + 1) := by
      dsimp [J]
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact Nat.succ.inj hab
    have hcard : (∑ j ∈ range (Nat.log p n), 1) = Nat.log p n := by simp
    calc
      Nat.log p n ≤ ∑ i ∈ J, t i := by
        rw [← hcard, hJsum]
        exact hJt
      _ ≤ ∑ i ∈ I, t i := hsub
      _ = _ := by
        rfl


/-- lcmUpto n ≤ Cn n : the multinomial bound dominates the lcm. -/
theorem lcmUpto_le_Cn (n : ℕ) : Nat.lcmUpto n ≤ Cn n :=
  Nat.le_of_dvd (Cn_pos n) (lcmUpto_dvd_Cn n)



/-! ## Real setup for the tail -/

/-- the Sylvester sequence as reals -/
def sylR (i : ℕ) : ℝ := Syl i

/-- `h(x) = x log x - x + log(2πx)/2`, the Stirling lower bound shape. -/
noncomputable def hLog (x : ℝ) : ℝ := x * Real.log x - x + Real.log (2 * Real.pi * x) / 2

/-- `A(n) = n log n - n + 1 + log n / 2`, an upper bound for `log n!`. -/
noncomputable def ALog (n : ℕ) : ℝ := (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + 1 + Real.log (n : ℝ) / 2

/-- number of indices `i` with `2 * Syl i ≤ n`  (equivalently `i < idxNat (n/2)`) -/
def mact (n : ℕ) : ℕ := idxNat (n / 2)

/-- the real upper-bound expression for `log (Cn n)` -/
noncomputable def Ulog (n : ℕ) : ℝ :=
  ALog n - ∑ i ∈ range (mact n), hLog ((n : ℝ) / (Syl i : ℝ) - 1)

/-- slack : `n log 3 - Ulog n` -/
noncomputable def slack (n : ℕ) : ℝ := (n : ℝ) * Real.log 3 - Ulog n

theorem sylR_pos (i : ℕ) : 0 < sylR i := by
  dsimp [sylR]
  exact_mod_cast (Syl_pos i)

theorem sylR_two_le (i : ℕ) : 2 ≤ sylR i := by
  dsimp [sylR]
  exact_mod_cast (Syl_two_le i)

/-- 1 + (1+t)⁻¹ style: t/(1+t) ≤ log(1+t) for t ≥ 0 -/
theorem log_one_add_ge_div (t : ℝ) (ht : 0 ≤ t) : t / (1 + t) ≤ Real.log (1 + t) := by
  have hp : 0 < 1 + t := by nlinarith
  have h := Real.one_sub_inv_le_log_of_pos hp
  have hiden : 1 - (1 + t)⁻¹ = t / (1 + t) := by
    have hden : 1 + t ≠ 0 := by linarith
    field_simp [hden] <;> try ring
  rwa [hiden] at h

/-- log(1+t) ≤ t for t > -1 -/
theorem log_one_add_le_self (t : ℝ) (ht : -1 < t) : Real.log (1 + t) ≤ t := by
  have hp : 0 < 1 + t := by linarith
  have h := Real.log_le_sub_one_of_pos hp
  have h' : 1 + t - 1 = t := by ring
  rwa [h'] at h

/-- log(1-y) ≥ - y/(1-y) for 0 < y < 1 -/
theorem log_one_sub_ge_neg (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) :
    -y / (1 - y) ≤ Real.log (1 - y) := by
  have hp : 0 < (1 - y)⁻¹ := by positivity
  have hle := Real.log_le_sub_one_of_pos hp
  have hrewrite : Real.log ((1 - y)⁻¹) = -Real.log (1 - y) := by rw [Real.log_inv]
  have hmain : -Real.log (1 - y) ≤ (1 - y)⁻¹ - 1 := by simpa [hrewrite] using hle
  let w : ℝ := y / (1 - y)
  have hident : (1 - y)⁻¹ - 1 = w := by
    dsimp [w]
    have hden : 1 - y ≠ 0 := by linarith
    field_simp [hden] <;> try ring
  have hmain' : -Real.log (1 - y) ≤ w := by rwa [hident] at hmain
  have hflip : -w ≤ Real.log (1 - y) := by linarith
  have hne : 1 - y ≠ 0 := by linarith
  simpa [w, neg_div, hne] using hflip

/-- log n ≤ (n : ℝ) − 1 for n ≥ 1 (real n) -/
theorem log_le_sub_one {x : ℝ} (hx0 : 0 < x) (hx1 : 1 ≤ x) :
    Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx0

/-! ### log of factorials -/

/-- log(q!) ≥ q log q - q + log(2πq)/2 for q ≥ 1  (Stirling lower, via mathlib) -/
theorem log_factorial_ge_hLog (q : ℕ) (hq : 1 ≤ q) :
    hLog (q : ℝ) ≤ Real.log (q.factorial : ℝ) := by
  have hq0 : q ≠ 0 := by omega
  have h := Stirling.le_log_factorial_stirling hq0
  -- mathlib: q * log q - q + log q / 2 + log (2π)/2 ≤ log q!
  dsimp [hLog]
  have hpi : (2 : ℝ) * Real.pi * (q : ℝ) ≠ 0 := by positivity
  have : Real.log (2 * Real.pi * (q : ℝ)) / 2 =
      Real.log (q : ℝ) / 2 + Real.log (2 * Real.pi) / 2 := by
    rw [Real.log_mul (by positivity : (2:ℝ) * Real.pi ≠ 0) (by exact_mod_cast hq0)]
    ring
  rw [this]
  linarith

/-- log n! ≤ A(n) for n ≥ 1 (Stirling upper via stirlingSeq antitone). -/
theorem log_factorial_le_ALog (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤ ALog n := by
  have hn0 : n ≠ 0 := by omega
  have hls := Stirling.log_stirlingSeq_formula n
  -- hls: log (stirlingSeq n) = log n! - ½ log(2n) - n log(n/e)
  have hid : Real.log (n.factorial : ℝ) =
      Real.log (Stirling.stirlingSeq n) + 1 / 2 * Real.log (2 * (n : ℝ)) +
        (n : ℝ) * Real.log ((n : ℝ) / Real.exp 1) := by
    nlinarith
  -- antitone bound
  have hant := Stirling.log_stirlingSeq'_antitone
  have h01 : 0 ≤ n - 1 := by omega
  have hle0 := hant h01
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hseq : Real.log (Stirling.stirlingSeq n) ≤ Real.log (Stirling.stirlingSeq 1) := by
    simpa [hn'] using hle0
  have hseq1 : Real.log (Stirling.stirlingSeq 1) = 1 - Real.log 2 / 2 := by
    rw [Stirling.stirlingSeq_one]
    calc
      Real.log (Real.exp 1 / √2) = Real.log (Real.exp 1) - Real.log (√2) :=
        Real.log_div (by positivity : (Real.exp 1 : ℝ) ≠ 0) (by positivity : (√2 : ℝ) ≠ 0)
      _ = 1 - Real.log (√2) := by rw [Real.log_exp]
      _ = 1 - Real.log 2 / 2 := by rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have he : Real.exp 1 ≠ 0 := by positivity
  have hn_e : (n : ℝ) / Real.exp 1 ≠ 0 := by positivity
  calc
    Real.log (n.factorial : ℝ) = Real.log (Stirling.stirlingSeq n) + 1 / 2 * Real.log (2 * (n : ℝ)) + (n : ℝ) * Real.log ((n : ℝ) / Real.exp 1) := hid
    _ ≤ (1 - Real.log 2 / 2) + 1 / 2 * Real.log (2 * (n : ℝ)) + (n : ℝ) * Real.log ((n : ℝ) / Real.exp 1) := by
        have h1 : Real.log (Stirling.stirlingSeq n) ≤ 1 - Real.log 2 / 2 := by
          calc
            Real.log (Stirling.stirlingSeq n) ≤ Real.log (Stirling.stirlingSeq 1) := hseq
            _ = 1 - Real.log 2 / 2 := hseq1
        nlinarith
    _ = ALog n := by
        dsimp [ALog]
        have hmul : Real.log (2 * (n : ℝ)) = Real.log (n : ℝ) + Real.log 2 := by
          rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hne]
          ring
        have hdiv : Real.log ((n : ℝ) / Real.exp 1) = Real.log (n : ℝ) - 1 := by
          rw [Real.log_div hne he, Real.log_exp]
        rw [hmul, hdiv]
        ring


/-! ### hLog is increasing on [1, ∞)  (elementary, no calculus) -/

/-- log(b/a) ≥ (b-a)/b for 1 ≤ a ≤ b -/
theorem log_ratio_ge (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (b - a) / b ≤ Real.log (b / a) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have ht0 : 0 ≤ (b - a) / a := by positivity
  have hlog := log_one_add_ge_div ((b - a) / a) ht0
  have hident : 1 + (b - a) / a = b / a := by
    field_simp [ha0.ne'] <;> try ring
  have hval : ((b - a) / a) / (1 + (b - a) / a) = (b - a) / b := by
    rw [hident]
    field_simp [ha0.ne', hb0.ne'] <;> try ring
  have hlog' : (b - a) / b ≤ Real.log (1 + (b - a) / a) := by
    rwa [hval] at hlog
  simpa [hident] using hlog'

/-- hLog is increasing on [1, ∞) -/
theorem hLog_mono (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) : hLog a ≤ hLog b := by
  have hb0 : 0 < b := by linarith
  have ha0 : 0 < a := by linarith
  have h1 := log_ratio_ge a b ha hab
  have hlogb : 1 - 1 / b ≤ Real.log b := by
    have hlg := log_ratio_ge 1 b (by norm_num) (by linarith)
    have hident : (b - 1) / b = 1 - 1 / b := by field_simp [hb0.ne'] <;> try ring
    simpa [hident] using hlg
  have hsplit : hLog b - hLog a =
      (b - a) * (Real.log b - 1) + (a + 1 / 2) * Real.log (b / a) := by
    dsimp [hLog]
    rw [Real.log_mul (by positivity : (2:ℝ) * Real.pi ≠ 0) (by linarith : b ≠ 0)]
    rw [Real.log_mul (by positivity : (2:ℝ) * Real.pi ≠ 0) (by linarith : a ≠ 0)]
    rw [Real.log_div (by linarith : b ≠ 0) (by linarith : a ≠ 0)]
    ring
  have hZ : (Real.log b - 1) + (a + 1 / 2) / b ≥ ((1 - 1 / b) - 1) + (3 / 2) / b := by
    have hdiv : (a + 1 / 2) / b ≥ (3 / 2) / b := by
      exact div_le_div_of_nonneg_right (by linarith : 3 / 2 ≤ a + 1 / 2) hb0.le
    have hh2 : 1 - 1 / b ≤ Real.log b := hlogb
    nlinarith
  have hW : (a + 1 / 2) * ((b - a) / b) ≤ (a + 1 / 2) * Real.log (b / a) := by
    exact mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ a + 1 / 2)
  have hnonneg : 0 ≤ hLog b - hLog a := by
    calc
      0 ≤ (b - a) * (((1 - 1 / b) - 1) + (3 / 2) / b) := by
        have hz0 : ((1 - 1 / b) - 1) + (3 / 2) / b = (1 / 2) / b := by
          field_simp [hb0.ne'] <;> try ring
        rw [hz0]
        positivity
      _ ≤ (b - a) * ((Real.log b - 1) + (a + 1 / 2) / b) := by
        exact mul_le_mul_of_nonneg_left hZ (by linarith : 0 ≤ b - a)
      _ = (b - a) * (Real.log b - 1) + (a + 1 / 2) * (b - a) / b := by
        field_simp [hb0.ne'] <;> try ring
      _ ≤ (b - a) * (Real.log b - 1) + (a + 1 / 2) * Real.log (b / a) := by
        have hW' : (a + 1 / 2) * (b - a) / b ≤ (a + 1 / 2) * Real.log (b / a) := by
          simpa [div_eq_mul_inv, mul_assoc] using hW
        nlinarith [hW']
      _ = hLog b - hLog a := hsplit.symm
  linarith


/-! ### log of Cn : pointwise bound  log(Cn n) ≤ Ulog n -/

/-- log of a positive finite product is the sum of logs -/
theorem log_prod_pos {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < f i) :
    Real.log (∏ i ∈ s, f i) = ∑ i ∈ s, Real.log (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
      have hfa : 0 < f a := hpos a (by simp)
      have hs : 0 < ∏ i ∈ s, f i := Finset.prod_pos (fun i hi => hpos i (Finset.mem_insert_of_mem hi))
      calc
        Real.log (∏ x ∈ insert a s, f x) = Real.log (f a * ∏ x ∈ s, f x) := by rw [Finset.prod_insert has]
        _ = Real.log (f a) + Real.log (∏ x ∈ s, f x) := Real.log_mul hfa.ne' (ne_of_gt hs)
        _ = Real.log (f a) + ∑ x ∈ s, Real.log (f x) := by
            rw [ih (fun i hi => hpos i (Finset.mem_insert_of_mem hi))]
        _ = ∑ x ∈ insert a s, Real.log (f x) := by rw [Finset.sum_insert has]

/-- real identity: (Cn n : ℝ) = n! / Dn n -/
theorem Cn_cast_eq_div (n : ℕ) : (Cn n : ℝ) = (n.factorial : ℝ) / (Dn n : ℝ) := by
  have hdiv : (Cn n) * (Dn n) = n.factorial := by
    unfold Cn
    rw [Nat.div_mul_cancel (Dn_dvd_factorial n)]
  have hD : (Dn n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Dn_pos n))
  have hmul : (Cn n : ℝ) * (Dn n : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast hdiv
  calc
    (Cn n : ℝ) = (Cn n : ℝ) * (Dn n : ℝ) / (Dn n : ℝ) := by field_simp [hD]
    _ = (n.factorial : ℝ) / (Dn n : ℝ) := by rw [hmul]

/-- log (Cn n) = log n! - log (Dn n) -/
theorem log_Cn_sub_log_Dn (n : ℕ) :
    Real.log (Cn n : ℝ) = Real.log (n.factorial : ℝ) - Real.log (Dn n : ℝ) := by
  have hpos2 : 0 < (n.factorial : ℝ) := by positivity
  have hpos3 : 0 < (Dn n : ℝ) := by exact_mod_cast (Dn_pos n)
  rw [Cn_cast_eq_div n]
  rw [Real.log_div hpos2.ne' hpos3.ne']

/-- log (Dn n) = Σ log(q_i!) -/
theorem log_Dn_eq_sum (n : ℕ) :
    Real.log (Dn n : ℝ) =
      ∑ i ∈ range (idxNat n), Real.log ((quot n i).factorial : ℝ) := by
  rw [Dn]
  rw [Nat.cast_prod]
  have hpos : ∀ i ∈ range (idxNat n), 0 < ((quot n i).factorial : ℝ) := by
    intro i hi
    positivity
  exact log_prod_pos (range (idxNat n)) (fun i => ((quot n i).factorial : ℝ)) hpos

/-- x - 1 ≤ ⌊x⌋ for x = (n : ℝ)/a -/
theorem sub_one_le_quot_real (n a : ℕ) (ha : 0 < a) :
    (n : ℝ) / a - 1 ≤ ((n / a : ℕ) : ℝ) := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hn : n < a * (n / a + 1) := by
    have hmod : n % a < a := Nat.mod_lt n ha
    calc
      n = a * (n / a) + n % a := (Nat.div_add_mod n a).symm
      _ < a * (n / a) + a := Nat.add_lt_add_left hmod (a * (n / a))
      _ = a * (n / a + 1) := by ring
  have hlt : (n : ℝ) / a < ((n / a : ℕ) : ℝ) + 1 := by
    have hreal : (n : ℝ) < (a : ℝ) * (((n / a : ℕ) : ℝ) + 1) := by exact_mod_cast hn
    rw [div_lt_iff₀ haR]
    simpa [mul_comm] using hreal
  linarith

/-- for an active index: 1 ≤ x_i - 1 and x_i - 1 ≤ q_i -/
theorem active_bounds (n i : ℕ) (hi : i < mact n) :
    1 ≤ (n : ℝ) / (Syl i : ℝ) - 1 ∧
      (n : ℝ) / (Syl i : ℝ) - 1 ≤ ((n / Syl i : ℕ) : ℝ) := by
  have hlt : Syl i ≤ n / 2 := by
    exact idxNat_min (n / 2) i hi
  have h2 : 2 * Syl i ≤ n := by
    have h2' : Syl i * 2 ≤ n := (Nat.le_div_iff_mul_le (by norm_num : 0 < (2:ℕ))).mp hlt
    simpa [mul_comm] using h2'
  have hcast : (2 : ℝ) * (Syl i : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
  have hsyl : 0 < (Syl i : ℝ) := by exact_mod_cast (Syl_pos i)
  have hge : 2 ≤ (n : ℝ) / (Syl i : ℝ) := by
    rw [le_div_iff₀ hsyl]
    simpa [mul_comm] using hcast
  constructor
  · linarith
  · exact sub_one_le_quot_real n (Syl i) (Syl_pos i)

/-- mact n ≤ idxNat n -/
theorem mact_le_idxNat (n : ℕ) : mact n ≤ idxNat n := by
  have hdiv : n / 2 ≤ n := Nat.div_le_self n 2
  exact idxNat_mono hdiv

/-- range (mact n) ⊆ range (idxNat n) -/
theorem range_mact_subset (n : ℕ) : range (mact n) ⊆ range (idxNat n) := by
  intro x hx
  exact Finset.mem_range.mpr (by
    have : x < mact n := Finset.mem_range.mp hx
    have : x < idxNat n := lt_of_lt_of_le this (mact_le_idxNat n)
    omega)

/-- log(q!) ≥ hLog(x-1) for active index -/
theorem log_quot_ge_hLog_x (n i : ℕ) (hi : i < mact n) (hn : 1 ≤ n) :
    hLog ((n : ℝ) / (Syl i : ℝ) - 1) ≤ Real.log ((quot n i).factorial : ℝ) := by
  have hq1 : 1 ≤ quot n i := quot_pos n i (by
    -- i < mact n ≤ idxNat n
    exact lt_of_lt_of_le hi (mact_le_idxNat n))
  have hlog1 : hLog (quot n i : ℝ) ≤ Real.log ((quot n i).factorial : ℝ) :=
    log_factorial_ge_hLog (quot n i) hq1
  have habs := active_bounds n i hi
  have hmono : hLog ((n : ℝ) / (Syl i : ℝ) - 1) ≤ hLog (quot n i : ℝ) := by
    exact hLog_mono ((n : ℝ) / (Syl i : ℝ) - 1) (quot n i : ℝ) habs.1 habs.2
  exact le_trans hmono hlog1

/-- pointwise: log(Cn n) ≤ Ulog n for n ≥ 1 -/
theorem log_Cn_le_Ulog (n : ℕ) (hn : 1 ≤ n) : Real.log (Cn n : ℝ) ≤ Ulog n := by
  rw [log_Cn_sub_log_Dn n, log_Dn_eq_sum n]
  -- goal: log n! − Σ_{range idxNat} log(q!) ≤ ALog n − Σ_{range mact} hLog(x−1)
  let g : ℕ → ℝ := fun i => hLog ((n : ℝ) / (Syl i : ℝ) - 1)
  let f : ℕ → ℝ := fun i => Real.log ((quot n i).factorial : ℝ)
  have hA : Real.log (n.factorial : ℝ) ≤ ALog n := log_factorial_le_ALog n hn
  have hsum : (∑ i ∈ range (mact n), g i) ≤ ∑ i ∈ range (idxNat n), f i := by
    -- split: per-term over mact ≤ f, then extend f-sum from mact to idxNat by nonneg terms
    have hsub0 : (∑ i ∈ range (mact n), g i) ≤ ∑ i ∈ range (mact n), f i := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have him : i < mact n := Finset.mem_range.mp hi
      have hg := log_quot_ge_hLog_x n i him hn
      exact hg
    have hnonneg : ∀ i ∈ range (idxNat n), i ∉ range (mact n) → 0 ≤ f i := by
      intro i hi hnot
      dsimp [f]
      have hqi : 1 ≤ quot n i := quot_pos n i (Finset.mem_range.mp hi)
      have hfact : 1 ≤ (quot n i).factorial := Nat.succ_le_of_lt (Nat.factorial_pos (quot n i))
      have hpos : 0 < ((quot n i).factorial : ℝ) := by exact_mod_cast (Nat.factorial_pos (quot n i))
      have hge1 : 1 ≤ ((quot n i).factorial : ℝ) := by exact_mod_cast hfact
      exact Real.log_nonneg hge1
    have hsub1 : (∑ i ∈ range (mact n), f i) ≤ ∑ i ∈ range (idxNat n), f i :=
      Finset.sum_le_sum_of_subset_of_nonneg (range_mact_subset n) hnonneg
    exact le_trans hsub0 hsub1
  have hcalc : Real.log (n.factorial : ℝ) - (∑ i ∈ range (idxNat n), f i)
      ≤ ALog n - (∑ i ∈ range (mact n), g i) := by
    -- log n! - F ≤ A - G  ⟸  log n! ≤ A  ∧  G ≤ F
    nlinarith [hA, hsum]
  simpa [Ulog, g, f] using hcalc


/-! ### increments of Ulog -/

/-- ALog over reals -/
noncomputable def AReal (x : ℝ) : ℝ := x * Real.log x - x + 1 + Real.log x / 2

theorem ALog_eq_AReal (n : ℕ) : ALog n = AReal (n : ℝ) := by
  rfl

/-- AReal increment: AReal(x+1) − AReal x ≤ log(x+1) + 1/(2x) for x ≥ 1 -/
theorem AReal_inc_le (x : ℝ) (hx1 : 1 ≤ x) :
    AReal (x + 1) - AReal x ≤ Real.log (x + 1) + 1 / (2 * x) := by
  have hx0 : 0 < x := by linarith
  have hx1n : x + 1 ≠ 0 := by positivity
  have hdiv : Real.log (x + 1) - Real.log x = Real.log ((x + 1) / x) := by
    rw [Real.log_div hx1n hx0.ne']
  have hid : AReal (x + 1) - AReal x =
      x * Real.log ((x + 1) / x) + Real.log (x + 1) - 1 + Real.log ((x + 1) / x) / 2 := by
    dsimp [AReal]
    calc
      ((x + 1) * Real.log (x + 1) - (x + 1) + 1 + Real.log (x + 1) / 2)
          - (x * Real.log x - x + 1 + Real.log x / 2)
          = ((x + 1) * Real.log (x + 1) - x * Real.log x) - 1 + (Real.log (x + 1) - Real.log x) / 2 := by ring
      _ = (x * (Real.log (x + 1) - Real.log x) + Real.log (x + 1)) - 1 + (Real.log (x + 1) - Real.log x) / 2 := by ring
      _ = (x * Real.log ((x + 1) / x) + Real.log (x + 1)) - 1 + Real.log ((x + 1) / x) / 2 := by rw [hdiv]
      _ = x * Real.log ((x + 1) / x) + Real.log (x + 1) - 1 + Real.log ((x + 1) / x) / 2 := by ring
  rw [hid]
  have hlg : Real.log ((x + 1) / x) ≤ 1 / x := by
    have hlg1 : Real.log (1 + 1 / x) ≤ 1 / x := by
      apply log_one_add_le_self
      have hxinv : 0 ≤ 1 / x := by positivity
      linarith
    have hident : 1 + 1 / x = (x + 1) / x := by field_simp [hx0.ne'] <;> try ring
    rw [← hident]
    exact hlg1
  have hA : x * Real.log ((x + 1) / x) ≤ 1 := by
    calc
      x * Real.log ((x + 1) / x) ≤ x * (1 / x) := mul_le_mul_of_nonneg_left hlg (by linarith : 0 ≤ x)
      _ = 1 := by field_simp [hx0.ne'] <;> try ring
  have hB : Real.log ((x + 1) / x) / 2 ≤ 1 / (2 * x) := by
    have hq := div_le_div_of_nonneg_right hlg (by norm_num : (0:ℝ) ≤ 2)
    have hnorm : (1 / x) / 2 = 1 / (2 * x) := by field_simp [hx0.ne'] <;> try ring
    rw [hnorm] at hq
    exact hq
  linarith

/-- ALog increment ≤ log(n+1) + 1/(2n) -/
theorem ALog_inc_le (n : ℕ) (hn : 1 ≤ n) :
    ALog (n + 1) - ALog n ≤ Real.log ((n + 1 : ℕ) : ℝ) + 1 / (2 * (n : ℝ)) := by
  have hx : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hinc := AReal_inc_le (n : ℝ) hx
  have hc1 : ALog (n + 1) = AReal ((n : ℝ) + 1) := by
    rw [ALog_eq_AReal (n + 1)]
    congr 1
    norm_num
  have hc2 : ALog n = AReal (n : ℝ) := ALog_eq_AReal n
  have hc3 : Real.log (((n + 1 : ℕ) : ℝ)) = Real.log ((n : ℝ) + 1) := by
    congr 1
    norm_num
  rw [← hc1, ← hc2, ← hc3] at hinc
  exact hinc

/-- h(x+δ) − h(x) ≥ δ log x for x ≥ 1, 0 < δ ≤ 1/2 -/
theorem hLog_inc_ge (x δ : ℝ) (hx : 1 ≤ x) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    δ * Real.log x ≤ hLog (x + δ) - hLog x := by
  have hx0 : 0 < x := by linarith
  have hxd : 0 < x + δ := by linarith
  have h1px : 0 < 1 + δ / x := by positivity
  have hz1 : (2 : ℝ) * Real.pi * (x + δ) ≠ 0 := by positivity
  have hz2 : (2 : ℝ) * Real.pi * x ≠ 0 := by positivity
  -- identity: hLog(x+δ) - hLog x = (x+1/2+δ) log(1+δ/x) + δ log x - δ
  have h1 : Real.log (2 * Real.pi * (x + δ)) - Real.log (2 * Real.pi * x)
      = Real.log (1 + δ / x) := by
    rw [← Real.log_div hz1 hz2]
    congr 1
    field_simp [hx0.ne'] <;> try ring
  have h2 : Real.log (x + δ) = Real.log x + Real.log (1 + δ / x) := by
    have hxprod : x * (1 + δ / x) = x + δ := by field_simp [hx0.ne'] <;> try ring
    rw [← hxprod]
    rw [Real.log_mul (ne_of_gt hx0) (ne_of_gt h1px)]
  have hid : hLog (x + δ) - hLog x =
      (x + 1 / 2 + δ) * Real.log (1 + δ / x) + δ * Real.log x - δ := by
    dsimp [hLog]
    calc
      ((x + δ) * Real.log (x + δ) - (x + δ) + Real.log (2 * Real.pi * (x + δ)) / 2)
          - (x * Real.log x - x + Real.log (2 * Real.pi * x) / 2)
          = (x + δ) * Real.log (x + δ) - x * Real.log x - δ
              + (Real.log (2 * Real.pi * (x + δ)) - Real.log (2 * Real.pi * x)) / 2 := by ring
      _ = (x + δ) * (Real.log x + Real.log (1 + δ / x)) - x * Real.log x - δ
              + Real.log (1 + δ / x) / 2 := by rw [h2, h1]
      _ = (x + 1 / 2 + δ) * Real.log (1 + δ / x) + δ * Real.log x - δ := by ring
  rw [hid]
  -- (x+1/2+δ)·log(1+δ/x) ≥ δ  via log(1+t) ≥ t/(1+t)
  have ht0 : 0 ≤ δ / x := by positivity
  have hlg := log_one_add_ge_div (δ / x) ht0
  have hident : (δ / x) / (1 + δ / x) = δ / (x + δ) := by
    field_simp [hx0.ne', hxd.ne'] <;> try ring
  have hlg' : δ / (x + δ) ≤ Real.log (1 + δ / x) := by
    rw [← hident]
    exact hlg
  have hbig : (x + 1 / 2 + δ) * (δ / (x + δ)) ≤ (x + 1 / 2 + δ) * Real.log (1 + δ / x) :=
    mul_le_mul_of_nonneg_left hlg' (by linarith : 0 ≤ x + 1 / 2 + δ)
  have hge_d : δ ≤ (x + 1 / 2 + δ) * (δ / (x + δ)) := by
    have hcmp : x + δ ≤ x + 1 / 2 + δ := by linarith
    have hδpos : 0 ≤ δ / (x + δ) := by positivity
    have hm := mul_le_mul_of_nonneg_right hcmp hδpos
    have hcancel : (x + δ) * (δ / (x + δ)) = δ := by field_simp [hxd.ne'] <;> try ring
    rwa [hcancel] at hm
  have hge : δ ≤ (x + 1 / 2 + δ) * Real.log (1 + δ / x) := le_trans hge_d hbig
  linarith


/-! ### sum over Sylvester indices of log quotients -/

/-- S_m = Σ_{i<m} log(a_i)/a_i -/
noncomputable def Slog (m : ℕ) : ℝ := ∑ i ∈ range m, Real.log (Syl i : ℝ) / (Syl i : ℝ)

/-- if Syl j ≤ m then j < idxNat m -/
theorem idxNat_lt_of_Syl_le {m j : ℕ} (h : Syl j ≤ m) : j < idxNat m := by
  by_contra hc
  have hmj : idxNat m ≤ j := by omega
  have : m < Syl j := Syl_gt_of_idxNat_le hmj
  omega

/-- inner per-term bound: log(n/a_i - 1) ≥ log n - a_i/(n-a_i) - log a_i -/
theorem term_log_bound_inner (n i : ℕ) (hact : 2 * Syl i ≤ n) :
    Real.log ((n : ℝ) / (Syl i : ℝ) - 1) ≥
      Real.log (n : ℝ) - (Syl i : ℝ) / ((n : ℝ) - (Syl i : ℝ)) - Real.log (Syl i : ℝ) := by
  let N : ℝ := n
  let A : ℝ := Syl i
  have hsyl0 : 0 < (Syl i : ℝ) := by exact_mod_cast (Syl_pos i)
  have hnR : 0 < (n : ℝ) := by
    have hc0 : (2 : ℝ) * (Syl i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hact
    nlinarith
  have hA0 : 0 < A := by simpa [A] using hsyl0
  have hN0 : 0 < N := by simpa [N] using hnR
  have hc : (2 : ℝ) * A ≤ N := by
    simpa [A, N] using (by exact_mod_cast hact : (2 : ℝ) * (Syl i : ℝ) ≤ (n : ℝ))
  have hA_lt_N : A < N := by nlinarith
  have hA_N0 : 0 < A / N := by positivity
  have hA_N1 : A / N < 1 := by
    rw [div_lt_one hN0]
    exact hA_lt_N
  have hmain : -(A / N) / (1 - A / N) ≤ Real.log (1 - A / N) :=
    log_one_sub_ge_neg (A / N) hA_N0 hA_N1
  have hsim : -(A / N) / (1 - A / N) = -A / (N - A) := by
    field_simp [hN0.ne'] <;> try ring
  have hw : -A / (N - A) ≤ Real.log (1 - A / N) := by
    rwa [hsim] at hmain
  have hprod : N * (1 - A / N) = N - A := by field_simp [hN0.ne'] <;> try ring
  have hlogm : Real.log (N * (1 - A / N)) = Real.log N + Real.log (1 - A / N) :=
    Real.log_mul (ne_of_gt hN0) (ne_of_gt (sub_pos.mpr hA_N1))
  have hid2 : Real.log (N - A) = Real.log N + Real.log (1 - A / N) := by
    rw [← hprod]
    exact hlogm
  have hld : Real.log (N / A - 1) = Real.log (N - A) - Real.log A := by
    have hNA : N - A ≠ 0 := by linarith
    have hdiv : Real.log ((N - A) / A) = Real.log (N - A) - Real.log A :=
      Real.log_div hNA hA0.ne'
    have hquot : (N - A) / A = N / A - 1 := by field_simp [hA0.ne'] <;> try ring
    rw [← hquot]
    exact hdiv
  rw [hld]
  let w : ℝ := A / (N - A)
  have hw' : -w ≤ Real.log (1 - A / N) := by
    have : -(A / (N - A)) ≤ Real.log (1 - A / N) := by
      simpa [neg_div] using hw
    simpa [w] using this
  have hlin : Real.log N - w ≤ Real.log (N - A) := by
    rw [hid2]
    linarith
  have hfin : Real.log N - A / (N - A) - Real.log A ≤ Real.log (N - A) - Real.log A := by
    simpa [w] using (sub_le_sub_right hlin (Real.log A))
  have hgoal : Real.log N - A / (N - A) - Real.log A ≤ Real.log (N / A - 1) := by
    rw [hld]
    exact hfin
  linarith

/-- per-term: (1/a_i) log(n/a_i - 1) ≥ log n/a_i - 1/(n-a_i) - log a_i/a_i -/
theorem term_log_split (n i : ℕ) (hact : 2 * Syl i ≤ n) :
    (1 / (Syl i : ℝ)) * Real.log ((n : ℝ) / (Syl i : ℝ) - 1) ≥
      Real.log (n : ℝ) / (Syl i : ℝ) - 1 / ((n : ℝ) - (Syl i : ℝ)) -
        Real.log (Syl i : ℝ) / (Syl i : ℝ) := by
  have hin := term_log_bound_inner n i hact
  have hmul := mul_le_mul_of_nonneg_left hin (by positivity : 0 ≤ 1 / (Syl i : ℝ))
  have hrew : (1 / (Syl i : ℝ)) *
        (Real.log (n : ℝ) - (Syl i : ℝ) / ((n : ℝ) - (Syl i : ℝ)) - Real.log (Syl i : ℝ))
      = Real.log (n : ℝ) / (Syl i : ℝ) - 1 / ((n : ℝ) - (Syl i : ℝ)) -
        Real.log (Syl i : ℝ) / (Syl i : ℝ) := by
    have hA : (Syl i : ℝ) ≠ 0 := by exact_mod_cast (Syl_pos i).ne'
    field_simp [hA] <;> ring
  rwa [hrew] at hmul

theorem mact_succ_eq_of_not_activation (n : ℕ) (h : ∀ j : ℕ, n + 1 ≠ 2 * Syl j) :
    mact (n + 1) = mact n := by
  unfold mact
  apply le_antisymm
  · -- idxNat((n+1)/2) ≤ idxNat(n/2)
    have hlem : ∀ j < idxNat ((n + 1) / 2), j < idxNat (n / 2) := by
      intro j hj
      have h1 : Syl j ≤ (n + 1) / 2 := idxNat_min ((n + 1) / 2) j hj
      have hx : 2 * Syl j ≤ 2 * ((n + 1) / 2) := Nat.mul_le_mul_left 2 h1
      have hb : 2 * ((n + 1) / 2) ≤ n + 1 := by omega
      have hle2 : 2 * Syl j ≤ n + 1 := by omega
      have hne2 : 2 * Syl j ≠ n + 1 := by
        intro hc
        exact h j hc.symm
      have h4 : 2 * Syl j ≤ n := by omega
      have h4' : Syl j * 2 ≤ n := by simpa [mul_comm] using h4
      have h5 : Syl j ≤ n / 2 := (Nat.le_div_iff_mul_le (by norm_num : 0 < (2:ℕ))).mpr h4'
      exact idxNat_lt_of_Syl_le h5
    by_contra hc
    have hgt : idxNat (n / 2) < idxNat ((n + 1) / 2) := by omega
    have hbad := hlem (idxNat (n / 2)) hgt
    omega
  · apply idxNat_mono
    omega


/-- x-argument of the hLog term at step n and index i -/
noncomputable def xquot (n i : ℕ) : ℝ := (n : ℝ) / (Syl i : ℝ) - 1

theorem xquot_ge_one_of_active (n i : ℕ) (hact : 2 * Syl i ≤ n) : 1 ≤ xquot n i := by
  dsimp [xquot]
  have hc : (2 : ℝ) * (Syl i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hact
  have hs : 0 < (Syl i : ℝ) := by exact_mod_cast (Syl_pos i)
  have : 2 ≤ (n : ℝ) / (Syl i : ℝ) := by
    rw [le_div_iff₀ hs]
    simpa [mul_comm] using hc
  linarith

theorem xquot_pos_of_active (n i : ℕ) (hact : 2 * Syl i ≤ n) : 0 < xquot n i := by
  have h1 := xquot_ge_one_of_active n i hact
  linarith

/-- δ = 1/a_i ≤ 1/2 -/
theorem inv_syl_le_half (i : ℕ) : 1 / (Syl i : ℝ) ≤ 1 / 2 := by
  have h2 : 2 ≤ (Syl i : ℝ) := by exact_mod_cast (Syl_two_le i)
  have hpos : 0 < (Syl i : ℝ) := by exact_mod_cast (Syl_pos i)
  have hpos2 : 0 < (2 : ℝ) := by norm_num
  exact (div_le_div_iff₀ hpos hpos2).mpr (by simpa using h2)

/-- Σ over active indices of per-term lower bounds -/
theorem sum_term_lower (n m : ℕ) (hm : ∀ i < m, 2 * Syl i ≤ n) :
    (∑ i ∈ range m, (1 / (Syl i : ℝ)) * Real.log (xquot n i)) ≥
      Real.log (n : ℝ) * (∑ i ∈ range m, 1 / (Syl i : ℝ))
        - (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) - Slog m := by
  have hper : ∀ i ∈ range m,
      (1 / (Syl i : ℝ)) * Real.log (xquot n i) ≥
        Real.log (n : ℝ) / (Syl i : ℝ) - 1 / ((n : ℝ) - (Syl i : ℝ))
          - Real.log (Syl i : ℝ) / (Syl i : ℝ) := by
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    have hact : 2 * Syl i ≤ n := hm i hi'
    have hlg : Real.log (xquot n i) = Real.log ((n : ℝ) / (Syl i : ℝ) - 1) := by
      dsimp [xquot]
    rw [hlg]
    exact term_log_split n i hact
  have hsum : (∑ i ∈ range m, (1 / (Syl i : ℝ)) * Real.log (xquot n i)) ≥
      ∑ i ∈ range m,
        (Real.log (n : ℝ) / (Syl i : ℝ) - 1 / ((n : ℝ) - (Syl i : ℝ))
          - Real.log (Syl i : ℝ) / (Syl i : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hper i hi
  have hsumA : (∑ i ∈ range m, Real.log (n : ℝ) / (Syl i : ℝ))
      = Real.log (n : ℝ) * (∑ i ∈ range m, 1 / (Syl i : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [div_eq_mul_inv, one_div]
  have hsplit : (∑ i ∈ range m,
        (Real.log (n : ℝ) / (Syl i : ℝ) - 1 / ((n : ℝ) - (Syl i : ℝ))
          - Real.log (Syl i : ℝ) / (Syl i : ℝ)))
      = Real.log (n : ℝ) * (∑ i ∈ range m, 1 / (Syl i : ℝ))
        - (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) - Slog m := by
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_sub_distrib]
    rw [hsumA]
    rfl
  rwa [hsplit] at hsum


/-- active indices of mact: 2·Syl i ≤ n -/
theorem active_of_lt_mact (n i : ℕ) (hi : i < mact n) : 2 * Syl i ≤ n := by
  have h1 : Syl i ≤ n / 2 := idxNat_min (n / 2) i hi
  have h2' : Syl i * 2 ≤ n := (Nat.le_div_iff_mul_le (by norm_num : 0 < (2:ℕ))).mp h1
  simpa [mul_comm] using h2'

/-- m ≥ 4 for n ≥ 2500 -/
theorem mact_ge_four_of_2500 (n : ℕ) (hn : 2500 ≤ n) : 4 ≤ mact n := by
  have hdiv : 1250 ≤ n / 2 := by omega
  have hmono := idxNat_mono hdiv
  have hidx : idxNat 1250 = 4 := by
    unfold idxNat
    apply le_antisymm
    · exact Nat.find_min' (Syl_unbounded 1250) (by norm_num [Syl])
    · by_contra h4
      have hx : Nat.find (Syl_unbounded 1250) < 4 := by omega
      have hall : ∀ j < 4, Syl j ≤ 1250 := by
        intro j hj
        have hmono2 : Syl j ≤ Syl 3 := Syl_strictMono.monotone (by omega)
        have h3 : Syl 3 = 43 := by norm_num [Syl]
        omega
      have hle : Syl (Nat.find (Syl_unbounded 1250)) ≤ 1250 := hall _ hx
      have hspec : 1250 < Syl (Nat.find (Syl_unbounded 1250)) := Nat.find_spec (Syl_unbounded 1250)
      omega
  unfold mact
  omega

/-- 1 − Σ_{i<m} 1/a_i = 1/(a_m − 1) -/
theorem sum_inv_Syl_sub (m : ℕ) :
    1 - (∑ i ∈ range m, 1 / (Syl i : ℝ)) = 1 / ((Syl m - 1 : ℕ) : ℝ) := by
  have h := sum_inv_Syl m
  -- h : Σ 1/Syl j = 1 − 1/(Syl m − 1)
  have hden : (Syl m - 1 : ℕ) ≠ 0 := by
    have hpos : 0 < Syl m - 1 := by
      have : 1 < Syl m := by
        have hs : 2 ≤ Syl m := Syl_two_le m
        omega
      omega
    exact ne_of_gt hpos
  rw [h]
  ring

/-- Σ_{i<m} 1/(n − a_i) ≤ (2m)/n -/
theorem sum_inv_diff_le (n m : ℕ) (hn0 : 0 < n) (h : ∀ i < m, 2 * Syl i ≤ n) :
    (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) ≤ (2 * (m : ℝ)) / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hterm : ∀ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ)) ≤ 2 / (n : ℝ) := by
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    have hact : 2 * Syl i ≤ n := h i hi'
    have hc0 : (2 : ℝ) * (Syl i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hact
    have hdiff0 : 0 < (n : ℝ) - (Syl i : ℝ) := by
      have ha0 : 0 ≤ (Syl i : ℝ) := by positivity
      have : (Syl i : ℝ) < (n : ℝ) := by nlinarith
      linarith
    have hcore : 1 / ((n : ℝ) - (Syl i : ℝ)) ≤ 2 / (n : ℝ) := by
      rw [div_le_div_iff₀ hdiff0 hnR]
      nlinarith
    exact hcore
  have hsum : (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ)))
      ≤ ∑ i ∈ range m, 2 / (n : ℝ) := by
    exact Finset.sum_le_sum (fun i hi => hterm i hi)
  have hconst : (∑ i ∈ range m, 2 / (n : ℝ)) = (m : ℝ) * (2 / (n : ℝ)) := by
    simp
  have hfinal : (m : ℝ) * (2 / (n : ℝ)) = (2 * (m : ℝ)) / (n : ℝ) := by
    field_simp [hnR.ne'] <;> try ring
  rwa [hconst, hfinal] at hsum

/-- log(n+1) − log n ≤ 1/n -/
theorem log_succ_sub_le (n : ℕ) (hn0 : 0 < n) :
    Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hdiv : Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) = Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
    rw [Real.log_div (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0) (ne_of_gt hnR)]
  rw [hdiv]
  have hident : ((n + 1 : ℕ) : ℝ) / (n : ℝ) = 1 + 1 / (n : ℝ) := by
    norm_num
    field_simp [hnR.ne'] <;> try ring
  rw [hident]
  apply log_one_add_le_self
  have hx : 0 ≤ 1 / (n : ℝ) := by positivity
  linarith

/-- per-term increment lower bound in the Ulog difference -/
theorem term_inc_lower (n i : ℕ) (hi : i < mact n) :
    (1 / (Syl i : ℝ)) * Real.log (xquot n i) ≤
      hLog (xquot (n + 1) i) - hLog (xquot n i) := by
  have hact : 2 * Syl i ≤ n := active_of_lt_mact n i hi
  have hx1 : 1 ≤ xquot n i := xquot_ge_one_of_active n i hact
  have hsyl0 : 0 < (Syl i : ℝ) := by exact_mod_cast (Syl_pos i)
  have hδ0 : 0 < 1 / (Syl i : ℝ) := by positivity
  have hδ1 : 1 / (Syl i : ℝ) ≤ 1 / 2 := inv_syl_le_half i
  have hinc := hLog_inc_ge (xquot n i) (1 / (Syl i : ℝ)) hx1 hδ0 hδ1
  have hdelta : xquot (n + 1) i = xquot n i + 1 / (Syl i : ℝ) := by
    dsimp [xquot]
    have hsyl : (Syl i : ℝ) ≠ 0 := by exact_mod_cast (Syl_pos i).ne'
    rw [show (((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1) by norm_num]
    field_simp [hsyl] <;> try ring
  rw [← hdelta] at hinc
  exact hinc


/-- main non-activation increment bound (with symbolic m) -/
theorem Ulog_inc_nonact_bound (n : ℕ) (hn : 2500 ≤ n) (h : ∀ j : ℕ, n + 1 ≠ 2 * Syl j) :
    Ulog (n + 1) - Ulog n ≤ Slog (mact n) + Real.log (n : ℝ) / (((Syl (mact n) - 1 : ℕ) : ℝ))
      + (2 * (mact n : ℝ) + 3 / 2) / (n : ℝ) := by
  let m := mact n
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn0)
  have hmeq : mact (n + 1) = m := by
    dsimp [m]
    exact mact_succ_eq_of_not_activation n h
  have hma : ∀ i < m, 2 * Syl i ≤ n := by
    intro i hi
    dsimp [m] at hi
    exact active_of_lt_mact n i hi
  have hΔeq : Ulog (n + 1) - Ulog n =
      (ALog (n + 1) - ALog n) - (∑ i ∈ range m, (hLog (xquot (n + 1) i) - hLog (xquot n i))) := by
    unfold Ulog
    rw [hmeq]
    dsimp [xquot]
    rw [Finset.sum_sub_distrib]
    ring
  have hT : (∑ i ∈ range m, (1 / (Syl i : ℝ)) * Real.log (xquot n i)) ≤
      ∑ i ∈ range m, (hLog (xquot (n + 1) i) - hLog (xquot n i)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    dsimp [m] at hi'
    exact term_inc_lower n i hi'
  have h1 : Ulog (n + 1) - Ulog n ≤
      (ALog (n + 1) - ALog n) - (∑ i ∈ range m, (1 / (Syl i : ℝ)) * Real.log (xquot n i)) := by
    rw [hΔeq]
    have hUU : (ALog (n + 1) - ALog n) - (∑ i ∈ range m, (hLog (xquot (n + 1) i) - hLog (xquot n i)))
        ≤ (ALog (n + 1) - ALog n) - (∑ i ∈ range m, (1 / (Syl i : ℝ)) * Real.log (xquot n i)) := by
      linarith [hT]
    exact hUU
  have h2 : Ulog (n + 1) - Ulog n ≤
      (Real.log ((n + 1 : ℕ) : ℝ) + 1 / (2 * (n : ℝ)))
        - (∑ i ∈ range m, (1 / (Syl i : ℝ)) * Real.log (xquot n i)) := by
    have hDA : ALog (n + 1) - ALog n ≤ Real.log ((n + 1 : ℕ) : ℝ) + 1 / (2 * (n : ℝ)) :=
      ALog_inc_le n hn1
    linarith [h1, hDA]
  have hTL := sum_term_lower n m hma
  have hS1 : 1 - (∑ i ∈ range m, 1 / (Syl i : ℝ)) = 1 / (((Syl m - 1 : ℕ) : ℝ)) := by
    dsimp [m]
    exact sum_inv_Syl_sub (mact n)
  have hS2 : (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) ≤ (2 * (m : ℝ)) / (n : ℝ) := by
    dsimp [m]
    exact sum_inv_diff_le n (mact n) hn0 (fun i hi => active_of_lt_mact n i hi)
  have hLogLe : Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := log_succ_sub_le n hn0
  have h3 : Ulog (n + 1) - Ulog n ≤
      Slog m + Real.log (n : ℝ) / (((Syl m - 1 : ℕ) : ℝ)) + (2 * (m : ℝ) + 3 / 2) / (n : ℝ) := by
    have hring : (Real.log ((n + 1 : ℕ) : ℝ) + 1 / (2 * (n : ℝ)))
          - (Real.log (n : ℝ) * (∑ i ∈ range m, 1 / (Syl i : ℝ))
            - (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) - Slog m)
        = (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))
            + Real.log (n : ℝ) * (1 - (∑ i ∈ range m, 1 / (Syl i : ℝ)))
            + (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) + 1 / (2 * (n : ℝ)) + Slog m := by ring
    have hS1' : 1 - (∑ i ∈ range m, 1 / (Syl i : ℝ)) = 1 / (((Syl m - 1 : ℕ) : ℝ)) := by
      simpa using hS1
    have hDen0 : (((Syl m - 1 : ℕ) : ℝ)) ≠ 0 := by
      have h2 : 2 ≤ Syl m := Syl_two_le m
      have hp : 0 < Syl m - 1 := by omega
      exact_mod_cast (ne_of_gt hp)
    have hE : Real.log (n : ℝ) * (1 / (((Syl m - 1 : ℕ) : ℝ))) = Real.log (n : ℝ) / (((Syl m - 1 : ℕ) : ℝ)) := by
      rw [one_div, div_eq_mul_inv]
    have hA : (Real.log ((n + 1 : ℕ) : ℝ) + 1 / (2 * (n : ℝ)))
          - (Real.log (n : ℝ) * (∑ i ∈ range m, 1 / (Syl i : ℝ))
            - (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) - Slog m)
        ≤ Slog m + Real.log (n : ℝ) / (((Syl m - 1 : ℕ) : ℝ)) + (2 * (m : ℝ) + 3 / 2) / (n : ℝ) := by
      calc
        (Real.log ((n + 1 : ℕ) : ℝ) + 1 / (2 * (n : ℝ)))
            - (Real.log (n : ℝ) * (∑ i ∈ range m, 1 / (Syl i : ℝ))
              - (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) - Slog m)
            = (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))
                + Real.log (n : ℝ) * (1 - (∑ i ∈ range m, 1 / (Syl i : ℝ)))
                + (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) + 1 / (2 * (n : ℝ)) + Slog m := hring
        _ = (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))
                + Real.log (n : ℝ) * (1 / (((Syl m - 1 : ℕ) : ℝ)))
                + (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) + 1 / (2 * (n : ℝ)) + Slog m := by
                rw [hS1']
        _ ≤ 1 / (n : ℝ) + Real.log (n : ℝ) / (((Syl m - 1 : ℕ) : ℝ))
                + (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) + 1 / (2 * (n : ℝ)) + Slog m := by
                linarith [hLogLe, hE]
        _ ≤ Slog m + Real.log (n : ℝ) / (((Syl m - 1 : ℕ) : ℝ))
                + (2 * (m : ℝ) + 3 / 2) / (n : ℝ) := by
                have hS2' : (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) ≤ (2 * (m : ℝ)) / (n : ℝ) := hS2
                have heq : 1 / (n : ℝ) + (2 * (m : ℝ)) / (n : ℝ) + 1 / (2 * (n : ℝ))
                    = (2 * (m : ℝ) + 3 / 2) / (n : ℝ) := by
                  field_simp [hnR] <;> ring
                linarith [hLogLe, hS2', heq]
    have hTlower : (Real.log (n : ℝ) * (∑ i ∈ range m, 1 / (Syl i : ℝ))
            - (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) - Slog m)
        ≤ (∑ i ∈ range m, (1 / (Syl i : ℝ)) * Real.log (xquot n i)) := hTL
    have h2' : Ulog (n + 1) - Ulog n ≤
        (Real.log ((n + 1 : ℕ) : ℝ) + 1 / (2 * (n : ℝ)))
          - (Real.log (n : ℝ) * (∑ i ∈ range m, 1 / (Syl i : ℝ))
            - (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) - Slog m) := by
      linarith [h2, hTlower]
    linarith [h2', hA]
  dsimp [m] at h3
  simpa using h3


/-! ### Sylvester growth facts -/

/-- 6 a_n ≤ a_{n+1} for n ≥ 2 -/
theorem Syl_six_le_succ (n : ℕ) (hn : 2 ≤ n) : 6 * Syl n ≤ Syl (n + 1) := by
  have h7 : 7 ≤ Syl n := by
    have h2 : Syl 2 = 7 := by norm_num [Syl]
    have hmono : Syl 2 ≤ Syl n := Syl_strictMono.monotone (by omega)
    rw [h2] at hmono
    exact hmono
  have hsub : 6 ≤ Syl n - 1 := by omega
  have hprod : Syl n * 6 ≤ Syl n * (Syl n - 1) := Nat.mul_le_mul_left (Syl n) hsub
  have hle : 6 * Syl n ≤ Syl n * (Syl n - 1) := by simpa [mul_comm] using hprod
  have hdef : Syl (n + 1) = Syl n * (Syl n - 1) + 1 := rfl
  rw [hdef]
  omega

/-- a_{n+1} ≤ a_n² -/
theorem Syl_succ_le_sq (n : ℕ) : Syl (n + 1) ≤ Syl n * Syl n := by
  have hdef : Syl (n + 1) = Syl n * (Syl n - 1) + 1 := rfl
  rw [hdef]
  have h1 : 1 ≤ Syl n := Syl_one_le n
  have hsub : Syl n - 1 + 1 = Syl n := Nat.sub_add_cancel h1
  calc
    Syl n * (Syl n - 1) + 1 ≤ Syl n * (Syl n - 1) + Syl n := by omega
    _ = Syl n * ((Syl n - 1) + 1) := by ring
    _ = Syl n * Syl n := by rw [hsub]

/-- a_m ≥ a_5 · 6^{m−5} for m ≥ 5 -/
theorem Syl_ge_a5 (m : ℕ) (hm : 5 ≤ m) : Syl 5 * 6 ^ (m - 5) ≤ Syl m := by
  have hmain : ∀ d : ℕ, Syl 5 * 6 ^ d ≤ Syl (5 + d) := by
    intro d
    induction d with
    | zero => norm_num [Syl]
    | succ d ih =>
        have h6 : 6 * Syl (5 + d) ≤ Syl (5 + d + 1) := Syl_six_le_succ (5 + d) (by omega)
        calc
          Syl 5 * 6 ^ (d + 1) = (Syl 5 * 6 ^ d) * 6 := by rw [pow_succ]; ring
          _ ≤ Syl (5 + d) * 6 := Nat.mul_le_mul_right 6 ih
          _ = 6 * Syl (5 + d) := by rw [mul_comm]
          _ ≤ Syl (5 + d + 1) := h6
  have hmd : m = 5 + (m - 5) := (Nat.add_sub_of_le hm).symm
  rw [hmd]
  rw [show (5 + (m - 5)) - 5 = m - 5 by omega]
  exact hmain (m - 5)

/-- log a_m ≤ 2^{m−5} · log a_5 for m ≥ 5 -/
theorem log_Syl_double (m : ℕ) (hm : 5 ≤ m) :
    Real.log (Syl m : ℝ) ≤ (2 : ℝ) ^ (m - 5) * Real.log (Syl 5 : ℝ) := by
  have hpos : ∀ k, 0 < (Syl k : ℝ) := fun k => by exact_mod_cast (Syl_pos k)
  have hmain : ∀ d : ℕ, Real.log (Syl (5 + d) : ℝ) ≤ (2 : ℝ) ^ d * Real.log (Syl 5 : ℝ) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
        have hsq : Syl (5 + d + 1) ≤ Syl (5 + d) * Syl (5 + d) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Syl_succ_le_sq (5 + d)
        have hmul : Real.log ((Syl (5 + d) : ℝ) * (Syl (5 + d) : ℝ)) = 2 * Real.log (Syl (5 + d) : ℝ) := by
          rw [Real.log_mul (ne_of_gt (hpos (5+d))) (ne_of_gt (hpos (5+d)))]
          ring
        have hmm : 0 < (Syl (5 + d + 1) : ℝ) := hpos (5 + d + 1)
        have harg : (Syl (5 + d + 1) : ℝ) ≤ (Syl (5 + d) : ℝ) * (Syl (5 + d) : ℝ) := by
          exact_mod_cast hsq
        have hl := Real.log_le_log hmm harg
        rw [hmul] at hl
        have h2 : 2 * Real.log (Syl (5 + d) : ℝ) ≤ 2 * ((2 : ℝ) ^ d * Real.log (Syl 5 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left ih (by norm_num)
        calc
          Real.log (Syl (5 + d + 1) : ℝ) ≤ 2 * Real.log (Syl (5 + d) : ℝ) := hl
          _ ≤ 2 * ((2 : ℝ) ^ d * Real.log (Syl 5 : ℝ)) := h2
          _ = (2 : ℝ) ^ (d + 1) * Real.log (Syl 5 : ℝ) := by rw [pow_succ]; ring
  have hmd : m = 5 + (m - 5) := (Nat.add_sub_of_le hm).symm
  rw [hmd]
  rw [show (5 + (m - 5)) - 5 = m - 5 by omega]
  exact hmain (m - 5)


/-! ### explicit logarithm interval bounds -/

/-- log((1+x)/(1−x)) ≥ 2·Σ_{i<n} x^{2i+1}/(2i+1) for 0 ≤ x < 1 -/
theorem log_ratio_lower (x : ℝ) (n : ℕ) (h0 : 0 ≤ x) (h1 : x < 1) :
    2 * (∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1)) ≤ Real.log ((1 + x) / (1 - x)) := by
  have hlow := Real.sum_range_le_log_div (x := x) h0 h1 n
  nlinarith

/-- log((1+x)/(1−x)) ≤ 2·Σ_{i<n} x^{2i+1}/(2i+1) + 2·x^{2n+1}/(1−x²) for 0 ≤ x < 1 -/
theorem log_ratio_upper (x : ℝ) (n : ℕ) (h0 : 0 ≤ x) (h1 : x < 1) :
    Real.log ((1 + x) / (1 - x)) ≤
      2 * (∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1)) + 2 * x ^ (2 * n + 1) / (1 - x ^ 2) := by
  have hup := Real.log_div_le_sum_range_add (x := x) h0 h1 n
  have hm := mul_le_mul_of_nonneg_left hup (by norm_num : 0 ≤ (2:ℝ))
  have hm0 : (2 : ℝ) * ((1 : ℝ) / 2 * Real.log ((1 + x) / (1 - x))) = Real.log ((1 + x) / (1 - x)) := by ring
  have hm1 : (2 : ℝ) * ((∑ i ∈ range n, x ^ (2 * i + 1) / (2 * ↑i + 1)) + x ^ (2 * n + 1) / (1 - x ^ 2))
      = 2 * (∑ i ∈ range n, x ^ (2 * i + 1) / (2 * ↑i + 1)) + 2 * x ^ (2 * n + 1) / (1 - x ^ 2) := by ring
  rw [hm0, hm1] at hm
  exact hm

/-- wrapper: log 2 ≤ 69316/100000 -/
theorem log2_le_num : Real.log 2 ≤ 69316 / 100000 := by
  have h := Real.log_two_lt_d9
  norm_num at h ⊢
  linarith

/-- wrapper: 69314/100000 ≤ log 2 -/
theorem log2_ge_num : 69314 / 100000 ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

/-- wrapper: log 3 ≤ 109863/100000 -/
theorem log3_le_num : Real.log 3 ≤ 109863 / 100000 := by
  have h := Real.log_three_lt_d9
  norm_num at h ⊢
  linarith

/-- wrapper: 109860/100000 ≤ log 3 -/
theorem log3_ge_num : 109860 / 100000 ≤ Real.log 3 := by
  have h := Real.log_three_gt_d9
  norm_num at h ⊢
  linarith

/-- wrapper: log 2 ≤ 1 -/
theorem log2_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_two_lt_d9
  norm_num at h ⊢
  linarith


/-- log q = k·log2 + log(q/2^k) -/
theorem log_nat_decomp (q k : ℕ) (hq : 0 < q) :
    Real.log ((q : ℕ) : ℝ) = (k : ℝ) * Real.log 2 + Real.log (((q : ℕ) : ℝ) / ((2 : ℝ) ^ k)) := by
  have hq0 : ((q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hc : ((q : ℕ) : ℝ) = (2 : ℝ) ^ k * (((q : ℕ) : ℝ) / ((2 : ℝ) ^ k)) := by
    field_simp [h2k]
  have hlog2 : Real.log ((2 : ℝ) ^ k) = (k : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  calc
    Real.log ((q : ℕ) : ℝ) = Real.log (((2 : ℝ) ^ k) * (((q : ℕ) : ℝ) / ((2 : ℝ) ^ k))) := by rw [← hc]
    _ = Real.log ((2 : ℝ) ^ k) + Real.log (((q : ℕ) : ℝ) / ((2 : ℝ) ^ k)) :=
        Real.log_mul h2k (by positivity : (((q : ℕ) : ℝ) / ((2 : ℝ) ^ k)) ≠ 0)
    _ = (k : ℝ) * Real.log 2 + Real.log (((q : ℕ) : ℝ) / ((2 : ℝ) ^ k)) := by rw [hlog2]

/-- log 43 ≤ 3763/1000 -/
theorem log43_upper : Real.log ((43 : ℕ) : ℝ) ≤ 3763 / 1000 := by
  have hx0 : (0 : ℝ) ≤ (11 : ℝ) / 75 := by norm_num
  have hx1 : (11 : ℝ) / 75 < (1 : ℝ) := by norm_num
  have hup := log_ratio_upper ((11 : ℝ) / 75) 3 hx0 hx1
  have hident : (1 + (11 : ℝ) / 75) / (1 - (11 : ℝ) / 75) = (43 : ℝ) / ((2 : ℝ) ^ 5) := by norm_num
  rw [hident] at hup
  have hdecomp := log_nat_decomp 43 5 (by norm_num)
  rw [hdecomp]
  have hk : (5 : ℝ) * Real.log 2 ≤ (5 : ℝ) * (69316 / 100000) := mul_le_mul_of_nonneg_left log2_le_num (by norm_num)
  have hsub : 2 * (∑ i ∈ range 3, ((11 : ℝ) / 75) ^ (2 * i + 1) / (2 * ↑i + 1)) + 2 * ((11 : ℝ) / 75) ^ (2 * 3 + 1) / (1 - ((11 : ℝ) / 75) ^ 2) ≤ 2960 / 10000 := by
    norm_num [Finset.sum_range_succ]
  have hmain : (5 : ℝ) * Real.log 2 + Real.log ((43 : ℝ) / ((2 : ℝ) ^ 5)) ≤ 3763 / 1000 := by
    linarith
  exact hmain

/-- log 1249 ≥ 7126/1000 -/
theorem log1249_lower : 7126 / 1000 ≤ Real.log ((1249 : ℕ) : ℝ) := by
  have hx0 : (0 : ℝ) ≤ (225 : ℝ) / 2273 := by norm_num
  have hx1 : (225 : ℝ) / 2273 < (1 : ℝ) := by norm_num
  have hlo := log_ratio_lower ((225 : ℝ) / 2273) 3 hx0 hx1
  have hident : (1 + (225 : ℝ) / 2273) / (1 - (225 : ℝ) / 2273) = (1249 : ℝ) / ((2 : ℝ) ^ 10) := by norm_num
  rw [hident] at hlo
  have hdecomp := log_nat_decomp 1249 10 (by norm_num)
  rw [hdecomp]
  have hk : (10 : ℝ) * (69314 / 100000) ≤ (10 : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left log2_ge_num (by norm_num)
  have hsum : 7126 / 1000 ≤ (10 : ℝ) * (69314 / 100000) + 2 * (∑ i ∈ range 3, ((225 : ℝ) / 2273) ^ (2 * i + 1) / (2 * ↑i + 1)) := by
    norm_num [Finset.sum_range_succ]
  linarith

/-- log 2497 ≥ 7818/1000 -/
theorem log2497_lower : 7818 / 1000 ≤ Real.log ((2497 : ℕ) : ℝ) := by
  have hx0 : (0 : ℝ) ≤ (449 : ℝ) / 4545 := by norm_num
  have hx1 : (449 : ℝ) / 4545 < (1 : ℝ) := by norm_num
  have hlo := log_ratio_lower ((449 : ℝ) / 4545) 3 hx0 hx1
  have hident : (1 + (449 : ℝ) / 4545) / (1 - (449 : ℝ) / 4545) = (2497 : ℝ) / ((2 : ℝ) ^ 11) := by norm_num
  rw [hident] at hlo
  have hdecomp := log_nat_decomp 2497 11 (by norm_num)
  rw [hdecomp]
  have hk : (11 : ℝ) * (69314 / 100000) ≤ (11 : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left log2_ge_num (by norm_num)
  have hsum : 7818 / 1000 ≤ (11 : ℝ) * (69314 / 100000) + 2 * (∑ i ∈ range 3, ((449 : ℝ) / 4545) ^ (2 * i + 1) / (2 * ↑i + 1)) := by
    norm_num [Finset.sum_range_succ]
  linarith

/-- log 2493 ≥ 7816/1000 -/
theorem log2493_lower : 7816 / 1000 ≤ Real.log ((2493 : ℕ) : ℝ) := by
  have hx0 : (0 : ℝ) ≤ (445 : ℝ) / 4541 := by norm_num
  have hx1 : (445 : ℝ) / 4541 < (1 : ℝ) := by norm_num
  have hlo := log_ratio_lower ((445 : ℝ) / 4541) 3 hx0 hx1
  have hident : (1 + (445 : ℝ) / 4541) / (1 - (445 : ℝ) / 4541) = (2493 : ℝ) / ((2 : ℝ) ^ 11) := by norm_num
  rw [hident] at hlo
  have hdecomp := log_nat_decomp 2493 11 (by norm_num)
  rw [hdecomp]
  have hk : (11 : ℝ) * (69314 / 100000) ≤ (11 : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left log2_ge_num (by norm_num)
  have hsum : 7816 / 1000 ≤ (11 : ℝ) * (69314 / 100000) + 2 * (∑ i ∈ range 3, ((445 : ℝ) / 4541) ^ (2 * i + 1) / (2 * ↑i + 1)) := by
    norm_num [Finset.sum_range_succ]
  linarith

/-- log 2457 ≥ 7804/1000 -/
theorem log2457_lower : 7804 / 1000 ≤ Real.log ((2457 : ℕ) : ℝ) := by
  have hx0 : (0 : ℝ) ≤ (409 : ℝ) / 4505 := by norm_num
  have hx1 : (409 : ℝ) / 4505 < (1 : ℝ) := by norm_num
  have hlo := log_ratio_lower ((409 : ℝ) / 4505) 3 hx0 hx1
  have hident : (1 + (409 : ℝ) / 4505) / (1 - (409 : ℝ) / 4505) = (2457 : ℝ) / ((2 : ℝ) ^ 11) := by norm_num
  rw [hident] at hlo
  have hdecomp := log_nat_decomp 2457 11 (by norm_num)
  rw [hdecomp]
  have hk : (11 : ℝ) * (69314 / 100000) ≤ (11 : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left log2_ge_num (by norm_num)
  have hsum : 7804 / 1000 ≤ (11 : ℝ) * (69314 / 100000) + 2 * (∑ i ∈ range 3, ((409 : ℝ) / 4505) ^ (2 * i + 1) / (2 * ↑i + 1)) := by
    norm_num [Finset.sum_range_succ]
  linarith

/-- log 7 ≤ 1947/1000 -/
theorem log7_upper : Real.log ((7 : ℕ) : ℝ) ≤ 1947 / 1000 := by
  have hx0 : (0 : ℝ) ≤ (3 : ℝ) / 11 := by norm_num
  have hx1 : (3 : ℝ) / 11 < (1 : ℝ) := by norm_num
  have hup := log_ratio_upper ((3 : ℝ) / 11) 3 hx0 hx1
  have hident : (1 + (3 : ℝ) / 11) / (1 - (3 : ℝ) / 11) = (7 : ℝ) / ((2 : ℝ) ^ 2) := by norm_num
  rw [hident] at hup
  have hdecomp := log_nat_decomp 7 2 (by norm_num)
  rw [hdecomp]
  have hk : (2 : ℝ) * Real.log 2 ≤ (2 : ℝ) * (69316 / 100000) := mul_le_mul_of_nonneg_left log2_le_num (by norm_num)
  have hsub : 2 * (∑ i ∈ range 3, ((3 : ℝ) / 11) ^ (2 * i + 1) / (2 * ↑i + 1)) + 2 * ((3 : ℝ) / 11) ^ 7 / (1 - ((3 : ℝ) / 11) ^ 2) ≤ 56 / 100 := by
    norm_num [Finset.sum_range_succ]
  have hmain : (2 : ℝ) * Real.log 2 + Real.log ((7 : ℝ) / ((2 : ℝ) ^ 2)) ≤ 1947 / 1000 := by
    linarith
  exact hmain


/-! ### Slog bounds and case split for the increment -/

/-- Slog 4 = ln2/2 + ln3/3 + ln7/7 + ln43/43 -/
theorem Slog4_eval : Slog 4 =
    Real.log 2 / 2 + Real.log 3 / 3 + Real.log 7 / 7 + Real.log 43 / 43 := by
  norm_num [Slog, Syl, Finset.sum_range_succ]

/-- Slog 4 ≤ 5393/5000 -/
theorem Slog4_le : Slog 4 ≤ 5393 / 5000 := by
  rw [Slog4_eval]
  have h1 : Real.log 2 / 2 ≤ (69316 / 100000) / 2 := by
    exact div_le_div_of_nonneg_right log2_le_num (by norm_num)
  have h2 : Real.log 3 / 3 ≤ (109863 / 100000) / 3 := by
    exact div_le_div_of_nonneg_right log3_le_num (by norm_num)
  have h3 : Real.log 7 / 7 ≤ (1947 / 1000) / 7 := by
    have hl : Real.log (7 : ℝ) ≤ 1947 / 1000 := by simpa using log7_upper
    exact div_le_div_of_nonneg_right hl (by norm_num)
  have h4 : Real.log 43 / 43 ≤ (3763 / 1000) / 43 := by
    have hl : Real.log (43 : ℝ) ≤ 3763 / 1000 := by simpa using log43_upper
    exact div_le_div_of_nonneg_right hl (by norm_num)
  norm_num at h1 h2 h3 h4 ⊢
  linarith

/-- log q ≤ k·log 2 when q < 2^k -/
theorem log_nat_le_mul_log_two {q k : ℕ} (hq : 0 < q) (h : q < 2 ^ k) :
    Real.log ((q : ℕ) : ℝ) ≤ (k : ℝ) * Real.log 2 := by
  have hpos : 0 < ((q : ℕ) : ℝ) := by exact_mod_cast hq
  have hle : ((q : ℕ) : ℝ) ≤ (((2 ^ k) : ℕ) : ℝ) := by exact_mod_cast (Nat.le_of_lt h)
  have hl : Real.log ((q : ℕ) : ℝ) ≤ Real.log (((2 ^ k) : ℕ) : ℝ) := Real.log_le_log hpos hle
  have hlog : Real.log (((2 ^ k) : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
    have hc : (((2 ^ k) : ℕ) : ℝ) = (2 : ℝ) ^ k := by
      rw [Nat.cast_pow]
      norm_num
    rw [hc, Real.log_pow]
  rwa [hlog] at hl

/-- log 1807 ≤ 11·log 2 -/
theorem log1807_le : Real.log ((1807 : ℕ) : ℝ) ≤ 11 * Real.log 2 := by
  apply log_nat_le_mul_log_two (by norm_num : 0 < 1807)
  norm_num

/-- log a_5 ≤ 16 -/
theorem log_a5_le : Real.log ((Syl 5 : ℕ) : ℝ) ≤ 16 := by
  have hlt : Syl 5 < 2 ^ 22 := by norm_num [Syl]
  have hb0 := log_nat_le_mul_log_two (Syl_pos 5) hlt
  have hb : Real.log ((Syl 5 : ℕ) : ℝ) ≤ 22 * Real.log 2 := by
    simpa using hb0
  have h22 : 22 * Real.log 2 ≤ 22 * (69316 / 100000) :=
    mul_le_mul_of_nonneg_left log2_le_num (by norm_num)
  have hnum : 22 * (69316 / 100000) ≤ 16 := by norm_num
  linarith

/-- Slog 5 = Slog 4 + ln1807/1807 -/
theorem Slog5_eval : Slog 5 = Slog 4 + Real.log 1807 / 1807 := by
  norm_num [Slog, Syl, Finset.sum_range_succ]

/-- Slog 5 ≤ 5393/5000 + 11·ln2/1807 -/
theorem Slog5_le : Slog 5 ≤ 5393 / 5000 + 11 * Real.log 2 / 1807 := by
  rw [Slog5_eval]
  have h4 : Slog 4 ≤ 5393 / 5000 := Slog4_le
  have hlog : Real.log 1807 ≤ 11 * Real.log 2 := by
    simpa using log1807_le
  have hdiv : Real.log 1807 / 1807 ≤ (11 * Real.log 2) / 1807 :=
    div_le_div_of_nonneg_right hlog (by norm_num)
  linarith

/-- geometric half sum bound -/
theorem geom_half_sum_le (N : ℕ) : (∑ i ∈ range N, ((1 : ℝ) / 2) ^ i) ≤ 2 := by
  have hmain : (∑ i ∈ range N, ((1 : ℝ) / 2) ^ i) ≤ 2 * (1 - ((1 : ℝ) / 2) ^ N) := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [sum_range_succ]
        calc
          (∑ i ∈ range N, ((1 : ℝ) / 2) ^ i) + ((1 : ℝ) / 2) ^ N ≤ 2 * (1 - ((1 : ℝ) / 2) ^ N) + ((1 : ℝ) / 2) ^ N := by
            nlinarith [ih]
          _ = 2 * (1 - ((1 : ℝ) / 2) ^ (N + 1)) := by
            let r : ℝ := (1 : ℝ) / 2
            change 2 * (1 - r ^ N) + r ^ N = 2 * (1 - r ^ (N + 1))
            have hr : 2 * r = 1 := by dsimp [r]; norm_num
            calc
              2 * (1 - r ^ N) + r ^ N = 2 - 2 * r ^ N + r ^ N := by ring
              _ = 2 - r ^ N := by ring
              _ = 2 - 2 * (r ^ N * r) := by
                have hx : 2 * (r ^ N * r) = r ^ N * (2 * r) := by ring
                rw [hx, hr]
                ring
              _ = 2 * (1 - r ^ (N + 1)) := by rw [pow_succ]; ring
  have hpos : 0 ≤ ((1 : ℝ) / 2) ^ N := by positivity
  calc
    (∑ i ∈ range N, ((1 : ℝ) / 2) ^ i) ≤ 2 * (1 - ((1 : ℝ) / 2) ^ N) := hmain
    _ ≤ 2 := by nlinarith


/-- Slog(a+1) = Slog a + ln a_a/a_a -/
theorem Slog_succ (a : ℕ) : Slog (a + 1) = Slog a + Real.log ((Syl a : ℕ) : ℝ) / (Syl a : ℝ) := by
  dsimp [Slog]
  rw [sum_range_succ]

/-- Slog (5+d) − Slog 5 = Σ_{j<d} ln a_{5+j}/a_{5+j} -/
theorem Slog_range_diff (d : ℕ) :
    Slog (5 + d) - Slog 5 = ∑ j ∈ range d, Real.log ((Syl (5 + j) : ℕ) : ℝ) / (Syl (5 + j) : ℝ) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [show 5 + (d + 1) = 5 + d + 1 by omega]
      have hsucc : Slog (5 + d + 1) = Slog (5 + d) + Real.log ((Syl (5 + d) : ℕ) : ℝ) / (Syl (5 + d) : ℝ) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Slog_succ (5 + d)
      rw [hsucc, sum_range_succ]
      have hring : (Slog (5 + d) + Real.log ((Syl (5 + d) : ℕ) : ℝ) / (Syl (5 + d) : ℝ)) - Slog 5
          = (Slog (5 + d) - Slog 5) + Real.log ((Syl (5 + d) : ℕ) : ℝ) / (Syl (5 + d) : ℝ) := by ring
      rw [hring, ih]

/-- term bound for the tail: ln a_{5+j}/a_{5+j} ≤ (1/2)^j · ln a_5 / a_5 (coarse) -/
theorem tail_term_bound_coarse (j : ℕ) :
    Real.log ((Syl (5 + j) : ℕ) : ℝ) / (Syl (5 + j) : ℝ) ≤
      ((1 : ℝ) / 2) ^ j * (Real.log ((Syl 5 : ℕ) : ℝ) / (Syl 5 : ℝ)) := by
  have hlg0 := log_Syl_double (5 + j) (by omega : 5 ≤ 5 + j)
  have hbnd0 := Syl_ge_a5 (5 + j) (by omega : 5 ≤ 5 + j)
  have hnum : Real.log ((Syl (5 + j) : ℕ) : ℝ) ≤ (2 : ℝ) ^ j * Real.log ((Syl 5 : ℕ) : ℝ) := by
    simpa [Nat.add_sub_cancel] using hlg0
  have hden : (Syl 5 : ℝ) * (6 : ℝ) ^ j ≤ (Syl (5 + j) : ℝ) := by
    have hbnd : Syl 5 * 6 ^ j ≤ Syl (5 + j) := by
      simpa [Nat.add_sub_cancel] using hbnd0
    have hc' : ((Syl 5 * 6 ^ j : ℕ) : ℝ) ≤ ((Syl (5 + j) : ℕ) : ℝ) := by exact_mod_cast hbnd
    -- rewrite cast of product/pow
    simpa [Nat.cast_mul, Nat.cast_pow] using hc'
  have hpos5 : 0 < (Syl (5 + j) : ℝ) := by exact_mod_cast (Syl_pos (5 + j))
  have hposa : 0 < (Syl 5 : ℝ) := by exact_mod_cast (Syl_pos 5)
  have hlogpos : 0 ≤ Real.log ((Syl 5 : ℕ) : ℝ) := by
    have : 1 ≤ ((Syl 5 : ℕ) : ℝ) := by
      have h1 : 1 ≤ Syl 5 := Syl_one_le 5
      exact_mod_cast h1
    exact Real.log_nonneg this
  -- want: ln a/(a) ≤ (1/2)^j ln a5 / a5:
  have hmain : Real.log ((Syl (5 + j) : ℕ) : ℝ) / (Syl (5 + j) : ℝ) ≤
      ((2 : ℝ) ^ j * Real.log ((Syl 5 : ℕ) : ℝ)) / ((Syl 5 : ℝ) * (6 : ℝ) ^ j) := by
    -- from hnum & hden: log/den ≤ (2^j·l5)/(den) ≤ (2^j l5)/(a5 6^j)
    have hle1 : Real.log ((Syl (5 + j) : ℕ) : ℝ) / (Syl (5 + j) : ℝ)
        ≤ ((2 : ℝ) ^ j * Real.log ((Syl 5 : ℕ) : ℝ)) / (Syl (5 + j) : ℝ) := by
      exact div_le_div_of_nonneg_right hnum hpos5.le
    have hle2 : ((2 : ℝ) ^ j * Real.log ((Syl 5 : ℕ) : ℝ)) / (Syl (5 + j) : ℝ)
        ≤ ((2 : ℝ) ^ j * Real.log ((Syl 5 : ℕ) : ℝ)) / ((Syl 5 : ℝ) * (6 : ℝ) ^ j) := by
      have hx0 : 0 ≤ (2 : ℝ) ^ j * Real.log ((Syl 5 : ℕ) : ℝ) := by positivity
      rw [div_le_div_iff₀ hpos5 (by positivity : 0 < (Syl 5 : ℝ) * (6 : ℝ) ^ j)]
      exact mul_le_mul_of_nonneg_left hden hx0
    exact le_trans hle1 hle2
  have hfinal : ((2 : ℝ) ^ j * Real.log ((Syl 5 : ℕ) : ℝ)) / ((Syl 5 : ℝ) * (6 : ℝ) ^ j)
      ≤ ((1 : ℝ) / 2) ^ j * (Real.log ((Syl 5 : ℕ) : ℝ) / (Syl 5 : ℝ)) := by
    -- (2^j·l)/(a·6^j) = (l/a)·(2/6)^j = (l/a)·(1/3)^j ≤ (l/a)·(1/2)^j
    have hden : (Syl 5 : ℝ) ≠ 0 := by exact_mod_cast (Syl_pos 5).ne'
    have hl5 : Real.log ((Syl 5 : ℕ) : ℝ) / (Syl 5 : ℝ) ≥ 0 := by positivity
    calc
      ((2 : ℝ) ^ j * Real.log ((Syl 5 : ℕ) : ℝ)) / ((Syl 5 : ℝ) * (6 : ℝ) ^ j)
          = (((2 : ℝ) / (6 : ℝ)) ^ j) * (Real.log ((Syl 5 : ℕ) : ℝ) / (Syl 5 : ℝ)) := by
            -- algebra with pow: (2^j l)/(a 6^j) = (2/6)^j·(l/a):
            have hc1 : ((2 : ℝ) ^ j * Real.log ((Syl 5 : ℕ) : ℝ)) / ((Syl 5 : ℝ) * (6 : ℝ) ^ j)
                = (Real.log ((Syl 5 : ℕ) : ℝ) / (Syl 5 : ℝ)) * ((2 : ℝ) ^ j / (6 : ℝ) ^ j) := by
              field_simp [hden] <;> ring
            have hpow : ((2 : ℝ) / (6 : ℝ)) ^ j = (2 : ℝ) ^ j / (6 : ℝ) ^ j := by
              exact div_pow (2 : ℝ) (6 : ℝ) j
            rw [hc1, ← hpow]
            ring
      _ ≤ ((1 : ℝ) / 2) ^ j * (Real.log ((Syl 5 : ℕ) : ℝ) / (Syl 5 : ℝ)) := by
            -- (2/6)^j ≤ (1/2)^j and factor ≥ 0
            have h2_6 : (2 : ℝ) / 6 ≤ (1 : ℝ) / 2 := by norm_num
            have hcmp : ((2 : ℝ) / 6) ^ j ≤ ((1 : ℝ) / 2) ^ j := by
              exact pow_le_pow_left₀ (by norm_num : 0 ≤ (2 : ℝ) / 6) h2_6 j
            exact mul_le_mul_of_nonneg_right hcmp hl5
  exact le_trans hmain hfinal

/-- tail: Slog (5+d) ≤ Slog 5 + 2·ln a_5 / a_5 -/
theorem Slog_tail_le (d : ℕ) :
    Slog (5 + d) ≤ Slog 5 + 2 * (Real.log ((Syl 5 : ℕ) : ℝ) / (Syl 5 : ℝ)) := by
  have hdiff := Slog_range_diff d
  have hterms : (∑ j ∈ range d, Real.log ((Syl (5 + j) : ℕ) : ℝ) / (Syl (5 + j) : ℝ))
      ≤ (Real.log ((Syl 5 : ℕ) : ℝ) / (Syl 5 : ℝ)) * (∑ j ∈ range d, ((1 : ℝ) / 2) ^ j) := by
    -- per-term ≤ c·(1/2)^j: sum: need Σ f_j ≤ c·Σ(1/2)^j: factor out c:
    have hc0 : 0 ≤ Real.log ((Syl 5 : ℕ) : ℝ) / (Syl 5 : ℝ) := by
      have : 1 ≤ ((Syl 5 : ℕ) : ℝ) := by
        have h1 : 1 ≤ Syl 5 := Syl_one_le 5
        exact_mod_cast h1
      have hl : 0 ≤ Real.log ((Syl 5 : ℕ) : ℝ) := Real.log_nonneg this
      have hp : 0 ≤ 1 / (Syl 5 : ℝ) := by positivity
      positivity
    -- rewrite c·Σ(1/2)^j = Σ c·(1/2)^j
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro j hj
    have ht := tail_term_bound_coarse j
    -- f_j ≤ (1/2)^j·c : commute the RHS to c·(1/2)^j
    calc
      Real.log ((Syl (5 + j) : ℕ) : ℝ) / (Syl (5 + j) : ℝ)
          ≤ ((1 : ℝ) / 2) ^ j * (Real.log ((Syl 5 : ℕ) : ℝ) / (Syl 5 : ℝ)) := ht
      _ = (Real.log ((Syl 5 : ℕ) : ℝ) / (Syl 5 : ℝ)) * ((1 : ℝ) / 2) ^ j := by ring
  have hgeom : (∑ j ∈ range d, ((1 : ℝ) / 2) ^ j) ≤ 2 := geom_half_sum_le d
  have hc0 : 0 ≤ Real.log ((Syl 5 : ℕ) : ℝ) / (Syl 5 : ℝ) := by
    have : 1 ≤ ((Syl 5 : ℕ) : ℝ) := by
      have h1 : 1 ≤ Syl 5 := Syl_one_le 5
      exact_mod_cast h1
    have hl : 0 ≤ Real.log ((Syl 5 : ℕ) : ℝ) := Real.log_nonneg this
    have hp : 0 ≤ 1 / (Syl 5 : ℝ) := by positivity
    positivity
  have hfin : (Real.log ((Syl 5 : ℕ) : ℝ) / (Syl 5 : ℝ)) * (∑ j ∈ range d, ((1 : ℝ) / 2) ^ j)
      ≤ 2 * (Real.log ((Syl 5 : ℕ) : ℝ) / (Syl 5 : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_left hgeom hc0
    simpa [mul_comm, mul_left_comm, mul_assoc] using hm
  calc
    Slog (5 + d) = Slog 5 + (∑ j ∈ range d, Real.log ((Syl (5 + j) : ℕ) : ℝ) / (Syl (5 + j) : ℝ)) := by linarith [hdiff]
    _ ≤ Slog 5 + (Real.log ((Syl 5 : ℕ) : ℝ) / (Syl 5 : ℝ)) * (∑ j ∈ range d, ((1 : ℝ) / 2) ^ j) := by
        linarith [hterms]
    _ ≤ Slog 5 + 2 * (Real.log ((Syl 5 : ℕ) : ℝ) / (Syl 5 : ℝ)) := by
        linarith [hfin]


/-- log a_5 / a_5 ≤ 16/3263443 -/
theorem log_a5_div_le : Real.log ((Syl 5 : ℕ) : ℝ) / (Syl 5 : ℝ) ≤ 16 / 3263443 := by
  have h5 : (Syl 5 : ℝ) = 3263443 := by norm_num [Syl]
  rw [h5]
  have ha5 : 0 < (3263443 : ℝ) := by norm_num
  have hnum : Real.log ((Syl 5 : ℕ) : ℝ) ≤ 16 := log_a5_le
  have hd : Real.log ((Syl 5 : ℕ) : ℝ) / (3263443 : ℝ) ≤ 16 / 3263443 :=
    div_le_div_of_nonneg_right hnum (by norm_num)
  exact hd

/-- Slog m ≤ 1083/1000 for m ≥ 5 -/
theorem Slog_ge5_le (m : ℕ) (hm : 5 ≤ m) : Slog m ≤ 1083 / 1000 := by
  have hm' : m = 5 + (m - 5) := (Nat.add_sub_of_le hm).symm
  rw [hm']
  have htail := Slog_tail_le (m - 5)
  have h1 : Slog 5 ≤ 5393 / 5000 + 11 * Real.log 2 / 1807 := Slog5_le
  have h11 : 11 * Real.log 2 ≤ 11 * (69316 / 100000) :=
    mul_le_mul_of_nonneg_left log2_le_num (by norm_num)
  have hA : 5393 / 5000 + 11 * Real.log 2 / 1807 ≤ 5393 / 5000 + 11 * (69316 / 100000) / 1807 := by
    have hd : 11 * Real.log 2 / 1807 ≤ 11 * (69316 / 100000) / 1807 :=
      div_le_div_of_nonneg_right h11 (by norm_num)
    linarith
  have hB : 2 * (Real.log ((Syl 5 : ℕ) : ℝ) / (Syl 5 : ℝ)) ≤ 2 * (16 / 3263443) := by
    have hf := log_a5_div_le
    exact mul_le_mul_of_nonneg_left hf (by norm_num)
  have hnum : 5393 / 5000 + 11 * (69316 / 100000) / 1807 + 2 * (16 / 3263443) ≤ 1083 / 1000 := by
    norm_num
  have h2 : Slog 5 + 2 * (Real.log ((Syl 5 : ℕ) : ℝ) / (Syl 5 : ℝ)) ≤ 1083 / 1000 := by
    linarith
  calc
    Slog (5 + (m - 5)) ≤ Slog 5 + 2 * (Real.log ((Syl 5 : ℕ) : ℝ) / (Syl 5 : ℝ)) := htail
    _ ≤ 1083 / 1000 := h2

/-- when mact n = m, n < 2·Syl m -/
theorem n_lt_two_Syl_of_mact {n m : ℕ} (h : mact n = m) : n < 2 * Syl m := by
  have hspec : n / 2 < Syl m := by
    dsimp [mact] at h
    -- m = idxNat (n/2): idxNat_spec: n/2 < Syl(idxNat(n/2))
    rw [← h]
    exact idxNat_spec (n / 2)
  have h2 : 2 * (n / 2) ≤ n := by omega
  have h2' : 2 * (n / 2) ≤ 2 * (Syl m - 1) := by omega
  -- from n/2 < Syl m: n/2 ≤ Syl m − 1 (integers): so 2·(n/2) ≤ 2(Syl m −1) ≤ n < ?
  have hn : n ≤ 2 * Syl m - 1 := by
    -- n/2 < Syl m implies 2·(n/2) < 2 Syl m; and n < 2(n/2)+2 → n ≤ 2(n/2)+1 ≤ ...
    have h1 : n ≤ 2 * (n / 2) + 1 := by omega
    have hhalf : 2 * (n / 2) + 1 < 2 * Syl m := by
      -- n/2 +1 ≤ Syl m (nats): from n/2 < Syl m: n/2 + 1 ≤ Syl m: so 2(n/2)+2 ≤ 2 Syl m → +1 ≤ 2Sylm -1?
      have : n / 2 + 1 ≤ Syl m := by omega
      have h2x : 2 * (n / 2 + 1) ≤ 2 * Syl m := Nat.mul_le_mul_left 2 this
      omega
    omega
  omega

/-- when mact n = m ≥ 5: ln n ≤ 17·2^{m−5} -/
theorem ln_n_le_17_of_mact {n m : ℕ} (hm : 5 ≤ m) (h : mact n = m) (hn0 : 0 < n) :
    Real.log ((n : ℕ) : ℝ) ≤ 17 * (2 : ℝ) ^ (m - 5) := by
  have hlt := n_lt_two_Syl_of_mact h
  have hlog2 : Real.log 2 ≤ 1 := log2_le_one
  have hlg1 : Real.log ((n : ℕ) : ℝ) ≤ Real.log ((2 * Syl m : ℕ) : ℝ) := by
    have hnpos : 0 < ((n : ℕ) : ℝ) := by exact_mod_cast hn0
    have hle : ((n : ℕ) : ℝ) ≤ ((2 * Syl m : ℕ) : ℝ) := by exact_mod_cast (Nat.le_of_lt hlt)
    exact Real.log_le_log hnpos hle
  have hlg2 : Real.log ((2 * Syl m : ℕ) : ℝ) ≤ 17 * (2 : ℝ) ^ (m - 5) := by
    -- log(2·a_m) ≤ log2 + log a_m ≤ log2 + 2^{m−5} log a5 ≤ 1 + 2^{m−5}·16 ≤ 17·2^{m−5}
    have hsplit : Real.log ((2 * Syl m : ℕ) : ℝ) = Real.log 2 + Real.log ((Syl m : ℕ) : ℝ) := by
      have h2 : ((2 * Syl m : ℕ) : ℝ) = (2 : ℝ) * ((Syl m : ℕ) : ℝ) := by norm_num [Nat.cast_mul]
      rw [h2, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact_mod_cast (Syl_pos m).ne')]
    rw [hsplit]
    have hlogm : Real.log ((Syl m : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m - 5) * Real.log ((Syl 5 : ℕ) : ℝ) := by
      simpa [Nat.add_sub_cancel] using (log_Syl_double m hm)
    have hlog5 : Real.log ((Syl 5 : ℕ) : ℝ) ≤ 16 := log_a5_le
    have hpow : 1 ≤ (2 : ℝ) ^ (m - 5) := by
      have hmono : (1 : ℝ) ^ (m - 5) ≤ (2 : ℝ) ^ (m - 5) :=
        pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) (by norm_num : 1 ≤ (2 : ℝ)) (m - 5)
      simpa using hmono
    calc
      Real.log 2 + Real.log ((Syl m : ℕ) : ℝ) ≤ 1 + (2 : ℝ) ^ (m - 5) * Real.log ((Syl 5 : ℕ) : ℝ) := by linarith
      _ ≤ 1 + (2 : ℝ) ^ (m - 5) * 16 := by
          have hmul : (2 : ℝ) ^ (m - 5) * Real.log ((Syl 5 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m - 5) * 16 := by
            exact mul_le_mul_of_nonneg_left hlog5 (by positivity : 0 ≤ (2 : ℝ) ^ (m - 5))
          linarith
      _ ≤ 17 * (2 : ℝ) ^ (m - 5) := by
          -- 1 + x·16 ≤ 17 x  ⟺ 1 ≤ x
          have hx : 1 ≤ (2 : ℝ) ^ (m - 5) := hpow
          nlinarith
  exact le_trans hlg1 hlg2

/-- TermA for m ≥ 5: ln n/(a_m−1) ≤ 34/3263443 -/
theorem termA_ge5 (n m : ℕ) (hm : 5 ≤ m) (h : mact n = m) (hn0 : 0 < n) :
    Real.log ((n : ℕ) : ℝ) / (((Syl m - 1 : ℕ) : ℝ)) ≤ 34 / 3263443 := by
  have hn := ln_n_le_17_of_mact (n := n) (m := m) hm h hn0
  have ha5 : (Syl 5 : ℝ) = 3263443 := by norm_num [Syl]
  have ha5pos : 0 < (Syl 5 : ℝ) := by exact_mod_cast (Syl_pos 5)
  have hg0 := Syl_ge_a5 m hm
  have hgrowth : (Syl 5 : ℝ) * (6 : ℝ) ^ (m - 5) ≤ (Syl m : ℝ) := by
    have hc : ((Syl 5 * 6 ^ (m - 5) : ℕ) : ℝ) ≤ ((Syl m : ℕ) : ℝ) := by exact_mod_cast hg0
    simpa [Nat.cast_mul, Nat.cast_pow] using hc
  have hden : ((Syl m : ℕ) : ℝ) / 2 ≤ ((Syl m - 1 : ℕ) : ℝ) := by
    have hle1 : 1 ≤ Syl m := Syl_one_le m
    have hc : ((Syl m - 1 : ℕ) : ℝ) = (Syl m : ℝ) - 1 := by
      rw [Nat.cast_sub hle1]
      norm_num
    rw [hc]
    have h2 : 2 ≤ (Syl m : ℝ) := by exact_mod_cast (Syl_two_le m)
    nlinarith
  have hD : ((Syl 5 : ℝ) * (6 : ℝ) ^ (m - 5)) / 2 ≤ ((Syl m - 1 : ℕ) : ℝ) := by
    have h3 : ((Syl 5 : ℝ) * (6 : ℝ) ^ (m - 5)) / 2 ≤ (Syl m : ℝ) / 2 := by
      exact div_le_div_of_nonneg_right hgrowth (by norm_num : 0 ≤ (2 : ℝ))
    exact le_trans h3 hden
  have hDpos : 0 < ((Syl 5 : ℝ) * (6 : ℝ) ^ (m - 5)) / 2 := by
    have hp : 0 < (Syl 5 : ℝ) * (6 : ℝ) ^ (m - 5) := mul_pos ha5pos (by positivity)
    positivity
  have hdn : 0 < ((Syl m - 1 : ℕ) : ℝ) := by
    have hp : 0 < Syl m - 1 := by
      have h2 : 2 ≤ Syl m := Syl_two_le m
      omega
    exact_mod_cast hp
  have hmain : Real.log ((n : ℕ) : ℝ) / (((Syl m - 1 : ℕ) : ℝ)) ≤
      (17 * (2 : ℝ) ^ (m - 5)) / (((Syl 5 : ℝ) * (6 : ℝ) ^ (m - 5)) / 2) := by
    rw [div_le_div_iff₀ hdn hDpos]
    have h1 : Real.log ((n : ℕ) : ℝ) * (((Syl 5 : ℝ) * (6 : ℝ) ^ (m - 5)) / 2)
        ≤ (17 * (2 : ℝ) ^ (m - 5)) * (((Syl m - 1 : ℕ) : ℝ)) := by
      have hc0 : 0 ≤ (((Syl 5 : ℝ) * (6 : ℝ) ^ (m - 5)) / 2) := by positivity
      have h1a := mul_le_mul_of_nonneg_right hn hc0
      have hD' : ((Syl 5 : ℝ) * (6 : ℝ) ^ (m - 5)) / 2 ≤ ((Syl m - 1 : ℕ) : ℝ) := hD
      have h17pos : 0 ≤ 17 * (2 : ℝ) ^ (m - 5) := by positivity
      have h1b : (17 * (2 : ℝ) ^ (m - 5)) * (((Syl 5 : ℝ) * (6 : ℝ) ^ (m - 5)) / 2)
          ≤ (17 * (2 : ℝ) ^ (m - 5)) * (((Syl m - 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hD' h17pos
      exact le_trans h1a h1b
    exact h1
  have hfinal : (17 * (2 : ℝ) ^ (m - 5)) / (((Syl 5 : ℝ) * (6 : ℝ) ^ (m - 5)) / 2) ≤ 34 / 3263443 := by
    rw [← ha5]
    have hd2 : (2 : ℝ) ^ (m - 5) ≤ (6 : ℝ) ^ (m - 5) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) (m - 5)
    have hdenb2 : 0 < ((Syl 5 : ℝ) * (6 : ℝ) ^ (m - 5)) / 2 := hDpos
    rw [div_le_div_iff₀ hdenb2 ha5pos]
    have hrew : 34 * (((Syl 5 : ℝ) * (6 : ℝ) ^ (m - 5)) / 2) = 17 * (Syl 5 : ℝ) * (6 : ℝ) ^ (m - 5) := by
      field_simp [show (2 : ℝ) ≠ 0 by norm_num] <;> try ring
    have h17 : 0 ≤ (17 : ℝ) := by norm_num
    have hc : 17 * (2 : ℝ) ^ (m - 5) ≤ 17 * (6 : ℝ) ^ (m - 5) := mul_le_mul_of_nonneg_left hd2 h17
    have hleft : (17 * (2 : ℝ) ^ (m - 5)) * (Syl 5 : ℝ) ≤ (17 * (6 : ℝ) ^ (m - 5)) * (Syl 5 : ℝ) :=
      mul_le_mul_of_nonneg_right hc ha5pos.le
    have hcomm : (17 * (6 : ℝ) ^ (m - 5)) * (Syl 5 : ℝ) = 17 * (Syl 5 : ℝ) * (6 : ℝ) ^ (m - 5) := by ring
    have hleft' : (17 * (2 : ℝ) ^ (m - 5)) * (Syl 5 : ℝ) ≤ 34 * (((Syl 5 : ℝ) * (6 : ℝ) ^ (m - 5)) / 2) := by
      rw [hrew]
      rwa [hcomm] at hleft
    exact hleft'
  exact le_trans hmain hfinal


/-- TermB for m ≥ 5: (2m+3/2)/(2·a_{m−1}) ≤ 23/7228 -/
theorem termB_ge5 (m : ℕ) (hm : 5 ≤ m) :
    (2 * (m : ℝ) + 3 / 2) / (2 * (Syl (m - 1) : ℝ)) ≤ 23 / 7228 := by
  induction m, hm using Nat.le_induction with
  | base =>
      have h4 : Syl 4 = 1807 := by norm_num [Syl]
      rw [h4]
      norm_num
  | succ m hm ih =>
      have hm4 : m - 1 ≥ 2 := by omega
      have hsix0 := Syl_six_le_succ (m - 1) hm4
      have hsix' : 6 * (Syl (m - 1) : ℝ) ≤ (Syl m : ℝ) := by
        have hm1n : 1 ≤ m := by omega
        have hs : 6 * Syl (m - 1) ≤ Syl m := by
          simpa [Nat.sub_add_cancel hm1n] using hsix0
        exact_mod_cast hs
      have hdec : (2 * ((m + 1 : ℕ) : ℝ) + 3 / 2) / (2 * (Syl m : ℝ))
          ≤ (2 * (m : ℝ) + 3 / 2) / (2 * (Syl (m - 1) : ℝ)) := by
        have hcast : (((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1) := by norm_num
        have h2a : (2 * (m : ℝ) + 3 / 2) ≥ 0 := by positivity
        have hAm : 0 < (Syl m : ℝ) := by exact_mod_cast (Syl_pos m)
        have hAm1 : 0 < (Syl (m - 1) : ℝ) := by exact_mod_cast (Syl_pos (m - 1))
        rw [div_le_div_iff₀ (by positivity : 0 < 2 * (Syl m : ℝ)) (by positivity : 0 < 2 * (Syl (m - 1) : ℝ))]
        have hm1 : (2 * ((m + 1 : ℕ) : ℝ) + 3 / 2) ≤ 6 * (2 * (m : ℝ) + 3 / 2) := by
          rw [hcast]
          nlinarith
        have hx : 12 * (Syl (m - 1) : ℝ) ≤ 2 * (Syl m : ℝ) := by
          have h6 : 6 * (Syl (m - 1) : ℝ) ≤ (Syl m : ℝ) := hsix'
          nlinarith
        calc
          (2 * ((m + 1 : ℕ) : ℝ) + 3 / 2) * (2 * (Syl (m - 1) : ℝ))
              ≤ (6 * (2 * (m : ℝ) + 3 / 2)) * (2 * (Syl (m - 1) : ℝ)) := by
                exact mul_le_mul_of_nonneg_right hm1 (by positivity)
          _ = (2 * (m : ℝ) + 3 / 2) * (12 * (Syl (m - 1) : ℝ)) := by ring
          _ ≤ (2 * (m : ℝ) + 3 / 2) * (2 * (Syl m : ℝ)) := by
                exact mul_le_mul_of_nonneg_left hx h2a
      exact le_trans hdec ih

/-- if mact n = m and m ≥ 1 then 2·Syl(m−1) ≤ n -/
theorem two_Syl_pred_le_of_mact {n m : ℕ} (hm : 1 ≤ m) (h : mact n = m) : 2 * Syl (m - 1) ≤ n := by
  have hlt : Syl (m - 1) ≤ n / 2 := by
    have hmin : m - 1 < mact n := by
      rw [← h]
      omega
    exact idxNat_min (n / 2) (m - 1) hmin
  have h2' : Syl (m - 1) * 2 ≤ n := (Nat.le_div_iff_mul_le (by norm_num : 0 < (2:ℕ))).mp hlt
  simpa [mul_comm] using h2'

/-- symbolic bound after case split ≤ 109/100 -/
theorem Ulog_symbolic_bound_le (n : ℕ) (hn : 2500 ≤ n) :
    Slog (mact n) + Real.log ((n : ℕ) : ℝ) / (((Syl (mact n) - 1 : ℕ) : ℝ))
      + (2 * (mact n : ℝ) + 3 / 2) / (n : ℝ) ≤ 109 / 100 := by
  have hm4 : 4 ≤ mact n := mact_ge_four_of_2500 n hn
  by_cases hm : mact n = 4
  · have hn0 : 0 < n := by omega
    have hlog1 : Real.log ((n : ℕ) : ℝ) ≤ 12 * Real.log 2 := by
      have hnlt : n < 2 ^ 12 := by
        have hn2 : n < 2 * Syl 4 := n_lt_two_Syl_of_mact hm
        have h4 : Syl 4 = 1807 := by norm_num [Syl]
        rw [h4] at hn2
        omega
      exact log_nat_le_mul_log_two hn0 hnlt
    have hS : Slog 4 ≤ 5393 / 5000 := Slog4_le
    have hb1 : Slog 4 + Real.log ((n : ℕ) : ℝ) / 1806 + (19 / 2) / (n : ℝ) ≤ 109 / 100 := by
      have hd12 : 12 * Real.log 2 ≤ 12 * (69316 / 100000) :=
        mul_le_mul_of_nonneg_left log2_le_num (by norm_num)
      have hd12' : (12 * Real.log 2) / 1806 ≤ (12 * (69316 / 100000)) / 1806 :=
        div_le_div_of_nonneg_right hd12 (by norm_num)
      have hlogd : Real.log ((n : ℕ) : ℝ) / 1806 ≤ (12 * Real.log 2) / 1806 :=
        div_le_div_of_nonneg_right hlog1 (by norm_num)
      have hfrac : (19 / 2) / (n : ℝ) ≤ (19 / 2) / 2500 := by
        have hposn : 0 < (n : ℝ) := by exact_mod_cast hn0
        have hn2500 : (2500 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hmul2 : (19 / 2) / (n : ℝ) ≤ (19 / 2) / 2500 := by
          rw [div_le_div_iff₀ hposn (by norm_num : (0 : ℝ) < 2500)]
          nlinarith
        exact hmul2
      have hnum : 5393 / 5000 + (12 * (69316 / 100000)) / 1806 + (19 / 2) / 2500 ≤ 109 / 100 := by
        norm_num
      linarith [hS, hlogd, hd12', hfrac, hnum]
    have hrew : Slog (mact n) + Real.log ((n : ℕ) : ℝ) / (((Syl (mact n) - 1 : ℕ) : ℝ))
          + (2 * (mact n : ℝ) + 3 / 2) / (n : ℝ)
        = Slog 4 + Real.log ((n : ℕ) : ℝ) / 1806 + (19 / 2) / (n : ℝ) := by
      rw [hm]
      norm_num [Syl]
    rw [hrew]
    exact hb1
  · have hm5 : 5 ≤ mact n := by omega
    have hn0 : 0 < n := by omega
    have hg5 : Slog (mact n) ≤ 1083 / 1000 := Slog_ge5_le (mact n) hm5
    have hA : Real.log ((n : ℕ) : ℝ) / (((Syl (mact n) - 1 : ℕ) : ℝ)) ≤ 34 / 3263443 :=
      termA_ge5 n (mact n) hm5 rfl hn0
    have hB0 : (2 * ((mact n : ℕ) : ℝ) + 3 / 2) / (n : ℝ)
        ≤ (2 * ((mact n : ℕ) : ℝ) + 3 / 2) / (2 * (Syl (mact n - 1) : ℝ)) := by
      have hnge : 2 * Syl (mact n - 1) ≤ n := two_Syl_pred_le_of_mact (by omega) rfl
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
      have hden : 0 < 2 * (Syl (mact n - 1) : ℝ) := by
        have : 0 < Syl (mact n - 1) := Syl_pos (mact n - 1)
        positivity
      have hnum : 0 ≤ 2 * ((mact n : ℕ) : ℝ) + 3 / 2 := by positivity
      have hcast : ((2 * Syl (mact n - 1) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnge
      rw [div_le_div_iff₀ hnR hden]
      have hd : (2 * (Syl (mact n - 1) : ℝ)) ≤ (n : ℝ) := by simpa using hcast
      exact mul_le_mul_of_nonneg_left hd hnum
    have hB1 : (2 * ((mact n : ℕ) : ℝ) + 3 / 2) / (2 * (Syl (mact n - 1) : ℝ)) ≤ 23 / 7228 :=
      termB_ge5 (mact n) hm5
    have hB : (2 * ((mact n : ℕ) : ℝ) + 3 / 2) / (n : ℝ) ≤ 23 / 7228 := le_trans hB0 hB1
    have hnum : 1083 / 1000 + 34 / 3263443 + 23 / 7228 ≤ 109 / 100 := by norm_num
    linarith

/-- non-activation increments ≤ 109/100 -/
theorem Ulog_inc_nonact_le (n : ℕ) (hn : 2500 ≤ n) (h : ∀ j : ℕ, n + 1 ≠ 2 * Syl j) :
    Ulog (n + 1) - Ulog n ≤ 109 / 100 := by
  have hb := Ulog_inc_nonact_bound n hn h
  have hle := Ulog_symbolic_bound_le n hn
  linarith

/-- idxNat (a_j − 1) = j for j ≥ 1 -/
theorem idxNat_sub_one (j : ℕ) (hj : 1 ≤ j) : idxNat (Syl j - 1) = j := by
  unfold idxNat
  apply le_antisymm
  · have hspec : Syl j - 1 < Syl j := by
      have : 1 ≤ Syl j := Syl_one_le j
      omega
    exact Nat.find_min' (Syl_unbounded (Syl j - 1)) hspec
  · by_contra hc
    have hx : Nat.find (Syl_unbounded (Syl j - 1)) < j := by omega
    have hle : Syl (Nat.find (Syl_unbounded (Syl j - 1))) ≤ Syl j - 1 := by
      have hall : ∀ k < j, Syl k ≤ Syl j - 1 := by
        intro k hk
        have hmono : Syl k ≤ Syl (j - 1) := Syl_strictMono.monotone (by omega)
        have hstep : Syl (j - 1) ≤ Syl j - 1 := by
          have hlt : Syl (j - 1) < Syl j := Syl_strictMono (by omega : j - 1 < j)
          omega
        omega
      exact hall _ hx
    have hspec2 : Syl j - 1 < Syl (Nat.find (Syl_unbounded (Syl j - 1))) :=
      Nat.find_spec (Syl_unbounded (Syl j - 1))
    omega

/-- mact(n+1) = mact n + 1 at an activation step -/
theorem mact_succ_activation (n j : ℕ) (hj : 1 ≤ j) (h : n + 1 = 2 * Syl j) :
    mact (n + 1) = mact n + 1 := by
  unfold mact
  have hn2 : n / 2 = Syl j - 1 := by
    have hn : n = 2 * Syl j - 1 := by omega
    rw [hn]
    omega
  have hn12 : (n + 1) / 2 = Syl j := by
    rw [h]
    omega
  rw [hn2, hn12]
  have h1 : idxNat (Syl j - 1) = j := idxNat_sub_one j hj
  have h2 : idxNat (Syl j) = j + 1 := by
    have hle : idxNat (Syl j) ≤ j + 1 := by
      unfold idxNat
      exact Nat.find_min' (Syl_unbounded (Syl j)) (Syl_lt_succ j)
    have hge : j + 1 ≤ idxNat (Syl j) := by
      have hjl : Syl j ≤ Syl j := le_rfl
      have hjlt : j < idxNat (Syl j) := idxNat_lt_of_Syl_le hjl
      omega
    omega
  omega

/-- ΔA − Σ_{i<mact n}Δh_i ≤ Slog m + ... (unrestricted version) -/
theorem ALog_minus_sum_bound (n : ℕ) (hn : 2500 ≤ n) :
    (ALog (n + 1) - ALog n) - (∑ i ∈ range (mact n), (hLog (xquot (n + 1) i) - hLog (xquot n i)))
      ≤ Slog (mact n) + Real.log ((n : ℕ) : ℝ) / (((Syl (mact n) - 1 : ℕ) : ℝ))
        + (2 * (mact n : ℝ) + 3 / 2) / (n : ℝ) := by
  let m := mact n
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn0)
  have hma : ∀ i < m, 2 * Syl i ≤ n := by
    intro i hi
    dsimp [m] at hi
    exact active_of_lt_mact n i hi
  have hT : (∑ i ∈ range m, (1 / (Syl i : ℝ)) * Real.log (xquot n i)) ≤
      ∑ i ∈ range m, (hLog (xquot (n + 1) i) - hLog (xquot n i)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    dsimp [m] at hi'
    exact term_inc_lower n i hi'
  have h1 : (ALog (n + 1) - ALog n) - (∑ i ∈ range m, (hLog (xquot (n + 1) i) - hLog (xquot n i)))
      ≤ (ALog (n + 1) - ALog n) - (∑ i ∈ range m, (1 / (Syl i : ℝ)) * Real.log (xquot n i)) := by
    linarith [hT]
  have h2 : (ALog (n + 1) - ALog n) - (∑ i ∈ range m, (hLog (xquot (n + 1) i) - hLog (xquot n i)))
      ≤ (Real.log ((n + 1 : ℕ) : ℝ) + 1 / (2 * (n : ℝ)))
        - (∑ i ∈ range m, (1 / (Syl i : ℝ)) * Real.log (xquot n i)) := by
    have hDA : ALog (n + 1) - ALog n ≤ Real.log ((n + 1 : ℕ) : ℝ) + 1 / (2 * (n : ℝ)) :=
      ALog_inc_le n hn1
    linarith [h1, hDA]
  have hTL := sum_term_lower n m hma
  have hS1 : 1 - (∑ i ∈ range m, 1 / (Syl i : ℝ)) = 1 / (((Syl m - 1 : ℕ) : ℝ)) := by
    dsimp [m]
    exact sum_inv_Syl_sub (mact n)
  have hS2 : (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) ≤ (2 * (m : ℝ)) / (n : ℝ) := by
    dsimp [m]
    exact sum_inv_diff_le n (mact n) hn0 (fun i hi => active_of_lt_mact n i hi)
  have hLogLe : Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := log_succ_sub_le n hn0
  have hring : (Real.log ((n + 1 : ℕ) : ℝ) + 1 / (2 * (n : ℝ)))
        - (Real.log (n : ℝ) * (∑ i ∈ range m, 1 / (Syl i : ℝ))
          - (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) - Slog m)
      = (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))
          + Real.log (n : ℝ) * (1 - (∑ i ∈ range m, 1 / (Syl i : ℝ)))
          + (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) + 1 / (2 * (n : ℝ)) + Slog m := by ring
  have hS1' : 1 - (∑ i ∈ range m, 1 / (Syl i : ℝ)) = 1 / (((Syl m - 1 : ℕ) : ℝ)) := by
    simpa using hS1
  have hDen0 : (((Syl m - 1 : ℕ) : ℝ)) ≠ 0 := by
    have h2n : 2 ≤ Syl m := Syl_two_le m
    have hp : 0 < Syl m - 1 := by omega
    exact_mod_cast (ne_of_gt hp)
  have hE : Real.log (n : ℝ) * (1 / (((Syl m - 1 : ℕ) : ℝ))) = Real.log (n : ℝ) / (((Syl m - 1 : ℕ) : ℝ)) := by
    rw [one_div, div_eq_mul_inv]
  have hA : (Real.log ((n + 1 : ℕ) : ℝ) + 1 / (2 * (n : ℝ)))
        - (Real.log (n : ℝ) * (∑ i ∈ range m, 1 / (Syl i : ℝ))
          - (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) - Slog m)
      ≤ Slog m + Real.log (n : ℝ) / (((Syl m - 1 : ℕ) : ℝ)) + (2 * (m : ℝ) + 3 / 2) / (n : ℝ) := by
    calc
      (Real.log ((n + 1 : ℕ) : ℝ) + 1 / (2 * (n : ℝ)))
          - (Real.log (n : ℝ) * (∑ i ∈ range m, 1 / (Syl i : ℝ))
            - (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) - Slog m)
          = (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))
              + Real.log (n : ℝ) * (1 - (∑ i ∈ range m, 1 / (Syl i : ℝ)))
              + (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) + 1 / (2 * (n : ℝ)) + Slog m := hring
      _ = (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))
              + Real.log (n : ℝ) / (((Syl m - 1 : ℕ) : ℝ))
              + (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) + 1 / (2 * (n : ℝ)) + Slog m := by
              rw [hS1', one_div, ← div_eq_mul_inv]
      _ ≤ 1 / (n : ℝ) + Real.log (n : ℝ) / (((Syl m - 1 : ℕ) : ℝ))
              + (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) + 1 / (2 * (n : ℝ)) + Slog m := by
              linarith [hLogLe]
      _ ≤ Slog m + Real.log (n : ℝ) / (((Syl m - 1 : ℕ) : ℝ)) + (2 * (m : ℝ) + 3 / 2) / (n : ℝ) := by
              have hS2' : (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) ≤ (2 * (m : ℝ)) / (n : ℝ) := hS2
              have heq : 1 / (n : ℝ) + (2 * (m : ℝ)) / (n : ℝ) + 1 / (2 * (n : ℝ))
                  = (2 * (m : ℝ) + 3 / 2) / (n : ℝ) := by
                field_simp [hnR] <;> ring
              linarith [hLogLe, hS2', heq]
  have hTlower : (Real.log (n : ℝ) * (∑ i ∈ range m, 1 / (Syl i : ℝ))
          - (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) - Slog m)
      ≤ (∑ i ∈ range m, (1 / (Syl i : ℝ)) * Real.log (xquot n i)) := hTL
  have h2' : (ALog (n + 1) - ALog n) - (∑ i ∈ range m, (hLog (xquot (n + 1) i) - hLog (xquot n i)))
      ≤ (Real.log ((n + 1 : ℕ) : ℝ) + 1 / (2 * (n : ℝ)))
        - (Real.log (n : ℝ) * (∑ i ∈ range m, 1 / (Syl i : ℝ))
          - (∑ i ∈ range m, 1 / ((n : ℝ) - (Syl i : ℝ))) - Slog m) := by
    linarith [h2, hTlower]
  linarith [h2', hA]


/-- activation increments ≤ 209/100 -/
theorem Ulog_inc_act_le (n j : ℕ) (hn : 2500 ≤ n) (hj : 1 ≤ j) (hact : n + 1 = 2 * Syl j) :
    Ulog (n + 1) - Ulog n ≤ 209 / 100 := by
  have hn0 : 0 < n := by omega
  have hmj : mact n = j := by
    have hn2 : n / 2 = Syl j - 1 := by
      have hn : n = 2 * Syl j - 1 := by omega
      rw [hn]
      omega
    dsimp [mact]
    rw [hn2]
    exact idxNat_sub_one j hj
  have hpart : (ALog (n + 1) - ALog n) - (∑ i ∈ range (mact n), (hLog (xquot (n + 1) i) - hLog (xquot n i))) ≤ 109 / 100 := by
    have hb := ALog_minus_sum_bound n hn
    have hle := Ulog_symbolic_bound_le n hn
    linarith
  have hms := mact_succ_activation n j hj hact
  have hsp : (∑ i ∈ range (mact n + 1), hLog ((((n + 1 : ℕ) : ℝ) / (Syl i : ℝ)) - 1)) =
      (∑ i ∈ range (mact n), hLog ((((n + 1 : ℕ) : ℝ) / (Syl i : ℝ)) - 1)) + hLog ((((n + 1 : ℕ) : ℝ) / (Syl (mact n) : ℝ)) - 1) := by
    exact Finset.sum_range_succ (fun i => hLog ((((n + 1 : ℕ) : ℝ) / (Syl i : ℝ)) - 1)) (mact n)
  have har : (((n + 1 : ℕ) : ℝ) / (Syl (mact n) : ℝ)) - 1 = 1 := by
    rw [hmj]
    have hsyl : (Syl j : ℝ) ≠ 0 := by exact_mod_cast (Syl_pos j).ne'
    have hc1 : (((n + 1 : ℕ) : ℝ) = (2 : ℝ) * (Syl j : ℝ)) := by
      have hnat : (((n + 1 : ℕ) : ℝ) = ((2 * Syl j : ℕ) : ℝ)) := by exact_mod_cast hact
      rw [hnat]
      rw [Nat.cast_mul]
      norm_num
    rw [hc1]
    field_simp [hsyl] <;> try ring
  have hlast : hLog ((((n + 1 : ℕ) : ℝ) / (Syl (mact n) : ℝ)) - 1) = hLog 1 := by
    exact congrArg hLog har
  unfold Ulog
  rw [hms, hsp, hlast]
  let S1 : ℝ := ∑ i ∈ range (mact n), hLog ((((n + 1 : ℕ) : ℝ) / (Syl i : ℝ)) - 1)
  let S0 : ℝ := ∑ i ∈ range (mact n), hLog (((n : ℕ) : ℝ) / (Syl i : ℝ) - 1)
  have halg : ALog (n + 1) - (S1 + hLog 1) - (ALog n - S0) = (ALog (n + 1) - ALog n) - (S1 - S0) - hLog 1 := by
    dsimp [S1, S0]
    ring
  rw [halg]
  have hdiff : S1 - S0 = ∑ i ∈ range (mact n), (hLog (xquot (n + 1) i) - hLog (xquot n i)) := by
    dsimp [S1, S0]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    dsimp [xquot]
  rw [hdiff]
  have hlog1 : -1 ≤ hLog 1 := by
    dsimp [hLog]
    rw [Real.log_one]
    have hx : (2 : ℝ) * Real.pi * 1 = 2 * Real.pi := by ring
    rw [hx]
    have hge1 : 1 ≤ 2 * Real.pi := by
      have h3 : 3 < Real.pi := Real.pi_gt_three
      norm_num
      linarith
    have hlog : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg hge1
    nlinarith
  have hneg : -hLog 1 ≤ 1 := by linarith
  calc
    (ALog (n + 1) - ALog n) - (∑ i ∈ range (mact n), (hLog (xquot (n + 1) i) - hLog (xquot n i))) - hLog 1
        ≤ 109 / 100 - hLog 1 := by linarith [hpart]
    _ ≤ 209 / 100 := by linarith [hneg]


/-! ### slack increments and event machinery -/

/-- events: e_i = 2·Syl(i+4) -/
def ev (i : ℕ) : ℕ := 2 * Syl (i + 4)

theorem ev_succ_gt (i : ℕ) : ev i < ev (i + 1) := by
  have hlt : Syl (i + 4) < Syl (i + 5) := Syl_strictMono (by omega)
  dsimp [ev]
  have hcast : (i + 1) + 4 = i + 5 := by omega
  rw [hcast]
  omega

theorem ev_strictMono : StrictMono ev := by
  intro a b h
  induction h with
  | refl => exact ev_succ_gt a
  | step h ih => exact lt_trans ih (ev_succ_gt _)

theorem ev_ge_2500 (i : ℕ) : 2500 ≤ ev i := by
  have h0 : ev 0 = 3614 := by norm_num [ev, Syl]
  have hle : ev 0 ≤ ev i := by
    have hmono : Syl 4 ≤ Syl (i + 4) := Syl_strictMono.monotone (by omega : 4 ≤ i + 4)
    dsimp [ev]
    exact Nat.mul_le_mul_left 2 hmono
  rw [h0] at hle
  omega

/-- events are unbounded -/
theorem ev_unbounded (m : ℕ) : ∃ i : ℕ, m < ev i := by
  rcases Syl_unbounded m with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  dsimp [ev]
  have h1 : Syl k ≤ Syl (k + 4) := Syl_strictMono.monotone (by omega)
  have hpos : 0 < Syl (k + 4) := Syl_pos (k + 4)
  have h2le : Syl (k + 4) * 1 ≤ Syl (k + 4) * 2 := Nat.mul_le_mul_left (Syl (k + 4)) (by norm_num)
  have hle1 : Syl (k + 4) ≤ 2 * Syl (k + 4) := by simpa [mul_comm] using h2le
  have : m < 2 * Syl (k + 4) := by omega
  omega

theorem activation_j_ge (n j : ℕ) (hn : 2500 ≤ n) (hact : n + 1 = 2 * Syl j) : 4 ≤ j := by
  by_contra hc
  have hj3 : j ≤ 3 := by omega
  have hs : Syl j ≤ Syl 3 := Syl_strictMono.monotone hj3
  have h3 : Syl 3 = 43 := by norm_num [Syl]
  have hb : 2 * Syl j ≤ 86 := by rw [h3] at hs; omega
  have hle : n + 1 ≤ 86 := by rw [hact]; exact hb
  omega

/-- slack gain at non-activation steps ≥ 1/200 -/
theorem slack_step_nonact (n : ℕ) (hn : 2500 ≤ n) (h : ∀ j : ℕ, n + 1 ≠ 2 * Syl j) :
    1 / 200 ≤ slack (n + 1) - slack n := by
  have hinc := Ulog_inc_nonact_le n hn h
  have h3 : (109860 / 100000 : ℝ) ≤ Real.log 3 := log3_ge_num
  dsimp [slack]
  -- slack(n+1) − slack n = log3 − (U(n+1) − U(n))
  have hval : (1 / 200 : ℝ) ≤ Real.log 3 - (Ulog (n + 1) - Ulog n) := by
    have hA : (109860 / 100000 : ℝ) - 109 / 100 ≥ 1 / 200 := by norm_num
    nlinarith [h3, hinc, hA]
  -- algebra: slack(n+1) − slack n = ((n+1)·log3 − U(n+1)) − (n·log3 − U(n)) = log3 − (U(n+1)−U(n)):
  have halg : slack (n + 1) - slack n = Real.log 3 - (Ulog (n + 1) - Ulog n) := by
    dsimp [slack]
    rw [show (((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1) by norm_num]
    ring
  calc
    1 / 200 ≤ Real.log 3 - (Ulog (n + 1) - Ulog n) := hval
    _ = slack (n + 1) - slack n := halg.symm

/-- slack change at activation steps ≥ −1 -/
theorem slack_step_act (n j : ℕ) (hn : 2500 ≤ n) (hj : 1 ≤ j) (hact : n + 1 = 2 * Syl j) :
    -1 ≤ slack (n + 1) - slack n := by
  have hinc := Ulog_inc_act_le n j hn hj hact
  have h3 : (109860 / 100000 : ℝ) ≤ Real.log 3 := log3_ge_num
  have hval : -1 ≤ Real.log 3 - (Ulog (n + 1) - Ulog n) := by
    have hA : (109860 / 100000 : ℝ) - 209 / 100 ≥ -1 := by norm_num
    nlinarith [h3, hinc, hA]
  have halg : slack (n + 1) - slack n = Real.log 3 - (Ulog (n + 1) - Ulog n) := by
    dsimp [slack]
    rw [show (((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1) by norm_num]
    ring
  calc
    -1 ≤ Real.log 3 - (Ulog (n + 1) - Ulog n) := hval
    _ = slack (n + 1) - slack n := halg.symm

/-- activation with n ≥ 2500 has index j ≥ 4, so j + 4 ≥ ... uses ev -/
theorem exists_ev_between {n : ℕ} (hn : 2500 ≤ n) :
    (∀ k : ℕ, n < ev k) ∨ ∃ k : ℕ, ev k ≤ n ∧ n < ev (k + 1) := by
  by_cases h0 : n < ev 0
  · left
    intro k
    have hmono : ev 0 ≤ ev k := by
      induction k with
      | zero => rfl
      | succ k ih => exact le_trans ih (le_of_lt (ev_succ_gt k))
    exact lt_of_lt_of_le h0 hmono
  · right
    let kf := Nat.find (ev_unbounded n)
    have hkf : n < ev kf := by
      dsimp [kf]
      exact Nat.find_spec (ev_unbounded n)
    have hkf_pos : 0 < kf := by
      by_contra hc
      have hz : kf = 0 := by omega
      have : n < ev 0 := by simpa [kf, hz] using hkf
      exact h0 this
    refine ⟨kf - 1, ?_, ?_⟩
    · have hnot : ¬(n < ev (kf - 1)) := by
        have hk := Nat.find_min (ev_unbounded n) (by dsimp [kf]; omega : kf - 1 < kf)
        exact hk
      exact le_of_not_gt hnot
    · have hcast : (kf - 1) + 1 = kf := Nat.sub_add_cancel hkf_pos
      have : n < ev ((kf - 1) + 1) := by simpa [hcast] using hkf
      exact this



/-- monotone slack along a run of non-activation steps -/
theorem slack_nonact_run (a b : ℕ) (ha : 2500 ≤ a) (hab : a ≤ b)
    (h : ∀ n : ℕ, a ≤ n → n < b → ∀ j : ℕ, n + 1 ≠ 2 * Syl j) : slack a ≤ slack b := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hb ih =>
      have hstep := slack_step_nonact b (by omega : 2500 ≤ b) (h b hb (by omega : b < b + 1))
      have hgain : slack b ≤ slack (b + 1) := by linarith [hstep]
      exact le_trans (ih (fun n hn1 hn2 j => h n hn1 (by omega) j)) hgain

/-- quantitative slack gain along a run of non-activation steps -/
theorem slack_nonact_run_gain (a b : ℕ) (ha : 2500 ≤ a) (hab : a ≤ b)
    (h : ∀ n : ℕ, a ≤ n → n < b → ∀ j : ℕ, n + 1 ≠ 2 * Syl j) :
    slack a + ((b - a : ℕ) : ℝ) / 200 ≤ slack b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
      have hb_prev : ∀ n : ℕ, a ≤ n → n < b → ∀ j : ℕ, n + 1 ≠ 2 * Syl j := by
        intro n hn1 hn2 j
        exact h n hn1 (by omega) j
      have ihb : slack a + ((b - a : ℕ) : ℝ) / 200 ≤ slack b := ih hb_prev
      have hstep := slack_step_nonact b (by omega : 2500 ≤ b) (h b hb (by omega : b < b + 1))
      have hcast : (((b + 1 - a : ℕ) : ℝ) = ((b - a : ℕ) : ℝ) + 1) := by
        have hnat : b + 1 - a = (b - a) + 1 := by omega
        rw [hnat]
        norm_num
      have hq : slack a + ((b - a : ℕ) : ℝ) / 200 + 1 / 200 ≤ slack (b + 1) := by linarith [ihb, hstep]
      nlinarith [hq, hcast]

/-- steps with n+1 < ev 0 are non-activation -/
theorem nonact_below_ev0 (n : ℕ) (h2500 : 2500 ≤ n) (hn : n + 1 < ev 0) :
    ∀ j : ℕ, n + 1 ≠ 2 * Syl j := by
  intro j hj
  have hj4 : 4 ≤ j := activation_j_ge n j h2500 hj
  have hev : n + 1 = ev (j - 4) := by
    have hjid : j = (j - 4) + 4 := by omega
    calc
      n + 1 = 2 * Syl j := hj
      _ = 2 * Syl ((j - 4) + 4) := by rw [← hjid]
      _ = ev (j - 4) := by rfl
  have hlt : ev (j - 4) < ev 0 := by
    rw [← hev]
    exact hn
  have hjlt : j - 4 < 0 := by
    exact ev_strictMono.lt_iff_lt.mp hlt
  exfalso
  have hneg : ¬ (j - 4 < 0) := by omega
  exact hneg hjlt

/-- steps inside the gap before the next event are non-activation -/
theorem nonact_between (k n : ℕ) (hn1 : ev k ≤ n) (hn2 : n + 1 < ev (k + 1)) :
    ∀ j : ℕ, n + 1 ≠ 2 * Syl j := by
  intro j hj
  have hge : 2500 ≤ n := le_trans (ev_ge_2500 k) hn1
  have hj4 : 4 ≤ j := activation_j_ge n j hge hj
  have hev : n + 1 = ev (j - 4) := by
    have hjid : j = (j - 4) + 4 := by omega
    calc
      n + 1 = 2 * Syl j := hj
      _ = 2 * Syl ((j - 4) + 4) := by rw [← hjid]
      _ = ev (j - 4) := by rfl
  have hlt : ev (j - 4) < ev (k + 1) := by
    rw [← hev]
    exact hn2
  have hil : j - 4 < k + 1 := by
    exact ev_strictMono.lt_iff_lt.mp hlt
  have hgt : ev k < ev (j - 4) := by
    calc ev k ≤ n := hn1
      _ < n + 1 := by omega
      _ = ev (j - 4) := hev
  have kgt : k < j - 4 := by
    exact ev_strictMono.lt_iff_lt.mp hgt
  exfalso
  omega

/-- event floors: slack(ev 0) ≤ slack(ev k) for all k -/
theorem slack_ev_ge_ev0 (k : ℕ) : slack (ev 0) ≤ slack (ev k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hge0 : 3614 ≤ ev k := by
        have h0 : ev 0 = 3614 := by norm_num [ev, Syl]
        have hmono0 : ev 0 ≤ ev k := ev_strictMono.monotone (by omega)
        rw [h0] at hmono0
        exact hmono0
      have h6 : 6 * ev k ≤ ev (k + 1) := by
        have hs0 := Syl_six_le_succ (k + 4) (by omega : 2 ≤ k + 4)
        have hcast1 : (k + 4) + 1 = k + 5 := by omega
        have hcast2 : (k + 1) + 4 = k + 5 := by omega
        dsimp [ev]
        rw [hcast2]
        calc
          6 * (2 * Syl (k + 4)) = 2 * (6 * Syl (k + 4)) := by ring
          _ ≤ 2 * Syl (k + 5) := Nat.mul_le_mul_left 2 (by simpa [hcast1] using hs0)
      have hnat : 200 ≤ (ev (k + 1) - 1) - ev k := by omega
      have hgap : (200 : ℝ) ≤ (((ev (k + 1) - 1 - ev k : ℕ) : ℝ)) := by
        exact_mod_cast hnat
      have hX : 1 ≤ (((ev (k + 1) - 1 - ev k : ℕ) : ℝ)) / 200 := by
        have hd : 0 < (200 : ℝ) := by norm_num
        exact (le_div_iff₀ hd).mpr (by simpa using hgap)
      have hrun : slack (ev k) + (((ev (k + 1) - 1) - ev k : ℕ) : ℝ) / 200 ≤ slack (ev (k + 1) - 1) := by
        apply slack_nonact_run_gain (ev k) (ev (k + 1) - 1)
        · exact ev_ge_2500 k
        · have hlt : ev k < ev (k + 1) := ev_succ_gt k
          omega
        · intro n hn1 hn2 j
          have hnk : n + 1 < ev (k + 1) := by omega
          exact nonact_between k n (by omega) hnk j
      have hpeq : (ev (k + 1) - 1) + 1 = ev (k + 1) := by omega
      have hbig : 2500 ≤ ev (k + 1) - 1 := by
        have : 2500 + 200 ≤ ev (k + 1) - 1 := by omega
        omega
      have hact2 : (ev (k + 1) - 1) + 1 = 2 * Syl (k + 5) := by
        have h2 : ev (k + 1) = 2 * Syl (k + 5) := by
          dsimp [ev]
        rw [hpeq, h2]
      have hg := slack_step_act (ev (k + 1) - 1) (k + 5) hbig (by omega : 1 ≤ k + 5) hact2
      have hg' : -1 ≤ slack (ev (k + 1)) - slack (ev (k + 1) - 1) := by
        rw [hpeq] at hg
        exact hg
      have hstep : slack (ev (k + 1) - 1) - 1 ≤ slack (ev (k + 1)) := by
        linarith [hg']
      have hnet : slack (ev k) ≤ slack (ev (k + 1)) := by
        linarith [hrun, hstep, hX]
      exact le_trans ih hnet

/-! ### base-point check : slack 2500 ≥ 1 -/

/-- wrapper: log 5 ≤ 160944/100000 -/
theorem log5_le_num : Real.log 5 ≤ 160944 / 100000 := by
  have h := Real.log_five_lt_d9
  norm_num at h ⊢
  linarith

/-- log 2500 = 2 log 2 + 4 log 5 -/
theorem log2500_eq : Real.log (2500 : ℝ) = 2 * Real.log 2 + 4 * Real.log 5 := by
  have h1 : (2500 : ℝ) = (2 : ℝ) ^ 2 * (5 : ℝ) ^ 4 := by norm_num
  rw [h1]
  rw [Real.log_mul (by positivity : (2 : ℝ) ^ 2 ≠ 0) (by positivity : (5 : ℝ) ^ 4 ≠ 0)]
  rw [Real.log_pow, Real.log_pow]
  ring

/-- lower bound for log π via π > 3 -/
theorem log_pi_ge_num : 109860 / 100000 ≤ Real.log Real.pi := by
  have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hlog3 : (109860 / 100000 : ℝ) ≤ Real.log (3 : ℝ) := log3_ge_num
  have hle : Real.log (3 : ℝ) ≤ Real.log Real.pi := Real.log_le_log (by norm_num) (le_of_lt h3)
  linarith

/-- idxNat 1250 = 4 -/
theorem idxNat_1250 : idxNat 1250 = 4 := by
  unfold idxNat
  apply le_antisymm
  · exact Nat.find_min' (Syl_unbounded 1250) (by norm_num [Syl])
  · by_contra h4
    have hx : Nat.find (Syl_unbounded 1250) < 4 := by omega
    have hall : ∀ k < 4, Syl k ≤ 1250 := by
      intro k hk
      have hmono : Syl k ≤ Syl 3 := Syl_strictMono.monotone (by omega)
      have h3 : Syl 3 = 43 := by norm_num [Syl]
      omega
    have hle : Syl (Nat.find (Syl_unbounded 1250)) ≤ 1250 := hall _ hx
    have hspec : 1250 < Syl (Nat.find (Syl_unbounded 1250)) := Nat.find_spec (Syl_unbounded 1250)
    omega

/-- mact 2500 = 4 -/
theorem mact_2500 : mact 2500 = 4 := by
  dsimp [mact]
  exact idxNat_1250

/-- generic lower bound for hLog x in terms of a lower bound of log x -/
theorem hLog_lower_gen (x L : ℝ) (hx1 : 1 ≤ x) (hL : L ≤ Real.log x) :
    (x + 1 / 2) * L - x + 1 / 2 * (69314 / 100000) + 1 / 2 * (109860 / 100000) ≤ hLog x := by
  have hx0 : 0 < x := by linarith
  have hcoef : 0 ≤ x + 1 / 2 := by linarith
  have hmul : (x + 1 / 2) * L ≤ (x + 1 / 2) * Real.log x := mul_le_mul_of_nonneg_left hL hcoef
  have hsplit : hLog x = (x + 1 / 2) * Real.log x - x + 1 / 2 * Real.log 2 + 1 / 2 * Real.log Real.pi := by
    dsimp [hLog]
    have h2p : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : Real.pi ≠ 0)]
    have hpx : Real.log (2 * Real.pi * x) = Real.log (2 * Real.pi) + Real.log x := by
      rw [Real.log_mul (by positivity : (2 : ℝ) * Real.pi ≠ 0) (ne_of_gt hx0)]
    rw [hpx, h2p]
    ring_nf
  rw [hsplit]
  have h2 : (69314 / 100000 : ℝ) ≤ Real.log 2 := log2_ge_num
  have hp : (109860 / 100000 : ℝ) ≤ Real.log Real.pi := log_pi_ge_num
  have hhalf2 : 1 / 2 * (69314 / 100000) ≤ 1 / 2 * Real.log 2 := by
    exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  have hhalfp : 1 / 2 * (109860 / 100000) ≤ 1 / 2 * Real.log Real.pi := by
    exact mul_le_mul_of_nonneg_left hp (by norm_num)
  nlinarith

/-- log(2497/3) ≥ 7818/1000 − 109863/100000 -/
theorem log_2497div3_lower : (7818 / 1000 : ℝ) - 109863 / 100000 ≤ Real.log ((2497 : ℝ) / 3) := by
  have hl : (7818 / 1000 : ℝ) ≤ Real.log (2497 : ℝ) := by
    have hl0 := log2497_lower
    simpa using hl0
  have h3u : Real.log 3 ≤ 109863 / 100000 := log3_le_num
  have hlogd : Real.log ((2497 : ℝ) / 3) = Real.log (2497 : ℝ) - Real.log 3 := by
    rw [Real.log_div (by norm_num : (2497 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
  rw [hlogd]
  linarith

/-- log(2493/7) ≥ 7816/1000 − 1947/1000 -/
theorem log_2493div7_lower : (7816 / 1000 : ℝ) - 1947 / 1000 ≤ Real.log ((2493 : ℝ) / 7) := by
  have hl : (7816 / 1000 : ℝ) ≤ Real.log (2493 : ℝ) := by
    have hl0 := log2493_lower
    simpa using hl0
  have h7u : Real.log 7 ≤ 1947 / 1000 := by
    have hl0 := log7_upper
    simpa using hl0
  have hlogd : Real.log ((2493 : ℝ) / 7) = Real.log (2493 : ℝ) - Real.log 7 := by
    rw [Real.log_div (by norm_num : (2493 : ℝ) ≠ 0) (by norm_num : (7 : ℝ) ≠ 0)]
  rw [hlogd]
  linarith

/-- log(2457/43) ≥ 7804/1000 − 3763/1000 -/
theorem log_2457div43_lower : (7804 / 1000 : ℝ) - 3763 / 1000 ≤ Real.log ((2457 : ℝ) / 43) := by
  have hl : (7804 / 1000 : ℝ) ≤ Real.log (2457 : ℝ) := by
    have hl0 := log2457_lower
    simpa using hl0
  have h43u : Real.log 43 ≤ 3763 / 1000 := by
    have hl0 := log43_upper
    simpa using hl0
  have hlogd : Real.log ((2457 : ℝ) / 43) = Real.log (2457 : ℝ) - Real.log 43 := by
    rw [Real.log_div (by norm_num : (2457 : ℝ) ≠ 0) (by norm_num : (43 : ℝ) ≠ 0)]
  rw [hlogd]
  linarith

/-- the four active hLog terms at n=2500, lower bounded -/
theorem slack2500_terms :
    hLog (xquot 2500 0) + hLog (xquot 2500 1) + hLog (xquot 2500 2) + hLog (xquot 2500 3) ≥
      ((1249 + 1 / 2) * (7126 / 1000) - 1249) +
      ((2497 / 3 + 1 / 2) * ((7818 / 1000) - 109863 / 100000) - 2497 / 3) +
      ((2493 / 7 + 1 / 2) * ((7816 / 1000) - 1947 / 1000) - 2493 / 7) +
      ((2457 / 43 + 1 / 2) * ((7804 / 1000) - 3763 / 1000) - 2457 / 43) +
      2 * ((1 / 2) * (69314 / 100000) + (1 / 2) * (109860 / 100000)) := by
  have h0 : hLog (xquot 2500 0) ≥ (1249 + 1 / 2) * (7126 / 1000) - 1249 + 1 / 2 * (69314 / 100000) + 1 / 2 * (109860 / 100000) := by
    have hlog : (7126 / 1000 : ℝ) ≤ Real.log (1249 : ℝ) := by
      have hl0 := log1249_lower
      simpa using hl0
    have hx : 1 ≤ (1249 : ℝ) := by norm_num
    have hcore := hLog_lower_gen (1249 : ℝ) (7126 / 1000) hx hlog
    have heq : hLog (xquot 2500 0) = hLog (1249 : ℝ) := by
      congr 1
      dsimp [xquot]
      norm_num [Syl]
    simpa [← heq] using hcore
  have h1 : hLog (xquot 2500 1) ≥ (2497 / 3 + 1 / 2) * ((7818 / 1000) - 109863 / 100000) - 2497 / 3 + 1 / 2 * (69314 / 100000) + 1 / 2 * (109860 / 100000) := by
    have hx : 1 ≤ (2497 : ℝ) / 3 := by norm_num
    have hcore := hLog_lower_gen ((2497 : ℝ) / 3) ((7818 / 1000) - 109863 / 100000) hx log_2497div3_lower
    have heq : hLog (xquot 2500 1) = hLog ((2497 : ℝ) / 3) := by
      congr 1
      dsimp [xquot]
      norm_num [Syl]
    simpa [← heq] using hcore
  have h2 : hLog (xquot 2500 2) ≥ (2493 / 7 + 1 / 2) * ((7816 / 1000) - 1947 / 1000) - 2493 / 7 + 1 / 2 * (69314 / 100000) + 1 / 2 * (109860 / 100000) := by
    have hx : 1 ≤ (2493 : ℝ) / 7 := by norm_num
    have hcore := hLog_lower_gen ((2493 : ℝ) / 7) ((7816 / 1000) - 1947 / 1000) hx log_2493div7_lower
    have heq : hLog (xquot 2500 2) = hLog ((2493 : ℝ) / 7) := by
      congr 1
      dsimp [xquot]
      norm_num [Syl]
    simpa [← heq] using hcore
  have h3 : hLog (xquot 2500 3) ≥ (2457 / 43 + 1 / 2) * ((7804 / 1000) - 3763 / 1000) - 2457 / 43 + 1 / 2 * (69314 / 100000) + 1 / 2 * (109860 / 100000) := by
    have hx : 1 ≤ (2457 : ℝ) / 43 := by norm_num
    have hcore := hLog_lower_gen ((2457 : ℝ) / 43) ((7804 / 1000) - 3763 / 1000) hx log_2457div43_lower
    have heq : hLog (xquot 2500 3) = hLog ((2457 : ℝ) / 43) := by
      congr 1
      dsimp [xquot]
      norm_num [Syl]
    simpa [← heq] using hcore
  nlinarith

/-- slack 2500 ≥ 1 -/
theorem slack2500_ge_one : 1 ≤ slack 2500 := by
  dsimp [slack]
  have hU : Ulog 2500 = ALog 2500 - (∑ i ∈ range 4, hLog (xquot 2500 i)) := by
    dsimp [Ulog]
    rw [mact_2500]
    dsimp [xquot]
  rw [hU]
  have hsum : (∑ i ∈ range 4, hLog (xquot 2500 i)) = hLog (xquot 2500 0) + hLog (xquot 2500 1) + hLog (xquot 2500 2) + hLog (xquot 2500 3) := by
    norm_num [Finset.sum_range_succ]
  rw [hsum]
  have hAlog : ALog 2500 ≤ (5001 / 2) * (2 * (69316 / 100000) + 4 * (160944 / 100000)) - 2499 := by
    have hA : ALog 2500 = (5001 / 2) * Real.log (2500 : ℝ) - 2499 := by
      dsimp [ALog]
      ring_nf
    rw [hA, log2500_eq]
    have h2 : Real.log 2 ≤ 69316 / 100000 := log2_le_num
    have h5 : Real.log 5 ≤ 160944 / 100000 := log5_le_num
    nlinarith
  have h3l : (2500 : ℝ) * (109860 / 100000) ≤ 2500 * Real.log 3 := by
    have h3 : (109860 / 100000 : ℝ) ≤ Real.log 3 := log3_ge_num
    exact mul_le_mul_of_nonneg_left h3 (by norm_num)
  have hterms := slack2500_terms
  have hnum : 1 ≤ (2500 : ℝ) * (109860 / 100000)
      - ((5001 / 2) * (2 * (69316 / 100000) + 4 * (160944 / 100000)) - 2499)
      + ((1249 + 1 / 2) * (7126 / 1000) - 1249)
      + ((2497 / 3 + 1 / 2) * ((7818 / 1000) - 109863 / 100000) - 2497 / 3)
      + ((2493 / 7 + 1 / 2) * ((7816 / 1000) - 1947 / 1000) - 2493 / 7)
      + ((2457 / 43 + 1 / 2) * ((7804 / 1000) - 3763 / 1000) - 2457 / 43)
      + 2 * ((1 / 2) * (69314 / 100000) + (1 / 2) * (109860 / 100000)) := by
    norm_num
  nlinarith


/-- slack is nonnegative for every n ≥ 2500 -/
theorem slack_nonneg_of_2500 (n : ℕ) (hn : 2500 ≤ n) : 0 ≤ slack n := by
  rcases exists_ev_between hn with hleft | ⟨k, hk0, hk1⟩
  · have hn0 : n < ev 0 := hleft 0
    have hrun : slack 2500 ≤ slack n := by
      apply slack_nonact_run 2500 n (by norm_num) (by omega)
      intro m hm1 hm2 j
      have hnext : m + 1 < ev 0 := by
        have : m + 1 ≤ n := by omega
        omega
      exact nonact_below_ev0 m (by omega) hnext j
    have hb := slack2500_ge_one
    linarith
  · have hrun : slack (ev k) ≤ slack n := by
      apply slack_nonact_run (ev k) n (ev_ge_2500 k) (by omega)
      intro m hm1 hm2 j
      have hnext : m + 1 < ev (k + 1) := by
        have : m + 1 ≤ n := by omega
        omega
      exact nonact_between k m hm1 hnext j
    have hfl : slack (ev k) ≥ slack (ev 0) := slack_ev_ge_ev0 k
    have hbase : 0 ≤ slack (ev 0) := by
      have hbig0 : 2500 ≤ ev 0 - 1 := by
        have h0 : ev 0 = 3614 := by norm_num [ev, Syl]
        rw [h0]
        norm_num
      have hrun0 : slack 2500 ≤ slack (ev 0 - 1) := by
        apply slack_nonact_run 2500 (ev 0 - 1) (by norm_num) hbig0
        intro m hm1 hm2 j
        have hnext : m + 1 < ev 0 := by
          have h0 : ev 0 = 3614 := by norm_num [ev, Syl]
          have hpos : 0 < ev 0 := by omega
          omega
        exact nonact_below_ev0 m (by omega) hnext j
      have hpeq0 : (ev 0 - 1) + 1 = ev 0 := by
        have h0 : ev 0 = 3614 := by norm_num [ev, Syl]
        omega
      have hact0 : (ev 0 - 1) + 1 = 2 * Syl 4 := by
        have h0 : ev 0 = 3614 := by norm_num [ev, Syl]
        have h14 : (2 : ℕ) * Syl 4 = 3614 := by norm_num [Syl]
        omega
      have hg := slack_step_act (ev 0 - 1) 4 hbig0 (by norm_num : 1 ≤ 4) hact0
      have hstep : slack (ev 0 - 1) - 1 ≤ slack (ev 0) := by
        have hg' : -1 ≤ slack (ev 0) - slack (ev 0 - 1) := by
          rw [hpeq0] at hg
          exact hg
        linarith [hg']
      have hb := slack2500_ge_one
      linarith
    linarith


/-- log (3^n) = n log 3 -/
theorem log_three_pow (n : ℕ) : Real.log (((3 ^ n : ℕ) : ℝ)) = (n : ℝ) * Real.log 3 := by
  have hc : (((3 ^ n : ℕ) : ℝ) = (3 : ℝ) ^ n) := by
    rw [Nat.cast_pow]
    norm_num
  rw [hc, Real.log_pow]

/-- Hanson's bound: lcm(1..n) ≤ 3^n for all n -/
theorem lcmUpto_le_three_pow (n : ℕ) : Nat.lcmUpto n ≤ 3 ^ n := by
  by_cases hn : n ≤ 2500
  · exact lcmUpto_table2500 n hn
  · have hn2500 : 2500 ≤ n := by omega
    have hn1 : 1 ≤ n := by omega
    have hleCn : Nat.lcmUpto n ≤ Cn n := lcmUpto_le_Cn n
    have hlog1 : Real.log (Cn n : ℝ) ≤ Ulog n := log_Cn_le_Ulog n hn1
    have hslack : Ulog n ≤ (n : ℝ) * Real.log 3 := by
      have hs : 0 ≤ slack n := slack_nonneg_of_2500 n hn2500
      dsimp [slack] at hs
      linarith
    have hlog : Real.log (Cn n : ℝ) ≤ (n : ℝ) * Real.log 3 := le_trans hlog1 hslack
    have hx : 0 < (Cn n : ℝ) := by exact_mod_cast (Cn_pos n)
    have hy : 0 < (((3 ^ n : ℕ) : ℝ)) := by positivity
    have hCnR : (Cn n : ℝ) ≤ ((3 ^ n : ℕ) : ℝ) := by
      have hlog2 : Real.log (Cn n : ℝ) ≤ Real.log (((3 ^ n : ℕ) : ℝ)) := by
        rw [log_three_pow]
        exact hlog
      have hmain := Real.exp_le_exp.mpr hlog2
      rw [Real.exp_log hx] at hmain
      rwa [Real.exp_log hy] at hmain
    have hCn : Cn n ≤ 3 ^ n := by exact_mod_cast hCnR
    exact le_trans hleCn hCn

end Commons.NumberTheory.Chebyshev