import Submission.ZagierHoffmanProof.PrimeGidx
import Submission.ZagierHoffmanProof.PrimeJMin
import Submission.Commons.Data.Nat.noCarry_iff_mod_sum
import Submission.Commons.Data.Nat.sum_digits_decomp

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# The reduction lemma (RED)

For `q = p` prime and `j` an admissible shift at `x` (that is: `j ≥ 1`, `(p-1) ∣ j` and adding
`j` to `x - 1` in base `p` produces no carry), the difference

  `δ = τ(x+j) - τ(x)`,   `τ(y) = (y + j_min(y)) / p`

is again an admissible shift, this time at `τ(x)`:

  `(p-1) ∣ δ`,  `1 ≤ δ`,  and no carry in `δ + (τ(x) - 1)`.
-/

namespace ZagierHoffmanPositiveChar

section Helpers

/-- Monotonicity of the cumulative capacity. -/
lemma csum_le_of_capp_le {p n n' : ℕ} (h : ∀ i, capp p n' i ≤ capp p n i) (m : ℕ) :
    csum p n' m ≤ csum p n m := by
  unfold csum
  exact Finset.sum_le_sum fun i _ => h i

/-- Adding without carry adds the digits. -/
lemma noCarry_div_add {p : ℕ} (i : ℕ) : ∀ (n j : ℕ), noCarry p j n →
    (n + j) / p ^ i % p = n / p ^ i % p + j / p ^ i % p := by
  induction i with
  | zero =>
      intro n j h
      have h0 : n % p + j % p < p := by
        have := h 0
        simp only [pow_zero, Nat.div_one] at this
        omega
      simp only [pow_zero, Nat.div_one]
      exact Nat.add_mod_of_add_mod_lt h0
  | succ i ih =>
      intro n j h
      have h0 : n % p + j % p < p := by
        have := h 0
        simp only [pow_zero, Nat.div_one] at this
        omega
      have hshift : noCarry p (j / p) (n / p) :=
        (Commons.Data.Nat.noCarry_rec p j n).mp h |>.2
      have hdiv : (n + j) / p = n / p + j / p := Nat.add_div_eq_of_add_mod_lt h0
      have h1 : (n + j) / p ^ (i + 1) = (n / p + j / p) / p ^ i := by
        rw [Commons.Data.Nat.div_pow_succ_eq, hdiv]
      have h2 : n / p ^ (i + 1) = (n / p) / p ^ i := Commons.Data.Nat.div_pow_succ_eq n p i
      have h3 : j / p ^ (i + 1) = (j / p) / p ^ i := Commons.Data.Nat.div_pow_succ_eq j p i
      rw [h1, h2, h3, ih (n / p) (j / p) hshift]

/-- The capacity of `n + j` when adding `j` to `n` produces no carry. -/
lemma capp_add_of_noCarry {p n j : ℕ} (h : noCarry p j n) (i : ℕ) :
    capp p (n + j) i = capp p n i - j / p ^ i % p := by
  have h0 : j / p ^ i % p + n / p ^ i % p < p := h i
  have hp0 : 0 < p := by omega
  have hd := noCarry_div_add i n j h
  have h1 : n / p ^ i % p ≤ p - 1 := by
    have := Nat.mod_lt (n / p ^ i) hp0; omega
  unfold capp
  rw [hd]
  omega

end Helpers

section GIdxMono

/-- If the cumulative capacity already reaches `r` at index `K`, then the greedy index is at
most `K`. -/
theorem gidx_le_of_csum {p : ℕ} (hp : 2 ≤ p) : ∀ (r n K : ℕ), r ≤ p - 1 →
    r ≤ csum p n (K + 1) → gidx p hp r n ≤ K := by
  intro r n
  induction r, n using gidx.induct p hp with
  | case1 n =>
      intro K hr h
      rw [gidx_eq_zero hp (r := 0) (n := n) (by omega) (Nat.zero_le _)]
      exact Nat.zero_le _
  | case2 r n hr0 hc0 ih =>
      intro K hr h
      have hsub : r - capp p n 0 = r := by rw [hc0]; omega
      rw [gidx_succ hp hr (by rw [hc0]; omega), hsub]
      have hh : r ≤ csum p (n / p) K := by
        have h1 := csum_succ_eq p n K
        omega
      rcases Nat.eq_zero_or_pos K with hK | hK
      · subst hK
        simp [csum] at hh
        omega
      · have h2 : (K - 1) + 1 = K := by omega
        have := ih (K - 1) (by omega) (by rw [h2]; exact hh)
        omega
  | case3 r n hr0 hc0 hle =>
      intro K hr h
      rw [gidx_eq_zero hp hr hle]
      exact Nat.zero_le _
  | case4 r n hr0 hc0 hnc ih =>
      intro K hr h
      have hclt : capp p n 0 < r := by omega
      rw [gidx_succ hp hr hclt]
      have hh : r - capp p n 0 ≤ csum p (n / p) K := by
        have h1 := csum_succ_eq p n K
        omega
      rcases Nat.eq_zero_or_pos K with hK | hK
      · subst hK
        simp [csum] at hh
        omega
      · have h2 : (K - 1) + 1 = K := by omega
        have := ih (K - 1) (by omega) (by rw [h2]; exact hh)
        omega

/-- The greedy index is monotone under pointwise domination of the capacities. -/
theorem gidx_mono_le {p n n' : ℕ} (hp : 2 ≤ p) (h : ∀ i, capp p n' i ≤ capp p n i) :
    gidx p hp (p - 1) n ≤ gidx p hp (p - 1) n' := by
  have h1 : p - 1 ≤ csum p n' (gidx p hp (p - 1) n' + 1) :=
    le_csum_gidx_succ hp (p - 1) n' le_rfl
  have h2 : csum p n' (gidx p hp (p - 1) n' + 1) ≤ csum p n (gidx p hp (p - 1) n' + 1) :=
    csum_le_of_capp_le h _
  exact gidx_le_of_csum hp (p - 1) n _ le_rfl (le_trans h1 h2)

end GIdxMono

section GreedyDigits

/-- The digits of the base-`p` greedy fill: saturated up to the greedy index, the remainder
there, and zero above. -/
theorem greedy_digit_eq {p : ℕ} (hp : 2 ≤ p) (n i : ℕ) :
    greedy p hp n / p ^ i % p =
      (if i < gidx p hp (p - 1) n then capp p n i
        else if i = gidx p hp (p - 1) n then
          (p - 1) - csum p n (gidx p hp (p - 1) n) else 0) := by
  set m := gidx p hp (p - 1) n with hm
  set d := (p - 1) - csum p n m with hd
  have hsum : greedy p hp n = ∑ k ∈ Finset.range (m + 1),
      (if k < m then capp p n k else if k = m then d else 0) * p ^ k := by
    rw [greedy, Gg_eq_sum hp (p - 1) n le_rfl, ← hm, ← hd, Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [if_pos (Finset.mem_range.mp hk)]
    · rw [if_neg (lt_irrefl m), if_pos rfl]
  have hlt : ∀ k < m + 1,
      (if k < m then capp p n k else if k = m then d else 0) < p := by
    intro k hk
    by_cases h1 : k < m
    · rw [if_pos h1]
      exact lt_of_le_of_lt (capp_le p n k) (by omega)
    · rw [if_neg h1]
      by_cases h2 : k = m
      · rw [if_pos h2]
        exact lt_of_le_of_lt (Nat.sub_le _ _) (by omega)
      · rw [if_neg h2]
        omega
  have key : (if i < m + 1 then
        (if i < m then capp p n i else if i = m then d else 0) else 0)
      = (if i < m then capp p n i else if i = m then d else 0) := by
    by_cases h1 : i < m
    · rw [if_pos (by omega : i < m + 1)]
    · rw [if_neg h1]
      by_cases h2 : i = m
      · rw [if_pos (by omega : i < m + 1)]
      · rw [if_neg (by omega : ¬ i < m + 1), if_neg h2]
  rw [hsum, Commons.Data.Nat.sum_digits_decomp _ hlt i, key]


/-- The sum of the first `m + 1` capacities is the sum of the first `m` plus `capp` at `m`. -/
lemma csum_succ_add (p n m : ℕ) : csum p n (m + 1) = csum p n m + capp p n m := by
  unfold csum
  rw [Finset.sum_range_succ]

/-- **Digitwise domination.**  Every digit of the greedy fill of `n` is at most the sum of the
corresponding digit of the shift `j` and the corresponding digit of the greedy fill of `n + j`. -/
theorem greedy_digit_add_le {p : ℕ} (hp : 2 ≤ p) {n j : ℕ} (h : noCarry p j n) (i : ℕ) :
    greedy p hp n / p ^ i % p ≤ j / p ^ i % p + greedy p hp (n + j) / p ^ i % p := by
  set m := gidx p hp (p - 1) n with hm
  set m' := gidx p hp (p - 1) (n + j) with hm'
  set d := (p - 1) - csum p n m with hd
  set d' := (p - 1) - csum p (n + j) m' with hd'
  have hcap : ∀ k, capp p (n + j) k = capp p n k - j / p ^ k % p :=
    fun k => capp_add_of_noCarry h k
  have hle : m ≤ m' := gidx_mono_le hp fun k => by rw [hcap k]; exact Nat.sub_le _ _
  have hjl : ∀ k, j / p ^ k % p ≤ capp p n k :=
    fun k => (noCarry_iff_capp (p := p) (n := n) (j := j) hp).mpr h k
  have hdm : d ≤ capp p n m := by
    have h4 := le_csum_gidx_succ hp (p - 1) n
    rw [← hm, csum_succ_add] at h4
    rw [hd]
    omega
  rw [greedy_digit_eq hp n i, greedy_digit_eq hp (n + j) i, ← hm, ← hm']
  by_cases h1 : i < m
  · rw [if_pos h1, if_pos (by omega : i < m')]
    rw [hcap i]
    omega
  · rw [if_neg h1]
    by_cases h2 : i = m
    · rw [if_pos h2]
      rcases lt_trichotomy i m' with h3 | h3 | h3
      · rw [if_pos h3, hcap i]
        have : capp p n m = capp p n i := by rw [h2]
        rw [this] at hdm
        omega
      · rw [if_neg (by omega : ¬ i < m'), if_pos h3]
        have hmm : m' = m := by omega
        have h5 : csum p (n + j) m ≤ csum p n m :=
          csum_le_of_capp_le (fun k => by rw [hcap k]; exact Nat.sub_le _ _) m
        rw [hmm] at hd'
        rw [hmm]
        rw [← hd, ← hd']
        omega
      · omega
    · rw [if_neg h2]
      rcases lt_trichotomy i m' with h3 | h3 | h3
      · rw [if_pos h3, hcap i]
        omega
      · rw [if_neg (by omega : ¬ i < m'), if_pos h3]
        omega
      · rw [if_neg (by omega : ¬ i < m'), if_neg (by omega : ¬ i = m')]
        omega




section ModPowDigits

/-- Splitting a residue modulo `p^(k+1)` into its residue modulo `p^k` and the `k`-th digit. -/
lemma mod_pow_succ_eq (x p k : ℕ) (hp : 0 < p) :
    x % p ^ (k + 1) = x % p ^ k + p ^ k * (x / p ^ k % p) := by
  have hk : x = p ^ k * (x / p ^ k) + x % p ^ k := (Nat.div_add_mod x (p ^ k)).symm
  have hlt : x % p ^ k < p ^ k := Nat.mod_lt _ (pow_pos hp k)
  have hdle : p ^ k ≤ p ^ (k + 1) := Nat.pow_le_pow_right hp (by omega)
  have h1 : p ^ k * (x / p ^ k) % p ^ (k + 1) = p ^ k * (x / p ^ k % p) := by
    rw [pow_succ, Nat.mul_mod_mul_left]
  have h2 : x % p ^ k % p ^ (k + 1) = x % p ^ k := Nat.mod_eq_of_lt (lt_of_lt_of_le hlt hdle)
  have h3 : x / p ^ k % p ≤ p - 1 := by
    have := Nat.mod_lt (x / p ^ k) hp
    omega
  calc x % p ^ (k + 1)
      = (p ^ k * (x / p ^ k) + x % p ^ k) % p ^ (k + 1) := by conv_lhs => rw [hk]
    _ = (p ^ k * (x / p ^ k) % p ^ (k + 1) + x % p ^ k % p ^ (k + 1)) % p ^ (k + 1) :=
          Nat.add_mod _ _ _
    _ = (p ^ k * (x / p ^ k % p) + x % p ^ k) % p ^ (k + 1) := by rw [h1, h2]
    _ = p ^ k * (x / p ^ k % p) + x % p ^ k := Nat.mod_eq_of_lt (by
          have h4 : p ^ k * (x / p ^ k % p) ≤ p ^ k * (p - 1) := Nat.mul_le_mul_left _ h3
          have h5 : p ^ k * (p - 1) = p ^ k * p - p ^ k := by
            rw [Nat.mul_sub_left_distrib, mul_one]
          have h6 : p ^ k * p = p ^ (k + 1) := (pow_succ p k).symm
          omega)
    _ = x % p ^ k + p ^ k * (x / p ^ k % p) := by rw [Nat.add_comm]

/-- The residue of `x` modulo `p^k` is the sum of its low digits. -/
lemma mod_pow_eq_sum_digits (x p : ℕ) (hp : 0 < p) : ∀ k : ℕ,
    x % p ^ k = ∑ i ∈ Finset.range k, (x / p ^ i % p) * p ^ i := by
  intro k
  induction k with
  | zero => rw [pow_zero, Nat.mod_one]; simp
  | succ k ih =>
      rw [mod_pow_succ_eq x p k hp, ih, Finset.sum_range_succ, mul_comm]

/-- Digitwise domination implies domination of the residues. -/
lemma mod_pow_le_of_digits_le {p x y : ℕ} (hp : 0 < p)
    (h : ∀ i, x / p ^ i % p ≤ y / p ^ i % p) (k : ℕ) :
    x % p ^ k ≤ y % p ^ k := by
  rw [mod_pow_eq_sum_digits x p hp k, mod_pow_eq_sum_digits y p hp k]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (h i)

/-- Subtracting a residue without borrowing. -/
lemma sub_mod_eq {a b n : ℕ} (hab : a ≤ b) (h : a % n ≤ b % n) :
    (b - a) % n = b % n - a % n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have h1 : (a + (b - a)) % n = b % n := by rw [Nat.add_sub_cancel' hab]
    rw [Nat.add_mod] at h1
    have h2 : a % n < n := Nat.mod_lt _ hn
    have h3 : (b - a) % n < n := Nat.mod_lt _ hn
    have h4 : b % n < n := Nat.mod_lt _ hn
    rcases lt_or_ge (a % n + (b - a) % n) n with h5 | h5
    · rw [Nat.mod_eq_of_lt h5] at h1
      omega
    · have h6 : (a % n + (b - a) % n) % n = a % n + (b - a) % n - n := by
        rw [Nat.mod_eq_sub_mod h5, Nat.mod_eq_of_lt (by omega)]
      rw [h6] at h1
      omega

end ModPowDigits
section MainRed

/-- The valuation map `τ(y) = (y + j_min(y))/p` of the reduction lemma. -/
def Tg (p : ℕ) (hp : 2 ≤ p) (n : ℕ) : ℕ := n + 1 + greedy p hp n

/-- The lowest digit of the greedy fill is the capacity of digit `0`. -/
lemma greedy_mod_p {p : ℕ} (hp : 2 ≤ p) (n : ℕ) : greedy p hp n % p = capp p n 0 := by
  set m := gidx p hp (p - 1) n with hm
  have h0 : greedy p hp n % p = greedy p hp n / p ^ 0 % p := by simp
  rw [h0, greedy_digit_eq hp n 0, ← hm]
  by_cases h : 0 < m
  · rw [if_pos h]
  · rw [if_neg h]
    have hm0 : m = 0 := by omega
    rw [if_pos hm0.symm, hm0]
    have h3 : csum p n 0 = 0 := by simp [csum]
    rw [h3, Nat.sub_zero]
    have h1 := le_csum_gidx_succ hp (p - 1) n le_rfl
    rw [← hm, hm0, Nat.zero_add, csum_succ_add, h3, Nat.zero_add] at h1
    have h2 := capp_le p n 0
    omega

/-- `T(y) = y + j_min(y)` is divisible by `p`. -/
lemma dvd_Tg {p : ℕ} (hp : 2 ≤ p) (n : ℕ) : p ∣ Tg p hp n := by
  have hnc : noCarry p (greedy p hp n) n :=
    (noCarry_iff_capp (p := p) (n := n) (j := greedy p hp n) hp).mp (greedy_digit_le hp n)
  have h1 : (n + greedy p hp n) % p = p - 1 := by
    have h2 : (n + greedy p hp n) % p
        = (n + greedy p hp n) / p ^ 0 % p := by simp
    rw [h2, noCarry_div_add 0 n (greedy p hp n) hnc]
    simp only [pow_zero, Nat.div_one]
    rw [greedy_mod_p hp n, capp_zero]
    have h3 : n % p ≤ p - 1 := by
      have := Nat.mod_lt n (by omega : 0 < p); omega
    omega
  rw [Nat.dvd_iff_mod_eq_zero, Tg]
  have h2 : n + 1 + greedy p hp n = (n + greedy p hp n) + 1 := by omega
  rw [h2, Nat.add_mod, h1, Nat.mod_eq_of_lt (by omega : 1 < p)]
  have h3 : p - 1 + 1 = p := Nat.sub_add_cancel (by omega : 1 ≤ p)
  rw [h3, Nat.mod_self]

/-- Dividing by `p` does not change a number modulo `p - 1`. -/
lemma div_modEq {p : ℕ} (hp : 2 ≤ p) {m : ℕ} (h : p ∣ m) :
    Nat.ModEq (p - 1) (m / p) m := by
  have hp1 : Nat.ModEq (p - 1) p 1 :=
    ((Nat.modEq_iff_dvd' (n := p - 1) (a := 1) (b := p)
      (show 1 ≤ p by omega)).mpr (dvd_refl (p - 1))).symm
  have hm : m = p * (m / p) := (Nat.mul_div_cancel' h).symm
  rw [hm, Nat.mul_div_cancel_left _ (by omega : 0 < p)]
  have h2 : Nat.ModEq (p - 1) (p * (m / p)) (m / p) := by
    simpa using hp1.mul (Nat.ModEq.refl (m / p))
  exact h2.symm

/-- **The reduction lemma (RED).** -/
theorem red_delta {p : ℕ} (hp : 2 ≤ p) (n j : ℕ) (hj : 1 ≤ j) (hadm : noCarry p j n)
    (hjdvd : (p - 1) ∣ j) :
    (p - 1) ∣ (Tg p hp (n + j) / p - Tg p hp n / p) ∧
    1 ≤ Tg p hp (n + j) / p - Tg p hp n / p ∧
    noCarry p (Tg p hp (n + j) / p - Tg p hp n / p) (Tg p hp n / p - 1) := by
  have hGle : greedy p hp n ≤ j := greedy_le hp n j
    (fun i => (noCarry_iff_capp (p := p) (n := n) (j := j) hp).mpr hadm i)
    (le_dsum_of_dvd hp hjdvd hj)
  set G := greedy p hp n with hG
  set G' := greedy p hp (n + j) with hG'
  -- (1) `T ≤ T'`, strictly
  have hTle : Tg p hp n ≤ Tg p hp (n + j) := by
    unfold Tg
    rw [← hG, ← hG']
    omega
  have hG'pos : 1 ≤ G' := greedy_pos hp (n + j)
  have hTlt : Tg p hp n < Tg p hp (n + j) := by
    unfold Tg
    rw [← hG, ← hG']
    omega
  -- (2) divisibility
  have hp1 : p ∣ Tg p hp n := dvd_Tg hp n
  have hp2 : p ∣ Tg p hp (n + j) := dvd_Tg hp (n + j)
  have hδeq : Tg p hp (n + j) / p - Tg p hp n / p
      = (Tg p hp (n + j) - Tg p hp n) / p := by
    have h2 : Tg p hp (n + j) = p * (Tg p hp (n + j) / p) := (Nat.mul_div_cancel' hp2).symm
    have h1 : Tg p hp n = p * (Tg p hp n / p) := (Nat.mul_div_cancel' hp1).symm
    have h3 : Tg p hp n / p ≤ Tg p hp (n + j) / p := Nat.div_le_div_right hTle
    have h4 : Tg p hp (n + j) - Tg p hp n
        = p * (Tg p hp (n + j) / p) - p * (Tg p hp n / p) := by
      conv_lhs => rw [h2, h1]
    rw [h4, ← Nat.mul_sub_left_distrib, Nat.mul_div_cancel_left _ (by omega : 0 < p)]
  -- (3) the digitwise domination of `z = n + G` by `z' = n + j + G'`
  have hncG : noCarry p G n :=
    (noCarry_iff_capp (p := p) (n := n) (j := G) hp).mp (greedy_digit_le hp n)
  have hncG' : noCarry p G' (n + j) :=
    (noCarry_iff_capp (p := p) (n := n + j) (j := G') hp).mp (greedy_digit_le hp (n + j))
  have hzdigit : ∀ k, (n + G) / p ^ k % p ≤ (n + j + G') / p ^ k % p := by
    intro k
    have h1 : (n + G) / p ^ k % p = n / p ^ k % p + G / p ^ k % p :=
      noCarry_div_add k n G hncG
    have h2 : (n + j + G') / p ^ k % p = (n + j) / p ^ k % p + G' / p ^ k % p :=
      noCarry_div_add k (n + j) G' hncG'
    have h3 : (n + j) / p ^ k % p = n / p ^ k % p + j / p ^ k % p :=
      noCarry_div_add k n j hadm
    have h4 := greedy_digit_add_le hp hadm k
    rw [← hG, ← hG'] at h4
    rw [h1, h2, h3]
    omega
  have hmod : ∀ k, (n + G) % p ^ k ≤ (n + j + G') % p ^ k :=
    fun k => mod_pow_le_of_digits_le (by omega : 0 < p) hzdigit k
  have hle' : n + G ≤ n + j + G' := by omega
  -- (4) the shift `X = T' - T` and its digits
  have hXeq : Tg p hp (n + j) - Tg p hp n = (n + j + G') - (n + G) := by
    unfold Tg
    rw [← hG, ← hG']
    omega
  have hsub : ∀ k, (Tg p hp (n + j) - Tg p hp n) % p ^ k + (n + G) % p ^ k < p ^ k := by
    intro k
    have h1 : ((n + j + G') - (n + G)) % p ^ k
        = (n + j + G') % p ^ k - (n + G) % p ^ k := sub_mod_eq hle' (hmod k)
    rw [hXeq, h1]
    have h2 : (n + j + G') % p ^ k < p ^ k := Nat.mod_lt _ (pow_pos (by omega : 0 < p) k)
    have h3 : (n + G) % p ^ k ≤ (n + j + G') % p ^ k := hmod k
    have h4 : (n + j + G') % p ^ k - (n + G) % p ^ k + (n + G) % p ^ k
        = (n + j + G') % p ^ k := Nat.sub_add_cancel h3
    rw [h4]
    exact h2
  have hncX : noCarry p (Tg p hp (n + j) - Tg p hp n) (n + G) :=
    (Commons.Data.Nat.noCarry_iff_mod_sum hp).mpr hsub
  -- (5) the digit identities for `δ` and `τ - 1`
  have hGpos : 1 ≤ G := greedy_pos hp n
  have hGp : p - 1 ≤ G := by
    have h := greedy_dsum hp n
    rw [← hG] at h
    have h2 := dsum_le (by omega : 1 < p) G
    omega
  have hzT : Tg p hp n - 1 = n + G := by
    unfold Tg; rw [← hG]; omega
  have hτ1 : Tg p hp n / p - 1 = (n + G) / p := by
    rw [← hzT]
    have h2 : Tg p hp n = p * (Tg p hp n / p) := (Nat.mul_div_cancel' hp1).symm
    have hq : 1 ≤ Tg p hp n / p := by
      have h4 : p ≤ Tg p hp n := by
        unfold Tg; rw [← hG]
        omega
      exact Nat.le_div_iff_mul_le (by omega : 0 < p) |>.mpr (by simpa using h4)
    have h8 : p * (Tg p hp n / p - 1) = p * (Tg p hp n / p) - p := by
      rw [Nat.mul_sub_left_distrib, mul_one]
    have h6 : Tg p hp n - 1 = p * (Tg p hp n / p - 1) + (p - 1) := by
      conv_lhs => rw [h2]
      rw [h8]
      omega
    rw [h6, Nat.mul_add_div (by omega : 0 < p), Nat.div_eq_of_lt (by omega : p - 1 < p),
      Nat.add_zero]
  -- (6) conclude
  refine ⟨?_, ?_, ?_⟩
  · have h1 : Nat.ModEq (p - 1) (Tg p hp n) (n + 1) := by
      have h2 : Nat.ModEq (p - 1) G 0 := Nat.modEq_zero_iff_dvd.mpr (greedy_dvd hp n)
      have h3 := h2.add_left (n + 1)
      have h4 : n + 1 + 0 = n + 1 := by omega
      rw [h4] at h3
      unfold Tg; rw [← hG]; exact h3
    have h5 : Nat.ModEq (p - 1) (Tg p hp n / p) (Tg p hp n) := div_modEq hp hp1
    have h1' : Nat.ModEq (p - 1) (Tg p hp (n + j)) (n + j + 1) := by
      have h2 : Nat.ModEq (p - 1) G' 0 := Nat.modEq_zero_iff_dvd.mpr (greedy_dvd hp (n + j))
      have h3 := h2.add_left (n + j + 1)
      have h4 : n + j + 1 + 0 = n + j + 1 := by omega
      rw [h4] at h3
      unfold Tg; rw [← hG']; exact h3
    have h5' : Nat.ModEq (p - 1) (Tg p hp (n + j) / p) (Tg p hp (n + j)) := div_modEq hp hp2
    have hj0 : Nat.ModEq (p - 1) j 0 := Nat.modEq_zero_iff_dvd.mpr hjdvd
    have hττ' : Nat.ModEq (p - 1) (Tg p hp n / p) (Tg p hp (n + j) / p) := by
      have e1 : Nat.ModEq (p - 1) (Tg p hp n / p) (n + 1) := h5.trans h1
      have e2 : Nat.ModEq (p - 1) (n + 1) (n + 1 + j) := by
        have hh := (hj0.add_left (n + 1)).symm
        simpa using hh
      have e3 : Nat.ModEq (p - 1) (n + 1 + j) (Tg p hp (n + j) / p) := by
        have h6 : n + 1 + j = n + j + 1 := by omega
        rw [h6]
        exact h1'.symm.trans h5'.symm
      exact e1.trans (e2.trans e3)
    have hτle : Tg p hp n / p ≤ Tg p hp (n + j) / p := Nat.div_le_div_right hTle
    exact (Nat.modEq_iff_dvd' hτle).mp hττ'
  · have h6 : Tg p hp (n + j) = p * (Tg p hp (n + j) / p) := (Nat.mul_div_cancel' hp2).symm
    have h7 : Tg p hp n = p * (Tg p hp n / p) := (Nat.mul_div_cancel' hp1).symm
    have h8 : p * (Tg p hp n / p) < p * (Tg p hp (n + j) / p) := by
      rw [← h7, ← h6]
      exact hTlt
    have h3 : Tg p hp n / p < Tg p hp (n + j) / p := Nat.lt_of_mul_lt_mul_left h8
    omega
  · intro i
    have h1 : Tg p hp (n + j) / p - Tg p hp n / p
        = (Tg p hp (n + j) - Tg p hp n) / p := hδeq
    rw [h1, hτ1, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    have h2 := hncX (i + 1)
    rw [pow_succ'] at h2
    exact h2

end MainRed


end GreedyDigits

end ZagierHoffmanPositiveChar
