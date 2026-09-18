import Mathlib

open scoped Nat BigOperators

/-!
# Growth of the coprime-window length (auxiliary for the non-decay zero-one reduction)

Let `k(q)` be the number of distinct prime factors of `q`.  We need that the window
length `1 + 2^(2k(q)+1)` grows sublinearly in `q`, i.e. for every `ε > 0`,
`1 + 2^(2k(q)+1) ≤ ε·q` for all large `q`.

Steps:

1. The radical `rad(q) := ∏_{p ∈ q.primeFactors} p` divides `q`, and since the
   distinct prime factors are distinct naturals `≥ 2`, `rad(q) ≥ (k(q)+1)!`.
   (`Finset.induction_on_max` for the factorial bound.)
2. For `ω ≥ 40` we have `(ω+1)! ≥ 2^(4ω+1)` (induction on `ω`, base `41! ≥ 2^161`).
3. Hence for `q ≥ 2^157`, `2^(4k(q)) < q` (otherwise, if `k ≤ 39` then
   `2^(4k) ≤ 2^156 < q`, and if `k ≥ 40` then `q ≥ rad(q) ≥ (k+1)! ≥ 2^(4k+1)`).
4. From `2^(4k) < q` and `q` large one gets `1 + 2^(2k+1) ≤ εq` by squaring:
   `(2^(2k+1))² < 4q`, so `(2·2^(2k+1))² < 16q`, and
   `16q ≤ (εq)²` once `q ≥ 16/ε²`.
5. Finally pick a single `Q ≥ max (2^157) (16/ε²)` via `exists_nat_ge`.
-/

namespace Submission.DS

/-- For a finset of naturals all `≥ 2` (so necessarily distinct), the product is at
least `(card + 1)!`. -/
private lemma prod_ge_factorial_of_forall_ge_two (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    (∏ p ∈ S, p) ≥ Nat.factorial (S.card + 1) := by
  classical
  let motive : Finset ℕ → Prop := fun T =>
    (∀ p ∈ T, 2 ≤ p) → (∏ p ∈ T, p) ≥ Nat.factorial (T.card + 1)
  have hmain : motive S := by
    refine Finset.induction_on_max (s := S) (motive := motive) ?empty ?insert
    · intro h
      simp
    · intro a T hTlt ih hAll
      have h2a : 2 ≤ a := by
        have := hAll a (by simp)
        exact this
      have h2T : ∀ p ∈ T, 2 ≤ p := by
        intro p hp
        exact hAll p (by simp [hp])
      have hanot : a ∉ T := by
        intro hmem
        have := hTlt a hmem
        omega
      have hprod_eq : (∏ p ∈ insert a T, p) = a * (∏ p ∈ T, p) := by
        simpa using (Finset.prod_insert (s := T) (a := a) (f := fun p : ℕ => p) hanot)
      have hTsub : T ⊆ Finset.Icc 2 (a - 1) := by
        intro x hx
        rw [Finset.mem_Icc]
        have hx2 : 2 ≤ x := h2T x hx
        have hxa : x < a := hTlt x hx
        constructor
        · exact hx2
        · omega
      have hcardT : T.card ≤ (a - 1) + 1 - 2 := by
        have := Finset.card_le_card hTsub
        rwa [Nat.card_Icc] at this
      have hale : T.card + 2 ≤ a := by
        omega
      have ih' : (∏ p ∈ T, p) ≥ Nat.factorial (T.card + 1) := ih h2T
      have hprod_ge : a * (∏ p ∈ T, p) ≥ a * Nat.factorial (T.card + 1) := by
        exact Nat.mul_le_mul_left a ih'
      have hstep : (T.card + 2) * Nat.factorial (T.card + 1) ≤
          a * Nat.factorial (T.card + 1) := by
        exact Nat.mul_le_mul_right (Nat.factorial (T.card + 1)) hale
      have hfac : (T.card + 2) * Nat.factorial (T.card + 1) = Nat.factorial (T.card + 2) := by
        rw [Nat.factorial_succ (T.card + 1)]
      have hcard_insert : (insert a T).card = T.card + 1 := Finset.card_insert_of_notMem hanot
      have htarget : Nat.factorial ((insert a T).card + 1) = Nat.factorial (T.card + 2) := by
        rw [hcard_insert]
      rw [hprod_eq, htarget]
      calc
        a * (∏ p ∈ T, p) ≥ a * Nat.factorial (T.card + 1) := hprod_ge
        _ ≥ (T.card + 2) * Nat.factorial (T.card + 1) := hstep
        _ = Nat.factorial (T.card + 2) := hfac
  exact hmain hS

/-- For `ω ≥ 40`, `(ω+1)! ≥ 2^(4ω+1)`. -/
private lemma factorial_succ_ge_two_pow (ω : ℕ) (hω : 40 ≤ ω) :
    Nat.factorial (ω + 1) ≥ 2 ^ (4 * ω + 1) := by
  induction ω with
  | zero => omega
  | succ ω ih =>
      by_cases h40 : 40 ≤ ω
      · have ih' := ih h40
        calc
          Nat.factorial (ω + 2) = (ω + 2) * Nat.factorial (ω + 1) :=
            (Nat.factorial_succ (ω + 1)).symm
          _ ≥ (ω + 2) * 2 ^ (4 * ω + 1) := Nat.mul_le_mul_left (ω + 2) ih'
          _ ≥ 16 * 2 ^ (4 * ω + 1) := by
              exact Nat.mul_le_mul_right (2 ^ (4 * ω + 1)) (by omega)
          _ = 2 ^ (4 * (ω + 1) + 1) := by
             calc
               16 * 2 ^ (4 * ω + 1) = 2 ^ 4 * 2 ^ (4 * ω + 1) := by norm_num
               _ = 2 ^ (4 + (4 * ω + 1)) := by rw [← pow_add]
               _ = 2 ^ (4 * (ω + 1) + 1) := by congr 1; omega
      · have hn : ω = 39 := by omega
        subst ω
        norm_num

/-- Once `q ≥ 2^157`, the number `k` of distinct prime factors of `q` satisfies
`2^(4k) < q`. -/
private lemma two_pow_four_mul_card_primeFactors_lt (q : ℕ) (hq : 2 ^ 157 ≤ q) :
    2 ^ (4 * q.primeFactors.card) < q := by
  by_cases hk40 : 40 ≤ q.primeFactors.card
  · have hrad_le_q : (∏ p ∈ q.primeFactors, p) ≤ q := by
      apply Nat.le_of_dvd
      · exact lt_of_lt_of_le (by norm_num : 0 < 2 ^ 157) hq
      · exact Nat.prod_primeFactors_dvd q
    have hfac_le_rad : Nat.factorial (q.primeFactors.card + 1) ≤ ∏ p ∈ q.primeFactors, p := by
      exact prod_ge_factorial_of_forall_ge_two q.primeFactors (by
        intro p hp
        exact (Nat.prime_of_mem_primeFactors hp).two_le)
    have hpow_le_fac : 2 ^ (4 * q.primeFactors.card + 1) ≤
        Nat.factorial (q.primeFactors.card + 1) :=
      factorial_succ_ge_two_pow q.primeFactors.card hk40
    have hstrict : 2 ^ (4 * q.primeFactors.card) < 2 ^ (4 * q.primeFactors.card + 1) := by
      exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega)
    exact lt_of_lt_of_le hstrict
      (le_trans hpow_le_fac (le_trans hfac_le_rad hrad_le_q))
  · have hk39 : q.primeFactors.card ≤ 39 := by omega
    have h4le : 4 * q.primeFactors.card ≤ 156 := by omega
    have hpow_le : 2 ^ (4 * q.primeFactors.card) ≤ 2 ^ 156 :=
      Nat.pow_le_pow_right (by norm_num : (2:ℕ) > 0) h4le
    have h156 : 2 ^ 156 < 2 ^ 157 := by
      exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by norm_num)
    exact lt_of_lt_of_le (lt_of_le_of_lt hpow_le h156) hq

/-- Nonnegativity lets us deduce `a < b` from `a^2 < b^2` (for real `a,b`). -/
private lemma sq_lt_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (h : a ^ 2 < b ^ 2) : a < b := by
  have habs : |a| < |b| := (sq_lt_sq).mp h
  rwa [abs_of_nonneg ha, abs_of_pos hb] at habs

/-- For every `ε > 0`, the window length `1 + 2^(2k(q)+1)` is eventually `≤ ε·q`,
where `k(q)` is the number of distinct prime factors of `q`. -/
theorem window_len_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      ((1 : ℝ) + (2 : ℝ) ^ (2 * q.primeFactors.card + 1)) ≤ ε * (q : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (16 / ε ^ 2)
  let Q : ℕ := max (2 ^ 157) N
  refine ⟨Q, ?_⟩
  intro q hq
  let k : ℕ := q.primeFactors.card
  have hqsize : 2 ^ 157 ≤ q := le_trans (le_max_left (2 ^ 157) N) hq
  have hqN : N ≤ q := le_trans (le_max_right (2 ^ 157) N) hq
  have hqge1 : (1 : ℝ) ≤ (q : ℝ) := by
    have : 1 ≤ q := le_trans (by norm_num : 1 ≤ 2 ^ 157) hqsize
    exact_mod_cast this
  have h16 : (16 : ℝ) ≤ ε ^ 2 * (q : ℝ) := by
    have hNcast : (16 / ε ^ 2 : ℝ) ≤ (q : ℝ) := by
      exact le_trans hN (by exact_mod_cast hqN)
    have hε2pos : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hε2ne : ε ^ 2 ≠ 0 := ne_of_gt hε2pos
    calc
      (16 : ℝ) = (16 / ε ^ 2) * ε ^ 2 := by field_simp [hε2ne]
      _ ≤ (q : ℝ) * ε ^ 2 := by
        exact mul_le_mul_of_nonneg_right hNcast (le_of_lt hε2pos)
      _ = ε ^ 2 * (q : ℝ) := by ring
  have h16q : 16 * (q : ℝ) ≤ (ε * (q : ℝ)) ^ 2 := by
    have hq0 : 0 ≤ (q : ℝ) := by exact le_trans zero_le_one hqge1
    have hm : 16 * (q : ℝ) ≤ (ε ^ 2 * (q : ℝ)) * (q : ℝ) :=
      mul_le_mul_of_nonneg_right h16 hq0
    have hre : (ε ^ 2 * (q : ℝ)) * (q : ℝ) = (ε * (q : ℝ)) ^ 2 := by ring
    exact le_trans hm (le_of_eq hre)
  have hpow4 : 2 ^ (4 * k) < q := by
    simpa [k] using two_pow_four_mul_card_primeFactors_lt q hqsize
  have hpow4R : (2 : ℝ) ^ (4 * k) < (q : ℝ) := by
    exact_mod_cast hpow4
  let x : ℝ := (2 : ℝ) ^ (2 * k + 1)
  let W : ℝ := 1 + x
  have hx2 : x ^ 2 < 4 * (q : ℝ) := by
    have hp : x ^ 2 = (2 : ℝ) ^ (4 * k + 2) := by
      dsimp [x]
      rw [← pow_mul]
      congr 1
      omega
    rw [hp]
    calc
      (2 : ℝ) ^ (4 * k + 2) = (2 : ℝ) ^ (4 * k) * (2 : ℝ) ^ 2 := by rw [pow_add]
      _ = (2 : ℝ) ^ (4 * k) * 4 := by norm_num
      _ = 4 * (2 : ℝ) ^ (4 * k) := by ring
      _ < 4 * (q : ℝ) := mul_lt_mul_of_pos_left hpow4R (by norm_num : (0 : ℝ) < 4)
  have hx1 : (1 : ℝ) ≤ x := by
    have hnat : 1 ≤ 2 ^ (2 * k + 1) := Nat.one_le_two_pow
    dsimp [x]
    exact_mod_cast hnat
  have hWz : W ≤ 2 * x := by
    dsimp [W]
    linarith
  have hz2 : (2 * x) ^ 2 < 16 * (q : ℝ) := by
    nlinarith [hx2]
  have hztlt : 2 * x < ε * (q : ℝ) := by
    have h : (2 * x) ^ 2 < (ε * (q : ℝ)) ^ 2 := lt_of_lt_of_le hz2 h16q
    exact sq_lt_sq_of_nonneg (by positivity) (by positivity) h
  have hWlt : W < ε * (q : ℝ) := lt_of_le_of_lt hWz hztlt
  have hW : W ≤ ε * (q : ℝ) := le_of_lt hWlt
  simpa [W, k, x] using hW

end Submission.DS
