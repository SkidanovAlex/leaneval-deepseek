import Submission.ZagierHoffmanProof.PrimeQ
import Mathlib.Data.Nat.Digits.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# The greedy "digit fill" and the least admissible shift

This module builds, for a base `p ≥ 2` and a natural number `n`, the *greedy fill* of the
capacities `capp p n i = p - 1 - n / p^i % p`: the number whose base-`p` digits fill the
capacities from the bottom until the total `r` is reached.  It is the value of the least
admissible shift `jMin` for a prime field of cardinality `p`.
-/

namespace ZagierHoffmanPositiveChar

/-- The capacity at digit `i`: the largest digit that can be added to the `i`-th digit of `n`
without producing a carry, namely `p - 1 - n / p^i % p = (p-1) - ` the `i`-th digit of `n`. -/
def capp (p n i : ℕ) : ℕ := (p - 1) - n / p ^ i % p

/-- The sum of the first `m` capacities. -/
def csum (p n m : ℕ) : ℕ := ∑ i ∈ Finset.range m, capp p n i

/-- The sum of the base-`p` digits of `n`. -/
def dsum (p n : ℕ) : ℕ := (Nat.digits p n).sum

lemma capp_le (p n i : ℕ) : capp p n i ≤ p - 1 := Nat.sub_le _ _

lemma capp_zero (p n : ℕ) : capp p n 0 = (p - 1) - n % p := by
  simp [capp]

/-- Shifting the capacities is shifting `n`. -/
lemma capp_tail (p n i : ℕ) : capp p (n / p) i = capp p n (i + 1) := by
  unfold capp
  rw [show n / p ^ (i + 1) = n / p / p ^ i from by rw [pow_succ', Nat.div_div_eq_div_mul]]

lemma capp_eq_zero_iff {p n : ℕ} (hp : 2 ≤ p) :
    capp p n 0 = 0 ↔ n % p = p - 1 := by
  have h1 : n % p ≤ p - 1 := by have h := Nat.mod_lt n (by omega : 0 < p); omega
  rw [capp_zero]
  omega

section DSum

variable {p : ℕ}

lemma dsum_zero (p : ℕ) : dsum p 0 = 0 := by simp [dsum]

lemma dsum_succ {p : ℕ} (hp : 1 < p) (j : ℕ) :
    dsum p (j + 1) = (j + 1) % p + dsum p ((j + 1) / p) := by
  unfold dsum
  rw [Nat.digits_def' hp (Nat.succ_pos j), List.sum_cons]

theorem dsum_le {p : ℕ} (hp : 1 < p) (j : ℕ) : dsum p j ≤ j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rcases j with _ | k
    · simp [dsum]
    · rw [dsum_succ hp k]
      have h1 : (k + 1) / p < k + 1 := Nat.div_lt_self (Nat.succ_pos k) hp
      have h2 : dsum p ((k + 1) / p) ≤ (k + 1) / p := ih _ h1
      have h3 : ((k + 1) % p) + ((k + 1) / p) ≤ k + 1 := by
        have h4 := Nat.div_add_mod (k + 1) p
        have h5 : (k + 1) / p ≤ p * ((k + 1) / p) :=
          Nat.le_mul_of_pos_left _ (show 0 < p by omega)
        omega
      omega

theorem dsum_modEq {p : ℕ} (hp : 1 < p) (j : ℕ) : Nat.ModEq (p - 1) j (dsum p j) := by
  have hpm : Nat.ModEq (p - 1) p 1 :=
    ((Nat.modEq_iff_dvd' (n := p - 1) (a := 1) (b := p)
      (show 1 ≤ p by omega)).mpr (dvd_refl (p - 1))).symm
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rcases j with _ | k
    · rw [dsum_zero]
    · rw [dsum_succ hp k]
      have hA : Nat.ModEq (p - 1) (k + 1) ((k + 1) % p + p * ((k + 1) / p)) := by
        rw [Nat.ModEq]
        exact congrArg (· % (p - 1)) (Nat.mod_add_div (k + 1) p).symm
      refine hA.trans ?_
      have h1 : p * ((k + 1) / p) ≡ 1 * ((k + 1) / p) [MOD p - 1] := hpm.mul (Nat.ModEq.refl _)
      rw [one_mul] at h1
      exact Nat.ModEq.add (Nat.ModEq.refl _)
        (h1.trans (ih ((k + 1) / p) (Nat.div_lt_self (Nat.succ_pos k) hp)))

theorem dsum_eq_zero_iff {p : ℕ} (hp : 1 < p) (j : ℕ) : dsum p j = 0 ↔ j = 0 := by
  constructor
  · induction j using Nat.strong_induction_on with
    | h j ih =>
      intro h
      rcases j with _ | k
      · rfl
      · rw [dsum_succ hp k] at h
        have h0 : (k + 1) % p = 0 := by omega
        have h1 : dsum p ((k + 1) / p) = 0 := by omega
        have h2 := ih ((k + 1) / p) (Nat.div_lt_self (Nat.succ_pos k) hp) h1
        have h3 := Nat.div_add_mod (k + 1) p
        rw [h2, mul_zero, zero_add] at h3
        omega
  · rintro rfl
    exact dsum_zero p

theorem dsum_pos {p : ℕ} (hp : 1 < p) {j : ℕ} (hj : 1 ≤ j) : 1 ≤ dsum p j := by
  rcases Nat.eq_zero_or_pos (dsum p j) with h | h
  · exact absurd (dsum_eq_zero_iff hp j |>.mp h) (by omega)
  · exact h

end DSum


section Greedy

/-- **The greedy fill.**  Filling the capacities `capp p n i` from the bottom (digit `0` upwards)
until a total of `r` is reached.  The recursion is on the pair `(r, n)` via the measure `r + n`. -/
def Gg (p : ℕ) (hp : 2 ≤ p) (r n : ℕ) : ℕ :=
  if r = 0 then 0
  else if capp p n 0 = 0 then p * Gg p hp r (n / p)
  else if r ≤ capp p n 0 then r
  else capp p n 0 + p * Gg p hp (r - capp p n 0) (n / p)
termination_by r + n
decreasing_by
  all_goals simp_wf
  · -- second branch: `capp p n 0 = 0`, so `n / p < n`
    have hp1 : 1 < p := by omega
    have h0 : n % p = p - 1 := (capp_eq_zero_iff hp).mp ‹capp p n 0 = 0›
    have h1 : 1 ≤ n := by
      have hle : n % p ≤ n := Nat.mod_le n p
      omega
    have h2 : n / p < n := Nat.div_lt_self h1 hp1
    omega
  · -- fourth branch
    have h2 : n / p ≤ n := Nat.div_le_self n p
    have h3 : 1 ≤ capp p n 0 := by
      rcases Nat.eq_zero_or_pos (capp p n 0) with h | h
      · exact absurd h ‹¬capp p n 0 = 0›
      · exact h
    omega

lemma dsum_mul_p {p : ℕ} (hp : 1 < p) (j : ℕ) : dsum p (p * j) = dsum p j := by
  rcases eq_or_ne j 0 with h | h
  · rw [h, mul_zero, dsum_zero]
  · have hd := Nat.digits_add p hp 0 j (by omega) (Or.inr h)
    rw [zero_add] at hd
    simp only [dsum, hd, List.sum_cons, Nat.zero_add]

lemma dsum_eq_mod_add {p : ℕ} (hp : 1 < p) {j : ℕ} (hj : j ≠ 0) :
    dsum p j = j % p + dsum p (j / p) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact dsum_succ hp k

lemma dsum_add_mul {p : ℕ} (hp : 1 < p) {c X : ℕ} (hc : c < p) (h : c ≠ 0 ∨ X ≠ 0) :
    dsum p (c + p * X) = c + dsum p X := by
  have hd := Nat.digits_add p hp c X hc h
  simp only [dsum, hd, List.sum_cons]

/-- The digits of the greedy fill are within the capacities. -/
theorem Gg_digit_le {p : ℕ} (hp : 2 ≤ p) : ∀ (r n i : ℕ), r ≤ p - 1 →
    Gg p hp r n / p ^ i % p ≤ capp p n i := by
  intro r n
  induction r, n using Gg.induct p hp with
  | case1 n =>
      intro i _
      rw [Gg.eq_def, if_pos rfl]
      simp
  | case2 r n hr0 hc0 ih =>
      intro i hr
      rw [Gg.eq_def, if_neg hr0, if_pos hc0]
      cases i with
      | zero =>
          rw [pow_zero, Nat.div_one, Nat.mul_mod_right, capp_zero]
          exact Nat.zero_le _
      | succ j =>
          rw [pow_succ', Nat.mul_div_mul_left _ _ (by omega : 0 < p), ← capp_tail]
          exact ih j hr
  | case3 r n hr0 hc0 hle =>
      intro i hr
      rw [Gg.eq_def, if_neg hr0, if_neg hc0, if_pos hle]
      have hrp : r < p := by omega
      cases i with
      | zero =>
          rw [pow_zero, Nat.div_one, Nat.mod_eq_of_lt hrp]
          exact hle
      | succ j =>
          rw [Nat.div_eq_of_lt (lt_of_lt_of_le hrp (Nat.le_pow (a := p) (by omega : 0 < j + 1)))]
          exact Nat.zero_le _
  | case4 r n hr0 hc0 hnc ih =>
      intro i hr
      rw [Gg.eq_def, if_neg hr0, if_neg hc0, if_neg hnc]
      have hle : r - capp p n 0 ≤ p - 1 := by omega
      cases i with
      | zero =>
          rw [pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt (by have := capp_le p n 0; omega : capp p n 0 < p)]
      | succ j =>
          rw [pow_succ', ← Nat.div_div_eq_div_mul,
            Nat.add_mul_div_left (capp p n 0) _ (by omega : 0 < p),
            Nat.div_eq_of_lt (by have := capp_le p n 0; omega : capp p n 0 < p),
            Nat.zero_add, ← capp_tail]
          exact ih j hle

/-- The digit sum of the greedy fill is `r`. -/
theorem Gg_dsum {p : ℕ} (hp : 2 ≤ p) : ∀ (r n : ℕ), r ≤ p - 1 →
    dsum p (Gg p hp r n) = r := by
  intro r n
  induction r, n using Gg.induct p hp with
  | case1 n =>
      intro _
      rw [Gg.eq_def, if_pos rfl, dsum_zero]
  | case2 r n hr0 hc0 ih =>
      intro hr
      rw [Gg.eq_def, if_neg hr0, if_pos hc0, dsum_mul_p (by omega : 1 < p)]
      exact ih hr
  | case3 r n hr0 hc0 hle =>
      intro hr
      rw [Gg.eq_def, if_neg hr0, if_neg hc0, if_pos hle]
      rw [dsum, Nat.digits_of_lt p r hr0 (by omega), List.sum_singleton]
  | case4 r n hr0 hc0 hnc ih =>
      intro hr
      rw [Gg.eq_def, if_neg hr0, if_neg hc0, if_neg hnc]
      have hc1 : 1 ≤ capp p n 0 := by
        rcases Nat.eq_zero_or_pos (capp p n 0) with h | h
        · exact absurd h hc0
        · exact h
      have hcl : capp p n 0 < p := by have := capp_le p n 0; omega
      rw [dsum_add_mul (by omega : 1 < p) hcl (Or.inl (by omega))]
      rw [ih (by omega)]
      omega

/-- **The minimality of the greedy fill.**  If `j` is a digitwise submask of the capacities and
has digit sum at least `r`, then the greedy fill is at most `j`; if the digit sum is strictly
larger, then it is strictly smaller than `j`. -/
theorem Gg_le_lt {p : ℕ} (hp : 2 ≤ p) : ∀ (r n j : ℕ), r ≤ p - 1 →
    (∀ i, j / p ^ i % p ≤ capp p n i) →
    (r ≤ dsum p j → Gg p hp r n ≤ j) ∧ (r + 1 ≤ dsum p j → Gg p hp r n < j) := by
  intro r n
  induction r, n using Gg.induct p hp with
  | case1 n =>
      intro j hr hj
      rw [Gg.eq_def, if_pos rfl]
      refine ⟨fun _ => Nat.zero_le _, fun h => ?_⟩
      have hj0 : j ≠ 0 := fun h0 => by rw [h0, dsum_zero] at h; omega
      omega
  | case2 r n hr0 hc0 ih =>
      intro j hr hj
      rw [Gg.eq_def, if_neg hr0, if_pos hc0]
      have hj0 : j % p = 0 := by
        have h := hj 0
        simp only [pow_zero, Nat.div_one] at h
        have h2 : (p - 1) - n % p = 0 := by
          have hh := hc0
          simp only [capp, pow_zero, Nat.div_one] at hh
          exact hh
        omega
      have hds : dsum p j = dsum p (j / p) := by
        rcases eq_or_ne j 0 with h | h
        · rw [h, Nat.zero_div]
        · rw [dsum_eq_mod_add (by omega : 1 < p) h, hj0, Nat.zero_add]
      obtain ⟨ih1, ih2⟩ := ih (j / p) hr (fun i => by
        rw [capp_tail]
        simpa [Commons.Data.Nat.div_pow_succ_eq] using hj (i + 1))
      constructor
      · intro hd
        rw [hds] at hd
        calc p * Gg p hp r (n / p) ≤ p * (j / p) := Nat.mul_le_mul_left _ (ih1 hd)
          _ ≤ j := Nat.mul_div_le j p
      · intro hd
        rw [hds] at hd
        calc p * Gg p hp r (n / p) < p * (j / p) :=
              Nat.mul_lt_mul_of_pos_left (ih2 hd) (by omega)
          _ ≤ j := Nat.mul_div_le j p
  | case3 r n hr0 hc0 hle =>
      intro j hr hj
      rw [Gg.eq_def, if_neg hr0, if_neg hc0, if_pos hle]
      exact ⟨fun hd => le_trans hd (dsum_le (by omega : 1 < p) j),
        fun hd => lt_of_lt_of_le hd (dsum_le (by omega : 1 < p) j)⟩
  | case4 r n hr0 hc0 hnc ih =>
      intro j hr hj
      rw [Gg.eq_def, if_neg hr0, if_neg hc0, if_neg hnc]
      rcases eq_or_ne j 0 with h | hjz
      · subst h
        rw [dsum_zero]
        exact ⟨fun hd => absurd hd (by omega), fun hd => absurd hd (by omega)⟩
      obtain ⟨ih1, ih2⟩ := ih (j / p) (by omega) (fun i => by
        rw [capp_tail]
        simpa [Commons.Data.Nat.div_pow_succ_eq] using hj (i + 1))
      have hcj : j % p ≤ capp p n 0 := by
        have h := hj 0
        simp only [pow_zero, Nat.div_one] at h
        exact h
      have hck : capp p n 0 < p := by have := capp_le p n 0; omega
      have hds : dsum p j = j % p + dsum p (j / p) := dsum_eq_mod_add (by omega : 1 < p) hjz
      by_cases heq : j % p = capp p n 0
      · have hjdec : j = capp p n 0 + p * (j / p) := by
          have h := Nat.mod_add_div j p
          rw [heq] at h
          exact h.symm
        constructor
        · intro hd
          have hd' : r - capp p n 0 ≤ dsum p (j / p) := by
            rw [hds, heq] at hd
            omega
          rw [hjdec]
          exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (ih1 hd')) _
        · intro hd
          have hd' : (r - capp p n 0) + 1 ≤ dsum p (j / p) := by
            rw [hds, heq] at hd
            omega
          rw [hjdec]
          exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left (ih2 hd') (by omega)) _
      · have hlt : j % p < capp p n 0 := lt_of_le_of_ne hcj heq
        have hmain : ∀ _ : r ≤ dsum p j,
            capp p n 0 + p * Gg p hp (r - capp p n 0) (n / p) < j := by
          intro hd
          have hd' : (r - capp p n 0) + 1 ≤ dsum p (j / p) := by
            rw [hds] at hd
            omega
          have hX : Gg p hp (r - capp p n 0) (n / p) < j / p := ih2 hd'
          have hpX : p * Gg p hp (r - capp p n 0) (n / p) + p ≤ p * (j / p) := by
            have h1 : Gg p hp (r - capp p n 0) (n / p) + 1 ≤ j / p := hX
            calc p * Gg p hp (r - capp p n 0) (n / p) + p
                = p * (Gg p hp (r - capp p n 0) (n / p) + 1) := by ring
              _ ≤ p * (j / p) := Nat.mul_le_mul_left _ h1
          have hjdec : j = j % p + p * (j / p) := (Nat.mod_add_div j p).symm
          omega
        exact ⟨fun hd => le_of_lt (hmain hd), fun hd => hmain (by omega)⟩

/-- The non-strict form of the greedy minimality. -/
theorem Gg_le {p : ℕ} (hp : 2 ≤ p) (r n j : ℕ) (hr : r ≤ p - 1)
    (hj : ∀ i, j / p ^ i % p ≤ capp p n i) (hd : r ≤ dsum p j) : Gg p hp r n ≤ j :=
  (Gg_le_lt hp r n j hr hj).1 hd

/-- The strict form of the greedy minimality. -/
theorem Gg_lt {p : ℕ} (hp : 2 ≤ p) (r n j : ℕ) (hr : r ≤ p - 1)
    (hj : ∀ i, j / p ^ i % p ≤ capp p n i) (hd : r + 1 ≤ dsum p j) : Gg p hp r n < j :=
  (Gg_le_lt hp r n j hr hj).2 hd

/-- The greedy fill for the full target `p - 1`: the least positive multiple of `p - 1` all of
whose digits fit into the capacities of `n`. -/
def greedy (p : ℕ) (hp : 2 ≤ p) (n : ℕ) : ℕ := Gg p hp (p - 1) n

lemma greedy_digit_le {p : ℕ} (hp : 2 ≤ p) (n i : ℕ) :
    greedy p hp n / p ^ i % p ≤ capp p n i :=
  Gg_digit_le hp (p - 1) n i le_rfl

lemma greedy_dsum {p : ℕ} (hp : 2 ≤ p) (n : ℕ) : dsum p (greedy p hp n) = p - 1 :=
  Gg_dsum hp (p - 1) n le_rfl

lemma greedy_le {p : ℕ} (hp : 2 ≤ p) (n j : ℕ)
    (hj : ∀ i, j / p ^ i % p ≤ capp p n i) (hd : p - 1 ≤ dsum p j) : greedy p hp n ≤ j :=
  Gg_le hp (p - 1) n j le_rfl hj hd

lemma greedy_pos {p : ℕ} (hp : 2 ≤ p) (n : ℕ) : 1 ≤ greedy p hp n := by
  have h := greedy_dsum hp n
  have hp1 : 1 ≤ p - 1 := by omega
  rcases Nat.eq_zero_or_pos (greedy p hp n) with h0 | h0
  · rw [h0, dsum_zero] at h
    omega
  · exact h0

lemma greedy_dvd {p : ℕ} (hp : 2 ≤ p) (n : ℕ) : (p - 1) ∣ greedy p hp n := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have h := dsum_modEq (p := p) (by omega : 1 < p) (greedy p hp n)
  rw [Nat.ModEq] at h
  rw [greedy_dsum hp n, Nat.mod_self] at h
  exact h

end Greedy

end ZagierHoffmanPositiveChar
