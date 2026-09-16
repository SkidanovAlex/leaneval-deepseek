import Submission.ZagierHoffmanProof.PrimeRed

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# The dominance lemma for the prime-`q` recursion

`T y = y + j_min(y)` and `τ y = T y / p`.  This module proves
* `τ y ≤ y` (the greedy fill is at most `(p-1)·y`),
* the scaling `T (p z) = p T z` and hence `τ (T y) = T (τ y)` and `T^i(u) = p^i τ^i(u)`,
* the reduction `δ = τ(x+j) - τ x ∈ A(τ x)`, and
* the **dominance**: for every admissible shift `j` at `x`, `T^i(T x) ≤ T^i(x + j)` for all `i`.
-/

namespace ZagierHoffmanPositiveChar

section Bound

/-- The arithmetic core of the bound: `c + (r-c)(n + p - s) ≤ r(n+1)` for `c = p-1-s`. -/
lemma arith_bound {p n r : ℕ} (hp : 2 ≤ p) (hr : r ≤ p - 1)
    (h1 : capp p n 0 = p - 1 - n % p) (h2 : capp p n 0 ≤ r) :
    capp p n 0 + (r - capp p n 0) * (n + (p - n % p)) ≤ r * (n + 1) := by
  have hsp : n % p < p := Nat.mod_lt n (by omega)
  have hsle : n % p ≤ n := Nat.mod_le n p
  have hcast : ((r - capp p n 0 : ℕ) : ℤ) = (r : ℤ) - (capp p n 0 : ℤ) :=
    Nat.cast_sub h2
  have hcastp : ((p - n % p : ℕ) : ℤ) = (p : ℤ) - (n % p : ℤ) :=
    Nat.cast_sub (Nat.le_of_lt hsp)
  have hA : ((capp p n 0 : ℕ) : ℤ) = (p : ℤ) - 1 - (n % p : ℤ) := by
    rw [h1]
    push_cast [Nat.cast_sub (show n % p ≤ p - 1 by omega), Nat.cast_sub (show 1 ≤ p by omega)]
    ring
  have hsZ : ((n % p : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hsle
  have hrZ : (r : ℤ) ≤ (p : ℤ) - 1 := by omega
  have hcZ : (0 : ℤ) ≤ ((capp p n 0 : ℕ) : ℤ) := by positivity
  have hfac : (0 : ℤ) ≤ ((capp p n 0 : ℕ) : ℤ) * ((n : ℤ) + (p : ℤ) - 1 - (n % p : ℤ) - (r : ℤ)) :=
    mul_nonneg hcZ (by omega)
  have goalZ : ((capp p n 0 + (r - capp p n 0) * (n + (p - n % p)) : ℕ) : ℤ)
      ≤ ((r * (n + 1) : ℕ) : ℤ) := by
    push_cast [hcast, hcastp]
    nlinarith [hA, hfac, hcZ]
  exact_mod_cast goalZ

/-- **The greedy fill is small.**  For `r ≤ p-1`, `Gg p hp r n ≤ r (n+1)`. -/
theorem Gg_le_mul {p : ℕ} (hp : 2 ≤ p) : ∀ (r n : ℕ), r ≤ p - 1 → Gg p hp r n ≤ r * (n + 1) := by
  intro r n
  induction r, n using Gg.induct p hp with
  | case1 n => intro hr; rw [Gg.eq_def, if_pos rfl]; omega
  | case2 r n hr0 hc0 ih =>
      intro hr
      rw [Gg.eq_def, if_neg hr0, if_pos hc0]
      have h1 := ih hr
      have hs : n % p = p - 1 := (capp_eq_zero_iff hp).mp hc0
      have h2 : p * (n / p + 1) = n + 1 := by
        have h3 : n = p * (n / p) + (p - 1) := by
          rw [← hs]; exact (Nat.div_add_mod n p).symm
        conv_rhs => rw [h3]
        rw [Nat.mul_add, mul_one]
        omega
      calc p * Gg p hp r (n / p) ≤ p * (r * (n / p + 1)) := Nat.mul_le_mul_left _ h1
        _ = r * (p * (n / p + 1)) := by ring
        _ = r * (n + 1) := by rw [h2]
  | case3 r n hr0 hc0 hle =>
      intro hr
      rw [Gg.eq_def, if_neg hr0, if_neg hc0, if_pos hle]
      exact Nat.le_mul_of_pos_right r (by omega)
  | case4 r n hr0 hc0 hnc ih =>
      intro hr
      rw [Gg.eq_def, if_neg hr0, if_neg hc0, if_neg hnc]
      have hc0' : capp p n 0 < r := by omega
      have h1 := ih (by omega)
      have h2 : p * (n / p + 1) = n + (p - n % p) := by
        have h4 : n % p ≤ p := Nat.le_of_lt (Nat.mod_lt n (by omega : 0 < p))
        have h6 : n - n % p = p * (n / p) := by
          have h7 : p * (n / p) + n % p = n := Nat.div_add_mod n p
          have h8 : n % p ≤ p * (n / p) + n % p := Nat.le_add_left _ _
          omega
        have hs0 : n % p ≤ n := Nat.mod_le n p
        have h5 : n + (p - n % p) = (n - n % p) + p := by omega
        rw [h5, h6, Nat.mul_add, mul_one]
      have hs : n % p ≤ n := Nat.mod_le n p
      have hsp : n % p < p := Nat.mod_lt n (by omega)
      have hc : capp p n 0 = p - 1 - n % p := capp_zero p n
      have hcr : capp p n 0 ≤ r := by omega
      have hsub : r - capp p n 0 + capp p n 0 = r := Nat.sub_add_cancel hcr
      calc capp p n 0 + p * Gg p hp (r - capp p n 0) (n / p)
          ≤ capp p n 0 + p * ((r - capp p n 0) * (n / p + 1)) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ h1) _
        _ = capp p n 0 + (r - capp p n 0) * (p * (n / p + 1)) := by ring
        _ = capp p n 0 + (r - capp p n 0) * (n + (p - n % p)) := by rw [h2]
        _ ≤ r * (n + 1) := arith_bound hp hr hc hcr

end Bound

section Scale

/-- `T(p z) = p T(z)`: the greedy fill scales with `p`. -/
theorem greedy_mul_p {p : ℕ} (hp : 2 ≤ p) {z : ℕ} (hz : 1 ≤ z) :
    greedy p hp (p * z - 1) = p * greedy p hp (z - 1) := by
  have hmul : p * (z - 1) = p * z - p := by
    rw [Nat.mul_sub_left_distrib, mul_one]
  have hmod : (p * z - 1) % p = p - 1 := by
    have h : p * z - 1 = p * (z - 1) + (p - 1) := by
      rw [hmul]
      have hz1 : p ≤ p * z := Nat.le_mul_of_pos_right p hz
      omega
    rw [h, Nat.mul_add_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega : p - 1 < p)
  have hdiv : (p * z - 1) / p = z - 1 := by
    have h : p * z - 1 = p * (z - 1) + (p - 1) := by
      rw [hmul]
      have hz1 : p ≤ p * z := Nat.le_mul_of_pos_right p hz
      omega
    rw [h, Nat.mul_add_div (by omega : 0 < p), Nat.div_eq_of_lt (by omega : p - 1 < p),
      Nat.add_zero]
  have hc : capp p (p * z - 1) 0 = 0 := by
    rw [capp_zero, hmod]; omega
  have h1 : greedy p hp (p * z - 1) = Gg p hp (p - 1) (p * z - 1) := rfl
  have h2 : greedy p hp (z - 1) = Gg p hp (p - 1) (z - 1) := rfl
  rw [h1, Gg.eq_def, if_neg (by omega : ¬ (p - 1 = 0)), if_pos hc, hdiv, ← h2]

/-- `T y = y + j_min(y)` as a function of `y ≥ 1`. -/
def TT (p : ℕ) (hp : 2 ≤ p) (x : ℕ) : ℕ := Tg p hp (x - 1)

/-- `τ y = T y / p`. -/
def tt (p : ℕ) (hp : 2 ≤ p) (x : ℕ) : ℕ := TT p hp x / p

/-- `T (p z) = p · T z`. -/
theorem TT_mul_p {p : ℕ} (hp : 2 ≤ p) {z : ℕ} (hz : 1 ≤ z) :
    TT p hp (p * z) = p * TT p hp z := by
  unfold TT Tg
  rw [greedy_mul_p hp hz]
  have h : z - 1 + 1 = z := Nat.sub_add_cancel hz
  have h2 : p * z - 1 + 1 = p * z :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))
  rw [h2, h]
  ring

lemma TT_pos' {p : ℕ} (hp : 2 ≤ p) (y : ℕ) : 0 < TT p hp y := by
  show 0 < Tg p hp (y - 1)
  unfold Tg
  omega

lemma dvd_TT {p : ℕ} (hp : 2 ≤ p) {x : ℕ} (hx : 1 ≤ x) : p ∣ TT p hp x := by
  show p ∣ Tg p hp (x - 1)
  exact dvd_Tg hp (x - 1)

lemma TT_eq {p : ℕ} (hp : 2 ≤ p) {x : ℕ} (hx : 1 ≤ x) :
    TT p hp x = p * tt p hp x :=
  (Nat.mul_div_cancel' (dvd_TT hp hx)).symm

lemma p_le_TT {p : ℕ} (hp : 2 ≤ p) {x : ℕ} (hx : 1 ≤ x) : p ≤ TT p hp x := by
  show p ≤ Tg p hp (x - 1)
  unfold Tg
  have h3 : p - 1 ≤ greedy p hp (x - 1) := by
    have h4 := greedy_dsum hp (x - 1)
    have h5 := dsum_le (by omega : 1 < p) (greedy p hp (x - 1))
    omega
  omega

lemma TT_pos {p : ℕ} (hp : 2 ≤ p) {x : ℕ} (hx : 1 ≤ x) : 1 ≤ TT p hp x :=
  le_trans (by omega : 1 ≤ p) (p_le_TT hp hx)

lemma tt_pos {p : ℕ} (hp : 2 ≤ p) {x : ℕ} (hx : 1 ≤ x) : 1 ≤ tt p hp x := by
  have h := p_le_TT hp hx
  have hp0 : 0 < p := by omega
  unfold tt
  exact Nat.le_div_iff_mul_le hp0 |>.mpr (by simpa using h)

/-- `τ (p z) = T z`. -/
theorem tt_mul_p {p : ℕ} (hp : 2 ≤ p) {z : ℕ} (hz : 1 ≤ z) :
    tt p hp (p * z) = TT p hp z := by
  unfold tt
  rw [TT_mul_p hp hz, Nat.mul_div_cancel_left _ (by omega : 0 < p)]

/-- `τ (T y) = T (τ y)`. -/
theorem tau_TT {p : ℕ} (hp : 2 ≤ p) {x : ℕ} (hx : 1 ≤ x) :
    tt p hp (TT p hp x) = TT p hp (tt p hp x) := by
  have h1 : TT p hp x = p * tt p hp x := TT_eq hp hx
  have h2 : 1 ≤ tt p hp x := tt_pos hp hx
  rw [h1, tt_mul_p hp h2]

/-- `T (p^a z) = p^a T z`. -/
theorem TT_pow_mul {p : ℕ} (hp : 2 ≤ p) (a : ℕ) {z : ℕ} (hz : 1 ≤ z) :
    TT p hp (p ^ a * z) = p ^ a * TT p hp z := by
  induction a with
  | zero => simp
  | succ a ih =>
      have h1 : p ^ (a + 1) * z = p * (p ^ a * z) := by rw [pow_succ']; ring
      have hp0 : 0 < p := by omega
      have h2 : 1 ≤ p ^ a * z := by
        have h3 : 1 ≤ p ^ a := Nat.one_le_pow a p hp0
        calc 1 = 1 * 1 := by ring
          _ ≤ p ^ a * z := Nat.mul_le_mul h3 hz
      rw [h1, TT_mul_p hp h2, ih]
      ring

lemma iterate_tt_pos {p : ℕ} (hp : 2 ≤ p) {u : ℕ} (hu : 1 ≤ u) (i : ℕ) :
    1 ≤ Nat.iterate (tt p hp) i u := by
  induction i with
  | zero => exact hu
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact tt_pos hp ih

lemma iterate_TT_pos {p : ℕ} (hp : 2 ≤ p) {u : ℕ} (hu : 1 ≤ u) (i : ℕ) :
    1 ≤ Nat.iterate (TT p hp) i u := by
  induction i with
  | zero => exact hu
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact TT_pos hp ih

/-- `T^i(u) = p^i · τ^i(u)`. -/
theorem pow_tau {p : ℕ} (hp : 2 ≤ p) : ∀ (i u : ℕ), 1 ≤ u →
    Nat.iterate (TT p hp) i u = p ^ i * Nat.iterate (tt p hp) i u := by
  intro i
  induction i with
  | zero => intro u hu; simp
  | succ i ih =>
      intro u hu
      have hT := ih u hu
      have hposTau : 1 ≤ Nat.iterate (tt p hp) i u := iterate_tt_pos hp hu i
      rw [Function.iterate_succ_apply', hT, TT_pow_mul hp i hposTau,
        TT_eq hp hposTau, Function.iterate_succ_apply']
      ring

/-- **`τ y ≤ y`.** -/
theorem tau_le_self {p : ℕ} (hp : 2 ≤ p) {x : ℕ} (hx : 1 ≤ x) : tt p hp x ≤ x := by
  have hG := Gg_le_mul hp (p - 1) (x - 1) le_rfl
  have hx1 : x - 1 + 1 = x := Nat.sub_add_cancel hx
  rw [hx1] at hG
  have hT : TT p hp x ≤ p * x := by
    show Tg p hp (x - 1) ≤ p * x
    unfold Tg
    rw [hx1]
    have h2 : x + (p - 1) * x = p * x := by
      have h4 : p - 1 + 1 = p := Nat.sub_add_cancel (by omega : 1 ≤ p)
      nlinarith [h4]
    have h3 : x + greedy p hp (x - 1) ≤ x + (p - 1) * x := Nat.add_le_add_left hG x
    omega
  unfold tt
  exact Nat.div_le_of_le_mul hT

end Scale

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

section Dominance

/-- The admissible shifts at `x`: `j ≥ 1`, `(p-1) ∣ j` and no carry when adding `j` to `x-1`. -/
def Adm (p : ℕ) (x j : ℕ) : Prop := 1 ≤ j ∧ noCarry p j (x - 1) ∧ (p - 1) ∣ j

/-- RED in the `Adm` language: the reduction step is again admissible, at `τ x`. -/
theorem red_Adm {p : ℕ} (hp : 2 ≤ p) {x j : ℕ} (hx : 1 ≤ x) (h : Adm p x j) :
    Adm p (tt p hp x) (tt p hp (x + j) - tt p hp x) := by
  obtain ⟨hj, hnc, hdvd⟩ := h
  obtain ⟨h1, h2, h3⟩ := red_delta hp (x - 1) j hj hnc hdvd
  have e : x - 1 + j = x + j - 1 := by omega
  rw [e] at h1 h2 h3
  exact ⟨h2, h3, h1⟩

/-- In the fixed-point case `τ x = x`, the iterates of `τ` at `T x` are constant. -/
lemma iterate_tt_TT_of_fix {p : ℕ} (hp : 2 ≤ p) {x : ℕ} (hx : 1 ≤ x)
    (hfix : tt p hp x = x) (i : ℕ) :
    Nat.iterate (tt p hp) i (TT p hp x) = TT p hp x := by
  induction i with
  | zero => rw [Function.iterate_zero_apply]
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, tau_TT hp hx, hfix]

/-- Iterates of a `τ`-fixed point are constant. -/
lemma iterate_tt_of_fix {p : ℕ} (hp : 2 ≤ p) {y : ℕ} (hy : 1 ≤ y)
    (hfix : tt p hp y = y) (i : ℕ) : Nat.iterate (tt p hp) i y = y := by
  induction i with
  | zero => rw [Function.iterate_zero_apply]
  | succ i ih => rw [Function.iterate_succ_apply', ih, hfix]

/-- The fixed-point case of the dominance: secondary strong induction on the shift. -/
lemma dominates_tau_fix {p : ℕ} (hp : 2 ≤ p) {x : ℕ} (hx : 1 ≤ x) (hfix : tt p hp x = x) :
    ∀ (j : ℕ), Adm p x j →
      ∀ i : ℕ, Nat.iterate (tt p hp) i (TT p hp x) ≤ Nat.iterate (tt p hp) i (x + j) := by
  have hconst : ∀ i, Nat.iterate (tt p hp) i (TT p hp x) = TT p hp x :=
    fun i => iterate_tt_TT_of_fix hp hx hfix i
  intro j
  induction j using Nat.strong_induction_on with
  | h j ihj =>
    intro hadm i
    have hTx_le : TT p hp x ≤ x + j := by
      obtain ⟨hj, hnc, hdvd⟩ := hadm
      have hgle : greedy p hp (x - 1) ≤ j := greedy_le hp (x - 1) j
        (fun k => (noCarry_iff_capp (p := p) (n := x - 1) (j := j) hp).mpr hnc k)
        (le_dsum_of_dvd hp hdvd hj)
      show Tg p hp (x - 1) ≤ x + j
      unfold Tg
      omega
    set δ := tt p hp (x + j) - tt p hp x with hδdef
    have hδadm : Adm p x δ := by
      simpa [hδdef, hfix] using red_Adm hp hx hadm
    have hδ1 : 1 ≤ δ := hδadm.1
    have hle : tt p hp x ≤ tt p hp (x + j) := by
      have h2 : δ = tt p hp (x + j) - tt p hp x := rfl
      omega
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      rw [Function.iterate_zero_apply, Function.iterate_zero_apply]
      exact hTx_le
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      by_cases heq : δ = j
      · have htau : tt p hp (x + j) = x + j := by
          have h4 : δ = tt p hp (x + j) - tt p hp x := rfl
          rw [hfix] at h4
          omega
        rw [hconst (i' + 1), iterate_tt_of_fix hp (by omega) htau (i' + 1)]
        exact hTx_le
      · have hlt : δ < j := by
          have h4 : δ = tt p hp (x + j) - tt p hp x := rfl
          have h5 : tt p hp (x + j) ≤ x + j := tau_le_self hp (by omega)
          omega
        have hIH := ihj δ hlt hδadm
        have hτ2 : tt p hp (x + j) = tt p hp x + δ := by
          have h4 : δ = tt p hp (x + j) - tt p hp x := rfl
          omega
        have hgoal : TT p hp x ≤ Nat.iterate (tt p hp) i' (x + δ) := by
          have h5 := hIH i'
          rw [hconst i'] at h5
          exact h5
        rw [hconst (i' + 1), Function.iterate_succ_apply, hτ2, hfix]
        exact hgoal

/-- **The dominance lemma** (in `τ`-form): for every admissible shift `j` at `x`,
`τ^i(T x) ≤ τ^i(x + j)` for all `i`. -/
theorem dominates_tau {p : ℕ} (hp : 2 ≤ p) :
    ∀ (x : ℕ), 1 ≤ x → ∀ (j : ℕ), Adm p x j →
      ∀ i : ℕ, Nat.iterate (tt p hp) i (TT p hp x) ≤ Nat.iterate (tt p hp) i (x + j) := by
  intro x
  induction x using Nat.strong_induction_on with
  | h x ih =>
    intro hx j hadm i
    have hTx_le : TT p hp x ≤ x + j := by
      obtain ⟨hj, hnc, hdvd⟩ := hadm
      have hgle : greedy p hp (x - 1) ≤ j := greedy_le hp (x - 1) j
        (fun k => (noCarry_iff_capp (p := p) (n := x - 1) (j := j) hp).mpr hnc k)
        (le_dsum_of_dvd hp hdvd hj)
      show Tg p hp (x - 1) ≤ x + j
      unfold Tg
      omega
    by_cases hfix : tt p hp x = x
    · exact dominates_tau_fix hp hx hfix j hadm i
    · have hlt : tt p hp x < x := lt_of_le_of_ne (tau_le_self hp hx) hfix
      have hx' : 1 ≤ tt p hp x := tt_pos hp hx
      have hδadm : Adm p (tt p hp x) (tt p hp (x + j) - tt p hp x) := red_Adm hp hx hadm
      have hle : tt p hp x ≤ tt p hp (x + j) := by
        obtain ⟨h1, -, -⟩ := hδadm
        omega
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · subst hi0
        rw [Function.iterate_zero_apply, Function.iterate_zero_apply]
        exact hTx_le
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        have hIH := ih (tt p hp x) hlt hx' (tt p hp (x + j) - tt p hp x) hδadm i'
        have hτ : tt p hp (TT p hp x) = TT p hp (tt p hp x) := tau_TT hp hx
        have hτ2 : tt p hp (x + j) = tt p hp x + (tt p hp (x + j) - tt p hp x) := by omega
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hτ, hτ2]
        exact hIH

/-- **The dominance lemma** (in `T`-form). -/
theorem dominates_TT {p : ℕ} (hp : 2 ≤ p) {x j : ℕ} (hx : 1 ≤ x) (h : Adm p x j) (i : ℕ) :
    Nat.iterate (TT p hp) i (TT p hp x) ≤ Nat.iterate (TT p hp) i (x + j) := by
  have h1 := dominates_tau hp x hx j h i
  rw [pow_tau hp i (TT p hp x) (TT_pos hp hx), pow_tau hp i (x + j) (by omega)]
  exact Nat.mul_le_mul_left _ h1

end Dominance

end ZagierHoffmanPositiveChar
