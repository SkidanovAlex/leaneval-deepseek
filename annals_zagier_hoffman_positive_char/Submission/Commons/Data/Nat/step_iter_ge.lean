import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.NormNum.Ineq

namespace Commons.Data.Nat


theorem exists_testBit_false (u : ℕ) : ∃ k, u.testBit k = false :=
  ⟨u + 1, Nat.testBit_lt_two_pow (by have := Nat.lt_two_pow_self (n := u + 1); omega)⟩

/-- `trail u` is the least index `k` with `u.testBit k = false`; equivalently the number of
trailing ones in the binary expansion of `u`. -/
def trail (u : ℕ) : ℕ := Nat.find (exists_testBit_false u)

theorem trail_spec (u : ℕ) : u.testBit (trail u) = false := Nat.find_spec (exists_testBit_false u)

theorem trail_min {u j : ℕ} (h : j < trail u) : u.testBit j = true := by
  cases hb : u.testBit j with
  | false => exact absurd (Nat.find_min' (exists_testBit_false u) hb) (not_le.mpr h)
  | true => rfl

theorem and_two_pow_sub_one_trail (u : ℕ) :
    u &&& (2 ^ trail u - 1) = 2 ^ trail u - 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases h : i < trail u
  · simp [h, trail_min h]
  · simp [h]

theorem mod_two_pow_trail (u : ℕ) : u % 2 ^ trail u = 2 ^ trail u - 1 := by
  rw [← Nat.and_two_pow_sub_one_eq_mod]
  exact and_two_pow_sub_one_trail u

theorem trail_decomp (u : ℕ) : u = 2 ^ trail u * (u / 2 ^ trail u) + (2 ^ trail u - 1) := by
  have hdiv := Nat.div_add_mod u (2 ^ trail u)
  have hmod := mod_two_pow_trail u
  rw [hmod] at hdiv
  exact hdiv.symm

theorem succ_eq_mul (u : ℕ) : u + 1 = 2 ^ trail u * (u / 2 ^ trail u + 1) := by
  conv_lhs => rw [trail_decomp u]
  rw [Nat.mul_add, Nat.mul_one]
  have hpos : 0 < 2 ^ trail u := Nat.two_pow_pos _
  omega

theorem div_two_pow_trail_mod_two (u : ℕ) : (u / 2 ^ trail u) % 2 = 0 := by
  have h := trail_spec u
  rw [Nat.testBit_eq_decide_div_mod_eq] at h
  rcases Nat.mod_two_eq_zero_or_one (u / 2 ^ trail u) with h2 | h2
  · exact h2
  · exfalso
    rw [h2] at h
    exact absurd h (by decide)

theorem testBit_succ_trail_lt {u j : ℕ} (h : j < trail u) : (u + 1).testBit j = false := by
  rw [succ_eq_mul u, Nat.testBit_two_pow_mul]
  simp only [Nat.not_le.mpr h, decide_false, Bool.false_and]

theorem testBit_succ_trail_self (u : ℕ) : (u + 1).testBit (trail u) = true := by
  rw [succ_eq_mul u, Nat.testBit_two_pow_mul]
  simp only [le_refl, decide_true, Bool.true_and, Nat.sub_self, Nat.testBit_zero]
  rw [decide_eq_true_iff]
  have := div_two_pow_trail_mod_two u
  omega

theorem div_two_succ_of_mod_two_eq_zero {m : ℕ} (hm : m % 2 = 0) : (m + 1) / 2 = m / 2 := by
  have h : m = 2 * (m / 2) := by
    have := Nat.div_add_mod m 2
    omega
  conv_lhs => rw [h]
  rw [show 2 * (m / 2) + 1 = 1 + 2 * (m / 2) by omega]
  rw [Nat.add_mul_div_left 1 (m / 2) (by norm_num : 0 < 2)]
  rw [Nat.div_eq_of_lt (by norm_num : 1 < 2)]
  simp

theorem testBit_succ_of_mod_two_eq_zero {m k : ℕ} (hm : m % 2 = 0) :
    (m + 1).testBit (k + 1) = m.testBit (k + 1) := by
  rw [Nat.testBit_succ, Nat.testBit_succ, div_two_succ_of_mod_two_eq_zero hm]

theorem testBit_succ_trail_gt {u j : ℕ} (h : trail u < j) : (u + 1).testBit j = u.testBit j := by
  rw [succ_eq_mul u, Nat.testBit_two_pow_mul]
  simp only [le_of_lt h, decide_true, Bool.true_and]
  conv_rhs => rw [trail_decomp u]
  rw [Nat.testBit_two_pow_mul_add _ (by have := Nat.two_pow_pos (trail u); omega)]
  simp only [Nat.not_lt.mpr (le_of_lt h), if_false]
  obtain ⟨m, hm⟩ : ∃ m, j - trail u = m + 1 := ⟨j - trail u - 1, by omega⟩
  rw [hm]
  exact testBit_succ_of_mod_two_eq_zero (div_two_pow_trail_mod_two u)

theorem or_succ_eq_or_two_pow_trail (u : ℕ) : u ||| (u + 1) = u ||| 2 ^ trail u := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_lor, Nat.testBit_lor, Nat.testBit_two_pow]
  by_cases h1 : i < trail u
  · rw [trail_min h1]
    simp [testBit_succ_trail_lt h1]
  · by_cases h2 : i = trail u
    · subst h2
      rw [trail_spec u, testBit_succ_trail_self u]
      simp
    · have h3 : trail u < i := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
      rw [testBit_succ_trail_gt h3]
      simp [Ne.symm h2]

theorem testBit_of_land_eq_left {u w i : ℕ} (h : u &&& w = u) (hi : u.testBit i = true) :
    w.testBit i = true := by
  have hc := congrArg (fun x => x.testBit i) h
  simp only [Nat.testBit_and] at hc
  rw [hi] at hc
  simpa using hc.symm

theorem le_of_land_eq_left {p q : ℕ} (h : p &&& q = p) : p ≤ q :=
  Nat.le_of_testBit (fun _ hi => testBit_of_land_eq_left h hi)

theorem trail_le_of_land {u w : ℕ} (h : u &&& w = u) : trail u ≤ trail w := by
  by_contra hc
  have hlt : trail w < trail u := not_le.mp hc
  have hu : u.testBit (trail w) = true := trail_min hlt
  have hw : w.testBit (trail w) = true := testBit_of_land_eq_left h hu
  rw [trail_spec w] at hw
  exact Bool.noConfusion hw

theorem or_succ_land_submask {u w : ℕ} (h : u &&& w = u) :
    (u ||| (u + 1)) &&& (w ||| (w + 1)) = u ||| (u + 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_lor]
  by_cases h1 : i < trail u
  · have hu : u.testBit i = true := trail_min h1
    have hw : w.testBit i = true := testBit_of_land_eq_left h hu
    simp [hu, hw]
  · by_cases h2 : i = trail u
    · subst h2
      have hu : u.testBit (trail u) = false := trail_spec u
      have hsu : (u + 1).testBit (trail u) = true := testBit_succ_trail_self u
      rcases lt_or_eq_of_le (trail_le_of_land h) with hlt | heq
      · have hw : w.testBit (trail u) = true := trail_min hlt
        simp [hu, hsu, hw]
      · have htw : (w + 1).testBit (trail w) = true := testBit_succ_trail_self w
        rw [← heq] at htw
        simp [hu, hsu, htw]
    · have h3 : trail u < i := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
      simp only [testBit_succ_trail_gt h3]
      cases hu : u.testBit i with
      | false => simp
      | true =>
        have hw : w.testBit i = true := testBit_of_land_eq_left h hu
        simp [hw]

theorem and_div_two_eq_zero {a b : ℕ} (h : a &&& b = 0) : a / 2 &&& (b / 2) = 0 := by
  have hc := congrArg (fun x => x / 2) h
  rw [Nat.and_div_two, Nat.zero_div] at hc
  exact hc

theorem two_mul_lor (x y : ℕ) : 2 * x ||| 2 * y = 2 * (x ||| y) := by
  have h := Nat.lor_bit false x false y
  simpa using h

theorem two_mul_lor_two_mul_succ (x y : ℕ) : 2 * x ||| (2 * y + 1) = 2 * (x ||| y) + 1 := by
  have h := Nat.lor_bit false x true y
  simpa using h

theorem two_mul_succ_lor_two_mul (x y : ℕ) : (2 * x + 1) ||| (2 * y) = 2 * (x ||| y) + 1 := by
  have h := Nat.lor_bit true x false y
  simpa using h

theorem add_eq_lor_of_land_eq_zero (a b : ℕ) (h : a &&& b = 0) : a + b = a ||| b := by
  revert b
  refine Nat.strong_induction_on a ?_
  intro a ih b h
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp
  · have hd : a / 2 &&& (b / 2) = 0 := and_div_two_eq_zero h
    have hih : a / 2 + b / 2 = a / 2 ||| b / 2 :=
      ih (a / 2) (Nat.div_lt_self ha (by norm_num)) (b / 2) hd
    have ha' : a = 2 * (a / 2) + a % 2 := by
      have := Nat.div_add_mod a 2; omega
    have hb' : b = 2 * (b / 2) + b % 2 := by
      have := Nat.div_add_mod b 2; omega
    rcases Nat.mod_two_eq_zero_or_one a with ha2 | ha2 <;>
      rcases Nat.mod_two_eq_zero_or_one b with hb2 | hb2
    · rw [ha', hb', ha2, hb2]
      simp only [add_zero]
      rw [two_mul_lor, ← hih]
      omega
    · rw [ha', hb', ha2, hb2]
      simp only [add_zero]
      rw [two_mul_lor_two_mul_succ, ← hih]
      omega
    · rw [ha', hb', ha2, hb2]
      simp only [add_zero]
      rw [two_mul_succ_lor_two_mul, ← hih]
      omega
    · exfalso
      have hodd := (Nat.and_mod_two_eq_one (a := a) (b := b)).mpr ⟨ha2, hb2⟩
      rw [h] at hodd
      omega

theorem and_eq_self_of_land_eq_zero {a b : ℕ} (h : a &&& b = 0) : a &&& (a + b) = a := by
  rw [add_eq_lor_of_land_eq_zero a b h, Nat.and_or_distrib_left, Nat.and_self, h, Nat.or_zero]

theorem succ_land_self_of_mod_two_eq_zero {a : ℕ} (h : a % 2 = 0) : (a + 1) &&& a = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  match i with
  | 0 =>
    rw [Nat.testBit_zero, Nat.testBit_zero]
    have h1 : (a + 1) % 2 = 1 := by omega
    simp [h1, h]
  | k + 1 =>
    rw [testBit_succ_of_mod_two_eq_zero h, Bool.and_self]

theorem or_two_pow_eq_add (u : ℕ) : u ||| 2 ^ trail u = u + 2 ^ trail u := by
  have h : u &&& 2 ^ trail u = 0 := by
    rw [Nat.and_two_pow, trail_spec u]
    simp
  exact (add_eq_lor_of_land_eq_zero u (2 ^ trail u) h).symm

theorem sub_land_succ (u : ℕ) : (u + 1) - ((u + 1) &&& u) = 2 ^ trail u := by
  have hq : (u + 1) / 2 ^ trail u = u / 2 ^ trail u + 1 := by
    rw [succ_eq_mul u, Nat.mul_div_cancel_left (u / 2 ^ trail u + 1) (Nat.two_pow_pos _)]
  have hdiv : ((u + 1) &&& u) / 2 ^ trail u = u / 2 ^ trail u := by
    rw [Nat.and_div_two_pow, hq, succ_land_self_of_mod_two_eq_zero (div_two_pow_trail_mod_two u)]
  have hmod : ((u + 1) &&& u) % 2 ^ trail u = 0 := by
    rw [Nat.and_mod_two_pow, mod_two_pow_trail u]
    have : (u + 1) % 2 ^ trail u = 0 := by
      rw [succ_eq_mul u, Nat.mul_mod_right]
    rw [this, Nat.zero_and]
  have hkey : (u + 1) &&& u = 2 ^ trail u * (u / 2 ^ trail u) := by
    conv_lhs => rw [← Nat.div_add_mod ((u + 1) &&& u) (2 ^ trail u)]
    rw [hdiv, hmod, add_zero]
  rw [hkey, succ_eq_mul u]
  rw [show 2 ^ trail u * (u / 2 ^ trail u + 1)
        = 2 ^ trail u * (u / 2 ^ trail u) + 2 ^ trail u by
      rw [Nat.mul_add, Nat.mul_one]]
  omega

def stepBit (u : ℕ) : ℕ := u ||| (u + 1)

def stepNat (n : ℕ) : ℕ := n + (n - (n &&& (n - 1)))

theorem stepNat_succ (u : ℕ) : stepNat (u + 1) = stepBit u + 1 := by
  have h1 : (u + 1) - 1 = u := by omega
  show (u + 1) + ((u + 1) - ((u + 1) &&& ((u + 1) - 1))) = (u ||| (u + 1)) + 1
  rw [h1, sub_land_succ u, or_succ_eq_or_two_pow_trail u, or_two_pow_eq_add u]
  omega

theorem iterate_stepBit_land {u w : ℕ} (h : u &&& w = u) (i : ℕ) :
    Nat.iterate stepBit i u &&& Nat.iterate stepBit i w = Nat.iterate stepBit i u := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
    simp only [Function.iterate_succ_apply']
    exact or_succ_land_submask ih

theorem stepNat_eq (n : ℕ) (hn : 1 ≤ n) : stepNat n = stepBit (n - 1) + 1 := by
  conv_lhs => rw [show n = (n - 1) + 1 by omega]
  rw [stepNat_succ]

theorem iterate_stepNat (n : ℕ) (hn : 1 ≤ n) (i : ℕ) :
    Nat.iterate stepNat i n = Nat.iterate stepBit i (n - 1) + 1 := by
  induction i with
  | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply]; omega
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, stepNat_succ]

/-- Iterating `T n = n + 2^(v_2 n)` (i.e. `n + lowbit n`, `lowbit n = n - (n &&& (n-1))`)
is monotone along a pair `(X, X+v)` whose increment `v` is bitwise disjoint from `X-1`.

This is the binary-carry heart of Thakur's proof that `s_d(k) = sum_{i=1}^d T^i(k)` for the
degree of the power sums over `F_2`. Numerical evidence: it holds for all `X ≤ 300`,
`v ≤ 300` with `(X-1) &&& v = 0`, all `i ≤ 30`.

Proof sketch: the key invariant is `R x y := (y ≤ x) ∧ ((y-1) &&& (x-y) = 0)`. One shows
`R x y → R (T x) (T y)`; then `R (T^i x) (T^i y)` for all `i` by induction, and `R x y`
gives `y ≤ x`, whence `Nat.iterate T i y ≤ Nat.iterate T i x`. The preservation step is a
purely bitwise computation: with `a = v_2 y`, `d = x - y` one has `2^a ∣ d` (because
`(y-1) &&& d = 0` and the bits `0..a-1` of `y-1` are all `1`), and then
`T x - T y = d + 2^(v_2 x) - 2^a`; case split on whether `v_2 x = a` or `v_2 x > a`
(isolating the bit at position `a`, which `d` does/does not carry). -/
theorem step_iter_ge (X v : ℕ) (hX : 1 ≤ X) (h : (X - 1) &&& v = 0) (i : ℕ) :
    Nat.iterate (fun n : ℕ => n + (n - (n &&& (n - 1)))) i X ≤
      Nat.iterate (fun n : ℕ => n + (n - (n &&& (n - 1)))) i (X + v) := by
  have hXv : 1 ≤ X + v := by omega
  have h1 := iterate_stepNat X hX i
  have h2 := iterate_stepNat (X + v) hXv i
  rw [show X + v - 1 = X - 1 + v by omega] at h2
  show Nat.iterate stepNat i X ≤ Nat.iterate stepNat i (X + v)
  rw [h1, h2]
  have hland : X - 1 &&& (X - 1 + v) = X - 1 := and_eq_self_of_land_eq_zero h
  have hiter := iterate_stepBit_land hland i
  have hle : Nat.iterate stepBit i (X - 1) ≤ Nat.iterate stepBit i (X - 1 + v) :=
    le_of_land_eq_left hiter
  omega

end Commons.Data.Nat