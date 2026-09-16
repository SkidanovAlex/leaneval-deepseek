import Mathlib

namespace StepR

/-! ## Part A: general bitwise identities (Mathlib-only) -/

theorem land_two_two (a b : ℕ) : (2*a) &&& (2*b) = 2*(a &&& b) := by
  rw [show 2*a = Nat.bit false a from rfl, show 2*b = Nat.bit false b from rfl, Nat.land_bit]; rfl
theorem lor_two_two (a b : ℕ) : (2*a) ||| (2*b) = 2*(a ||| b) := by
  rw [show 2*a = Nat.bit false a from rfl, show 2*b = Nat.bit false b from rfl, Nat.lor_bit]; rfl
theorem land_odd_odd (a b : ℕ) : (2*a+1) &&& (2*b+1) = 2*(a &&& b)+1 := by
  rw [show 2*a+1 = Nat.bit true a from rfl, show 2*b+1 = Nat.bit true b from rfl, Nat.land_bit]; rfl
theorem lor_odd_odd (a b : ℕ) : (2*a+1) ||| (2*b+1) = 2*(a ||| b)+1 := by
  rw [show 2*a+1 = Nat.bit true a from rfl, show 2*b+1 = Nat.bit true b from rfl, Nat.lor_bit]; rfl
theorem land_odd_two (a b : ℕ) : (2*a+1) &&& (2*b) = 2*(a &&& b) := by
  rw [show 2*a+1 = Nat.bit true a from rfl, show 2*b = Nat.bit false b from rfl, Nat.land_bit]; rfl
theorem lor_odd_two (a b : ℕ) : (2*a+1) ||| (2*b) = 2*(a ||| b)+1 := by
  rw [show 2*a+1 = Nat.bit true a from rfl, show 2*b = Nat.bit false b from rfl, Nat.lor_bit]; rfl
theorem land_two_odd (a b : ℕ) : (2*a) &&& (2*b+1) = 2*(a &&& b) := by
  rw [show 2*a = Nat.bit false a from rfl, show 2*b+1 = Nat.bit true b from rfl, Nat.land_bit]; rfl
theorem lor_two_odd (a b : ℕ) : (2*a) ||| (2*b+1) = 2*(a ||| b)+1 := by
  rw [show 2*a = Nat.bit false a from rfl, show 2*b+1 = Nat.bit true b from rfl, Nat.lor_bit]; rfl

/-- `(a & b) + (a | b) = a + b`. -/
theorem land_add_lor (a b : ℕ) : (a &&& b) + (a ||| b) = a + b := by
  suffices H : ∀ n, ∀ a b : ℕ, a + b = n → (a &&& b) + (a ||| b) = a + b from H _ a b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b hab
    rcases n with _ | m
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha; subst hb; simp
    · obtain ⟨a', ha'⟩ | ⟨a', ha'⟩ := Nat.even_or_odd a
      · obtain ⟨b', hb'⟩ | ⟨b', hb'⟩ := Nat.even_or_odd b
        · have ha : a = 2*a' := by rw [ha']; ring
          have hb : b = 2*b' := by rw [hb']; ring
          rw [ha, hb] at hab ⊢
          rw [land_two_two, lor_two_two]
          have hlt : a' + b' < m + 1 := by omega
          have ih' := ih (a' + b') hlt a' b' rfl
          omega
        · have ha : a = 2*a' := by rw [ha']; ring
          have hb : b = 2*b' + 1 := hb'
          rw [ha, hb] at hab ⊢
          rw [land_two_odd, lor_two_odd]
          have hlt : a' + b' < m + 1 := by omega
          have ih' := ih (a' + b') hlt a' b' rfl
          omega
      · obtain ⟨b', hb'⟩ | ⟨b', hb'⟩ := Nat.even_or_odd b
        · have ha : a = 2*a' + 1 := ha'
          have hb : b = 2*b' := by rw [hb']; ring
          rw [ha, hb] at hab ⊢
          rw [land_odd_two, lor_odd_two]
          have hlt : a' + b' < m + 1 := by omega
          have ih' := ih (a' + b') hlt a' b' rfl
          omega
        · have ha : a = 2*a' + 1 := ha'
          have hb : b = 2*b' + 1 := hb'
          rw [ha, hb] at hab ⊢
          rw [land_odd_odd, lor_odd_odd]
          have hlt : a' + b' < m + 1 := by omega
          have ih' := ih (a' + b') hlt a' b' rfl
          omega

/-- If `a` and `b` have disjoint binary expansions then `a + b = a ||| b`. -/
theorem land_eq_zero_add_lor (a b : ℕ) (h : a &&& b = 0) : a + b = a ||| b := by
  have := land_add_lor a b
  omega

/-- Absorption: `a & (a | b) = a`. -/
theorem land_lor_self (a b : ℕ) : a &&& (a ||| b) = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_or]
  cases a.testBit i <;> simp

/-- Extract per-index information from a submask `a ⊆ b`. -/
theorem testBit_imp_of_submask {a b : ℕ} (h : a &&& b = a) (i : ℕ)
    (hi : a.testBit i = true) : b.testBit i = true := by
  have hc := congrArg (fun x : ℕ => x.testBit i) h
  simp only [Nat.testBit_and, hi] at hc
  simpa using hc

/-- Transitivity of the submask relation. -/
theorem submask_trans {a b c : ℕ} (hab : a &&& b = a) (hbc : b &&& c = b) : a &&& c = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : a.testBit i = true
  · rw [hi, testBit_imp_of_submask hbc i (testBit_imp_of_submask hab i hi)]
    simp
  · simp [hi]

/-- Union of two submasks of `c` is a submask of `c`. -/
theorem submask_lor {a b c : ℕ} (ha : a &&& c = a) (hb : b &&& c = b) :
    (a ||| b) &&& c = a ||| b := by
  rw [Nat.and_or_distrib_right, ha, hb]

/-- A submask is bounded by the containing number. -/
theorem submask_le {a b : ℕ} (h : a &&& b = a) : a ≤ b :=
  Nat.le_of_testBit (fun i hi => testBit_imp_of_submask h i hi)

theorem ldiff_land_self (a b : ℕ) : a &&& b.ldiff a = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_ldiff]
  cases a.testBit i <;> simp

theorem lor_ldiff_self {a b : ℕ} (h : a &&& b = a) : a ||| b.ldiff a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_ldiff]
  by_cases hi : a.testBit i = true
  · rw [hi, testBit_imp_of_submask h i hi]; simp
  · simp [hi]

/-- For a submask `a ⊆ b`, `b - a` is the complement of `a` inside `b`. -/
theorem sub_eq_ldiff_of_submask {a b : ℕ} (h : a &&& b = a) : b - a = b.ldiff a := by
  have h1 := land_eq_zero_add_lor a (b.ldiff a) (ldiff_land_self a b)
  rw [lor_ldiff_self h] at h1
  omega

/-- For a submask `a ⊆ b`, `a` and `b - a` are disjoint. -/
theorem sub_land_self_eq_zero {a b : ℕ} (h : a &&& b = a) : a &&& (b - a) = 0 := by
  rw [sub_eq_ldiff_of_submask h, ldiff_land_self]

/-! ## Part B: the lowest set bit -/

/-- The lowest set bit of `n` (ruler function), in the form used in the target. -/
def lowbit (n : ℕ) : ℕ := n - (n &&& (n - 1))

theorem lowbit_two_mul (m : ℕ) (hm : 1 ≤ m) : lowbit (2*m) = 2 * lowbit m := by
  unfold lowbit
  have hbits : (2*m) &&& (2*m - 1) = 2*(m &&& (m-1)) := by
    have hm1 : 2*m - 1 = Nat.bit true (m-1) := by simp only [Nat.bit_true]; omega
    rw [hm1, show (2:ℕ)*m = Nat.bit false m from rfl, Nat.land_bit]
    simp
  rw [hbits, ← Nat.mul_sub_left_distrib]

theorem lowbit_two_mul_add_one (m : ℕ) : lowbit (2*m+1) = 1 := by
  unfold lowbit
  have hland : (2*m+1) &&& (2*m) = 2*m := by
    rw [show 2*m+1 = Nat.bit true m from rfl, show 2*m = Nat.bit false m from rfl, Nat.land_bit]
    simp
  have hsub : 2*m+1 - 1 = 2*m := by omega
  rw [hsub, hland]
  omega

/-- Existence of the exponent of the lowest set bit, together with the fact that
`n - 1` has all bits below it set and the bit itself clear. -/
theorem lowbit_spec (n : ℕ) (hn : 1 ≤ n) :
    ∃ t, lowbit n = 2^t ∧ (n-1) &&& (2^t - 1) = 2^t - 1 ∧ (n-1) &&& 2^t = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨m, hm⟩ | ⟨m, hm⟩ := Nat.even_or_odd n
    · have hn2 : n = 2*m := by rw [hm]; ring
      rw [hn2] at hn ⊢
      have hm1 : 1 ≤ m := by omega
      obtain ⟨t, ht1, ht2, ht3⟩ := ih m (by omega) hm1
      refine ⟨t+1, ?_, ?_, ?_⟩
      · rw [lowbit_two_mul m hm1, ht1]; ring
      · have hA : 2*m - 1 = Nat.bit true (m-1) := by simp only [Nat.bit_true]; omega
        have hB : 2^(t+1) - 1 = Nat.bit true (2^t - 1) := by
          have hle : 1 ≤ 2^t := Nat.one_le_two_pow
          show 2^(t+1) - 1 = 2*(2^t - 1) + 1
          rw [pow_succ]
          omega
        rw [hA, hB, Nat.land_bit, ht2]
        simp
      · have hA : 2*m - 1 = Nat.bit true (m-1) := by simp only [Nat.bit_true]; omega
        have hB : 2^(t+1) = Nat.bit false (2^t) := by rw [Nat.bit_false]; ring
        rw [hA, hB, Nat.land_bit, ht3]
        simp
    · have hn2 : n = 2*m+1 := hm
      rw [hn2] at hn ⊢
      refine ⟨0, ?_, ?_, ?_⟩
      · rw [lowbit_two_mul_add_one m]; norm_num
      · rw [show 2*m+1-1 = 2*m from by omega, show (2:ℕ)^0 - 1 = 0 from rfl]
        simp
      · rw [show 2*m+1-1 = 2*m from by omega, show (2:ℕ)^0 = 1 from rfl]
        rw [show (1:ℕ) = Nat.bit true 0 from rfl, show 2*m = Nat.bit false m from rfl, Nat.land_bit]
        simp

/-- The exponent of the lowest set bit is determined by the bits of `n - 1`. -/
theorem lowbit_pred_unique {n t s : ℕ}
    (h1 : (n-1) &&& (2^t - 1) = 2^t - 1) (h1' : (n-1) &&& 2^t = 0)
    (h2 : (n-1) &&& (2^s - 1) = 2^s - 1) (h2' : (n-1) &&& 2^s = 0) : t = s := by
  rcases lt_trichotomy t s with hlt | heq | hlt
  · exfalso
    have ht : (n-1).testBit t = true :=
      testBit_imp_of_submask (by rw [Nat.land_comm]; exact h2) t
        (by rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hlt)
    have hf : (n-1).testBit t = false := by
      have hc := congrArg (fun x : ℕ => x.testBit t) h1'
      simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit, decide_true, Bool.and_true] at hc
      exact hc
    rw [ht] at hf; exact Bool.noConfusion hf
  · exact heq
  · exfalso
    have ht : (n-1).testBit s = true :=
      testBit_imp_of_submask (by rw [Nat.land_comm]; exact h1) s
        (by rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hlt)
    have hf : (n-1).testBit s = false := by
      have hc := congrArg (fun x : ℕ => x.testBit s) h2'
      simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit, decide_true, Bool.and_true] at hc
      exact hc
    rw [ht] at hf; exact Bool.noConfusion hf

/-- Converse of `lowbit_spec`: bits of `n - 1` determine the lowest set bit. -/
theorem lowbit_of_pred (n : ℕ) (hn : 1 ≤ n) (t : ℕ)
    (hlo : (n-1) &&& (2^t - 1) = 2^t - 1) (hhi : (n-1) &&& 2^t = 0) :
    lowbit n = 2^t := by
  obtain ⟨s, hs1, hs2, hs3⟩ := lowbit_spec n hn
  have hts : t = s := lowbit_pred_unique hlo hhi hs2 hs3
  rw [hs1, hts]

end StepR

namespace Commons.Data.Nat

open StepR

theorem step_R_pres (x y : ℕ) (hy : 1 ≤ y) (hyx : y ≤ x) (h : (y - 1) &&& (x - y) = 0) :
    y + (y - (y &&& (y - 1))) ≤ x + (x - (x &&& (x - 1))) ∧
    (y + (y - (y &&& (y - 1))) - 1) &&&
      (x + (x - (x &&& (x - 1))) - (y + (y - (y &&& (y - 1))))) = 0 := by
  change y + StepR.lowbit y ≤ x + StepR.lowbit x ∧
    (y + StepR.lowbit y - 1) &&& (x + StepR.lowbit x - (y + StepR.lowbit y)) = 0
  have hx : 1 ≤ x := le_trans hy hyx
  obtain ⟨t, hyt, hy1, hy2⟩ := StepR.lowbit_spec y hy
  obtain ⟨s, hxs, hx1, hx2⟩ := StepR.lowbit_spec x hx
  -- Subclaim 1 : (y-1) ⊆ (x-1)
  have hsub1 : (y-1) &&& (x-1) = y-1 := by
    have hxy : (y-1) + (x-y) = x - 1 := by omega
    rw [← hxy, StepR.land_eq_zero_add_lor (y-1) (x-y) h]
    exact StepR.land_lor_self (y-1) (x-y)
  -- (2^t - 1) ⊆ (x-1)
  have hsub_lo : (2^t - 1) &&& (x-1) = 2^t - 1 :=
    StepR.submask_trans (by rw [Nat.land_comm]; exact hy1) hsub1
  -- `2^t` is a submask of `(x-1) ||| lowbit x`
  have hb : 2^t &&& ((x-1) ||| StepR.lowbit x) = 2^t := by
    cases ht : (x-1).testBit t
    · have hhi : (x-1) &&& 2^t = 0 := by rw [Nat.and_two_pow, ht]; simp
      have hlx : StepR.lowbit x = 2^t := StepR.lowbit_of_pred x hx t (by rw [Nat.land_comm]; exact hsub_lo) hhi
      rw [hlx, Nat.lor_comm]
      exact StepR.land_lor_self (2^t) (x-1)
    · have hxt : 2^t &&& (x-1) = 2^t := by rw [Nat.land_comm, Nat.and_two_pow, ht]; simp
      exact StepR.submask_trans hxt (StepR.land_lor_self (x-1) (StepR.lowbit x))
  -- Decompose Y-1 and X-1
  have hY1 : y + StepR.lowbit y - 1 = (y-1) ||| 2^t := by
    rw [hyt]
    have htmp : y + 2^t - 1 = (y-1) + 2^t := by omega
    rw [htmp, StepR.land_eq_zero_add_lor (y-1) (2^t) hy2]
  have hX1 : x + StepR.lowbit x - 1 = (x-1) ||| StepR.lowbit x := by
    rw [hxs]
    have htmp : x + 2^s - 1 = (x-1) + 2^s := by omega
    rw [htmp, StepR.land_eq_zero_add_lor (x-1) (2^s) hx2]
  -- Y-1 ⊆ X-1
  have hsubY : (y + StepR.lowbit y - 1) &&& (x + StepR.lowbit x - 1) = y + StepR.lowbit y - 1 := by
    rw [hY1, hX1]
    apply StepR.submask_lor
    · exact StepR.submask_trans hsub1 (StepR.land_lor_self (x-1) (StepR.lowbit x))
    · exact hb
  constructor
  · have hle := StepR.submask_le hsubY
    omega
  · have hYpos : 1 ≤ y + StepR.lowbit y := by
      rw [hyt]
      have h2t : 1 ≤ 2^t := Nat.one_le_two_pow
      omega
    have hXY : x + StepR.lowbit x - (y + StepR.lowbit y) =
        (x + StepR.lowbit x - 1) - (y + StepR.lowbit y - 1) := by omega
    rw [hXY]
    exact StepR.sub_land_self_eq_zero hsubY

end Commons.Data.Nat
