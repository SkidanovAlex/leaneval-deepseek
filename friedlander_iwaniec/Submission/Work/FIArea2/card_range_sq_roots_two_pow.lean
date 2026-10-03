import Mathlib
import Submission.Work.FIArea2.card_sq_roots_nat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.FIArea2

open Finset

/-- **Fiber bound.**  In `{0, …, 2m-1}` each residue class modulo `m` occurs at most twice:
if `r < 2m` and `(r : ZMod m) = v` then `r = v.val` or `r = v.val + m`.  Hence the number of
`r` in `range (2 * m)` with `(r : ZMod m) = v` is at most `2`. -/
lemma card_filter_eq_zmod_le_two (m : ℕ) [NeZero m] (v : ZMod m) :
    ((Finset.range (2 * m)).filter (fun r : ℕ => (r : ZMod m) = v)).card ≤ 2 := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hsub : (Finset.range (2 * m)).filter (fun r : ℕ => (r : ZMod m) = v)
      ⊆ ({v.val, v.val + m} : Finset ℕ) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨hrlt, hrv⟩ := hr
    have hvlt : v.val < m := ZMod.val_lt v
    have heq : (r : ZMod m) = (v.val : ZMod m) := by rw [hrv, ZMod.natCast_zmod_val]
    rw [ZMod.natCast_eq_natCast_iff'] at heq
    have hmod : r % m = v.val := by rwa [Nat.mod_eq_of_lt hvlt] at heq
    have hdiv : r / m ≤ 1 := by
      have : r / m < 2 := (Nat.div_lt_iff_lt_mul hm0).mpr hrlt
      omega
    have hrdecomp : r = m * (r / m) + v.val := by
      have h := Nat.div_add_mod r m
      rw [hmod] at h
      exact h.symm
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdiv with h0 | h1
    · left; rw [hrdecomp, h0]; ring
    · right; rw [hrdecomp, h1]; ring
  have hle : ({v.val, v.val + m} : Finset ℕ).card ≤ 2 := by
    have := Finset.card_insert_le v.val ({v.val + m} : Finset ℕ)
    simp only [Finset.card_singleton] at this
    simpa using this
  exact le_trans (Finset.card_le_card hsub) hle

/-- **Two odd integers whose squares are congruent mod `2^n` are congruent mod `2^{n-1}` up to
sign.**  For odd `x, y` and `n ≥ 1`, `2^n ∣ x² - y²` implies `2^{n-1} ∣ x - y` or
`2^{n-1} ∣ x + y`.  Indeed `x - y` and `x + y` are both even and their sum is `2x ≡ 2 (mod 4)`,
so at most one of them is divisible by `4`; the one with `2`-adic valuation `1` and its partner
in `(x-y)(x+y) = x² - y²` share at least `n` powers of `2`, so the partner carries `n - 1`. -/
lemma two_pow_dvd_sub_or_add (n : ℕ) (hn : 1 ≤ n) (x y : ℤ) (hx : Odd x) (hy : Odd y)
    (h : (2:ℤ)^n ∣ x^2 - y^2) :
    (2:ℤ)^(n-1) ∣ x - y ∨ (2:ℤ)^(n-1) ∣ x + y := by
  rcases eq_or_lt_of_le hn with h1 | h2
  · rw [← h1]; exact Or.inl (by norm_num)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn2 : 2 ≤ n := h2
  rcases eq_or_ne (x - y) 0 with hD0 | hD0
  · exact Or.inl (by rw [hD0]; exact dvd_zero _)
  rcases eq_or_ne (x + y) 0 with hS0 | hS0
  · exact Or.inr (by rw [hS0]; exact dvd_zero _)
  have hD2 : (2:ℤ) ∣ x - y := even_iff_two_dvd.mp (hx.sub_odd hy)
  have hS2 : (2:ℤ) ∣ x + y := even_iff_two_dvd.mp (hx.add_odd hy)
  have hprod : x^2 - y^2 = (x-y)*(x+y) := by ring
  have hprodne : x^2 - y^2 ≠ 0 := by
    rw [hprod]; exact mul_ne_zero hD0 hS0
  have hval : padicValInt 2 (x^2 - y^2) = padicValInt 2 (x-y) + padicValInt 2 (x+y) := by
    rw [hprod]; exact padicValInt.mul hD0 hS0
  have hge : n ≤ padicValInt 2 (x^2-y^2) := by
    rcases (padicValInt_dvd_iff (p := 2) n (x^2-y^2)).mp h with h0 | hle
    · exact absurd h0 hprodne
    · exact hle
  have h1' : 1 ≤ padicValInt 2 (x - y) := by
    rcases (padicValInt_dvd_iff (p:=2) 1 (x-y)).mp (by simpa using hD2) with h0 | hle
    · exact absurd h0 hD0
    · simpa using hle
  have h2' : 1 ≤ padicValInt 2 (x + y) := by
    rcases (padicValInt_dvd_iff (p:=2) 1 (x+y)).mp (by simpa using hS2) with h0 | hle
    · exact absurd h0 hS0
    · simpa using hle
  have hnotboth : ¬ (2 ≤ padicValInt 2 (x-y) ∧ 2 ≤ padicValInt 2 (x+y)) := by
    rintro ⟨hvD, hvS⟩
    have h4D : (4:ℤ) ∣ x - y := by
      simpa using (padicValInt_dvd_iff (p:=2) 2 (x-y)).mpr (Or.inr hvD)
    have h4S : (4:ℤ) ∣ x + y := by
      simpa using (padicValInt_dvd_iff (p:=2) 2 (x+y)).mpr (Or.inr hvS)
    have h42x : (4:ℤ) ∣ 2 * x := by
      have : 2 * x = (x - y) + (x + y) := by ring
      rw [this]; exact dvd_add h4D h4S
    obtain ⟨k, hk⟩ := hx
    obtain ⟨j, hj⟩ := h42x
    omega
  have hmin : min (padicValInt 2 (x-y)) (padicValInt 2 (x+y)) = 1 := by
    apply le_antisymm
    · rcases Nat.lt_or_ge (padicValInt 2 (x-y)) 2 with hh | hh
      · have : padicValInt 2 (x-y) ≤ 1 := by omega
        exact le_trans (min_le_left _ _) this
      · have hvS : padicValInt 2 (x+y) ≤ 1 := by
          by_contra hc
          exact hnotboth ⟨hh, by omega⟩
        exact le_trans (min_le_right _ _) hvS
    · exact le_min h1' h2'
  have hmax : n - 1 ≤ max (padicValInt 2 (x-y)) (padicValInt 2 (x+y)) := by
    rcases Nat.le_total (padicValInt 2 (x-y)) (padicValInt 2 (x+y)) with hle | hle
    · have hmin1 : padicValInt 2 (x-y) = 1 := by rw [← hmin, min_eq_left hle]
      rw [max_eq_right hle]
      omega
    · have hmin1 : padicValInt 2 (x+y) = 1 := by rw [← hmin, min_eq_right hle]
      rw [max_eq_left hle]
      omega
  rcases Nat.le_total (padicValInt 2 (x-y)) (padicValInt 2 (x+y)) with hle | hle
  · right
    rw [max_eq_right hle] at hmax
    exact (padicValInt_dvd_iff (p:=2) (n-1) (x+y)).mpr (Or.inr hmax)
  · left
    rw [max_eq_left hle] at hmax
    exact (padicValInt_dvd_iff (p:=2) (n-1) (x-y)).mpr (Or.inr hmax)

/-- If `a` is odd and `2^n ∣ r² - a` with `n ≥ 1`, then `r` is odd. -/
lemma odd_of_dvd_sq_sub (n : ℕ) (hn : 1 ≤ n) (a : ℤ) (ha : Odd a) (r : ℕ)
    (h : ((2^n : ℕ) : ℤ) ∣ (r : ℤ)^2 - a) : Odd (r : ℤ) := by
  have h2n : (2:ℤ) ∣ ((2^n:ℕ):ℤ) := by
    rw [Nat.cast_pow]
    exact dvd_pow_self (2:ℤ) (by omega)
  have h2r : (2:ℤ) ∣ (r:ℤ)^2 - a := dvd_trans h2n h
  have heven : Even ((r:ℤ)^2 - a) := even_iff_two_dvd.mpr h2r
  have hodd2 : Odd ((r:ℤ)^2) := by
    have := heven.add_odd ha
    simpa using this
  rw [pow_two, Int.odd_mul] at hodd2
  exact hodd2.1

/-- **The number of square roots of an odd integer modulo `2^n` is at most `4`.**  All roots of
`r² ≡ a (mod 2^n)` (with `a` odd, `n ≥ 1`) are odd, and any two of them are congruent modulo
`2^{n-1}` up to sign (`two_pow_dvd_sub_or_add`).  Hence they all lie in one signed residue class
modulo `2^{n-1}`, i.e. in `{c, c + 2^{n-1}, -c, -c + 2^{n-1}} ∩ [0, 2^n)`: at most four
elements. -/
theorem card_range_sq_roots_two_pow (n : ℕ) (hn : 1 ≤ n) (a : ℤ) (ha : Odd a) :
    ((Finset.range (2 ^ n)).filter
      (fun r : ℕ => ((2 ^ n : ℕ) : ℤ) ∣ (r : ℤ) ^ 2 - a)).card ≤ 4 := by
  classical
  have hN : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ']
  haveI : NeZero (2 ^ (n - 1)) := ⟨pow_ne_zero _ (by norm_num)⟩
  set S : Finset ℕ := (Finset.range (2 ^ n)).filter
      (fun r : ℕ => ((2 ^ n : ℕ) : ℤ) ∣ (r : ℤ) ^ 2 - a) with hSdef
  rcases S.eq_empty_or_nonempty with hem | ⟨r0, hr0⟩
  · rw [hem, Finset.card_empty]; norm_num
  · have hr0' := hr0
    rw [hSdef] at hr0'
    simp only [Finset.mem_filter, Finset.mem_range] at hr0'
    obtain ⟨hr0lt, hr0dvd⟩ := hr0'
    set T : Finset ℕ := (Finset.range (2 ^ n)).filter
        (fun r : ℕ => (r : ZMod (2 ^ (n - 1))) = (r0 : ZMod (2 ^ (n - 1))) ∨
                      (r : ZMod (2 ^ (n - 1))) = -(r0 : ZMod (2 ^ (n - 1)))) with hTdef
    have hST : S ⊆ T := by
      intro r hr
      have hr' := hr
      rw [hSdef] at hr'
      simp only [Finset.mem_filter, Finset.mem_range] at hr'
      obtain ⟨hrlt, hrdvd⟩ := hr'
      rw [hTdef]
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨hrlt, ?_⟩
      have hrodd : Odd (r : ℤ) := odd_of_dvd_sq_sub n hn a ha r hrdvd
      have hr0odd : Odd (r0 : ℤ) := odd_of_dvd_sq_sub n hn a ha r0 hr0dvd
      have hrr0 : (2:ℤ)^n ∣ (r:ℤ)^2 - (r0:ℤ)^2 := by
        have : (r:ℤ)^2 - (r0:ℤ)^2 = ((r:ℤ)^2 - a) - ((r0:ℤ)^2 - a) := by ring
        rw [this]
        exact dvd_sub hrdvd hr0dvd
      rcases two_pow_dvd_sub_or_add n hn (r:ℤ) (r0:ℤ) hrodd hr0odd hrr0 with hd | hd
      · left
        have hzero : (((r:ℤ) - (r0:ℤ) : ℤ) : ZMod (2 ^ (n-1))) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; simpa using hd
        have h2 : (r : ZMod (2^(n-1))) - (r0 : ZMod (2^(n-1))) = 0 := by
          have hh : ((r:ℤ) : ZMod (2^(n-1))) - ((r0:ℤ) : ZMod (2^(n-1))) = 0 := by
            rw [← Int.cast_sub]; exact hzero
          simpa using hh
        exact sub_eq_zero.mp h2
      · right
        have hzero : (((r:ℤ) + (r0:ℤ) : ℤ) : ZMod (2 ^ (n-1))) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; simpa using hd
        have h2 : (r : ZMod (2^(n-1))) + (r0 : ZMod (2^(n-1))) = 0 := by
          have hh : ((r:ℤ) : ZMod (2^(n-1))) + ((r0:ℤ) : ZMod (2^(n-1))) = 0 := by
            rw [← Int.cast_add]; exact hzero
          simpa using hh
        exact (add_eq_zero_iff_eq_neg).mp h2
    have hTcard : T.card ≤ 4 := by
      have hunion : T = (Finset.range (2 ^ n)).filter
            (fun r : ℕ => (r : ZMod (2 ^ (n - 1))) = (r0 : ZMod (2 ^ (n - 1))))
          ∪ (Finset.range (2 ^ n)).filter
            (fun r : ℕ => (r : ZMod (2 ^ (n - 1))) = -(r0 : ZMod (2 ^ (n - 1)))) := by
        rw [hTdef, Finset.filter_or]
      rw [hunion]
      have hA : ((Finset.range (2 ^ n)).filter
          (fun r : ℕ => (r : ZMod (2 ^ (n - 1))) = (r0 : ZMod (2 ^ (n - 1))))).card ≤ 2 := by
        rw [hN]
        exact card_filter_eq_zmod_le_two (2 ^ (n - 1)) (r0 : ZMod (2 ^ (n - 1)))
      have hB : ((Finset.range (2 ^ n)).filter
          (fun r : ℕ => (r : ZMod (2 ^ (n - 1))) = -(r0 : ZMod (2 ^ (n - 1))))).card ≤ 2 := by
        rw [hN]
        exact card_filter_eq_zmod_le_two (2 ^ (n - 1)) (-(r0 : ZMod (2 ^ (n - 1))))
      calc ((Finset.range (2 ^ n)).filter
              (fun r : ℕ => (r : ZMod (2 ^ (n - 1))) = (r0 : ZMod (2 ^ (n - 1))))
            ∪ (Finset.range (2 ^ n)).filter
              (fun r : ℕ => (r : ZMod (2 ^ (n - 1))) = -(r0 : ZMod (2 ^ (n - 1))))).card
          ≤ ((Finset.range (2 ^ n)).filter
              (fun r : ℕ => (r : ZMod (2 ^ (n - 1))) = (r0 : ZMod (2 ^ (n - 1))))).card
            + ((Finset.range (2 ^ n)).filter
              (fun r : ℕ => (r : ZMod (2 ^ (n - 1))) = -(r0 : ZMod (2 ^ (n - 1))))).card :=
            Finset.card_union_le _ _
        _ ≤ 2 + 2 := add_le_add hA hB
        _ ≤ 4 := by norm_num
    exact le_trans (Finset.card_le_card hST) hTcard

end Work.FIArea2
