import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star

/-!
# Cardinality of multiples in a window

We bound the number of `t < L` such that `d ∣ b + t` — i.e. the number of
multiples of `d` in the `L` consecutive integers `b, b+1, …, b+L-1` — by
`L/d ± 1`.

Strategy: `d ∣ b + t` is a congruence condition on `t` modulo `d`, and the
number of `t < L` in a fixed residue class modulo `d` is `L/d` or `L/d + 1`
(`Nat.count_modEq_card`); casting the resulting natural-number bounds to `ℝ`
gives the two real inequalities.
-/

namespace Commons.Data.Nat

/-- For the natural division `q = L/d` one has `q ≤ L/d` in the reals. -/
lemma card_multiples_nat_div_le_real_div (L d : ℕ) :
    ((L / d : ℕ) : ℝ) ≤ (L : ℝ) / (d : ℝ) := by
  by_cases hd0 : d = 0
  · subst d
    simp
  · have hd : 0 < d := Nat.pos_of_ne_zero hd0
    have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
    rw [le_div_iff₀ hd']
    exact_mod_cast Nat.div_mul_le_self L d

/-- For the natural division `q = L/d` one has `L/d < q + 1` in the reals. -/
lemma card_multiples_real_div_lt_nat_div_add_one (L d : ℕ) :
    (L : ℝ) / (d : ℝ) < ((L / d : ℕ) : ℝ) + 1 := by
  by_cases hd0 : d = 0
  · subst d
    simp
  · have hd : 0 < d := Nat.pos_of_ne_zero hd0
    have hmod : L % d < d := Nat.mod_lt L hd
    have hmain : L = (L / d) * d + L % d := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod L d).symm
    have hlt : L < (L / d + 1) * d := by
      rw [add_mul, one_mul]
      nlinarith
    have hlt' : (L : ℝ) < (((L / d + 1) * d : ℕ) : ℝ) := by exact_mod_cast hlt
    have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
    rw [div_lt_iff₀ hd']
    simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hlt'

/-- The solutions of `d ∣ r + s` with `0 ≤ r, s < d` are exactly `s ≡ -r (mod d)`. -/
lemma card_multiples_sum_mod_eq_zero_iff (r s d : ℕ) (_hd : 0 < d) (hr : r < d)
    (hs : s < d) :
    (r + s) % d = 0 ↔ s = (d - r) % d := by
  constructor
  · intro h
    by_cases hr0 : r = 0
    · subst r
      have : s % d = 0 := by simpa using h
      have hs0 : s = 0 := by
        exact Nat.eq_zero_of_dvd_of_lt (Nat.dvd_iff_mod_eq_zero.mpr this) hs
      simp [hs0]
    · by_cases hlt : r + s < d
      · exfalso
        have : (r + s) % d = r + s := Nat.mod_eq_of_lt hlt
        omega
      · have hge : d ≤ r + s := by omega
        have hred : (r + s) % d = (r + s - d) % d := Nat.mod_eq_sub_mod hge
        have hsm : r + s - d < d := by omega
        have h0 : r + s - d = 0 := by
          have : (r + s - d) % d = 0 := by simpa [hred] using h
          exact (Nat.mod_eq_of_lt hsm).symm.trans this
        have hrs : r + s = d := by omega
        have hsdr : s = d - r := by omega
        have hdr_lt : d - r < d := by omega
        have hdr_mod : (d - r) % d = d - r := Nat.mod_eq_of_lt hdr_lt
        rw [hsdr, hdr_mod]
  · intro h
    by_cases hr0 : r = 0
    · subst r
      have hs0 : s = 0 := by simpa using h
      simp [hs0]
    · have hdr_lt : d - r < d := by omega
      have hdr_mod : (d - r) % d = d - r := Nat.mod_eq_of_lt hdr_lt
      have hs' : s = d - r := by
        rw [hdr_mod] at h
        exact h
      have hrs : r + s = d := by omega
      simp [hrs]

/-- `d ∣ b + t` is a congruence condition on `t` modulo `d`. -/
lemma card_multiples_modEq_dvd_add_iff (b t d : ℕ) (hd : 0 < d) :
    d ∣ b + t ↔ t ≡ (d - b % d) % d [MOD d] := by
  rw [Nat.ModEq]
  have hv : ((d - b % d) % d) % d = (d - b % d) % d := Nat.mod_mod _ _
  rw [hv]
  rw [Nat.dvd_iff_mod_eq_zero]
  have hr : b % d < d := Nat.mod_lt b hd
  have hs : t % d < d := Nat.mod_lt t hd
  rw [Nat.add_mod]
  exact card_multiples_sum_mod_eq_zero_iff (b % d) (t % d) d hd hr hs

/-- The number of `t < L` with `d | b + t` is either `L/d` or `L/d + 1`. -/
lemma card_valid_window_bound (L b d : ℕ) (hd : 0 < d) :
    let m := ((Finset.range L).filter (fun t => d ∣ b + t)).card
    L / d ≤ m ∧ m ≤ L / d + 1 := by
  intro m
  let v := (d - b % d) % d
  have hcnt : m = Nat.count (fun t => t ≡ v [MOD d]) L := by
    dsimp [m, v]
    rw [Nat.count_eq_card_filter_range]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [card_multiples_modEq_dvd_add_iff b t d hd]
  have hcnt2 := Nat.count_modEq_card (b := L) hd (v := v)
  constructor
  · rw [hcnt, hcnt2]
    by_cases h : v % d < L % d
    · simp [h]
    · simp [h]
  · rw [hcnt, hcnt2]
    by_cases h : v % d < L % d
    · simp [h]
    · simp [h]

/-- The window multiple count is within `1` of `L/d`. -/
theorem card_multiples_window_bound (L b d : ℕ) (hd : 0 < d) :
    let m := ((Finset.range L).filter (fun t => d ∣ b + t)).card
    (m : ℝ) ≤ (L : ℝ) / (d : ℝ) + 1 ∧ (L : ℝ) / (d : ℝ) - 1 ≤ (m : ℝ) := by
  intro m
  have hb := card_valid_window_bound L b d hd
  constructor
  · have hle : (m : ℝ) ≤ ((L / d : ℕ) : ℝ) + 1 := by exact_mod_cast hb.2
    have hdvd : ((L / d : ℕ) : ℝ) ≤ (L : ℝ) / (d : ℝ) :=
      card_multiples_nat_div_le_real_div L d
    nlinarith
  · have hge : ((L / d : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hb.1
    have hlt : (L : ℝ) / (d : ℝ) < ((L / d : ℕ) : ℝ) + 1 :=
      card_multiples_real_div_lt_nat_div_add_one L d
    nlinarith

end Commons.Data.Nat