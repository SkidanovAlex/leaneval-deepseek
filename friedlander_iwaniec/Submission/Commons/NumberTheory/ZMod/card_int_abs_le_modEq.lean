import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Star
import Mathlib.Data.ZMod.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.ZMod

/-- **Counting integers of bounded size in a residue class.**

Let `d ≥ 1`, `0 ≤ β < d`, `Y ≥ 0`.  Then the number of integers `a` with
`|a| ≤ Y` and `a ≡ β (mod d)` (represented here by enumerating the integers
`a` in `[-(⌊Y⌋₊+1), ⌊Y⌋₊+1]` satisfying both conditions) equals
`⌊(Y-β)/d⌋ + ⌊(Y+β)/d⌋ + 1`.

Indeed the integers `a ≡ β (mod d)` are exactly `β + k·d` (`k ∈ ℤ`), and
`|β + k·d| ≤ Y` is equivalent to `k ∈ [-⌊(Y+β)/d⌋, ⌊(Y-β)/d⌋]`, an interval
of integers containing `⌊(Y-β)/d⌋ + ⌊(Y+β)/d⌋ + 1` elements. -/
theorem card_int_abs_le_modEq (d : ℕ) (hd : 1 ≤ d) (β : ℕ) (hβ : β < d) (Y : ℝ) (hY : 0 ≤ Y) :
    ((Finset.filter (fun a : ℤ => |(a : ℝ)| ≤ Y ∧ ((a : ZMod d) = ((β : ℤ) : ZMod d)))
        (Finset.Icc (-(⌊Y⌋₊ + 1 : ℤ)) (⌊Y⌋₊ + 1 : ℤ))).card : ℤ)
      = ⌊(Y - (β : ℝ)) / (d : ℝ)⌋ + ⌊(Y + (β : ℝ)) / (d : ℝ)⌋ + 1 := by
  classical
  -- numeric facts
  have hdR : (0 : ℝ) < (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hdZ : (0 : ℤ) < (d : ℤ) := by
    have : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  have hdZne : (d : ℤ) ≠ 0 := ne_of_gt hdZ
  have hβlt : (β : ℝ) < (d : ℝ) := by exact_mod_cast hβ
  have hβ0 : (0 : ℝ) ≤ (β : ℝ) := by positivity
  -- the counted set, and the two floor endpoints
  set S : Finset ℤ :=
    Finset.filter (fun a : ℤ => |(a : ℝ)| ≤ Y ∧ ((a : ZMod d) = ((β : ℤ) : ZMod d)))
      (Finset.Icc (-(⌊Y⌋₊ + 1 : ℤ)) (⌊Y⌋₊ + 1 : ℤ)) with hS
  set k_hi : ℤ := ⌊(Y - (β : ℝ)) / (d : ℝ)⌋ with hkhi
  set k_lo : ℤ := -(⌊(Y + (β : ℝ)) / (d : ℝ)⌋) with hklo
  let f : ℤ → ℤ := fun k => (β : ℤ) + k * (d : ℤ)
  have hf_inj : Function.Injective f := by
    intro k1 k2 h
    simp only [f] at h
    have h' : k1 * (d : ℤ) = k2 * (d : ℤ) := by linarith
    exact mul_right_cancel₀ hdZne h'
  -- the explicit bijection between the residue class and the interval of `k`'s
  have hSe : S = (Finset.Icc k_lo k_hi).image f := by
    rw [hS, hkhi, hklo]
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨-, -⟩, habs, hmod⟩
      have habs_le := abs_le.mp habs
      have hdv : (d : ℤ) ∣ a - (β : ℤ) := by
        have h := (ZMod.intCast_eq_intCast_iff_dvd_sub a (β : ℤ) d).mp hmod
        have h2 : (d : ℤ) ∣ -((β : ℤ) - a) := dvd_neg.mpr h
        simpa [neg_sub] using h2
      obtain ⟨k, hk⟩ := hdv
      have ha : a = (β : ℤ) + k * (d : ℤ) := by
        have h1 : a = (β : ℤ) + (d : ℤ) * k := by linarith [hk]
        rw [h1]; ring
      have haR : (a : ℝ) = (β : ℝ) + (k : ℝ) * (d : ℝ) := by
        have h := congrArg (fun z : ℤ => (z : ℝ)) ha
        push_cast at h
        exact h
      have hk_le_hi : k ≤ ⌊(Y - (β : ℝ)) / (d : ℝ)⌋ := by
        apply Int.le_floor.mpr
        rw [le_div_iff₀ hdR]
        linarith [haR, habs_le.2]
      have hk_ge_lo : -(⌊(Y + (β : ℝ)) / (d : ℝ)⌋) ≤ k := by
        have hk_ge_frac : -(k : ℝ) ≤ (Y + (β : ℝ)) / (d : ℝ) := by
          rw [le_div_iff₀ hdR]
          have hkd : -((Y : ℝ) + (β : ℝ)) ≤ (k : ℝ) * (d : ℝ) := by
            linarith [haR, habs_le.1]
          nlinarith [hkd]
        have h1 : -(k) ≤ ⌊(Y + (β : ℝ)) / (d : ℝ)⌋ := by
          rw [Int.le_floor]
          push_cast
          exact hk_ge_frac
        linarith
      exact ⟨k, ⟨hk_ge_lo, hk_le_hi⟩, by simp only [f]; rw [ha]⟩
    · rintro ⟨k, ⟨hk_ge_lo, hk_le_hi⟩, hkfa⟩
      have ha : a = (β : ℤ) + k * (d : ℤ) := by
        rw [← hkfa]
      have haR : (a : ℝ) = (β : ℝ) + (k : ℝ) * (d : ℝ) := by
        have h := congrArg (fun z : ℤ => (z : ℝ)) ha
        push_cast at h
        exact h
      have hkhiR : (k : ℝ) ≤ (Y - (β : ℝ)) / (d : ℝ) := by
        have h2 : k ≤ ⌊(Y - (β : ℝ)) / (d : ℝ)⌋ := by simpa [hkhi] using hk_le_hi
        exact le_trans (by exact_mod_cast h2) (Int.floor_le _)
      have hkd_ub : (k : ℝ) * (d : ℝ) ≤ Y - (β : ℝ) := (le_div_iff₀ hdR).mp hkhiR
      have ha_ub : (a : ℝ) ≤ Y := by linarith [haR, hkd_ub]
      have hk_neg_le : ((-(k) : ℤ) : ℝ) ≤ (Y + (β : ℝ)) / (d : ℝ) := by
        have h1 : -(k) ≤ ⌊(Y + (β : ℝ)) / (d : ℝ)⌋ := by
          have hh : k_lo ≤ k := hk_ge_lo
          rw [hklo] at hh
          linarith
        exact le_trans (by exact_mod_cast h1) (Int.floor_le _)
      have hkd_lb : -((Y : ℝ) + (β : ℝ)) ≤ (k : ℝ) * (d : ℝ) := by
        have hm := (le_div_iff₀ hdR).mp hk_neg_le
        have hthis : ((-(k) : ℤ) : ℝ) = -(k : ℝ) := by simp
        rw [hthis, neg_mul] at hm
        linarith [hm]
      have ha_lb : -(Y : ℝ) ≤ (a : ℝ) := by linarith [haR, hkd_lb]
      have habs : |(a : ℝ)| ≤ Y := abs_le.mpr ⟨ha_lb, ha_ub⟩
      have hmod : (a : ZMod d) = ((β : ℤ) : ZMod d) := by
        rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
        rw [ha]
        exact ⟨-k, by ring⟩
      have hN : Y ≤ ((⌊Y⌋₊ : ℤ) + 1 : ℝ) := by
        have h := Nat.lt_floor_add_one Y
        have heq : ((⌊Y⌋₊ : ℤ) + 1 : ℝ) = (⌊Y⌋₊ : ℝ) + 1 := by push_cast; ring
        rw [heq]; exact le_of_lt h
      have ha_up : (a : ℝ) ≤ ((⌊Y⌋₊ : ℤ) + 1 : ℝ) := le_trans ha_ub hN
      have ha_lo : -((⌊Y⌋₊ : ℤ) + 1 : ℝ) ≤ (a : ℝ) := by linarith [ha_lb, hN]
      exact ⟨⟨by exact_mod_cast ha_lo, by exact_mod_cast ha_up⟩, habs, hmod⟩
  -- cardinality transfer
  have hcard : S.card = (Finset.Icc k_lo k_hi).card := by
    rw [hSe]
    exact Finset.card_image_of_injective (Finset.Icc k_lo k_hi) hf_inj
  -- evaluate the interval cardinality
  have hfl1 : (-1 : ℤ) ≤ ⌊(Y - (β : ℝ)) / (d : ℝ)⌋ := by
    rw [Int.le_floor]
    rw [le_div_iff₀ hdR]
    push_cast
    nlinarith [hY, hβlt]
  have hfl2 : (0 : ℤ) ≤ ⌊(Y + (β : ℝ)) / (d : ℝ)⌋ := by
    rw [Int.le_floor]
    push_cast
    apply div_nonneg
    · linarith [hY, hβ0]
    · exact le_of_lt hdR
  have hE : 0 ≤ k_hi + 1 - k_lo := by
    rw [hkhi, hklo]
    linarith [hfl1, hfl2]
  have h1 : ((Finset.Icc k_lo k_hi).card : ℤ) = k_hi + 1 - k_lo := by
    rw [Int.card_Icc]
    exact Int.toNat_of_nonneg hE
  rw [hcard, h1]
  rw [hklo]
  ring

end Commons.NumberTheory.ZMod