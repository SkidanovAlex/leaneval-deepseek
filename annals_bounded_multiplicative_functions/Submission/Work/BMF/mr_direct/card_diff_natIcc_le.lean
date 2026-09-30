import Mathlib
import Submission.Work.BMF.mr_direct_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The two-sided `natIcc` difference count

For `X ≥ 1` and `K ≥ 1` the set of integers in the slightly enlarged window
`[X e^{-1/K}, 2X e^{1/K}]` which fall outside the window `[X, 2X]` has at most
`8X/K + 8` elements: the two "spill" pieces at either end are of length at most
about `X/K` and `2X/K` respectively.  This is the crude counting input used in the
Buchstab/Ramaré direct route.

## Main result

* `Work.BMF.mr_direct.card_diff_natIcc_le`
-/

set_option autoImplicit false

namespace Work.BMF.mr_direct

open scoped BigOperators

noncomputable section

/-- `1 - e^{-t} ≤ t` for every real `t` (convexity of the exponential). -/
lemma one_sub_exp_neg_le (t : ℝ) : 1 - Real.exp (-t) ≤ t := by
  have h := Real.add_one_le_exp (-t)
  linarith

/-- `e^t - 1 ≤ t e^t` for every real `t` (the same inequality reversed). -/
lemma exp_sub_one_le_mul_exp (t : ℝ) : Real.exp t - 1 ≤ t * Real.exp t := by
  have h := Real.add_one_le_exp (-t)
  have h' : 1 - t ≤ Real.exp (-t) := by linarith
  have hpos : 0 < Real.exp t := Real.exp_pos t
  have h2 : (1 - t) * Real.exp t ≤ Real.exp (-t) * Real.exp t :=
    mul_le_mul_of_nonneg_right h' (le_of_lt hpos)
  have h3 : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith [h2, h3, hpos]

/-- Integers in `[X e^{-1/K}, 2X e^{1/K}]` but outside `[X, 2X]`: at most `8X/K + 8`
of them, for `X, K ≥ 1`. -/
lemma card_diff_natIcc_le (X K : ℝ) (hX : 1 ≤ X) (hK : 1 ≤ K) :
    ((Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K))).filter
        (fun n => n ∉ Work.BMF.natIcc X (2 * X))).card ≤ 8 * X / K + 8 := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have htK : 0 ≤ 1 / K := by positivity
  -- the relevant integer endpoints
  set a : ℕ := ⌈X * Real.exp (-(1 / K))⌉₊ with ha
  set b : ℕ := ⌊2 * X * Real.exp (1 / K)⌋₊ with hb
  set c : ℕ := ⌈X⌉₊ with hc
  set d : ℕ := ⌊2 * X⌋₊ with hd
  have hAeq : Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K))
      = Finset.Icc a b := by
    simp only [Work.BMF.natIcc, ← ha, ← hb]
  have hBeq : Work.BMF.natIcc X (2 * X) = Finset.Icc c d := by
    simp only [Work.BMF.natIcc, ← hc, ← hd]
  rw [hAeq, hBeq]
  -- every exceptional element lies in `[a,c] ∪ [d,b]`
  have hsub : (Finset.Icc a b).filter (fun n => n ∉ Finset.Icc c d) ⊆
      Finset.Icc a c ∪ Finset.Icc d b := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hna, hnb⟩, hnd⟩ := hn
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
    rcases lt_or_ge n c with h1 | h1
    · exact Or.inl ⟨hna, le_of_lt h1⟩
    · exact Or.inr ⟨le_of_lt (lt_of_not_ge fun h => hnd ⟨h1, h⟩), hnb⟩
  have hcard' : ((Finset.Icc a b).filter (fun n => n ∉ Finset.Icc c d)).card ≤
      (Finset.Icc a c).card + (Finset.Icc d b).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  -- order of the endpoints: `a ≤ c` and `d ≤ b`
  have hac : a ≤ c := by
    rw [ha, hc]
    apply Nat.ceil_mono
    have he : Real.exp (-(1 / K)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    simpa using mul_le_of_le_one_right (le_of_lt hXpos) he
  have hdb : d ≤ b := by
    rw [hd, hb]
    apply Nat.floor_mono
    have he : 1 ≤ Real.exp (1 / K) := Real.one_le_exp htK
    simpa using le_mul_of_one_le_right (by positivity : (0:ℝ) ≤ 2 * X) he
  -- cardinality of the lower spill piece
  have hcast1 : ((Finset.Icc a c).card : ℝ) ≤ X / K + 2 := by
    have hcardc : ((Finset.Icc a c).card : ℝ) ≤ (c : ℝ) - a + 1 := by
      rw [Nat.card_Icc]
      have hle : a ≤ c + 1 := by omega
      rw [Nat.cast_sub hle]
      push_cast
      linarith
    have hc_lt : (c : ℝ) < X + 1 := by
      have h := Nat.ceil_lt_add_one (le_of_lt hXpos)
      simpa [hc] using h
    have ha_ge : X * Real.exp (-(1 / K)) ≤ (a : ℝ) := by
      rw [ha]; exact Nat.le_ceil _
    have hbnd : 1 - Real.exp (-(1 / K)) ≤ 1 / K := one_sub_exp_neg_le (1 / K)
    have hmul : X * (1 - Real.exp (-(1 / K))) ≤ X / K :=
      calc X * (1 - Real.exp (-(1 / K))) ≤ X * (1 / K) :=
            mul_le_mul_of_nonneg_left hbnd (le_of_lt hXpos)
        _ = X / K := by ring
    linarith
  -- cardinality of the upper spill piece
  have hcast2 : ((Finset.Icc d b).card : ℝ) ≤ 6 * (X / K) + 2 := by
    have hcardd : ((Finset.Icc d b).card : ℝ) ≤ (b : ℝ) + 1 - d := by
      rw [Nat.card_Icc]
      have hle : d ≤ b + 1 := by omega
      rw [Nat.cast_sub hle]
      push_cast
      linarith
    have hb_le : (b : ℝ) ≤ 2 * X * Real.exp (1 / K) := by
      rw [hb]; exact Nat.floor_le (by positivity)
    have hd_gt : 2 * X - 1 < (d : ℝ) := by
      have h := Nat.lt_floor_add_one (2 * X)
      rw [hd]
      linarith
    have hexp_le3 : Real.exp (1 / K) ≤ 3 := by
      have h1 : (1 : ℝ) / K ≤ 1 := by
        rw [div_le_one hKpos]; linarith
      calc Real.exp (1 / K) ≤ Real.exp 1 := Real.exp_le_exp.mpr h1
        _ ≤ 3 := le_of_lt Real.exp_one_lt_three
    have he1 : Real.exp (1 / K) - 1 ≤ (1 / K) * Real.exp (1 / K) :=
      exp_sub_one_le_mul_exp (1 / K)
    have hmul : 2 * X * (Real.exp (1 / K) - 1) ≤ 6 * (X / K) := by
      have hX0 : (0:ℝ) ≤ 2 * X := by positivity
      have h1 : 2 * X * (Real.exp (1/K) - 1) ≤ 2 * X * ((1/K) * Real.exp (1/K)) :=
        mul_le_mul_of_nonneg_left he1 hX0
      have h2 : 2 * X * ((1/K) * Real.exp (1/K)) ≤ 6 * (X / K) := by
        have h3 : 2 * X * Real.exp (1/K) ≤ 6 * X := by nlinarith [hexp_le3, hX0]
        calc 2 * X * ((1/K) * Real.exp (1/K)) = (2 * X * Real.exp (1/K)) * (1/K) := by ring
          _ ≤ (6 * X) * (1/K) := mul_le_mul_of_nonneg_right h3 (by positivity)
          _ = 6 * (X / K) := by ring
      linarith
    nlinarith [hcardd, hb_le, hd_gt, hmul]
  have hfin : (((Finset.Icc a b).filter (fun n => n ∉ Finset.Icc c d)).card : ℝ) ≤
      ((Finset.Icc a c).card : ℝ) + ((Finset.Icc d b).card : ℝ) := by
    exact_mod_cast hcard'
  have hnonneg : 0 ≤ X / K := by positivity
  have hgoal : (8:ℝ) * X / K + 8 = 8 * (X / K) + 8 := by ring
  rw [hgoal]
  linarith

end

end Work.BMF.mr_direct
