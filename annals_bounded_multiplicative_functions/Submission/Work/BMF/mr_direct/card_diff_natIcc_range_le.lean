import Mathlib
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.card_diff_natIcc_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The two-sided `natIcc` difference count for comparable endpoints `A ≤ B`

For real `1 ≤ A ≤ B` and `K ≥ 1`, the integers lying in the enlarged window
`[A e^{-1/K}, B e^{1/K}]` but outside `[A, B]` number at most `8 B / K + 8`:
the lower spill `[A e^{-1/K}, A]` contributes at most `A/K` and the upper spill
`[B, B e^{1/K}]` at most `3 B / K`, which is absorbed by the stated constant since `A ≤ B`.

## Main result

* `Work.BMF.mr_direct.card_diff_natIcc_range_le`
-/

set_option autoImplicit false

namespace Work.BMF.mr_direct

open scoped BigOperators

noncomputable section

theorem card_diff_natIcc_range_le (A B K : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B) (hK : 1 ≤ K) :
    ((Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K))).filter
        (fun n => n ∉ Work.BMF.natIcc A B)).card ≤ 8 * B / K + 8 := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_trans hA hAB)
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have htK : 0 ≤ 1 / K := by positivity
  -- the relevant integer endpoints
  set a : ℕ := ⌈A * Real.exp (-(1 / K))⌉₊ with ha
  set b : ℕ := ⌊B * Real.exp (1 / K)⌋₊ with hb
  set c : ℕ := ⌈A⌉₊ with hc
  set d : ℕ := ⌊B⌋₊ with hd
  have hAeq : Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K))
      = Finset.Icc a b := by
    simp only [Work.BMF.natIcc, ← ha, ← hb]
  have hBeq : Work.BMF.natIcc A B = Finset.Icc c d := by
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
    simpa using mul_le_of_le_one_right (le_of_lt hApos) he
  have hdb : d ≤ b := by
    rw [hd, hb]
    apply Nat.floor_mono
    have he : 1 ≤ Real.exp (1 / K) := Real.one_le_exp htK
    simpa using le_mul_of_one_le_right (le_of_lt hBpos) he
  -- cardinality of the lower spill piece
  have hcast1 : ((Finset.Icc a c).card : ℝ) ≤ A / K + 2 := by
    have hcardc : ((Finset.Icc a c).card : ℝ) ≤ (c : ℝ) - a + 1 := by
      rw [Nat.card_Icc]
      have hle : a ≤ c + 1 := by omega
      rw [Nat.cast_sub hle]
      push_cast
      linarith
    have hc_lt : (c : ℝ) < A + 1 := by
      have h := Nat.ceil_lt_add_one (le_of_lt hApos)
      simpa [hc] using h
    have ha_ge : A * Real.exp (-(1 / K)) ≤ (a : ℝ) := by
      rw [ha]; exact Nat.le_ceil _
    have hbnd : 1 - Real.exp (-(1 / K)) ≤ 1 / K := one_sub_exp_neg_le (1 / K)
    have hmul : A * (1 - Real.exp (-(1 / K))) ≤ A / K :=
      calc A * (1 - Real.exp (-(1 / K))) ≤ A * (1 / K) :=
            mul_le_mul_of_nonneg_left hbnd (le_of_lt hApos)
        _ = A / K := by ring
    linarith
  -- cardinality of the upper spill piece
  have hcast2 : ((Finset.Icc d b).card : ℝ) ≤ 3 * (B / K) + 2 := by
    have hcardd : ((Finset.Icc d b).card : ℝ) ≤ (b : ℝ) + 1 - d := by
      rw [Nat.card_Icc]
      have hle : d ≤ b + 1 := by omega
      rw [Nat.cast_sub hle]
      push_cast
      linarith
    have hb_le : (b : ℝ) ≤ B * Real.exp (1 / K) := by
      rw [hb]; exact Nat.floor_le (by positivity)
    have hd_gt : B - 1 < (d : ℝ) := by
      have h := Nat.lt_floor_add_one B
      rw [hd]
      linarith
    have hexp_le3 : Real.exp (1 / K) ≤ 3 := by
      have h1 : (1 : ℝ) / K ≤ 1 := by
        rw [div_le_one hKpos]; linarith
      calc Real.exp (1 / K) ≤ Real.exp 1 := Real.exp_le_exp.mpr h1
        _ ≤ 3 := le_of_lt Real.exp_one_lt_three
    have he1 : Real.exp (1 / K) - 1 ≤ (1 / K) * Real.exp (1 / K) :=
      exp_sub_one_le_mul_exp (1 / K)
    have hmul : B * (Real.exp (1 / K) - 1) ≤ 3 * (B / K) := by
      have hB0 : (0:ℝ) ≤ B := le_of_lt hBpos
      have h1 : B * (Real.exp (1 / K) - 1) ≤ B * ((1 / K) * Real.exp (1 / K)) :=
        mul_le_mul_of_nonneg_left he1 hB0
      have h2 : B * ((1 / K) * Real.exp (1 / K)) ≤ 3 * (B / K) := by
        have h3 : B * Real.exp (1 / K) ≤ 3 * B := by nlinarith [hexp_le3, hB0]
        calc B * ((1 / K) * Real.exp (1 / K)) = (B * Real.exp (1 / K)) * (1 / K) := by ring
          _ ≤ (3 * B) * (1 / K) := mul_le_mul_of_nonneg_right h3 (by positivity)
          _ = 3 * (B / K) := by ring
      linarith
    nlinarith [hcardd, hb_le, hd_gt, hmul]
  have hfin : (((Finset.Icc a b).filter (fun n => n ∉ Finset.Icc c d)).card : ℝ) ≤
      ((Finset.Icc a c).card : ℝ) + ((Finset.Icc d b).card : ℝ) := by
    exact_mod_cast hcard'
  have hnonneg : 0 ≤ B / K := by positivity
  have hAle : A / K ≤ B / K := div_le_div_of_nonneg_right hAB (le_of_lt hKpos)
  have hgoal : (8:ℝ) * B / K + 8 = 8 * (B / K) + 8 := by ring
  rw [hgoal]
  linarith

end

end Work.BMF.mr_direct
