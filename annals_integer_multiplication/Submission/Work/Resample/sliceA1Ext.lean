import Mathlib
import Submission.Work.Resample.sliceA1defs

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## Size facts for `L = slL p α s` and `h = slH p α s` -/

lemma slL_le_s (p α s : ℕ) : slL p α s ≤ s := Nat.min_le_left _ _

lemma slL_pos (p α s : ℕ) (hs : 2 ≤ s) : 1 ≤ slL p α s := by
  rw [slL]
  exact le_min (by omega) (by simp)

lemma slH_le_slL (p α s : ℕ) : slH p α s ≤ slL p α s := by
  rw [slH]; exact Nat.div_le_self _ _

lemma slH_le_s (p α s : ℕ) (_hs : 2 ≤ s) : slH p α s ≤ s :=
  le_trans (slH_le_slL p α s) (slL_le_s p α s)

lemma slL_sub_slH_le_s (p α s : ℕ) : slL p α s - slH p α s ≤ s :=
  le_trans (Nat.sub_le _ _) (slL_le_s p α s)

lemma slL_eq_of_lt (p α s : ℕ) (h : slL p α s < s) : slL p α s = 2 * slM p α + 1 := by
  rw [slL] at h ⊢
  by_cases hle : s ≤ 2 * slM p α + 1
  · rw [Nat.min_eq_left hle] at h; exact absurd h (lt_irrefl s)
  · exact Nat.min_eq_right (by omega)

lemma slH_eq_of_lt (p α s : ℕ) (h : slL p α s < s) : slH p α s = slM p α := by
  rw [slH, slL_eq_of_lt p α s h]
  omega

/-! ## Facts about the window starts `slK` and the advances `slD` -/

lemma slK_mono (s t k : ℕ) : slK s t k ≤ slK s t (k + 1) := by
  rw [slK, slK]
  apply Nat.div_le_div_right
  nlinarith

lemma slK_zero (s t : ℕ) (ht : 0 < t) : slK s t 0 = 0 := by
  rw [slK]
  simp only [Nat.mul_zero, Nat.zero_mul, Nat.zero_add]
  exact Nat.div_eq_of_lt (by omega)

lemma slK_succ_le (s t k : ℕ) (hst : s ≤ t) (ht : 0 < t) :
    slK s t (k + 1) ≤ slK s t k + 1 := by
  have h2t : 0 < 2 * t := by omega
  have hle : 2 * k * s + t + 2 * s ≤ 2 * k * s + t + 2 * t := by omega
  have hnum : 2 * (k + 1) * s + t = 2 * k * s + t + 2 * s := by ring
  rw [slK, hnum]
  calc (2 * k * s + t + 2 * s) / (2 * t)
      ≤ (2 * k * s + t + 2 * t) / (2 * t) := Nat.div_le_div_right hle
    _ = (2 * k * s + t) / (2 * t) + 1 := by
        have := Nat.add_mul_div_right (2 * k * s + t) 1 h2t
        simpa [Nat.mul_comm] using this

lemma slD_le_one (s t k : ℕ) (hst : s ≤ t) (ht : 0 < t) : slD s t k ≤ 1 := by
  rw [slD, Nat.sub_le_iff_le_add]
  have := slK_succ_le s t k hst ht
  omega

lemma slK_le' (s t k : ℕ) (ht : 0 < t) :
    (slK s t k : ℝ) ≤ (k : ℝ) * s / t + 1 / 2 := by
  have htR : (t : ℝ) ≠ 0 := by positivity
  have hcast : (slK s t k : ℝ) ≤ ((2 * k * s + t : ℕ) : ℝ) / ((2 * t : ℕ) : ℝ) := by
    rw [slK]; exact Nat.cast_div_le
  have heq : ((2 * k * s + t : ℕ) : ℝ) / ((2 * t : ℕ) : ℝ)
      = (k : ℝ) * s / t + 1 / 2 := by
    push_cast
    field_simp
  linarith [hcast, heq.le, heq.ge]

lemma slK_ge' (s t k : ℕ) (ht : 0 < t) :
    (k : ℝ) * s / t - 1 / 2 ≤ (slK s t k : ℝ) := by
  have h2t : 0 < 2 * t := by omega
  have hlt : 2 * k * s + t < (slK s t k + 1) * (2 * t) := by
    have h1 : (2 * k * s + t) / (2 * t) < slK s t k + 1 := by
      rw [slK]; exact Nat.lt_succ_self _
    exact (Nat.div_lt_iff_lt_mul h2t).mp h1
  have hltR : ((2 * k * s + t : ℕ) : ℝ) < ((slK s t k : ℝ) + 1) * (2 * (t : ℝ)) := by
    exact_mod_cast hlt
  push_cast at hltR
  have hdiv : ((2 * k * s + t : ℕ) : ℝ) / ((2 * t : ℕ) : ℝ) < (slK s t k : ℝ) + 1 := by
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < (2 * t : ℕ))]
    push_cast
    linarith [hltR]
  have heq : ((2 * k * s + t : ℕ) : ℝ) / ((2 * t : ℕ) : ℝ)
      = (k : ℝ) * s / t + 1 / 2 := by
    push_cast
    field_simp
  linarith [hdiv, heq.le, heq.ge]

/-! ## The extended list `slExt` -/

lemma slExt_length (p α s : ℕ) (hs : 2 ≤ s) (u : List (ℤ × ℤ)) (hu : u.length = s) :
    (slExt p α s u).length = s + slL p α s := by
  have hh : slH p α s ≤ s := slH_le_s p α s hs
  have hL : slL p α s ≤ s := slL_le_s p α s
  have hhL : slH p α s ≤ slL p α s := slH_le_slL p α s
  have htake : min (slL p α s - slH p α s) s = slL p α s - slH p α s :=
    Nat.min_eq_left (by omega)
  rw [slExt, List.length_append, List.length_append, List.length_drop, List.length_take,
    hu, htake]
  have h1 : s - (s - slH p α s) = slH p α s := by omega
  rw [h1]
  omega

lemma slExt_getElem? (p α s : ℕ) (hs : 2 ≤ s) (u : List (ℤ × ℤ)) (hu : u.length = s)
    {i : ℕ} (hi : i < s + slL p α s) :
    (slExt p α s u)[i]? = u[((i + s - slH p α s) % s)]? := by
  have hh : slH p α s ≤ s := slH_le_s p α s hs
  have hL : slL p α s ≤ s := slL_le_s p α s
  have hhL : slH p α s ≤ slL p α s := slH_le_slL p α s
  have hdrop : (u.drop (s - slH p α s)).length = slH p α s := by
    rw [List.length_drop, hu]; omega
  have htot : (u.drop (s - slH p α s) ++ u).length = slH p α s + s := by
    rw [List.length_append, hdrop, hu]
  have htake : slL p α s - slH p α s ≤ s := by omega
  rw [slExt, List.getElem?_append, List.getElem?_append, List.getElem?_drop,
    List.getElem?_take]
  rw [htot, hdrop]
  by_cases h1 : i < slH p α s
  · rw [if_pos h1, if_pos (by omega), Nat.mod_eq_of_lt (by omega)]
    congr 1
    omega
  · by_cases h2 : i < slH p α s + s
    · have hmod : i + s - slH p α s = (i - slH p α s) + s := by omega
      rw [if_pos h2, if_neg h1, hmod, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    · have hlt : i - (slH p α s + s) < slL p α s - slH p α s := by omega
      rw [if_neg h2, if_pos hlt]
      have hmod : i + s - slH p α s = (i - (slH p α s + s)) + 2 * s := by omega
      rw [hmod, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

theorem sliceA1Ext (p α s t : ℕ) (hs : 2 ≤ s) (ht : 0 < t) (hst : s ≤ t) :
    Work.Resample.slL p α s ≤ s ∧ 1 ≤ Work.Resample.slL p α s ∧
    Work.Resample.slH p α s ≤ s ∧ Work.Resample.slH p α s ≤ Work.Resample.slL p α s ∧
    Work.Resample.slL p α s - Work.Resample.slH p α s ≤ s ∧
    (∀ k : ℕ, Work.Resample.slK s t k ≤ Work.Resample.slK s t (k + 1)) ∧
    (∀ k : ℕ, Work.Resample.slD s t k ≤ 1) ∧
    Work.Resample.slK s t 0 = 0 ∧
    (∀ k : ℕ, (Work.Resample.slK s t k : ℝ) ≤ (k : ℝ) * s / t + 1 / 2) ∧
    (∀ k : ℕ, (k : ℝ) * s / t - 1 / 2 ≤ (Work.Resample.slK s t k : ℝ)) ∧
    (Work.Resample.slL p α s < s →
      Work.Resample.slL p α s = 2 * Work.Resample.slM p α + 1 ∧
      Work.Resample.slH p α s = Work.Resample.slM p α) ∧
    (∀ u : List (ℤ × ℤ), u.length = s →
      (Work.Resample.slExt p α s u).length = s + Work.Resample.slL p α s) ∧
    (∀ u : List (ℤ × ℤ), u.length = s → ∀ i, i < s + Work.Resample.slL p α s →
      (Work.Resample.slExt p α s u).getD i (0, 0) =
        u.getD ((i + s - Work.Resample.slH p α s) % s) (0, 0)) := by
  refine ⟨slL_le_s p α s, slL_pos p α s hs, slH_le_s p α s hs, slH_le_slL p α s,
    slL_sub_slH_le_s p α s, ?_, ?_, slK_zero s t ht, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; exact slK_mono s t k
  · intro k; exact slD_le_one s t k hst ht
  · intro k; exact slK_le' s t k ht
  · intro k; exact slK_ge' s t k ht
  · intro h; exact ⟨slL_eq_of_lt p α s h, slH_eq_of_lt p α s h⟩
  · intro u hu; exact slExt_length p α s hs u hu
  · intro u hu i hi
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      slExt_getElem? p α s hs u hu hi]

end Work.Resample
