import Mathlib
import Submission.Work.KMTPlan.A6.lacunaryCard

namespace Work.KMTPlan.A6

open Finset
open scoped NNReal

/-- A lacunary sequence with `a n ≥ 1` grows at least geometrically: `Λ ^ d * a n ≤ a (n + d)`. -/
private lemma pow_mul_le_of_lacunary {Λ : ℝ≥0} {a : ℕ → ℝ≥0}
    (ha : ∀ n, a (n + 1) / a n > Λ) (ha1 : ∀ n, 1 ≤ a n) :
    ∀ d n, Λ ^ d * a n ≤ a (n + d) := by
  intro d
  induction d with
  | zero => intro n; simp
  | succ k ih =>
    intro n
    have hpos : (0 : ℝ≥0) < a (n + k) := lt_of_lt_of_le zero_lt_one (ha1 (n + k))
    have hstep : Λ * a (n + k) ≤ a (n + (k + 1)) :=
      le_of_lt ((lt_div_iff₀ hpos).mp (ha (n + k)))
    calc Λ ^ (k + 1) * a n = Λ * (Λ ^ k * a n) := by rw [pow_succ]; ring
      _ ≤ Λ * a (n + k) := mul_le_mul_of_nonneg_left (ih n) (by positivity)
      _ ≤ a (n + (k + 1)) := hstep

/-- **Counting a multiplicative window of a lacunary sequence.**
For `Λ > 1` and a `Λ`-lacunary sequence `a` with `a n ≥ 1`, the number of indices `m < K` with
`A ≤ ⌊a m⌋ < 8 A` is bounded by a constant depending on `Λ` only (namely
`log 9 / log Λ + 1`), uniformly in `K` and in `A > 0`.

The proof: if the set `S` of such indices is non-empty and `m₀ = min S`, then for every `m ∈ S`
lacunarity gives `Λ ^ (m - m₀) * a m₀ ≤ a m`, while `A ≤ ⌊a m₀⌋ ≤ a m₀`, `a m₀ ≥ 1` and
`a m < ⌊a m⌋ + 1 < 8 A + 1 ≤ 9 max A 1`.  Hence `Λ ^ (m - m₀) < 9`, i.e.
`m - m₀ < log 9 / log Λ`, and `S` is contained in an interval of length `⌊log 9 / log Λ⌋`. -/
theorem lacWindow_card (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → NNReal), PointwiseErgodicTheorems.Lacunary Λ a →
      (∀ n, 1 ≤ a n) → ∀ (K : ℕ) (A : ℝ), 0 < A →
      (((Finset.range K).filter (fun m => A ≤ (Nat.floor (a m) : ℝ) ∧
          (Nat.floor (a m) : ℝ) < 8 * A)).card : ℝ) ≤ C := by
  refine ⟨Real.log 9 / Real.log (Λ : ℝ) + 1, ?_, ?_⟩
  · have hΛ1 : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
    have h9 : 0 < Real.log (9 : ℝ) := Real.log_pos (by norm_num)
    have hΛl : 0 < Real.log (Λ : ℝ) := Real.log_pos hΛ1
    linarith [div_pos h9 hΛl]
  · intro a ha ha1 K A hA
    have hΛ1 : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
    have hΛl : 0 < Real.log (Λ : ℝ) := Real.log_pos hΛ1
    set L : ℝ := Real.log 9 / Real.log (Λ : ℝ) with hLdef
    have hL0 : 0 ≤ L := by
      rw [hLdef]
      exact div_nonneg (Real.log_nonneg (by norm_num)) hΛl.le
    have hCpos : 0 < L + 1 := by linarith
    set S : Finset ℕ := (Finset.range K).filter (fun m => A ≤ (Nat.floor (a m) : ℝ) ∧
          (Nat.floor (a m) : ℝ) < 8 * A) with hSdef
    by_cases hne : S.Nonempty
    · set m₀ : ℕ := S.min' hne with hm₀def
      have hminmem : m₀ ∈ S := Finset.min'_mem S hne
      have hsub : S ⊆ Finset.Icc m₀ (m₀ + ⌊L⌋₊) := by
        intro m hm
        have hm0le : m₀ ≤ m := Finset.min'_le S m hm
        rw [Finset.mem_Icc]
        refine ⟨hm0le, ?_⟩
        have hmf := Finset.mem_filter.mp hm
        -- `A ≤ a m₀`
        have hA0 : A ≤ (a m₀ : ℝ) := by
          have h := (Finset.mem_filter.mp hminmem).2.1
          have hfl : ((Nat.floor (a m₀) : ℕ) : ℝ) ≤ (a m₀ : ℝ) := by
            have h' : (↑(⌊a m₀⌋₊) : NNReal) ≤ a m₀ := Nat.floor_le (by positivity)
            exact_mod_cast h'
          linarith
        -- `a m < 8 A + 1`
        have hAm : (a m : ℝ) < 8 * A + 1 := by
          have h := hmf.2.2
          have hfl : (a m : ℝ) < ((Nat.floor (a m) : ℕ) : ℝ) + 1 := by
            have h' : a m < ↑(⌊a m⌋₊) + 1 := Nat.lt_floor_add_one (a m)
            exact_mod_cast h'
          linarith
        -- `a m₀ ≥ max A 1`
        have hPle : max A 1 ≤ (a m₀ : ℝ) :=
          max_le hA0 (by exact_mod_cast ha1 m₀)
        -- `8 A + 1 ≤ 9 max A 1`
        have h81 : 8 * A + 1 ≤ 9 * max A 1 := by
          rcases lt_or_ge A 1 with h | h
          · rw [max_eq_right h.le]; linarith
          · rw [max_eq_left h]; linarith
        -- geometric growth
        have hpow := pow_mul_le_of_lacunary ha ha1 (m - m₀) m₀
        rw [Nat.add_sub_cancel' hm0le] at hpow
        have hpowR : (Λ : ℝ) ^ (m - m₀) * (a m₀ : ℝ) ≤ (a m : ℝ) := by
          have h := NNReal.coe_le_coe.mpr hpow
          push_cast at h
          exact h
        -- `Λ ^ (m - m₀) < 9`
        have hmaxpos : 0 < max A 1 := lt_of_lt_of_le one_pos (le_max_right A 1)
        have hlt9 : (Λ : ℝ) ^ (m - m₀) < 9 := by
          have h1 : (Λ : ℝ) ^ (m - m₀) * max A 1 ≤ (Λ : ℝ) ^ (m - m₀) * (a m₀ : ℝ) :=
            mul_le_mul_of_nonneg_left hPle (by positivity)
          have h2 : (Λ : ℝ) ^ (m - m₀) * max A 1 < 9 * max A 1 := by linarith
          nlinarith [h2, hmaxpos]
        -- hence `m - m₀ ≤ L`
        have hmain : ((m - m₀ : ℕ) : ℝ) ≤ L := by
          have hlogle : ((m - m₀ : ℕ) : ℝ) * Real.log (Λ : ℝ) < Real.log 9 := by
            have hpos : (0 : ℝ) < (Λ : ℝ) ^ (m - m₀) := by positivity
            have h := Real.log_lt_log hpos hlt9
            rwa [Real.log_pow] at h
          rw [hLdef, le_div_iff₀ hΛl]
          exact le_of_lt hlogle
        have hfl : m - m₀ ≤ ⌊L⌋₊ := Nat.le_floor hmain
        omega
      have hcard : S.card ≤ ⌊L⌋₊ + 1 := by
        have h1 : S.card ≤ (Finset.Icc m₀ (m₀ + ⌊L⌋₊)).card := Finset.card_le_card hsub
        have h2 : (Finset.Icc m₀ (m₀ + ⌊L⌋₊)).card = ⌊L⌋₊ + 1 := by
          simp
          omega
        omega
      calc (S.card : ℝ) ≤ ((⌊L⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = (⌊L⌋₊ : ℝ) + 1 := by push_cast; ring
        _ ≤ L + 1 := by
            have hfl : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le hL0
            linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp only [Finset.card_empty, Nat.cast_zero]
      linarith

end Work.KMTPlan.A6
