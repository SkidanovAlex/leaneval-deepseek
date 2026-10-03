import Mathlib
import Submission.Commons.Analysis.ExponentialSums.second_derivative_test

namespace Commons.Analysis.ExponentialSums

open Finset
open scoped BigOperators Real

/-- **Interval counting**: a finite set of natural numbers all lying in a real
interval `[a, b]` (with `a ≤ b`) has at most `b - a + 1` elements. -/
private lemma card_nat_le_of_bounded (S : Finset ℕ) {a b : ℝ} (hab : a ≤ b)
    (hS : ∀ n ∈ S, a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b) : (S.card : ℝ) ≤ b - a + 1 := by
  by_cases hS0 : S = ∅
  · rw [hS0, Finset.card_empty, Nat.cast_zero]
    linarith
  · obtain ⟨n0, hn0⟩ := Finset.nonempty_iff_ne_empty.mpr hS0
    obtain ⟨_, hb0'⟩ := hS n0 hn0
    have hb0 : (0 : ℝ) ≤ b := le_trans (Nat.cast_nonneg n0) hb0'
    have hsub : S ⊆ Finset.Icc (Nat.ceil a) (Nat.floor b) := by
      intro n hn
      obtain ⟨h1, h2⟩ := hS n hn
      rw [Finset.mem_Icc]
      exact ⟨(Nat.ceil_le).mpr h1, Nat.le_floor h2⟩
    have hcard : (S.card : ℝ) ≤ ((Finset.Icc (Nat.ceil a) (Nat.floor b)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hle : Nat.ceil a ≤ Nat.floor b := by
      obtain ⟨h1, h2⟩ := hS n0 hn0
      exact le_trans (Nat.ceil_le.mpr h1) (Nat.le_floor h2)
    refine le_trans hcard ?_
    rw [Nat.card_Icc]
    have hcast : (((Nat.floor b + 1 - Nat.ceil a : ℕ) : ℝ)) =
        (Nat.floor b : ℝ) - (Nat.ceil a : ℝ) + 1 := by
      have h1 : Nat.ceil a ≤ Nat.floor b + 1 := by omega
      rw [Nat.cast_sub h1]
      push_cast
      ring
    rw [hcast]
    have hb : (Nat.floor b : ℝ) ≤ b := Nat.floor_le hb0
    have ha : a ≤ (Nat.ceil a : ℝ) := Nat.le_ceil a
    linarith

/-- **Nearest integer in `{0,1,2}`**: for `x ∈ [0,2)` the `intDist` to the nearest
integer is realized by one of `0, 1, 2`. -/
private lemma exists_abs_le_of_intDist_le {x ε : ℝ} (hx0 : 0 ≤ x) (hx2 : x < 2)
    (h : Submission.VanDerCorput.intDist x ≤ ε) :
    ∃ k ∈ ({0, 1, 2} : Finset ℤ), |x - (k : ℝ)| ≤ ε := by
  set n : ℤ := ⌊x⌋ with hn
  set f : ℝ := Int.fract x with hf
  have hxn : x = (n : ℝ) + f := by
    rw [hn, hf]
    exact (Int.floor_add_fract x).symm
  have hf0 : 0 ≤ f := by rw [hf]; exact Int.fract_nonneg x
  have hf1 : f < 1 := by rw [hf]; exact Int.fract_lt_one x
  have hn0 : 0 ≤ n := by rw [hn]; exact (Int.floor_nonneg).mpr hx0
  have hn2 : n ≤ 1 := by
    rw [hn]
    have hlt : ⌊x⌋ < 2 := by rw [Int.floor_lt]; exact_mod_cast hx2
    omega
  have hdist : Submission.VanDerCorput.intDist x = min f (1 - f) := by
    rw [Submission.VanDerCorput.intDist, ← hf]
  by_cases hcase : f ≤ (1 / 2 : ℝ)
  · refine ⟨n, ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · have hmin : min f (1 - f) = f := min_eq_left (by linarith)
      have hthis : Submission.VanDerCorput.intDist x = f := by rw [hdist, hmin]
      have hxk : |x - (n : ℝ)| = f := by
        rw [hxn, show (n : ℝ) + f - (n : ℝ) = f by ring]
        exact abs_of_nonneg hf0
      rw [hxk, ← hthis]
      exact h
  · push Not at hcase
    refine ⟨n + 1, ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · have hmin : min f (1 - f) = 1 - f := min_eq_right (by linarith)
      have hthis : Submission.VanDerCorput.intDist x = 1 - f := by rw [hdist, hmin]
      have hxk : |x - ((n + 1 : ℤ) : ℝ)| = 1 - f := by
        rw [hxn]
        have h2 : (n : ℝ) + f - ((n + 1 : ℤ) : ℝ) = f - 1 := by push_cast; ring
        rw [h2, abs_of_nonpos (by linarith : f - 1 ≤ 0)]
        ring
      rw [hxk, ← hthis]
      exact h

theorem card_small_intDist_residues (q : ℕ) (hq : 0 < q) {ε : ℝ} (hε : 0 ≤ ε) :
    ((Finset.filter (fun s : ℕ => Submission.VanDerCorput.intDist (2 * (s:ℝ) / (q:ℝ)) ≤ ε)
        (Finset.range q)).card : ℝ) ≤ 4 * (q:ℝ) * ε + 4 := by
  classical
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  set S : Finset ℕ :=
    Finset.filter (fun s : ℕ => Submission.VanDerCorput.intDist (2 * (s:ℝ) / (q:ℝ)) ≤ ε)
      (Finset.range q) with hSdef
  set B : ℤ → Finset ℕ :=
    fun k => Finset.filter (fun s : ℕ => |2 * (s:ℝ) / (q:ℝ) - (k:ℝ)| ≤ ε)
      (Finset.range q) with hBdef
  have memS : ∀ s : ℕ, s ∈ S ↔ s < q ∧
      Submission.VanDerCorput.intDist (2 * (s:ℝ) / (q:ℝ)) ≤ ε := by
    intro s
    rw [hSdef]
    simp [Finset.mem_filter, Finset.mem_range]
  have memB : ∀ (k : ℤ) (s : ℕ), s ∈ B k ↔ s < q ∧
      |2 * (s:ℝ) / (q:ℝ) - (k:ℝ)| ≤ ε := by
    intro k s
    rw [hBdef]
    simp [Finset.mem_filter, Finset.mem_range]
  -- Step 1: every good residue is within `ε` of one of `0, 1, 2`.
  have hsub : S ⊆ ({0, 1, 2} : Finset ℤ).biUnion B := by
    intro s hs
    rw [memS] at hs
    obtain ⟨hslt, hscond⟩ := hs
    have hsle : (s : ℝ) < (q : ℝ) := by exact_mod_cast hslt
    have hx0 : 0 ≤ 2 * (s : ℝ) / (q : ℝ) := by positivity
    have hx2 : 2 * (s : ℝ) / (q : ℝ) < 2 := by
      rw [div_lt_iff₀ hqpos]
      nlinarith [hsle]
    obtain ⟨k, hkmem, hk⟩ := exists_abs_le_of_intDist_le hx0 hx2 hscond
    rw [Finset.mem_biUnion]
    exact ⟨k, hkmem, (memB k s).mpr ⟨hslt, hk⟩⟩
  -- Step 2: card `S` ≤ sum of the three cardinalities.
  have hcard : (S.card : ℝ) ≤ ∑ k ∈ ({0, 1, 2} : Finset ℤ), ((B k).card : ℝ) := by
    have h1 : S.card ≤ (({0, 1, 2} : Finset ℤ).biUnion B).card := Finset.card_le_card hsub
    have h2 : (({0, 1, 2} : Finset ℤ).biUnion B).card ≤
        ∑ k ∈ ({0, 1, 2} : Finset ℤ), (B k).card := Finset.card_biUnion_le
    calc (S.card : ℝ) ≤ ((({0, 1, 2} : Finset ℤ).biUnion B).card : ℝ) := by exact_mod_cast h1
      _ ≤ ((∑ k ∈ ({0, 1, 2} : Finset ℤ), (B k).card : ℕ) : ℝ) := by exact_mod_cast h2
      _ = ∑ k ∈ ({0, 1, 2} : Finset ℤ), ((B k).card : ℝ) := by push_cast; ring
  -- Step 3: each `B k` has at most `q * ε + 1` elements.
  have hterm : ∀ k ∈ ({0, 1, 2} : Finset ℤ), ((B k).card : ℝ) ≤ (q : ℝ) * ε + 1 := by
    intro k _
    have hle : ((q : ℝ) * (k : ℝ) - (q : ℝ) * ε) / 2 ≤
        ((q : ℝ) * (k : ℝ) + (q : ℝ) * ε) / 2 := by
      nlinarith [hε, hqpos]
    have hbound : ∀ n ∈ B k, ((q : ℝ) * (k : ℝ) - (q : ℝ) * ε) / 2 ≤ (n : ℝ) ∧
        (n : ℝ) ≤ ((q : ℝ) * (k : ℝ) + (q : ℝ) * ε) / 2 := by
      intro n hn
      rw [memB] at hn
      obtain ⟨_, hncond⟩ := hn
      have habs : |2 * (n : ℝ) - (q : ℝ) * (k : ℝ)| ≤ (q : ℝ) * ε := by
        have hmul := mul_le_mul_of_nonneg_left hncond (le_of_lt hqpos)
        have heq : (q : ℝ) * |2 * (n : ℝ) / (q : ℝ) - (k : ℝ)| =
            |2 * (n : ℝ) - (q : ℝ) * (k : ℝ)| := by
          rw [show (q : ℝ) * |2 * (n : ℝ) / (q : ℝ) - (k : ℝ)| =
              |(q : ℝ)| * |2 * (n : ℝ) / (q : ℝ) - (k : ℝ)| by
                rw [abs_of_pos hqpos]]
          rw [← abs_mul]
          congr 1
          field_simp
        rwa [heq] at hmul
      have h1 := (abs_le.mp habs).1
      have h2 := (abs_le.mp habs).2
      constructor <;> nlinarith
    have hmain := card_nat_le_of_bounded (B k) hle hbound
    have hba : ((q : ℝ) * (k : ℝ) + (q : ℝ) * ε) / 2 -
        ((q : ℝ) * (k : ℝ) - (q : ℝ) * ε) / 2 + 1 = (q : ℝ) * ε + 1 := by ring
    rwa [hba] at hmain
  -- Step 4: put everything together.
  have hcard3 : ({0, 1, 2} : Finset ℤ).card = 3 := by decide
  have hsum : ∑ k ∈ ({0, 1, 2} : Finset ℤ), ((B k).card : ℝ) ≤ 3 * ((q : ℝ) * ε + 1) := by
    calc ∑ k ∈ ({0, 1, 2} : Finset ℤ), ((B k).card : ℝ)
        ≤ ∑ _k ∈ ({0, 1, 2} : Finset ℤ), ((q : ℝ) * ε + 1) := Finset.sum_le_sum hterm
      _ = 3 * ((q : ℝ) * ε + 1) := by
          rw [Finset.sum_const, hcard3, nsmul_eq_mul]
          norm_num
  calc (S.card : ℝ) ≤ ∑ k ∈ ({0, 1, 2} : Finset ℤ), ((B k).card : ℝ) := hcard
    _ ≤ 3 * ((q : ℝ) * ε + 1) := hsum
    _ ≤ 4 * (q : ℝ) * ε + 4 := by nlinarith [hε, hqpos]

end Commons.Analysis.ExponentialSums
