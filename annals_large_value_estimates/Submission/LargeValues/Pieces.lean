import Submission.LargeValues.KeyProp

open LargeValueEstimates
open Asymptotics Complex
set_option autoImplicit false

/-!
# The three pieces of `[N,2N]` and their rescaled lengths

In the reduction of Guth–Maynard Theorem 1.1 to Proposition 4.1 the sum
`∑_{n∈[N,2N]} b_n n^{it}` is split into the three pieces
`[N,6N/5]`, `[6N/5,9N/5]`, `[9N/5,2N]`.  The middle piece is exactly the region where the
smoothing bump `w(·/N)` equals `1`; the outer pieces are handled by the same Proposition 4.1
applied with rescaled length `N' = 5N/6` (left) and `N' = 3N/2` (right), for which the region
`w(n/N') = 1` is `n ∈ [6N'/5, 9N'/5] ⊇` the corresponding piece.
-/

namespace Submission.LargeValues

/-- Index of the piece of `[N,2N]` containing `n`:
`0` if `n < 6N/5`, `1` if `6N/5 ≤ n ≤ 9N/5`, `2` if `n > 9N/5`. -/
noncomputable def pieceIdx (N n : ℕ) : ℕ :=
  if 5 * (n : ℝ) < 6 * (N : ℝ) then 0
  else if 5 * (n : ℝ) ≤ 9 * (N : ℝ) then 1 else 2

/-- The `i`-th piece of `[N,2N]`. -/
noncomputable def pieceSet (N i : ℕ) : Finset ℕ :=
  (Finset.Icc N (2 * N)).filter (fun n => pieceIdx N n = i)

/-- Rescaled length attached to the `i`-th piece. -/
def scaledN (N i : ℕ) : ℕ :=
  if i = 0 then 5 * N / 6 else if i = 1 then N else 3 * N / 2

/-- The `i`-th piece sum. -/
noncomputable def pieceSum (N i : ℕ) (b : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ pieceSet N i, b n * (n : ℂ) ^ (I * (t : ℂ))

lemma pieceIdx_lt_three (N n : ℕ) : pieceIdx N n < 3 := by
  unfold pieceIdx; split_ifs <;> omega

private lemma pieceIdx_zero (N n : ℕ) (h : pieceIdx N n = 0) : 5 * (n : ℝ) < 6 * (N : ℝ) := by
  by_contra hc
  rw [not_lt] at hc
  by_cases h2 : 5 * (n : ℝ) ≤ 9 * (N : ℝ)
  · have h1 : pieceIdx N n = 1 := by unfold pieceIdx; rw [if_neg (not_lt.mpr hc), if_pos h2]
    omega
  · have h1 : pieceIdx N n = 2 := by unfold pieceIdx; rw [if_neg (not_lt.mpr hc), if_neg h2]
    omega

private lemma pieceIdx_two (N n : ℕ) (h : pieceIdx N n = 2) : 9 * (N : ℝ) < 5 * (n : ℝ) := by
  by_contra hc
  rw [not_lt] at hc
  by_cases h1 : 5 * (n : ℝ) < 6 * (N : ℝ)
  · have : pieceIdx N n = 0 := by unfold pieceIdx; rw [if_pos h1]
    omega
  · have : pieceIdx N n = 1 := by unfold pieceIdx; rw [if_neg h1, if_pos hc]
    omega

private lemma pieceIdx_one (N n : ℕ) (h : pieceIdx N n = 1) :
    6 * (N : ℝ) ≤ 5 * (n : ℝ) ∧ 5 * (n : ℝ) ≤ 9 * (N : ℝ) := by
  constructor
  · by_contra hc
    rw [not_le] at hc
    have h1 : pieceIdx N n = 0 := by unfold pieceIdx; rw [if_pos hc]
    omega
  · by_contra hc
    rw [not_le] at hc
    by_cases h0 : 5 * (n : ℝ) < 6 * (N : ℝ)
    · have h1 : pieceIdx N n = 0 := by unfold pieceIdx; rw [if_pos h0]
      omega
    · have h1 : pieceIdx N n = 2 := by
        unfold pieceIdx; rw [if_neg h0, if_neg (not_le.mpr hc)]
      omega

/-- The three pieces partition `[N,2N]`. -/
theorem sum_pieceSet (N : ℕ) (f : ℕ → ℂ) :
    ∑ i ∈ Finset.range 3, ∑ n ∈ pieceSet N i, f n
      = ∑ n ∈ Finset.Icc N (2 * N), f n := by
  have hmap : ∀ n ∈ Finset.Icc N (2 * N), pieceIdx N n ∈ Finset.range 3 :=
    fun n _ => Finset.mem_range.mpr (pieceIdx_lt_three N n)
  have := Finset.sum_fiberwise_of_maps_to hmap f
  simpa [pieceSet] using this

lemma le_six_mul_div (N : ℕ) : 5 * N ≤ 6 * (5 * N / 6) + 5 := by
  have h := Nat.div_add_mod (5 * N) 6
  have h2 := Nat.mod_lt (5 * N) (by norm_num : 0 < 6)
  omega

lemma le_two_mul_div (N : ℕ) : 3 * N ≤ 2 * (3 * N / 2) + 2 := by
  have h := Nat.div_add_mod (3 * N) 2
  have h2 := Nat.mod_lt (3 * N) (by norm_num : 0 < 2)
  omega

lemma mul_div_le_six (N : ℕ) : 6 * (5 * N / 6) ≤ 5 * N := by
  have := Nat.div_mul_le_self (5 * N) 6
  omega

lemma mul_div_le_two (N : ℕ) : 2 * (3 * N / 2) ≤ 3 * N := by
  have := Nat.div_mul_le_self (3 * N) 2
  omega

/-- Real bounds on the rescaled lengths: `N/2 ≤ N_i ≤ 2N`. -/
theorem scaledN_bounds (N : ℕ) (hN : 3 ≤ N) {i : ℕ} (hi : i < 3) :
    (N : ℝ) / 2 ≤ (scaledN N i : ℝ) ∧ (scaledN N i : ℝ) ≤ 2 * (N : ℝ) := by
  have hNr : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have c1 : 5 * (N : ℝ) ≤ 6 * ((5 * N / 6 : ℕ) : ℝ) + 5 := by
    exact_mod_cast le_six_mul_div N
  have c2 : 6 * ((5 * N / 6 : ℕ) : ℝ) ≤ 5 * (N : ℝ) := by exact_mod_cast mul_div_le_six N
  have c3 : 3 * (N : ℝ) ≤ 2 * ((3 * N / 2 : ℕ) : ℝ) + 2 := by
    exact_mod_cast le_two_mul_div N
  have c4 : 2 * ((3 * N / 2 : ℕ) : ℝ) ≤ 3 * (N : ℝ) := by exact_mod_cast mul_div_le_two N
  interval_cases i
  · have h0 : scaledN N 0 = 5 * N / 6 := by simp [scaledN]
    rw [h0]
    exact ⟨by linarith, by linarith⟩
  · have h0 : scaledN N 1 = N := by simp [scaledN]
    rw [h0]; exact ⟨by linarith, by linarith⟩
  · have h0 : scaledN N 2 = 3 * N / 2 := by simp [scaledN]
    rw [h0]
    exact ⟨by linarith, by linarith⟩

/-- The `i`-th piece is contained in `[N_i, 2N_i]`. -/
theorem pieceSet_subset_Icc {N : ℕ} (hN : 6 ≤ N) {i : ℕ} (hi : i < 3) {n : ℕ}
    (hn : n ∈ pieceSet N i) : n ∈ Finset.Icc (scaledN N i) (2 * scaledN N i) := by
  classical
  have hnIcc : n ∈ Finset.Icc N (2 * N) := (Finset.mem_filter.mp hn).1
  have hidx : pieceIdx N n = i := (Finset.mem_filter.mp hn).2
  obtain ⟨hNn, hn2⟩ := Finset.mem_Icc.mp hnIcc
  have hNnr : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
  have hn2r : (n : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hn2
  have hNr : (6 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have c1 : 5 * (N : ℝ) ≤ 6 * ((5 * N / 6 : ℕ) : ℝ) + 5 := by exact_mod_cast le_six_mul_div N
  have c2 : 6 * ((5 * N / 6 : ℕ) : ℝ) ≤ 5 * (N : ℝ) := by exact_mod_cast mul_div_le_six N
  have c3 : 3 * (N : ℝ) ≤ 2 * ((3 * N / 2 : ℕ) : ℝ) + 2 := by exact_mod_cast le_two_mul_div N
  have c4 : 2 * ((3 * N / 2 : ℕ) : ℝ) ≤ 3 * (N : ℝ) := by exact_mod_cast mul_div_le_two N
  have key : (scaledN N i : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (scaledN N i : ℝ) := by
    interval_cases i
    · have h0 : scaledN N 0 = 5 * N / 6 := by simp [scaledN]
      rw [h0]
      have hb : ((5 * N / 6 : ℕ) : ℝ) ≤ (N : ℝ) := by linarith
      constructor
      · linarith
      · nlinarith [pieceIdx_zero N n hidx, c1, hNnr]
    · have h0 : scaledN N 1 = N := by simp [scaledN]
      rw [h0]; exact ⟨hNnr, hn2r⟩
    · have h0 : scaledN N 2 = 3 * N / 2 := by simp [scaledN]
      rw [h0]
      constructor
      · nlinarith [pieceIdx_two N n hidx, hNnr]
      · nlinarith [c3, hn2r, hNr]
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast key.1, by exact_mod_cast key.2⟩

/-- The window condition: on the `i`-th piece the rescaled argument lies in `[6/5,9/5]`,
so the bump `w` equals `1` there. -/
theorem pieceSet_window {N : ℕ} (hN : 6 ≤ N) {i : ℕ} (hi : i < 3) {n : ℕ}
    (hn : n ∈ pieceSet N i) :
    (6 / 5 : ℝ) ≤ (n : ℝ) / (scaledN N i : ℝ) ∧
      (n : ℝ) / (scaledN N i : ℝ) ≤ (9 / 5 : ℝ) := by
  classical
  have hnIcc : n ∈ Finset.Icc N (2 * N) := (Finset.mem_filter.mp hn).1
  have hidx : pieceIdx N n = i := (Finset.mem_filter.mp hn).2
  obtain ⟨hNn, hn2⟩ := Finset.mem_Icc.mp hnIcc
  have hNnr : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
  have hn2r : (n : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hn2
  have hNr : (6 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have c1 : 5 * (N : ℝ) ≤ 6 * ((5 * N / 6 : ℕ) : ℝ) + 5 := by exact_mod_cast le_six_mul_div N
  have c2 : 6 * ((5 * N / 6 : ℕ) : ℝ) ≤ 5 * (N : ℝ) := by exact_mod_cast mul_div_le_six N
  have c3 : 3 * (N : ℝ) ≤ 2 * ((3 * N / 2 : ℕ) : ℝ) + 2 := by exact_mod_cast le_two_mul_div N
  have c4 : 2 * ((3 * N / 2 : ℕ) : ℝ) ≤ 3 * (N : ℝ) := by exact_mod_cast mul_div_le_two N
  have hpos : (0 : ℝ) < (scaledN N i : ℝ) := by
    have h := (scaledN_bounds N (by omega) hi).1
    linarith
  rw [le_div_iff₀ hpos, div_le_iff₀ hpos]
  interval_cases i
  · have h0 : scaledN N 0 = 5 * N / 6 := by simp [scaledN]
    rw [h0]
    constructor
    · nlinarith [c2, hNnr]
    · nlinarith [pieceIdx_zero N n hidx, c1, hNr]
  · have h0 : scaledN N 1 = N := by simp [scaledN]
    rw [h0]
    obtain ⟨h1, h2⟩ := pieceIdx_one N n hidx
    constructor <;> linarith
  · have h0 : scaledN N 2 = 3 * N / 2 := by simp [scaledN]
    rw [h0]
    constructor
    · nlinarith [pieceIdx_two N n hidx, c4]
    · nlinarith [c3, hn2r, hNr]
end Submission.LargeValues
