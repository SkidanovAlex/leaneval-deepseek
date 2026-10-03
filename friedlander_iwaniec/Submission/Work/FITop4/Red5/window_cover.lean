/-
# `Submission.Work.FITop4.Red5.window_cover` — the window ladder covers the whole `m`-range

The outer `m`-sum of `BformPiTau` runs over `1 ≤ m ≤ ⌊x/N⌋`.  The proof of the
reduction chops it into the pieces of the ladder

* the small-`m` block `1 ≤ m ≤ M₀`,
* the dyadic windows `(2^j M₀, 2^{j+1} M₀]` for `j < JJ`,
* the top window `(M_top, 2 M_top]`.

This file records the purely combinatorial fact that these pieces cover the
range `1 ≤ m ≤ 2 M_top` (with `M_top = ⌊x/(2N)⌋`), and hence that the total
`m`-mass of the whole range is at most the sum of the masses of the pieces.
No number theory enters; only `M_top < 2^JJ M₀` and `M₀ ≥ 2` are used.
-/
import Mathlib
import Submission.Work.FITop4.Red5.window_setup

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

/-- `∑` over a union is at most the sum of the two sums, for a nonnegative summand. -/
lemma sum_union_le_of_nonneg (s t : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ m, 0 ≤ f m) :
    ∑ m ∈ s ∪ t, f m ≤ ∑ m ∈ s, f m + ∑ m ∈ t, f m := by
  have hdisj : Disjoint (s \ t) t := (Finset.disjoint_sdiff (s := t) (t := s)).symm
  calc ∑ m ∈ s ∪ t, f m = ∑ m ∈ (s \ t) ∪ t, f m := by rw [Finset.sdiff_union_self_eq_union]
    _ = ∑ m ∈ s \ t, f m + ∑ m ∈ t, f m := Finset.sum_union hdisj
    _ ≤ ∑ m ∈ s, f m + ∑ m ∈ t, f m := by
        have h := Finset.sum_le_sum_of_subset_of_nonneg (f := f) (s := s \ t) (t := s)
          Finset.sdiff_subset (fun i _ _ => hf i)
        linarith

/-- `∑` over a binary union is at most the iterated sum, for a nonnegative summand. -/
lemma sum_biUnion_le_of_nonneg (s : Finset ℕ) (t : ℕ → Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ m, 0 ≤ f m) :
    ∑ m ∈ s.biUnion t, f m ≤ ∑ j ∈ s, ∑ m ∈ t j, f m := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.biUnion_insert]
      calc ∑ m ∈ t a ∪ s.biUnion t, f m
          ≤ ∑ m ∈ t a, f m + ∑ m ∈ s.biUnion t, f m := sum_union_le_of_nonneg _ _ f hf
        _ ≤ ∑ m ∈ t a, f m + ∑ j ∈ s, ∑ m ∈ t j, f m := by linarith
        _ = ∑ j ∈ insert a s, ∑ m ∈ t j, f m := by rw [Finset.sum_insert ha]

/-- For `1 ≤ a < m` there is a dyadic window `(2^j a, 2^{j+1} a]` containing `m`. -/
lemma exists_dyadic_window {a m : ℕ} (ha : 1 ≤ a) (hm : a < m) :
    ∃ j : ℕ, 2 ^ j * a < m ∧ m ≤ 2 ^ (j + 1) * a := by
  have hp : ∃ k, m ≤ 2 ^ (k + 1) * a := by
    refine ⟨m, ?_⟩
    have h1 : m < 2 ^ m := Nat.lt_two_pow_self
    have h2 : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc m ≤ 2 ^ m := le_of_lt h1
      _ ≤ 2 ^ (m + 1) := h2
      _ = 2 ^ (m + 1) * 1 := (mul_one _).symm
      _ ≤ 2 ^ (m + 1) * a := Nat.mul_le_mul_left _ ha
  refine ⟨Nat.find hp, ?_, Nat.find_spec hp⟩
  rcases Nat.eq_zero_or_pos (Nat.find hp) with hj | hj
  · rw [hj, pow_zero, one_mul]; exact hm
  · have hk : Nat.find hp - 1 < Nat.find hp := by omega
    have hnot := Nat.find_min hp hk
    have hstep : (Nat.find hp - 1) + 1 = Nat.find hp := by omega
    rw [hstep] at hnot
    omega

/-- The ladder covers `1 ≤ m ≤ 2 M_top`: the small block, the dyadic windows and
the top window together contain every `m` in `[1, 2 M_top]`. -/
lemma window_cover_subset (x N : ℕ) :
    Finset.Icc 1 (2 * MtopN x N) ⊆
      (Finset.Icc 1 (M0N x N) ∪
        (Finset.range (JJN x N)).biUnion
          (fun j => Finset.Icc (2 ^ j * M0N x N + 1) (2 ^ (j + 1) * M0N x N)))
      ∪ Finset.Icc (MtopN x N + 1) (2 * MtopN x N) := by
  intro m hm
  rw [Finset.mem_Icc] at hm
  obtain ⟨hm1, hm2⟩ := hm
  rw [Finset.mem_union, Finset.mem_union]
  by_cases hle : m ≤ M0N x N
  · exact Or.inl (Or.inl (Finset.mem_Icc.mpr ⟨hm1, hle⟩))
  · have hmgt : M0N x N < m := by omega
    obtain ⟨j, hjlow, hjup⟩ :=
      exists_dyadic_window (a := M0N x N) (m := m)
        (by have := M0N_ge_two x N; omega) hmgt
    by_cases hj : j < JJN x N
    · refine Or.inl (Or.inr ?_)
      rw [Finset.mem_biUnion]
      exact ⟨j, Finset.mem_range.mpr hj, Finset.mem_Icc.mpr ⟨by omega, hjup⟩⟩
    · refine Or.inr (Finset.mem_Icc.mpr ⟨?_, hm2⟩)
      have hj' : JJN x N ≤ j := by omega
      have hmono : 2 ^ (JJN x N) * M0N x N ≤ 2 ^ j * M0N x N :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hj')
      have hlt := MtopN_lt_two_pow_JJN x N
      have hm2' : MtopN x N < m := lt_of_lt_of_le hlt (le_trans hmono (le_of_lt hjlow))
      omega

theorem window_cover (x N : ℕ) (F : ℕ → ℝ) (hF : ∀ m, 0 ≤ F m) :
    (∑ m ∈ Finset.Icc 1 (2 * Work.FITop4.Red5.MtopN x N), F m)
      ≤ (∑ m ∈ Finset.Icc 1 (Work.FITop4.Red5.M0N x N), F m)
        + (∑ j ∈ Finset.range (Work.FITop4.Red5.JJN x N),
            ∑ m ∈ Finset.Icc (2 ^ j * Work.FITop4.Red5.M0N x N + 1)
              (2 ^ (j + 1) * Work.FITop4.Red5.M0N x N), F m)
        + (∑ m ∈ Finset.Icc (Work.FITop4.Red5.MtopN x N + 1)
            (2 * Work.FITop4.Red5.MtopN x N), F m) := by
  have hsub := window_cover_subset x N
  have h1 : ∑ m ∈ Finset.Icc 1 (2 * MtopN x N), F m
      ≤ ∑ m ∈ (Finset.Icc 1 (M0N x N) ∪
          (Finset.range (JJN x N)).biUnion
            (fun j => Finset.Icc (2 ^ j * M0N x N + 1) (2 ^ (j + 1) * M0N x N)))
          ∪ Finset.Icc (MtopN x N + 1) (2 * MtopN x N), F m :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hF i)
  have h2 := sum_union_le_of_nonneg
      (Finset.Icc 1 (M0N x N) ∪ (Finset.range (JJN x N)).biUnion
        (fun j => Finset.Icc (2 ^ j * M0N x N + 1) (2 ^ (j + 1) * M0N x N)))
      (Finset.Icc (MtopN x N + 1) (2 * MtopN x N)) F hF
  have h3 := sum_union_le_of_nonneg (Finset.Icc 1 (M0N x N))
      ((Finset.range (JJN x N)).biUnion
        (fun j => Finset.Icc (2 ^ j * M0N x N + 1) (2 ^ (j + 1) * M0N x N))) F hF
  have h4 := sum_biUnion_le_of_nonneg (Finset.range (JJN x N))
      (fun j => Finset.Icc (2 ^ j * M0N x N + 1) (2 ^ (j + 1) * M0N x N)) F hF
  linarith

end Work.FITop4.Red5
