import Mathlib

/-!
# A cardinality bound for grid points lying near an arithmetic progression

This is the elementary counting lemma behind the "small grid" reduction in Area `A4`.

If every `j` in a finite set `s ⊆ {0, …, N-1}` lies within `ρ` of the coset `a + ℤ`
(with `|a| ≤ 1/2`, `ρ < 1/2` and `N ρ ≤ 4`), then `s` has at most `20` elements:
the integer `m = m(j)` of the coset is forced into `{0,1}`, and for a fixed `m` the
points `j/N` lie in a real interval of length `2 ρ N ≤ 8`, which contains at most `9`
consecutive integers.

The two auxiliary lemmas are stated in the generality in which they are used:

* `pairwiseDist_card_le` — a finite set of naturals whose elements are pairwise at
  distance at most `d` has at most `d + 1` elements;
* `gridCard_le_nine` — the counting step: all elements `j` of `T` satisfying
  `|j/N - a - c| ≤ ρ` (any `c`) with `2 N ρ ≤ 8` number at most `9`.
-/

namespace Work.KMTAreas.A4

/-- A finite set of natural numbers whose elements are pairwise at distance at most `d`
has at most `d + 1` elements. -/
lemma pairwiseDist_card_le (S : Finset ℕ) (d : ℕ)
    (h : ∀ x ∈ S, ∀ y ∈ S, x ≤ y → y - x ≤ d) : S.card ≤ d + 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hsub : S ⊆ Finset.Ico (S.min' hne) (S.min' hne + (d + 1)) := by
      intro x hx
      rw [Finset.mem_Ico]
      refine ⟨S.min'_le x hx, ?_⟩
      have := h (S.min' hne) (S.min'_mem hne) x hx (S.min'_le x hx)
      omega
    calc S.card ≤ (Finset.Ico (S.min' hne) (S.min' hne + (d + 1))).card :=
          Finset.card_le_card hsub
      _ = d + 1 := by rw [Nat.card_Ico]; omega

/-- If every element `j` of `T ⊆ ℕ` satisfies `|j / N - a - c| ≤ ρ` (for any fixed real `c`)
and `2 N ρ ≤ 8`, then `T` has at most `9` elements: the set of such `j` is an interval of
reals of length `2 ρ N`, hence its integer points are within `8` of one another. -/
lemma gridCard_le_nine {T : Finset ℕ} {N : ℕ} {a ρ c : ℝ} (hN : 0 < N)
    (h : ∀ j ∈ T, |(j : ℝ) / (N : ℝ) - a - c| ≤ ρ) (hρN : 2 * (N : ℝ) * ρ ≤ 8) :
    T.card ≤ 9 := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  refine pairwiseDist_card_le T 8 fun x hx y hy hxy => ?_
  have hx' : |(x : ℝ) / (N : ℝ) - a - c| ≤ ρ := h x hx
  have hy' : |(y : ℝ) / (N : ℝ) - a - c| ≤ ρ := h y hy
  have key : |((y : ℝ) - (x : ℝ))| ≤ 2 * (N : ℝ) * ρ := by
    have hsplit : (y : ℝ) - (x : ℝ) =
        (N : ℝ) * (((y : ℝ) / (N : ℝ) - a - c) - ((x : ℝ) / (N : ℝ) - a - c)) := by
      have hne : (N : ℝ) ≠ 0 := ne_of_gt hNr
      field_simp
      ring
    rw [hsplit, abs_mul, abs_of_pos hNr]
    calc (N : ℝ) * |((y : ℝ) / (N : ℝ) - a - c) - ((x : ℝ) / (N : ℝ) - a - c)|
        ≤ (N : ℝ) * (|(y : ℝ) / (N : ℝ) - a - c| + |(x : ℝ) / (N : ℝ) - a - c|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) (le_of_lt hNr)
      _ ≤ (N : ℝ) * (ρ + ρ) :=
          mul_le_mul_of_nonneg_left (add_le_add hy' hx') (le_of_lt hNr)
      _ = 2 * (N : ℝ) * ρ := by ring
  have hxy' : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast hxy
  have hcast : ((y - x : ℕ) : ℝ) = (y : ℝ) - (x : ℝ) := Nat.cast_sub hxy
  have hle : ((y - x : ℕ) : ℝ) ≤ 8 := by
    rw [← hcast, abs_of_nonneg (Nat.cast_nonneg (y - x))] at key
    linarith
  exact_mod_cast hle

theorem cardGridArcLe {N : ℕ} {a ρ : ℝ} (ha : |a| ≤ 1 / 2) (hρ : ρ < 1 / 2)
    (hρN : (N : ℝ) * ρ ≤ 4) {s : Finset ℕ} (hs : ∀ j ∈ s, j < N)
    (h : ∀ j ∈ s, ∃ m : ℤ, |(j : ℝ) / (N : ℝ) - a - (m : ℝ)| ≤ ρ) : s.card ≤ 20 := by
  classical
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · -- `N = 0`: the condition `j < N` is vacuous.
    subst hN0
    have hss : s = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro j hj
      exact Nat.not_lt_zero j (hs j hj)
    rw [hss, Finset.card_empty]
    norm_num
  · -- `N ≥ 1`: split `s` according to whether `j / N` is within `ρ` of `a` or of `a + 1`.
    set p : ℕ → Prop := fun j => |(j : ℝ) / (N : ℝ) - a| ≤ ρ with hp
    have hρN' : 2 * (N : ℝ) * ρ ≤ 8 := by nlinarith [hρN]
    -- every witness integer `m` for `j ∈ s` is `0` or `1`.
    have hm01 : ∀ j ∈ s, ∀ m : ℤ,
        |(j : ℝ) / (N : ℝ) - a - (m : ℝ)| ≤ ρ → m = 0 ∨ m = 1 := by
      intro j hj m hm
      have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
      have hjN0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hjNlt : (j : ℝ) < (N : ℝ) := by exact_mod_cast hs j hj
      have hjn0 : (0 : ℝ) ≤ (j : ℝ) / (N : ℝ) := div_nonneg hjN0 (le_of_lt hNr)
      have hjn1 : (j : ℝ) / (N : ℝ) < 1 := (div_lt_one hNr).mpr hjNlt
      have ha1 : -(1 / 2 : ℝ) ≤ a := (abs_le.mp ha).1
      have ha2 : a ≤ 1 / 2 := (abs_le.mp ha).2
      have hle := (abs_le.mp hm)
      have hlow : (-1 : ℝ) < (m : ℝ) := by linarith [hle.2, hjn0, ha2, hρ]
      have hhigh : (m : ℝ) < 2 := by linarith [hle.1, hjn1, ha1, hρ]
      have hm0 : (-1 : ℤ) < m := by exact_mod_cast hlow
      have hm2 : m < 2 := by exact_mod_cast hhigh
      omega
    have h0card : (s.filter p).card ≤ 9 := by
      refine gridCard_le_nine (T := s.filter p) (N := N) (a := a) (ρ := ρ) (c := 0)
        hNpos (fun j hj => ?_) hρN'
      rw [Finset.mem_filter] at hj
      simpa using hj.2
    have h1card : (s.filter (fun j => ¬ p j)).card ≤ 9 := by
      refine gridCard_le_nine (T := s.filter (fun j => ¬ p j)) (N := N) (a := a) (ρ := ρ)
        (c := 1) hNpos (fun j hj => ?_) hρN'
      rw [Finset.mem_filter] at hj
      obtain ⟨hjs, hpj⟩ := hj
      obtain ⟨m, hm⟩ := h j hjs
      rcases hm01 j hjs m hm with hm0 | hm1
      · exact absurd (by simpa [hp, hm0] using hm) hpj
      · simpa [hm1] using hm
    have hcard := Finset.card_filter_add_card_filter_not (s := s) p
    omega

end Work.KMTAreas.A4
