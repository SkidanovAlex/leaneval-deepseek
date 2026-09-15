import Mathlib

namespace Commons.Combinatorics.LevelBlocks

/-- Auxiliary helper: from `a / b = c` with `b > 0`, the two characteristic
inequalities of Euclidean division. -/
private lemma div_eq_bounds {a b c : ℕ} (hb : 0 < b) (h : a / b = c) :
    c * b ≤ a ∧ a < (c + 1) * b := by
  constructor
  · calc c * b = a / b * b := by rw [h]
      _ ≤ a := Nat.div_mul_le_self a b
  · have hlt : a / b < c + 1 := by rw [h]; omega
    exact (Nat.div_lt_iff_lt_mul hb).mp hlt

theorem card_filter_blkIdx_le {m n I : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ((Finset.univ : Finset (Fin m)).filter
      (fun i : Fin m => (n * (2 * i.val + 1)) / (2 * m) = I)).card ≤ m / n + 1 := by
  classical
  set S : Finset (Fin m) := (Finset.univ : Finset (Fin m)).filter
      (fun i : Fin m => (n * (2 * i.val + 1)) / (2 * m) = I) with hS
  have h2m : 0 < 2 * m := by omega
  -- For every `i ∈ S` the Euclidean-division inequalities hold.
  have hbounds : ∀ i ∈ S,
      2 * m * I ≤ n * (2 * i.val + 1) ∧ n * (2 * i.val + 1) < 2 * m * (I + 1) := by
    intro i hi
    have hI : (n * (2 * i.val + 1)) / (2 * m) = I := by
      rw [hS] at hi
      exact (Finset.mem_filter.mp hi).2
    obtain ⟨h1, h2⟩ := div_eq_bounds h2m hI
    constructor
    · calc 2 * m * I = I * (2 * m) := by ring
        _ ≤ n * (2 * i.val + 1) := h1
    · calc n * (2 * i.val + 1) < (I + 1) * (2 * m) := h2
        _ = 2 * m * (I + 1) := by ring
  by_cases hne : S.Nonempty
  · -- pick the smallest element of `S`
    obtain ⟨i0, hi0mem, hmin⟩ : ∃ i0 ∈ S, ∀ i ∈ S, i0 ≤ i :=
      ⟨S.min' hne, Finset.min'_mem S hne, fun i hi => Finset.min'_le S i hi⟩
    -- key gap bound: every element of `S` is at most `m / n` above `i0`
    have hgap : ∀ i ∈ S, i.val - i0.val ≤ m / n := by
      intro i hi
      have hle' : i0.val ≤ i.val := hmin i hi
      have hI0 : 2 * m * I ≤ n * (2 * i0.val + 1) := (hbounds i0 hi0mem).1
      have hI1 : n * (2 * i.val + 1) < 2 * m * (I + 1) := (hbounds i hi).2
      have hA : n * (2 * i.val + 1) =
          n * (2 * i0.val + 1) + 2 * (n * (i.val - i0.val)) := by
        have hv : i.val = i0.val + (i.val - i0.val) := by omega
        conv_lhs => rw [hv]
        ring
      have hlt : 2 * (n * (i.val - i0.val)) < 2 * m := by
        have h2 : 2 * m * (I + 1) = 2 * m * I + 2 * m := by ring
        rw [h2, hA] at hI1
        omega
      have hnDm : n * (i.val - i0.val) < m := by omega
      exact (Nat.le_div_iff_mul_le hn).mpr (by rw [mul_comm]; omega)
    -- inject `S` into `{0, …, m / n}` via `i ↦ i.val - i0.val`
    have hmaps : Set.MapsTo (fun i : Fin m => i.val - i0.val) (S : Set (Fin m))
        ((Finset.Icc 0 (m / n) : Finset ℕ) : Set ℕ) := by
      intro i hi
      rw [Finset.mem_coe, Finset.mem_Icc]
      exact ⟨Nat.zero_le _, hgap i hi⟩
    have hinj : (S : Set (Fin m)).InjOn (fun i : Fin m => i.val - i0.val) := by
      intro i hi j hj heq
      change i.val - i0.val = j.val - i0.val at heq
      have h1 : i0.val ≤ i.val := hmin i hi
      have h2 : i0.val ≤ j.val := hmin j hj
      have : i.val = j.val := by omega
      exact Fin.ext this
    have hcard : S.card ≤ (Finset.Icc 0 (m / n)).card :=
      Finset.card_le_card_of_injOn (fun i : Fin m => i.val - i0.val) hmaps hinj
    have hccard : (Finset.Icc 0 (m / n)).card = m / n + 1 := by
      rw [Nat.card_Icc]; simp
    rw [hccard] at hcard
    exact hcard
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp

end Commons.Combinatorics.LevelBlocks
