import Mathlib

namespace Commons.NumberTheory.Int

/-- **Counting integer points in a real interval (finset form).**

A finset `s` of integers all of whose elements lie (as reals) in the interval `[p, q]`
contains at most `q - p + 1` elements.  Indeed the elements of `s` are distinct integers inside
the integer interval `[min s, max s]` whose length is at most `q - p`. -/
private theorem finset_card_le_of_mem_Icc_real {s : Finset ℤ} {p q : ℝ} (hpq : p ≤ q)
    (h : ∀ x ∈ s, p ≤ (x : ℝ) ∧ (x : ℝ) ≤ q) :
    (s.card : ℝ) ≤ q - p + 1 := by
  rcases Finset.eq_empty_or_nonempty s with h0 | hne
  · rw [h0]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith
  · have hm : s.min' hne ∈ s := Finset.min'_mem s hne
    have hM : s.max' hne ∈ s := Finset.max'_mem s hne
    have hsub : s ⊆ Finset.Icc (s.min' hne) (s.max' hne) := by
      intro x hx
      rw [Finset.mem_Icc]
      exact ⟨Finset.min'_le s x hx, Finset.le_max' s x hx⟩
    have hle_card : s.card ≤ (Finset.Icc (s.min' hne) (s.max' hne)).card :=
      Finset.card_le_card hsub
    have hmm : s.min' hne ≤ s.max' hne := Finset.min'_le_max' s hne
    have hIcc : ((Finset.Icc (s.min' hne) (s.max' hne)).card : ℝ)
        = ((s.max' hne : ℤ) : ℝ) + 1 - ((s.min' hne : ℤ) : ℝ) := by
      have hcast : ((Finset.Icc (s.min' hne) (s.max' hne)).card : ℤ)
          = (s.max' hne) + 1 - (s.min' hne) := Int.card_Icc_of_le _ _ (by omega)
      exact_mod_cast hcast
    have h1 : p ≤ ((s.min' hne : ℤ) : ℝ) := (h _ hm).1
    have h2 : ((s.max' hne : ℤ) : ℝ) ≤ q := (h _ hM).2
    have h3 : (s.card : ℝ) ≤ ((Finset.Icc (s.min' hne) (s.max' hne)).card : ℝ) := by
      exact_mod_cast hle_card
    linarith

/-- **Counting integer points in a real interval (set form).**

A set `s` of integers all of whose elements lie (as reals) in the interval `[p, q]`
satisfies `s.ncard ≤ q - p + 1`. -/
private theorem ncard_le_of_subset_Icc_real {s : Set ℤ} {p q : ℝ} (hpq : p ≤ q)
    (h : ∀ x ∈ s, p ≤ (x : ℝ) ∧ (x : ℝ) ≤ q) :
    (s.ncard : ℝ) ≤ q - p + 1 := by
  have hfin : s.Finite := by
    refine Set.Finite.subset (Finset.finite_toSet (Finset.Icc ⌈p⌉ ⌊q⌋)) ?_
    intro x hx
    rw [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨Int.ceil_le.mpr (h x hx).1, Int.le_floor.mpr (h x hx).2⟩
  rw [Set.ncard_eq_toFinset_card s hfin]
  exact finset_card_le_of_mem_Icc_real hpq (fun x hx => h x (hfin.mem_toFinset.mp hx))

/-- **Counting integers whose square is close to `M`.**  If `2L ≤ M` then the number of integers
`x` with `|x^2 - M| ≤ L` is at most `4L / √M + 4`.  The `+4` comes from the two symmetric
integer intervals `[√(M-L), √(M+L)]` and `[-√(M+L), -√(M-L)]`, each of which contains at most
`√(M+L) - √(M-L) + 1 ≤ 2L/√M + 1` integers. -/
theorem ncard_sq_close_le (M L : ℕ) (hM : 1 ≤ M) (h : 2 * L ≤ M) :
    ((({x : ℤ | |((x : ℤ) ^ 2 - (M : ℤ))| ≤ (L : ℤ)} : Set ℤ)).ncard : ℝ)
      ≤ 4 * (L : ℝ) / Real.sqrt M + 4 := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hLM : (L : ℝ) ≤ (M : ℝ) / 2 := by
    have h2 : (2 : ℝ) * (L : ℝ) ≤ (M : ℝ) := by exact_mod_cast h
    linarith
  have hML_pos : 0 < (M : ℝ) - (L : ℝ) := by linarith
  have hL_nonneg : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  set S : Set ℤ := {x : ℤ | |((x : ℤ) ^ 2 - (M : ℤ))| ≤ (L : ℤ)} with hS
  set P : Set ℤ := {x : ℤ | 0 < x ∧ |((x : ℤ) ^ 2 - (M : ℤ))| ≤ (L : ℤ)} with hP
  set Q : Set ℤ := {x : ℤ | x < 0 ∧ |((x : ℤ) ^ 2 - (M : ℤ))| ≤ (L : ℤ)} with hQ
  have hSQ : S = P ∪ Q := by
    ext x
    simp only [hS, hP, hQ, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro hx
      have hx2 : (1 : ℤ) ≤ x ^ 2 := by
        have hle : (M : ℤ) - (L : ℤ) ≤ x ^ 2 := by
          have h1 := (abs_le.mp hx).1
          linarith
        linarith
      have hxne : x ≠ 0 := by
        intro h0
        rw [h0] at hx2
        norm_num at hx2
      rcases lt_or_gt_of_ne (Ne.symm hxne) with hpos | hneg
      · exact Or.inl ⟨hpos, hx⟩
      · exact Or.inr ⟨hneg, hx⟩
    · rintro (⟨_, hx⟩ | ⟨_, hx⟩)
      · exact hx
      · exact hx
  have hQP : Q = (fun x : ℤ => -x) '' P := by
    ext y
    simp only [hP, hQ, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hy0, hy⟩
      refine ⟨-y, ⟨by omega, ?_⟩, by ring⟩
      simpa only [neg_sq] using hy
    · rintro ⟨x, ⟨hx0, hx⟩, rfl⟩
      refine ⟨by omega, ?_⟩
      simpa only [neg_sq] using hx
  have hQcard : Q.ncard = P.ncard := by
    rw [hQP]
    exact Set.ncard_image_of_injective P neg_injective
  have hS_le : S.ncard ≤ P.ncard + Q.ncard := by
    rw [hSQ]
    exact Set.ncard_union_le P Q
  rw [hQcard] at hS_le
  have hS_le2 : (S.ncard : ℝ) ≤ 2 * (P.ncard : ℝ) := by
    have h1 : (S.ncard : ℝ) ≤ ((P.ncard + P.ncard : ℕ) : ℝ) := by exact_mod_cast hS_le
    push_cast at h1
    linarith
  -- interval bound for the positive part
  have hPbound : (P.ncard : ℝ)
      ≤ Real.sqrt ((M : ℝ) + (L : ℝ)) - Real.sqrt ((M : ℝ) - (L : ℝ)) + 1 := by
    refine ncard_le_of_subset_Icc_real ?_ ?_
    · exact Real.sqrt_le_sqrt (by linarith)
    · intro x hx
      obtain ⟨hx0, hxabs⟩ := hx
      have hx0R : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx0
      have hx2le : ((x : ℝ)) ^ 2 ≤ (M : ℝ) + (L : ℝ) := by
        have h2 := (abs_le.mp hxabs).2
        have h2' : (x : ℤ) ^ 2 ≤ (M : ℤ) + (L : ℤ) := by linarith
        exact_mod_cast h2'
      have hx2ge : (M : ℝ) - (L : ℝ) ≤ ((x : ℝ)) ^ 2 := by
        have h1 := (abs_le.mp hxabs).1
        have h1' : (M : ℤ) - (L : ℤ) ≤ (x : ℤ) ^ 2 := by linarith
        exact_mod_cast h1'
      exact ⟨(Real.sqrt_le_iff).mpr ⟨le_of_lt hx0R, hx2ge⟩,
        (Real.le_sqrt (le_of_lt hx0R) (by linarith)).mpr hx2le⟩
  -- the square-root difference bound
  have hdiff : Real.sqrt ((M : ℝ) + (L : ℝ)) - Real.sqrt ((M : ℝ) - (L : ℝ))
      ≤ 2 * (L : ℝ) / Real.sqrt (M : ℝ) := by
    have hsq1 : (Real.sqrt ((M : ℝ) + (L : ℝ))) ^ 2 = (M : ℝ) + (L : ℝ) :=
      Real.sq_sqrt (by linarith)
    have hsq2 : (Real.sqrt ((M : ℝ) - (L : ℝ))) ^ 2 = (M : ℝ) - (L : ℝ) :=
      Real.sq_sqrt (le_of_lt hML_pos)
    have hd_pos : 0 < Real.sqrt ((M : ℝ) + (L : ℝ)) + Real.sqrt ((M : ℝ) - (L : ℝ)) := by
      have h1 : 0 < Real.sqrt ((M : ℝ) - (L : ℝ)) := Real.sqrt_pos.mpr hML_pos
      have h2 : 0 ≤ Real.sqrt ((M : ℝ) + (L : ℝ)) := Real.sqrt_nonneg _
      linarith
    have hd_ge : Real.sqrt (M : ℝ)
        ≤ Real.sqrt ((M : ℝ) + (L : ℝ)) + Real.sqrt ((M : ℝ) - (L : ℝ)) := by
      have h1 : Real.sqrt (M : ℝ) ≤ Real.sqrt ((M : ℝ) + (L : ℝ)) :=
        Real.sqrt_le_sqrt (by linarith)
      have h2 : 0 ≤ Real.sqrt ((M : ℝ) - (L : ℝ)) := Real.sqrt_nonneg _
      linarith
    have hprod : (Real.sqrt ((M : ℝ) + (L : ℝ)) - Real.sqrt ((M : ℝ) - (L : ℝ)))
        * (Real.sqrt ((M : ℝ) + (L : ℝ)) + Real.sqrt ((M : ℝ) - (L : ℝ))) = 2 * (L : ℝ) := by
      nlinarith [hsq1, hsq2]
    have heq : Real.sqrt ((M : ℝ) + (L : ℝ)) - Real.sqrt ((M : ℝ) - (L : ℝ))
        = 2 * (L : ℝ)
          / (Real.sqrt ((M : ℝ) + (L : ℝ)) + Real.sqrt ((M : ℝ) - (L : ℝ))) := by
      rw [eq_div_iff (ne_of_gt hd_pos)]
      linarith
    rw [heq]
    exact div_le_div_of_nonneg_left (by linarith) (Real.sqrt_pos.mpr hMpos) hd_ge
  have hPbound2 : (P.ncard : ℝ) ≤ 2 * (L : ℝ) / Real.sqrt (M : ℝ) + 1 := by
    linarith [hPbound, hdiff]
  have hS_bound : (S.ncard : ℝ) ≤ 2 * (2 * (L : ℝ) / Real.sqrt (M : ℝ) + 1) := by
    calc (S.ncard : ℝ) ≤ 2 * (P.ncard : ℝ) := hS_le2
      _ ≤ 2 * (2 * (L : ℝ) / Real.sqrt (M : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hPbound2 (by norm_num)
  have hEq : 2 * (2 * (L : ℝ) / Real.sqrt (M : ℝ) + 1)
      = 4 * (L : ℝ) / Real.sqrt (M : ℝ) + 2 := by ring
  have hfinal : (S.ncard : ℝ) ≤ 4 * (L : ℝ) / Real.sqrt (M : ℝ) + 4 := by
    linarith [hS_bound, hEq]
  exact hfinal

end Commons.NumberTheory.Int
