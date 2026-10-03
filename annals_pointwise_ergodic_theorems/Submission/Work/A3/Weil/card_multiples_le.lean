import Mathlib

namespace Work.A3.Weil

/-- **Counting nonzero multiples of `q` in `[-M, M]`.**  A set `S` of nonzero integers in
`[-M, M]` all divisible by `q ≥ 1` has at most `2M/q` elements: the map `P ↦ |P| / |q|` sends `S`
into `{1, …, ⌊M/q⌋}` with fibres of size at most `2` (the fibre of `y` lies in
`{q y, -q y}`). -/
theorem card_multiples_le (M : ℕ) {q : ℤ} (hq : 1 ≤ q) (S : Finset ℤ)
    (hS : S ⊆ (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun P : ℤ => P ≠ 0))
    (hdvd : ∀ P ∈ S, q ∣ P) :
    (S.card : ℝ) ≤ 2 * (M : ℝ) / (q : ℝ) := by
  classical
  have hq0 : (0 : ℤ) < q := lt_of_lt_of_le zero_lt_one hq
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hqabs : 0 < q.natAbs := Int.natAbs_pos.mpr hqne
  set K : ℕ := M / q.natAbs with hK
  -- bounds and nonvanishing for the elements of `S`
  have hmem : ∀ P ∈ S, -(M : ℤ) ≤ P ∧ P ≤ (M : ℤ) ∧ P ≠ 0 := by
    intro P hP
    have h := Finset.mem_filter.mp (hS hP)
    rw [Finset.mem_Icc] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hnatAbs_le : ∀ P ∈ S, P.natAbs ≤ M := by
    intro P hP
    obtain ⟨h1, h2, -⟩ := hmem P hP
    have h3 : |P| ≤ (M : ℤ) := abs_le.mpr ⟨h1, h2⟩
    rw [Int.abs_eq_natAbs] at h3
    exact_mod_cast h3
  have hdiv : ∀ P ∈ S, q.natAbs ∣ P.natAbs := fun P hP =>
    Int.natAbs_dvd_natAbs.mpr (hdvd P hP)
  -- the fibres of `P ↦ |P| / |q|`
  have hfib : ∀ b ∈ S.image (fun P : ℤ => P.natAbs / q.natAbs),
      (S.filter (fun P : ℤ => P.natAbs / q.natAbs = b)).card ≤ 2 := by
    intro b _
    have hsub : (S.filter (fun P : ℤ => P.natAbs / q.natAbs = b))
        ⊆ ({((q.natAbs * b : ℕ) : ℤ), -(((q.natAbs * b : ℕ) : ℤ))} : Finset ℤ) := by
      intro P hP
      rw [Finset.mem_filter] at hP
      obtain ⟨hPS, hgP⟩ := hP
      have hnat : P.natAbs = q.natAbs * b := by
        rw [← Nat.mul_div_cancel' (hdiv P hPS), hgP]
      rcases Int.natAbs_eq P with h | h
      · rw [Finset.mem_insert, Finset.mem_singleton]
        left
        rw [h, hnat]
      · rw [Finset.mem_insert, Finset.mem_singleton]
        right
        rw [h, hnat]
    calc (S.filter (fun P : ℤ => P.natAbs / q.natAbs = b)).card
        ≤ ({((q.natAbs * b : ℕ) : ℤ), -(((q.natAbs * b : ℕ) : ℤ))} : Finset ℤ).card :=
          Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  -- the image of `S` lies in `{1, …, K}`
  have hTcard : (S.image (fun P : ℤ => P.natAbs / q.natAbs)).card ≤ K := by
    have hTsub : (S.image (fun P : ℤ => P.natAbs / q.natAbs)) ⊆ Finset.Icc 1 K := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨P, hPS, rfl⟩ := hy
      rw [Finset.mem_Icc]
      constructor
      · have hle : q.natAbs ≤ P.natAbs :=
          Int.natAbs_le_of_dvd_ne_zero (hdvd P hPS) (hmem P hPS).2.2
        rw [Nat.le_div_iff_mul_le hqabs]
        simpa using hle
      · have := Nat.div_le_div_right (c := q.natAbs) (hnatAbs_le P hPS)
        simpa [hK] using this
    have := Finset.card_le_card hTsub
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at this
  have hmain : S.card ≤ K * 2 := by
    calc S.card = ∑ b ∈ S.image (fun P : ℤ => P.natAbs / q.natAbs),
              (S.filter (fun P : ℤ => P.natAbs / q.natAbs = b)).card :=
            Finset.card_eq_sum_card_fiberwise
              (fun P hP => Finset.mem_image.mpr ⟨P, hP, rfl⟩)
      _ ≤ ∑ _b ∈ S.image (fun P : ℤ => P.natAbs / q.natAbs), 2 :=
            Finset.sum_le_sum (fun b hb => hfib b hb)
      _ = (S.image (fun P : ℤ => P.natAbs / q.natAbs)).card * 2 := by
            rw [Finset.sum_const, smul_eq_mul]
      _ ≤ K * 2 := Nat.mul_le_mul_right 2 hTcard
  have hR : (S.card : ℝ) ≤ (K : ℝ) * 2 := by exact_mod_cast hmain
  have hqR : ((q.natAbs : ℕ) : ℝ) = (q : ℝ) := by
    have h : ((q.natAbs : ℕ) : ℤ) = q := Int.natAbs_of_nonneg (le_of_lt hq0)
    rw [show ((q.natAbs : ℕ) : ℝ) = (((q.natAbs : ℕ) : ℤ) : ℝ) from by simp, h]
  have hKle : (K : ℝ) ≤ (M : ℝ) / (q : ℝ) := by
    have h := Nat.cast_div_le (α := ℝ) (m := M) (n := q.natAbs)
    rw [hqR] at h
    rw [hK]
    exact h
  have hfin : (K : ℝ) * 2 ≤ 2 * (M : ℝ) / (q : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hKle (show (0 : ℝ) ≤ 2 by norm_num)
    have h3 : (2 : ℝ) * (M : ℝ) / (q : ℝ) = 2 * ((M : ℝ) / (q : ℝ)) := by ring
    linarith [h, h3]
  linarith

end Work.A3.Weil
