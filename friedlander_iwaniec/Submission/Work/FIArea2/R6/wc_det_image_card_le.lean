import Mathlib

namespace Work.FIArea2.R6

/-- **Count of bounded nonzero multiples.**

A finite set `M` of nonzero integral multiples of `I` (`I ≥ 1`), all of absolute value at most `K`,
has at most `2 K / I` elements: the value map `m ↦ m.natAbs` sends `M` onto a set `T` of positive
multiples of `I` inside `[1, K]` (at most `K / I` of them), and every fibre of `natAbs` on `ℤ`
contains at most the two elements `±m`. -/
theorem wc_det_image_card_le (I K : ℕ) (hI : 1 ≤ I) (M : Finset ℤ)
    (hdvd : ∀ m ∈ M, (I : ℤ) ∣ m) (hne : ∀ m ∈ M, m ≠ 0)
    (habs : ∀ m ∈ M, m.natAbs ≤ K) :
    (M.card : ℝ) ≤ 2 * (K : ℝ) / (I : ℝ) := by
  set T : Finset ℕ := M.image (fun m => m.natAbs) with hT
  have hmemT : ∀ m ∈ M, m.natAbs ∈ T := by
    intro m hm
    rw [hT]
    exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
  -- Step 1: `M` is contained in the two images of `T` under `n ↦ n` and `n ↦ -n`.
  have hsub : M ⊆ T.image (fun n : ℕ => (n : ℤ)) ∪ T.image (fun n : ℕ => -(n : ℤ)) := by
    intro m hm
    have hmn : m.natAbs ∈ T := hmemT m hm
    rcases Int.natAbs_eq m with h | h
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨m.natAbs, hmn, h.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨m.natAbs, hmn, h.symm⟩)
  -- Each fibre of `natAbs` on `ℤ` has at most two points, so `#M ≤ 2 #T`.
  have hcard1 : M.card ≤ 2 * T.card := by
    have h1 : M.card ≤ (T.image (fun n : ℕ => (n : ℤ)) ∪ T.image (fun n : ℕ => -(n : ℤ))).card :=
      Finset.card_le_card hsub
    have h2 : (T.image (fun n : ℕ => (n : ℤ)) ∪ T.image (fun n : ℕ => -(n : ℤ))).card
        ≤ (T.image (fun n : ℕ => (n : ℤ))).card + (T.image (fun n : ℕ => -(n : ℤ))).card :=
      Finset.card_union_le _ _
    have h3 : (T.image (fun n : ℕ => (n : ℤ))).card ≤ T.card := Finset.card_image_le
    have h4 : (T.image (fun n : ℕ => -(n : ℤ))).card ≤ T.card := Finset.card_image_le
    omega
  -- Step 2: `T` consists of positive multiples of `I` not exceeding `K`.
  have hTle : T.card ≤ K / I := by
    have hsub2 : T ⊆ (Finset.Icc 1 (K / I)).image (fun c => I * c) := by
      intro n hn
      rw [hT, Finset.mem_image] at hn
      obtain ⟨m, hm, rfl⟩ := hn
      obtain ⟨c, hc⟩ := hdvd m hm
      have hIabs : (I : ℤ).natAbs = I := Int.natAbs_natCast I
      have hnat : m.natAbs = I * c.natAbs := by
        rw [hc, Int.natAbs_mul, hIabs]
      have hcne : c ≠ 0 := by
        intro hc_eq
        exact hne m hm (by rw [hc, hc_eq, mul_zero])
      have hge1 : 1 ≤ c.natAbs := by
        have : c.natAbs ≠ 0 := (Int.natAbs_ne_zero).mpr hcne
        omega
      have hle : c.natAbs ≤ K / I := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < I)]
        have hb := habs m hm
        rw [hnat] at hb
        calc c.natAbs * I = I * c.natAbs := Nat.mul_comm _ _
          _ ≤ K := hb
      rw [Finset.mem_image]
      exact ⟨c.natAbs, Finset.mem_Icc.mpr ⟨hge1, hle⟩, hnat.symm⟩
    calc T.card ≤ ((Finset.Icc 1 (K / I)).image (fun c => I * c)).card := Finset.card_le_card hsub2
      _ ≤ (Finset.Icc 1 (K / I)).card := Finset.card_image_le
      _ = K / I := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hM : (M.card : ℝ) ≤ 2 * (T.card : ℝ) := by exact_mod_cast hcard1
  have hTreal : (T.card : ℝ) ≤ (K : ℝ) / (I : ℝ) := by
    have hcast : (T.card : ℝ) ≤ ((K / I : ℕ) : ℝ) := by exact_mod_cast hTle
    have hdiv : ((K / I : ℕ) : ℝ) ≤ (K : ℝ) / (I : ℝ) := Nat.cast_div_le
    linarith
  calc (M.card : ℝ) ≤ 2 * (T.card : ℝ) := hM
    _ ≤ 2 * ((K : ℝ) / (I : ℝ)) := by linarith
    _ = 2 * (K : ℝ) / (I : ℝ) := by ring

end Work.FIArea2.R6
