import Mathlib

namespace Work.HP.NA

/-- A finite set `T` of integers, all contained in `[-A, A]` and all congruent to one
another modulo `W ≥ 1`, has at most `2A/W + 1` elements. -/
theorem card_int_residue_le {W : ℕ} (hW : 0 < W) {A : ℝ} (hA : 0 ≤ A) (T : Finset ℤ)
    (hbd : ∀ x ∈ T, |(x : ℝ)| ≤ A)
    (hres : ∀ x ∈ T, ∀ y ∈ T, ((x : ℤ) : ZMod W) = ((y : ℤ) : ZMod W)) :
    (T.card : ℝ) ≤ 2 * A / W + 1 := by
  classical
  have hWposZ : (0 : ℤ) < (W : ℤ) := by exact_mod_cast hW
  have hWne : (W : ℤ) ≠ 0 := by omega
  have hWposR : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  rcases T.eq_empty_or_nonempty with hT | hT
  · rw [hT]
    simp only [Finset.card_empty, Nat.cast_zero]
    have h1 : (0 : ℝ) ≤ 2 * A / (W : ℝ) :=
      div_nonneg (by linarith) (by exact_mod_cast hW.le)
    linarith
  · set lo := T.min' hT with hlo_def
    set hi := T.max' hT with hhi_def
    have hlo_mem : lo ∈ T := T.min'_mem hT
    have hhi_mem : hi ∈ T := T.max'_mem hT
    have hle_lo : ∀ x ∈ T, lo ≤ x := fun x hx => T.min'_le x hx
    have hle_hi : ∀ x ∈ T, x ≤ hi := fun x hx => T.le_max' x hx
    have hle_lohi : lo ≤ hi := hle_hi lo hlo_mem
    set n : ℤ := (hi - lo) / (W : ℤ) with hn_def
    have hn_nonneg : 0 ≤ n := by
      rw [hn_def]
      exact Int.ediv_nonneg (by omega) (le_of_lt hWposZ)
    let f : ℤ → ℤ := fun x => (x - lo) / (W : ℤ)
    -- distinct elements of `T` differ by at least `W`, so the floor map `f` is strict
    have hkey : ∀ u ∈ T, ∀ v ∈ T, u < v → f u < f v := by
      intro u hu v hv huv
      have hmod : u ≡ v [ZMOD (W : ℤ)] :=
        (ZMod.intCast_eq_intCast_iff u v W).mp (hres u hu v hv)
      have hdvd : (W : ℤ) ∣ v - u := Int.modEq_iff_dvd.mp hmod
      have hpos : 0 < v - u := by omega
      have hWle : (W : ℤ) ≤ v - u := Int.le_of_dvd hpos hdvd
      have hule : u - lo ≤ v - lo - (W : ℤ) := by omega
      have h1 : f u ≤ (v - lo - (W : ℤ)) / (W : ℤ) := Int.ediv_le_ediv hWposZ hule
      have h2 : (v - lo - (W : ℤ)) / (W : ℤ) = (v - lo) / (W : ℤ) - 1 := by
        rw [show v - lo - (W : ℤ) = (v - lo) + (W : ℤ) * (-1) by ring,
          Int.add_mul_ediv_left (v - lo) (-1) hWne]
        ring
      have h3 : (v - lo) / (W : ℤ) - 1 < (v - lo) / (W : ℤ) := by omega
      calc f u ≤ (v - lo - (W : ℤ)) / (W : ℤ) := h1
        _ = (v - lo) / (W : ℤ) - 1 := h2
        _ < (v - lo) / (W : ℤ) := h3
        _ = f v := rfl
    -- `f` injects `T` into `{0, …, n}`
    have hle_card : T.card ≤ (Finset.Icc (0 : ℤ) n).card := by
      apply Finset.card_le_card_of_injOn f
      · intro x hx
        rw [Finset.mem_coe, Finset.mem_Icc]
        constructor
        · exact Int.ediv_nonneg (by have := hle_lo x hx; omega) (le_of_lt hWposZ)
        · rw [hn_def]
          apply Int.ediv_le_ediv hWposZ
          have := hle_hi x hx; omega
      · intro x hx y hy hxy
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact absurd hxy (ne_of_lt (hkey x hx y hy hlt))
        · exact absurd hxy.symm (ne_of_lt (hkey y hy x hx hgt))
    have hcc : ((Finset.Icc (0 : ℤ) n).card : ℤ) = n + 1 := by
      rw [Int.card_Icc_of_le (0 : ℤ) n (by omega)]
      ring
    have hcardZ : (T.card : ℤ) ≤ n + 1 := by
      have h : (T.card : ℤ) ≤ ((Finset.Icc (0 : ℤ) n).card : ℤ) := by exact_mod_cast hle_card
      rwa [hcc] at h
    have hcardR : (T.card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hcardZ
    have hn_le : (n : ℝ) ≤ ((hi - lo : ℤ) : ℝ) / (W : ℝ) := by
      have hmul : n * (W : ℤ) ≤ hi - lo := by
        rw [hn_def]; exact Int.ediv_mul_le (hi - lo) hWne
      have hmulR : (n : ℝ) * (W : ℝ) ≤ ((hi - lo : ℤ) : ℝ) := by exact_mod_cast hmul
      rw [le_div_iff₀ hWposR]
      exact hmulR
    have hdiff : ((hi - lo : ℤ) : ℝ) ≤ 2 * A := by
      have h1 := abs_le.mp (hbd hi hhi_mem)
      have h2 := abs_le.mp (hbd lo hlo_mem)
      have : ((hi - lo : ℤ) : ℝ) = (hi : ℝ) - (lo : ℝ) := by push_cast; ring
      rw [this]; linarith
    have hdiv : ((hi - lo : ℤ) : ℝ) / (W : ℝ) ≤ 2 * A / (W : ℝ) :=
      div_le_div_of_nonneg_right hdiff (le_of_lt hWposR)
    calc (T.card : ℝ) ≤ (n : ℝ) + 1 := hcardR
      _ ≤ ((hi - lo : ℤ) : ℝ) / (W : ℝ) + 1 := by linarith [hn_le]
      _ ≤ 2 * A / (W : ℝ) + 1 := by linarith [hdiv]

end Work.HP.NA
