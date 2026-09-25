import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Fourier

open scoped BigOperators

/-- Auxiliary form of the dyadic boundary-layer tiling bound, stated for an abstract
scale sequence `h : ℕ → ℝ` which is positive, bounded by `1/2`, satisfies the dyadic
self-similarity `h (j+1) = h j / 2` and is antitone.  The concrete instance
`h j = 2^{-(j:ℝ)-1}` is used in `dyadic_boundary_tiling_separated_bounded`. -/
private lemma dyadic_boundary_tiling_aux (K : ℕ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (φ : ℝ → ℝ) (h1 : ∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1) (h0 : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hbdd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1)
    (h : ℕ → ℝ) (hpos : ∀ j : ℕ, 0 < h j) (hle : ∀ j : ℕ, h j ≤ 1 / 2)
    (hhalf : ∀ j : ℕ, h (j + 1) = h j / 2) (hmono : ∀ j j' : ℕ, j ≤ j' → h j' ≤ h j)
    (θ : ℝ) :
    ∑' j : ℕ, |(if ∃ k : Fin K, |θ - lam k| ≤ h j then (1 : ℝ) else 0)
        - ∑ k : Fin K, φ ((θ - lam k) / h j)| ^ 2 ≤ 4 := by
  classical
  let I : ℕ → ℝ := fun j => if ∃ k : Fin K, |θ - lam k| ≤ h j then (1 : ℝ) else 0
  let S : ℕ → ℝ := fun j => ∑ k : Fin K, φ ((θ - lam k) / h j)
  let T : ℕ → ℝ := fun j => |I j - S j| ^ 2
  change ∑' j : ℕ, T j ≤ 4
  have hIunfold : ∀ j : ℕ,
      I j = (if ∃ k : Fin K, |θ - lam k| ≤ h j then (1 : ℝ) else 0) := fun j => rfl
  have hTunfold : ∀ j : ℕ, T j = |I j - S j| ^ 2 := fun j => rfl
  -- ### 1. Within one scale only the (essentially unique) nearest frequency contributes.
  have hzero : ∀ (j : ℕ) (k0 : Fin K), |θ - lam k0| ≤ h j →
      ∀ k : Fin K, k ≠ k0 → φ ((θ - lam k) / h j) = 0 := by
    intro j k0 hk0 k hk
    by_contra hne
    have hlt1 : |(θ - lam k) / h j| < 1 := by
      by_contra hcon
      simp only [not_lt] at hcon
      exact hne (h0 _ hcon)
    rw [abs_div, abs_of_pos (hpos j)] at hlt1
    have hlt2 : |θ - lam k| < h j := (div_lt_one (hpos j)).mp hlt1
    have htri : |lam k - lam k0| ≤ |θ - lam k| + |θ - lam k0| := by
      calc |lam k - lam k0| = |(lam k - θ) + (θ - lam k0)| := by congr 1; ring
        _ ≤ |lam k - θ| + |θ - lam k0| := abs_add_le _ _
        _ = |θ - lam k| + |θ - lam k0| := by rw [abs_sub_comm]
    have hlt3 : |lam k - lam k0| < 1 := by
      have := hle j
      linarith
    have hge := hsep k k0 hk
    linarith
  -- ### 2. Collapse of the sum over frequencies when one frequency is within reach.
  have hsum_single : ∀ (j : ℕ) (k0 : Fin K), |θ - lam k0| ≤ h j →
      S j = φ ((θ - lam k0) / h j) := by
    intro j k0 hk0
    exact Finset.sum_eq_single k0 (fun k _ hk => hzero j k0 hk0 k hk)
      (fun hmem => absurd (Finset.mem_univ k0) hmem)
  -- ### 3. If no frequency is within reach, both the indicator and the sum vanish.
  have hsum_zero : ∀ j : ℕ, (¬ ∃ k : Fin K, |θ - lam k| ≤ h j) → S j = 0 := by
    intro j hex
    show (∑ k : Fin K, φ ((θ - lam k) / h j)) = 0
    apply Finset.sum_eq_zero
    intro k _
    apply h0
    have hk : h j < |θ - lam k| := by
      by_contra hc
      simp only [not_lt] at hc
      exact hex ⟨k, hc⟩
    rw [abs_div, abs_of_pos (hpos j), one_le_div (hpos j)]
    exact le_of_lt hk
  -- ### 4. Every single term is at most `1`.
  have hterm : ∀ j : ℕ, T j ≤ 1 := by
    intro j
    rw [hTunfold j]
    by_cases hex : ∃ k : Fin K, |θ - lam k| ≤ h j
    · obtain ⟨k0, hk0⟩ := hex
      have hI : I j = 1 := by rw [hIunfold j, if_pos ⟨k0, hk0⟩]
      have hS := hsum_single j k0 hk0
      have hS0 : 0 ≤ S j := by rw [hS]; exact (hbdd _).1
      have hS1 : S j ≤ 1 := by rw [hS]; exact (hbdd _).2
      have habs : |I j - S j| ≤ 1 := by
        rw [hI, abs_le]
        constructor <;> linarith
      exact pow_le_one₀ (abs_nonneg _) habs
    · have hI : I j = 0 := by rw [hIunfold j, if_neg hex]
      have hS := hsum_zero j hex
      rw [hI, hS]
      norm_num
  -- ### 5. A nonzero term pins down the distance to the frequency set.
  have hwit : ∀ j : ℕ, T j ≠ 0 →
      ∃ k : Fin K, h j / 2 < |θ - lam k| ∧ |θ - lam k| ≤ h j := by
    intro j hTj
    have hIS : I j ≠ S j := by
      intro hc
      exact hTj (by rw [hTunfold j, hc]; simp)
    by_cases hex : ∃ k : Fin K, |θ - lam k| ≤ h j
    · obtain ⟨k0, hk0⟩ := hex
      refine ⟨k0, ?_, hk0⟩
      have hI : I j = 1 := by rw [hIunfold j, if_pos ⟨k0, hk0⟩]
      have hS := hsum_single j k0 hk0
      have hne1 : φ ((θ - lam k0) / h j) ≠ 1 := by
        intro hc
        exact hIS (by rw [hI, hS, hc])
      have hb1 : ¬ (|(θ - lam k0) / h j| ≤ 1 / 2) := fun hc => hne1 (h1 _ hc)
      simp only [not_le] at hb1
      rw [abs_div, abs_of_pos (hpos j)] at hb1
      rw [lt_div_iff₀ (hpos j)] at hb1
      linarith
    · exfalso
      exact hIS (by rw [hIunfold j, if_neg hex, hsum_zero j hex])
  -- ### 6. At most one scale carries a nonzero term.
  have huniq : ∀ j j' : ℕ, T j ≠ 0 → T j' ≠ 0 → j = j' := by
    intro j j' hj hj'
    by_contra hne
    obtain ⟨k, hk1, hk2⟩ := hwit j hj
    obtain ⟨k', hk1', hk2'⟩ := hwit j' hj'
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · -- j < j'
      have hjj : j + 1 ≤ j' := hlt
      have hhalf_le : h j' ≤ h j / 2 := le_trans (hmono (j + 1) j' hjj) (le_of_eq (hhalf j))
      rcases eq_or_ne k k' with hkk | hkk
      · have hd : |θ - lam k| = |θ - lam k'| := by rw [hkk]
        linarith
      · have htri : |lam k - lam k'| ≤ |θ - lam k| + |θ - lam k'| := by
          calc |lam k - lam k'| = |(lam k - θ) + (θ - lam k')| := by congr 1; ring
            _ ≤ |lam k - θ| + |θ - lam k'| := abs_add_le _ _
            _ = |θ - lam k| + |θ - lam k'| := by rw [abs_sub_comm]
        have hlt3 : |lam k - lam k'| < 1 := by
          have := hle j
          linarith
        have hge := hsep k k' hkk
        linarith
    · -- j' < j
      have hjj : j' + 1 ≤ j := hlt
      have hhalf_le : h j ≤ h j' / 2 := le_trans (hmono (j' + 1) j hjj) (le_of_eq (hhalf j'))
      rcases eq_or_ne k k' with hkk | hkk
      · have hd : |θ - lam k| = |θ - lam k'| := by rw [hkk]
        linarith
      · have htri : |lam k - lam k'| ≤ |θ - lam k| + |θ - lam k'| := by
          calc |lam k - lam k'| = |(lam k - θ) + (θ - lam k')| := by congr 1; ring
            _ ≤ |lam k - θ| + |θ - lam k'| := abs_add_le _ _
            _ = |θ - lam k| + |θ - lam k'| := by rw [abs_sub_comm]
        have hlt3 : |lam k - lam k'| < 1 := by
          have := hle j'
          linarith
        have hge := hsep k k' hkk
        linarith
  -- ### 7. Assemble.
  by_cases hnon : ∃ j : ℕ, T j ≠ 0
  · obtain ⟨j0, hj0⟩ := hnon
    have hsingle : ∀ b : ℕ, b ≠ j0 → T b = 0 := by
      intro b hb
      by_contra hb'
      exact hb (huniq b j0 hb' hj0)
    rw [tsum_eq_single j0 hsingle]
    have := hterm j0
    linarith
  · simp only [not_exists, not_not] at hnon
    have hzeroall : (∑' j : ℕ, T j) = 0 := by
      rw [show (fun j : ℕ => T j) = (fun _ : ℕ => (0 : ℝ)) from funext hnon]
      exact tsum_zero
    rw [hzeroall]
    norm_num

/-- **Dyadic tiling of the boundary layers of a `1`-separated family of frequencies
(bounded-plateau version).**  Same as `dyadic_boundary_tiling_separated` but with the
missing hypothesis `0 ≤ φ x ≤ 1`; each dyadic scale contributes at most `1` and at most
one scale contributes its boundary layer, so the sum is `≤ 1` (hence `≤ 4`). -/
theorem dyadic_boundary_tiling_separated_bounded (K : ℕ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (φ : ℝ → ℝ) (h1 : ∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1) (h0 : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hbdd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1)
    (θ : ℝ) :
    ∑' j : ℕ,
        |(if ∃ k : Fin K, |θ - lam k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1) then (1 : ℝ) else 0)
          - ∑ k : Fin K, φ ((θ - lam k) / (2 : ℝ) ^ (-(j : ℝ) - 1))| ^ 2 ≤ 4 := by
  have hpos : ∀ j : ℕ, 0 < (2 : ℝ) ^ (-(j : ℝ) - 1) :=
    fun j => Real.rpow_pos_of_pos (by norm_num) _
  have hle : ∀ j : ℕ, (2 : ℝ) ^ (-(j : ℝ) - 1) ≤ 1 / 2 := by
    intro j
    have h2 : -(j : ℝ) - 1 ≤ -(1 : ℝ) := by
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    calc (2 : ℝ) ^ (-(j : ℝ) - 1) ≤ (2 : ℝ) ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
      _ = 1 / 2 := by
          rw [show (-(1 : ℝ)) = (-1 : ℝ) by norm_num, Real.rpow_neg_one]
          norm_num
  have hhalf : ∀ j : ℕ,
      (2 : ℝ) ^ (-(((j + 1 : ℕ) : ℝ)) - 1) = (2 : ℝ) ^ (-(j : ℝ) - 1) / 2 := by
    intro j
    have he : -(((j + 1 : ℕ) : ℝ)) - 1 = (-(j : ℝ) - 1) + (-(1 : ℝ)) := by
      push_cast; ring
    rw [he, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [show (-(1 : ℝ)) = (-1 : ℝ) by norm_num, Real.rpow_neg_one]
    ring
  have hmono : ∀ j j' : ℕ, j ≤ j' →
      (2 : ℝ) ^ (-(j' : ℝ) - 1) ≤ (2 : ℝ) ^ (-(j : ℝ) - 1) := by
    intro j j' hjj
    have h2 : -(j' : ℝ) - 1 ≤ -(j : ℝ) - 1 := by
      have : (j : ℝ) ≤ (j' : ℝ) := by exact_mod_cast hjj
      linarith
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
  exact dyadic_boundary_tiling_aux K lam hsep φ h1 h0 hbdd
    (fun j => (2 : ℝ) ^ (-(j : ℝ) - 1)) hpos hle hhalf hmono θ

end Commons.Analysis.Fourier