import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.gridPinningCount

namespace Work.Peluse.Ulower.StepLe

/-- **Pinning of grid values.**  Suppose every `ψ k` (`k ∈ H`) is a grid value `m/T` with
`0 ≤ m ≤ T`, and every `ψ k` is `ε`-close to a rational `a/t` with `1 ≤ t ≤ T₀`.  Then `H` has a
sub-family `H'` on which `ψ` is constant, containing a `K`-th fraction of `H` where
`K = 4 ((T₀+1) T₀) (⌊2εT⌋+1)`: the number of *distinct* grid values that can be pinned this way is
at most `K` (this is `gridPinningCount` with `σ = 0`). -/
theorem pinValues {T T₀ : ℕ} (hT : 1 ≤ T) {ε : ℝ} (hε : 0 ≤ ε) {ι : Type} [DecidableEq ι]
    (H : Finset ι) (ψ : ι → ℝ)
    (hgr : ∀ k ∈ H, ∃ m : ℕ, m ≤ T ∧ ψ k = (m : ℝ) / (T : ℝ))
    (hpin : ∀ k ∈ H, ∃ t : ℕ, 1 ≤ t ∧ t ≤ T₀ ∧ ∃ a : ℤ,
      |ψ k - (a : ℝ) / (t : ℝ)| ≤ ε) :
    ∃ H' ⊆ H,
      (H.card : ℝ) ≤ (4 * ((T₀ + 1) * T₀) * (Nat.floor (2 * ε * (T : ℝ)) + 1)) * (H'.card : ℝ) ∧
      ∃ v₀ : ℝ, ∀ k ∈ H', ψ k = v₀ := by
  classical
  by_cases hH : H = ∅
  · refine ⟨∅, Finset.empty_subset H, ?_, 0, ?_⟩
    · simp [hH]
    · intro k hk
      exact absurd hk (Finset.notMem_empty k)
  · -- the set of grid numerators that can be pinned
    set S : Finset ℕ := (Finset.range (T + 1)).filter (fun m =>
        ∃ t : ℕ, 1 ≤ t ∧ t ≤ T₀ ∧ ∃ a : ℤ,
          |(m : ℝ) / (T : ℝ) - (a : ℝ) / (t : ℝ)| ≤ ε) with hSdef
    have hScond : ∀ m ∈ S, m ≤ 2 ^ 0 * T ∧ ∃ t : ℕ, 1 ≤ t ∧ t ≤ T₀ ∧ ∃ a : ℤ,
        |(m : ℝ) / (T : ℝ) - (a : ℝ) / (t : ℝ)| ≤ ε := by
      intro m hm
      simp only [hSdef, Finset.mem_filter, Finset.mem_range] at hm
      exact ⟨by simpa using hm.1, hm.2⟩
    have hScard : (S.card : ℝ) ≤ 4 * ((T₀ + 1) * T₀) * (Nat.floor (2 * ε * (T : ℝ)) + 1) := by
      have h := gridPinningCount (σ := 0) hT hε S hScond
      simpa using h
    -- every value of `ψ` on `H` is one of the pinning grid values
    have hsub : H.image ψ ⊆ S.image (fun m : ℕ => (m : ℝ) / (T : ℝ)) := by
      intro v hv
      obtain ⟨k, hk, hkψ⟩ := Finset.mem_image.mp hv
      obtain ⟨m, hmT, hmv⟩ := hgr k hk
      rw [Finset.mem_image]
      refine ⟨m, ?_, ?_⟩
      · simp only [hSdef, Finset.mem_filter, Finset.mem_range]
        refine ⟨Nat.lt_succ_of_le hmT, ?_⟩
        obtain ⟨t, ht1, htT, a, ha⟩ := hpin k hk
        exact ⟨t, ht1, htT, a, by rw [← hmv]; exact ha⟩
      · rw [← hmv]; exact hkψ
    have hDle : (H.image ψ).card ≤ S.card :=
      le_trans (Finset.card_le_card hsub) Finset.card_image_le
    -- pigeonhole: take a value of `ψ` with a maximal fibre
    have hne : H.Nonempty := Finset.nonempty_iff_ne_empty.mpr hH
    obtain ⟨k₀, hk₀⟩ := hne
    obtain ⟨v₀, hv₀, hmax⟩ := Finset.exists_max_image (H.image ψ)
      (fun b => (H.filter (fun k => ψ k = b)).card)
      ⟨ψ k₀, Finset.mem_image_of_mem ψ hk₀⟩
    set H' : Finset ι := H.filter (fun k => ψ k = v₀) with hH'def
    have hH'sub : H' ⊆ H := Finset.filter_subset _ _
    have hconst : ∀ k ∈ H', ψ k = v₀ := fun k hk => (Finset.mem_filter.mp hk).2
    have hsum := Finset.card_eq_sum_card_fiberwise (s := H) (t := H.image ψ) (f := ψ)
      (fun k hk => Finset.mem_image_of_mem ψ hk)
    have hle : H.card ≤ (H.image ψ).card * H'.card := by
      rw [hsum]
      calc ∑ b ∈ H.image ψ, (H.filter fun k => ψ k = b).card
          ≤ ∑ _b ∈ H.image ψ, H'.card := by
            apply Finset.sum_le_sum
            intro b hb
            simpa [hH'def] using hmax b hb
        _ = (H.image ψ).card * H'.card := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    have hleR : (H.card : ℝ) ≤ ((H.image ψ).card : ℝ) * (H'.card : ℝ) := by
      exact_mod_cast hle
    refine ⟨H', hH'sub, ?_, v₀, hconst⟩
    have hK : ((H.image ψ).card : ℝ)
        ≤ 4 * ((T₀ + 1) * T₀) * (Nat.floor (2 * ε * (T : ℝ)) + 1) := by
      have h1 : ((H.image ψ).card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hDle
      linarith [h1, hScard]
    calc (H.card : ℝ) ≤ ((H.image ψ).card : ℝ) * (H'.card : ℝ) := hleR
      _ ≤ (4 * ((T₀ + 1) * T₀) * (Nat.floor (2 * ε * (T : ℝ)) + 1)) * (H'.card : ℝ) :=
          mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg _)

end Work.Peluse.Ulower.StepLe
