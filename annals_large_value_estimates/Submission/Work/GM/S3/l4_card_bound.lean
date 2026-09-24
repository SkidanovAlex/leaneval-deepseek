import Mathlib
import Submission.Work.GM.S3.Base

namespace Work.GM.S3

/-- A `δ`-separated (with `δ ≥ 1`) finite set of reals inside `[0,T]` (with `T ≥ 1`) has at
most `T + 1` elements. (Proof idea: `t ↦ ⌊t⌋` is injective on a `1`-separated set and lands in
`{0,…,⌊T⌋}`, so `W.card ≤ ⌊T⌋ + 1 ≤ T + 1`.) -/
theorem l4_card_bound {W : Finset ℝ} {δ T : ℝ} (hT : 1 ≤ T) (hδ : 1 ≤ δ)
    (hW : ∀ t ∈ W, t ∈ Set.Icc 0 T)
    (hsep : ∀ t ∈ W, ∀ s ∈ W, t ≠ s → δ ≤ |t - s|) :
    (W.card : ℝ) ≤ T + 1 := by
  -- `⌊·⌋` is injective on `W`, because two elements with the same floor lie in a half-open
  -- interval of length `1`, contradicting `1`-separation.
  have hinj : Set.InjOn (fun t : ℝ => ⌊t⌋) (↑W : Set ℝ) := by
    intro t ht s hs h
    have h' : ⌊t⌋ = ⌊s⌋ := by simpa using h
    have hst : ⌊s⌋ = ⌊t⌋ := h'.symm
    by_contra hne
    have h1 : (1 : ℝ) ≤ |t - s| := le_trans hδ (hsep t ht s hs hne)
    have hlt : |t - s| < 1 := by
      rw [abs_lt]
      refine ⟨?_, ?_⟩
      · have hs_lt : s < (⌊s⌋ : ℤ) + 1 := Int.lt_floor_add_one s
        have ht_le : (⌊t⌋ : ℤ) ≤ t := Int.floor_le t
        rw [hst] at hs_lt
        linarith
      · have ht_lt : t < (⌊t⌋ : ℤ) + 1 := Int.lt_floor_add_one t
        have hs_le : (⌊s⌋ : ℤ) ≤ s := Int.floor_le s
        rw [hst] at hs_le
        linarith
    linarith
  have heq : W.card = (W.image (fun t : ℝ => ⌊t⌋)).card :=
    (Finset.card_image_of_injOn hinj).symm
  rw [heq]
  -- The image lies in `{0, …, ⌊T⌋}`.
  have hsub : W.image (fun t : ℝ => ⌊t⌋) ⊆ Finset.Icc (0 : ℤ) ⌊T⌋ := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨t, ht, rfl⟩ := hk
    rw [Finset.mem_Icc]
    exact ⟨Int.floor_nonneg.mpr (hW t ht).1, Int.floor_mono (hW t ht).2⟩
  have hcard : (W.image (fun t : ℝ => ⌊t⌋)).card ≤ (Finset.Icc (0 : ℤ) ⌊T⌋).card :=
    Finset.card_le_card hsub
  have hT0 : (0 : ℤ) ≤ ⌊T⌋ := Int.floor_nonneg.mpr (le_trans zero_le_one hT)
  have h2 : ((W.image (fun t : ℝ => ⌊t⌋)).card : ℝ) ≤ (⌊T⌋.toNat : ℝ) + 1 := by
    rw [Int.card_Icc] at hcard
    have h3 : (⌊T⌋ + 1 - 0 : ℤ).toNat = ⌊T⌋.toNat + 1 := by omega
    rw [h3] at hcard
    exact_mod_cast hcard
  have h5 : ((⌊T⌋.toNat : ℕ) : ℝ) ≤ T := by
    have h6 : ((⌊T⌋).toNat : ℤ) = ⌊T⌋ := Int.toNat_of_nonneg hT0
    calc ((⌊T⌋.toNat : ℕ) : ℝ) = ((⌊T⌋.toNat : ℤ) : ℝ) := by push_cast; ring
      _ = ((⌊T⌋ : ℤ) : ℝ) := by rw [h6]
      _ ≤ T := Int.floor_le T
  linarith [h2, h5]

end Work.GM.S3
