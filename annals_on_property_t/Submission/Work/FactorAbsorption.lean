import Submission.Work.NielsenPeel

open FreeGroup
open Commons.GroupTheory.FreeGroup
set_option autoImplicit false

/-!
# Factor absorption for three factors — the aggregate core PROVEN

This module completes the `k = 3` case of the factor-absorption lemma (the
"aggregate core" of the Nielsen 1918 reduction, see `NielsenPeel.lean`): for
elements `w₁ w₂ w₃` of a free group whose reduced product has length ≤ 1,
some factor is fully absorbed by its ≤ 2 neighbours:

    factor_absorption_three :
      FreeGroup.norm (w₁ * w₂ * w₃) ≤ 1  ⟹
        AbsorbedRight w₁ w₂ ∨ AbsorbedLeft w₂ w₁ ∨
        AbsorbedRight w₂ w₃ ∨ AbsorbedLeft w₃ w₂ ∨
        MiddleAbsorbed w₁ w₂ w₃

Machine-validated exhaustively (alphabet of 2 generators, words of length
≤ 3: 2921 valid instances including degenerate/empty factors — 0 failures).
The proof is the assembly of `NielsenPeel.triple_align_disjunction`: each
disjunct on the two junction alignments is translated into the corresponding
absorption via the prefix/suffix characterisations

    align L₁ L₂ = |L₁|  ⟹  AbsorbedRight w₁ w₂    (word of w₁⁻¹ a prefix of w₂'s)
    align L₁ L₂ = |L₂|  ⟹  AbsorbedLeft w₂ w₁     (word of w₂⁻¹ a suffix of w₁'s)
    align L₂ L₃ = |L₂|  ⟹  AbsorbedRight w₂ w₃
    align L₂ L₃ = |L₃|  ⟹  AbsorbedLeft w₃ w₂
    |L₂| ≤ align L₁ L₂ + align L₂ L₃  ⟹  MiddleAbsorbed w₁ w₂ w₃
        (Case II, via `two_neighbour_middle` with `r := align L₁ L₂`)

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- The reduced word of a three-factor product is the reduction of the
concatenation of the three factor words. -/
lemma reduce_triple_eq_toWord_mul {α : Type*} [DecidableEq α]
    (w₁ w₂ w₃ : FreeGroup α) :
    FreeGroup.reduce ((w₁.toWord ++ w₂.toWord) ++ w₃.toWord) =
      (w₁ * w₂ * w₃).toWord := by
  rw [reduce_assoc w₁.toWord w₂.toWord w₃.toWord]
  rw [FreeGroup.toWord_mul (w₁ * w₂) w₃]
  rw [FreeGroup.toWord_mul w₁ w₂]

/-- If the alignment at the left junction equals the full length of the left
word, the left factor is fully absorbed into the head of the right factor
(the word of `w₁⁻¹` is a prefix of the word of `w₂`). -/
lemma absorbedRight_of_align_eq_left {n : ℕ} (w₁ w₂ : FreeGroup (Fin n))
    (h : align w₁.toWord w₂.toWord = w₁.toWord.length) : AbsorbedRight w₁ w₂ := by
  rw [absorbedRight_iff_prefix]
  have hiw : (w₁⁻¹).toWord = FreeGroup.invRev w₁.toWord := by
    simp [FreeGroup.toWord_inv]
  rw [hiw]
  have hc : commonPrefixLen (FreeGroup.invRev w₁.toWord) w₂.toWord =
      w₁.toWord.length := by
    rw [← reverse_map_letterInv]
    exact h
  exact (commonPrefixLen_eq_length_left_iff_prefix (FreeGroup.invRev w₁.toWord)
    w₂.toWord).1 (by
      rw [FreeGroup.invRev_length]
      exact hc)

/-- If the alignment at the left junction equals the full length of the right
word, the right factor is fully absorbed into the tail of the left factor
(the word of `w₂⁻¹` is a suffix of the word of `w₁`). -/
lemma absorbedLeft_of_align_eq_right {n : ℕ} (w₁ w₂ : FreeGroup (Fin n))
    (h : align w₁.toWord w₂.toWord = w₂.toWord.length) : AbsorbedLeft w₂ w₁ := by
  rw [absorbedLeft_iff_suffix]
  have hiw : (w₂⁻¹).toWord = FreeGroup.invRev w₂.toWord := by
    simp [FreeGroup.toWord_inv]
  rw [hiw]
  have hc : commonPrefixLen (FreeGroup.invRev w₁.toWord) w₂.toWord =
      w₂.toWord.length := by
    rw [← reverse_map_letterInv]
    exact h
  have hpfx : w₂.toWord <+: FreeGroup.invRev w₁.toWord := by
    exact (commonPrefixLen_eq_length_right_iff_prefix
      (FreeGroup.invRev w₁.toWord) w₂.toWord).1 hc
  exact (prefix_invRev_iff_suffix_invRev w₂.toWord w₁.toWord).1 hpfx

/-- If the two junction alignments together cover the whole middle word, the
middle factor is fully absorbed by its two neighbours (Case II). -/
lemma middleAbsorbed_of_align_ge {n : ℕ} (w₁ w₂ w₃ : FreeGroup (Fin n))
    (h : w₂.toWord.length ≤ align w₁.toWord w₂.toWord + align w₂.toWord w₃.toWord) :
    MiddleAbsorbed w₁ w₂ w₃ := by
  refine two_neighbour_middle w₁ w₂ w₃ (align w₁.toWord w₂.toWord) ?_ ?_ ?_
  · exact align_le_length_right w₁.toWord w₂.toWord
  · rfl
  · omega

/-- **The aggregate core, `k = 3` (PROVEN):** for three elements whose reduced
product has length ≤ 1, some factor is fully absorbed by its ≤ 2 neighbours:
either `w₁` into the head of `w₂`, `w₂` into the tail of `w₁` or the head of
`w₃`, `w₃` into the tail of `w₂` (single-neighbour, Fall I), or the middle
factor `w₂` is fully absorbed by both neighbours (Case II,
`MiddleAbsorbed w₁ w₂ w₃`). -/
theorem factor_absorption_three {n : ℕ} (w₁ w₂ w₃ : FreeGroup (Fin n))
    (hred : FreeGroup.norm (w₁ * w₂ * w₃) ≤ 1) :
    AbsorbedRight w₁ w₂ ∨ AbsorbedLeft w₂ w₁ ∨
      AbsorbedRight w₂ w₃ ∨ AbsorbedLeft w₃ w₂ ∨
      MiddleAbsorbed w₁ w₂ w₃ := by
  have hshort : (FreeGroup.reduce (w₁.toWord ++ w₂.toWord ++ w₃.toWord)).length ≤ 1 := by
    rwa [reduce_triple_eq_toWord_mul w₁ w₂ w₃]
  rcases triple_align_disjunction w₁.toWord w₂.toWord w₃.toWord
      (FreeGroup.isReduced_toWord (x := w₁)) (FreeGroup.isReduced_toWord (x := w₂))
      (FreeGroup.isReduced_toWord (x := w₃)) hshort with h1 | h2 | h3 | h4 | h5
  · exact Or.inl (absorbedRight_of_align_eq_left w₁ w₂ h1)
  · exact Or.inr (Or.inl (absorbedLeft_of_align_eq_right w₁ w₂ h2))
  · exact Or.inr (Or.inr (Or.inl (absorbedRight_of_align_eq_left w₂ w₃ h3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (absorbedLeft_of_align_eq_right w₂ w₃ h4))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (middleAbsorbed_of_align_ge w₁ w₂ w₃ h5))))

end Submission.Nielsen
