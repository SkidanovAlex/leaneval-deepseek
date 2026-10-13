import Mathlib
import Submission.Work.WilC4.ULPMDev

namespace Work.WilC4

/-- The set of geometric midpoints of a finite set of reals is finite: every `x ∈ Mid E` is
`√(ρ₁ * ρ₂)` for the witnessing pair `ρ₁, ρ₂ ∈ E`, so `Mid E` is contained in the image of the
finite set `E ×ˢ E`. -/
private lemma Mid_finite {E : Set ℝ} (hE : E.Finite) : (Mid E).Finite := by
  have hEE : (E ×ˢ E).Finite := hE.prod hE
  refine Set.Finite.subset (hEE.image (fun p : ℝ × ℝ => Real.sqrt (p.1 * p.2))) ?_
  rintro x ⟨ρ₁, h₁, ρ₂, h₂, hρ₁, hρ₂lt, hcon, hx, hxpos⟩
  refine ⟨(ρ₁, ρ₂), ?_, ?_⟩
  · rw [Set.mem_prod]; exact ⟨h₁, h₂⟩
  · rw [Real.sqrt_eq_iff_eq_sq
        (mul_nonneg (le_of_lt hρ₁) (le_of_lt (lt_trans hρ₁ hρ₂lt))) (le_of_lt hxpos),
      pow_two]
    exact hx.symm

/-- A geometric midpoint of two consecutive positive elements of `E` is distinct from every
positive element of `E`. -/
private lemma Mid_ne_of_mem {E : Set ℝ} {m ρ : ℝ} (hm : m ∈ Mid E) (hρ : ρ ∈ E)
    (hρpos : 0 < ρ) : m ≠ ρ := by
  obtain ⟨ρ₁, h₁, ρ₂, h₂, hρ₁pos, hlt, hcon, hmx, hmpos⟩ := hm
  intro heq
  rw [heq] at hmx
  rcases hcon ρ hρ hρpos with h | h
  · have h1 : ρ ^ 2 ≤ ρ₁ ^ 2 := pow_le_pow_left₀ (le_of_lt hρpos) h 2
    have h2 : ρ₁ * ρ₁ < ρ₁ * ρ₂ := mul_lt_mul_of_pos_left hlt hρ₁pos
    nlinarith [h1, h2, hmx]
  · have h1 : ρ₂ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (le_of_lt (lt_trans hρ₁pos hlt)) h 2
    have h2 : ρ₁ * ρ₂ < ρ₂ * ρ₂ := mul_lt_mul_of_pos_right hlt (lt_trans hρ₁pos hlt)
    nlinarith [h1, h2, hmx]

theorem mid_sep {E : Set ℝ} (hE : E.Finite) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ ∈ E, 0 < ρ → ∀ m ∈ Work.WilC4.Mid E, δ * ρ ≤ |ρ - m| := by
  classical
  -- The positive part of `E` is finite, and so is the set of midpoints.
  have hP : (E ∩ Set.Ioi (0 : ℝ)).Finite := hE.subset Set.inter_subset_left
  have hM : (Mid E).Finite := Mid_finite hE
  let s := hP.toFinset
  let t := hM.toFinset
  -- The finite set of ratios `|ρ - m| / ρ` over the (finitely many) pairs `(ρ, m)`.
  let R : Finset ℝ := (s ×ˢ t).image (fun p : ℝ × ℝ => |p.1 - p.2| / p.1)
  by_cases hRne : R.Nonempty
  · -- There is at least one pair: the minimum of the (positive) ratio set is our `δ`.
    refine ⟨R.min' hRne, ?_, ?_⟩
    · have hmem : R.min' hRne ∈ R := Finset.min'_mem R hRne
      obtain ⟨p, hp, hpval⟩ := Finset.mem_image.mp hmem
      rw [Finset.mem_product] at hp
      obtain ⟨hp1, hp2⟩ := hp
      have hp1E : p.1 ∈ E := ((Set.Finite.mem_toFinset hP).mp hp1).1
      have hp1pos : 0 < p.1 := ((Set.Finite.mem_toFinset hP).mp hp1).2
      have hp2M : p.2 ∈ Mid E := (Set.Finite.mem_toFinset hM).mp hp2
      have hne : p.1 ≠ p.2 := (Mid_ne_of_mem hp2M hp1E hp1pos).symm
      rw [← hpval]
      exact div_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) hp1pos
    · intro ρ hρ hρpos m hm
      have hρs : ρ ∈ s := by
        rw [Set.Finite.mem_toFinset hP, Set.mem_inter_iff, Set.mem_Ioi]
        exact ⟨hρ, hρpos⟩
      have hmt : m ∈ t := by
        rw [Set.Finite.mem_toFinset hM]
        exact hm
      have hq : |ρ - m| / ρ ∈ R := by
        rw [Finset.mem_image]
        exact ⟨(ρ, m), by rw [Finset.mem_product]; exact ⟨hρs, hmt⟩, rfl⟩
      have hle : R.min' hRne ≤ |ρ - m| / ρ := Finset.min'_le R _ hq
      have h2 := mul_le_mul_of_nonneg_right hle (le_of_lt hρpos)
      rw [div_mul_cancel₀ _ (ne_of_gt hρpos)] at h2
      exact h2
  · -- No pair: the statement is vacuous, and `δ = 1` works.
    refine ⟨1, one_pos, ?_⟩
    intro ρ hρ hρpos m hm
    have hq : |ρ - m| / ρ ∈ R := by
      rw [Finset.mem_image]
      refine ⟨(ρ, m), ?_, rfl⟩
      rw [Finset.mem_product]
      constructor
      · rw [Set.Finite.mem_toFinset hP, Set.mem_inter_iff, Set.mem_Ioi]
        exact ⟨hρ, hρpos⟩
      · rw [Set.Finite.mem_toFinset hM]; exact hm
    exact (hRne ⟨_, hq⟩).elim

end Work.WilC4
