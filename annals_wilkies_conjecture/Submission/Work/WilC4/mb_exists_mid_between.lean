import Mathlib
import Submission.Work.WilC4.ULPMDev

namespace Work.WilC4

/-- For a finite `E ⊆ ℝ`, two points `a < b` of `E` with `a > 0` straddle a geometric midpoint of
two *consecutive* positive elements of `E`: namely the pair (`ρ₁`, `ρ₂`) bounding `a` from above
and `b` from below. -/
theorem mb_exists_mid_between {E : Set ℝ} (hE : E.Finite) {a b : ℝ}
    (ha : a ∈ E) (ha0 : 0 < a) (hb : b ∈ E) (hab : a < b) :
    ∃ m : ℝ, m ∈ Work.WilC4.Mid E ∧ a < m ∧ m < b := by
  have hmem : ∀ x : ℝ, x ∈ hE.toFinset ↔ x ∈ E := fun x => hE.mem_toFinset
  -- upper endpoint: least element of `E` lying in `(a, b]`
  let t : Finset ℝ := hE.toFinset.filter (fun ρ => a < ρ ∧ ρ ≤ b)
  have ht : t.Nonempty :=
    ⟨b, by rw [Finset.mem_filter]; exact ⟨(hmem b).mpr hb, hab, le_refl b⟩⟩
  set ρ₂ : ℝ := t.min' ht with hρ₂
  have hρ₂t : ρ₂ ∈ t := by rw [hρ₂]; exact Finset.min'_mem t ht
  have hρ₂min : ∀ x ∈ t, ρ₂ ≤ x := by
    intro x hx; rw [hρ₂]; exact Finset.min'_le t x hx
  obtain ⟨hρ₂E, hρ₂gt, hρ₂le⟩ := Finset.mem_filter.mp hρ₂t
  have hρ₂E' : ρ₂ ∈ E := (hmem ρ₂).mp hρ₂E
  -- lower endpoint: greatest element of `E` lying in `[a, ρ₂)`
  let u : Finset ℝ := hE.toFinset.filter (fun ρ => a ≤ ρ ∧ ρ < ρ₂)
  have hu : u.Nonempty :=
    ⟨a, by rw [Finset.mem_filter]; exact ⟨(hmem a).mpr ha, le_refl a, hρ₂gt⟩⟩
  set ρ₁ : ℝ := u.max' hu with hρ₁
  have hρ₁u : ρ₁ ∈ u := by rw [hρ₁]; exact Finset.max'_mem u hu
  have hρ₁max : ∀ x ∈ u, x ≤ ρ₁ := by
    intro x hx; rw [hρ₁]; exact Finset.le_max' u x hx
  obtain ⟨hρ₁E, hρ₁ge, hρ₁lt⟩ := Finset.mem_filter.mp hρ₁u
  have hρ₁E' : ρ₁ ∈ E := (hmem ρ₁).mp hρ₁E
  -- `ρ₁` and `ρ₂` are consecutive positive elements of `E`
  have hconsec : ∀ ρ ∈ E, 0 < ρ → ρ ≤ ρ₁ ∨ ρ₂ ≤ ρ := by
    intro ρ hρE _
    rcases lt_or_ge ρ ρ₁ with h | h
    · exact Or.inl (le_of_lt h)
    · rcases lt_or_eq_of_le h with hlt | heq
      · refine Or.inr ?_
        by_contra hlt2
        rw [not_le] at hlt2
        have hpρ : ρ ∈ t := by
          rw [Finset.mem_filter]
          exact ⟨(hmem ρ).mpr hρE, lt_of_le_of_lt hρ₁ge hlt,
            le_of_lt (lt_of_lt_of_le hlt2 hρ₂le)⟩
        exact absurd (hρ₂min ρ hpρ) (not_le.mpr hlt2)
      · exact Or.inl (le_of_eq heq.symm)
  have hρ₁pos : 0 < ρ₁ := lt_of_lt_of_le ha0 hρ₁ge
  have hρ₂pos : 0 < ρ₂ := lt_trans ha0 hρ₂gt
  have hbpos : 0 < b := lt_of_lt_of_le hρ₂pos hρ₂le
  refine ⟨Real.sqrt (ρ₁ * ρ₂), ?_, ?_, ?_⟩
  · refine ⟨ρ₁, hρ₁E', ρ₂, hρ₂E', hρ₁pos, hρ₁lt, hconsec, ?_, ?_⟩
    · rw [← sq, Real.sq_sqrt (le_of_lt (mul_pos hρ₁pos hρ₂pos))]
    · exact Real.sqrt_pos_of_pos (mul_pos hρ₁pos hρ₂pos)
  · rw [Real.lt_sqrt ha0.le]
    nlinarith [hρ₁ge, ha0, hρ₁lt]
  · rw [Real.sqrt_lt (le_of_lt (mul_pos hρ₁pos hρ₂pos)) (le_of_lt hbpos)]
    nlinarith [hρ₂le, hρ₁lt, hρ₂gt, ha0]

end Work.WilC4
