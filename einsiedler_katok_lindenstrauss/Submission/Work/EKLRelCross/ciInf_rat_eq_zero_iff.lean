import Mathlib

set_option linter.style.haveILetI false

namespace Work.EKLRelCross

open Set Filter

/-- The rational points of `Icc a b` approximate any point of the interval: for every
`τ ∈ Icc a b` and every `δ > 0` there is a rational `q` with `a ≤ q ≤ b` and
`|q - τ| < δ`. -/
private lemma exists_rat_mem_Icc_near {a b : ℚ} (hab : (a : ℝ) ≤ (b : ℝ)) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (a : ℝ) (b : ℝ)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℚ, (a : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ≤ (b : ℝ) ∧ |(q : ℝ) - τ| < δ := by
  rcases eq_or_lt_of_le hab with h | h
  · -- degenerate interval `a = b`: any point of it equals `a`
    have haτ : (a : ℝ) = τ := by
      have h1 : τ ≤ (a : ℝ) := by rw [h]; exact hτ.2
      exact le_antisymm hτ.1 h1
    refine ⟨a, le_refl _, hab, ?_⟩
    rw [haτ, sub_self, abs_zero]; exact hδ
  · -- nondegenerate interval: pick a rational strictly between `max a (τ-δ)` and `min b (τ+δ)`
    obtain ⟨q, hq1, hq2⟩ :=
      exists_rat_btwn (show max (a : ℝ) (τ - δ) < min (b : ℝ) (τ + δ) from by
        rw [max_lt_iff]
        exact ⟨by rw [lt_min_iff]; exact ⟨h, by linarith [hτ.1, hδ]⟩,
               by rw [lt_min_iff]; exact ⟨by linarith [hτ.2, hδ], by linarith [hδ]⟩⟩)
    refine ⟨q, ?_, ?_, ?_⟩
    · exact le_of_lt (lt_of_le_of_lt (le_max_left _ _) hq1)
    · exact le_of_lt (lt_of_lt_of_le hq2 (min_le_left _ _))
    · rw [abs_lt]
      exact ⟨by linarith [le_max_right (a : ℝ) (τ - δ), hq1],
             by linarith [lt_of_lt_of_le hq2 (min_le_right (b : ℝ) (τ + δ))]⟩

theorem ciInf_rat_eq_zero_iff {a b : ℚ} (hab : (a:ℝ) ≤ (b:ℝ))
    (f : ℝ → ℝ) (hf : Continuous f) (h0 : ∀ τ, 0 ≤ f τ) :
    (⨅ (q : {q : ℚ // (a:ℝ) ≤ (q:ℝ) ∧ (q:ℝ) ≤ (b:ℝ)}), f (q:ℝ)) = 0 ↔
      ∃ τ ∈ Set.Icc (a:ℝ) (b:ℝ), f τ = 0 := by
  haveI : Nonempty {q : ℚ // (a:ℝ) ≤ (q:ℝ) ∧ (q:ℝ) ≤ (b:ℝ)} := ⟨⟨a, le_refl _, hab⟩⟩
  constructor
  · -- `inf = 0 → 0` is attained: otherwise `f` has a strictly positive minimum on `Icc a b`,
    -- which would bound the infimum from below by a positive number.
    intro hinf
    by_contra hno
    rw [not_exists] at hno
    have hfnz : ∀ τ, τ ∈ Set.Icc (a:ℝ) (b:ℝ) → f τ ≠ 0 := fun τ hτ hh => hno τ ⟨hτ, hh⟩
    have hne : (Set.Icc (a:ℝ) (b:ℝ)).Nonempty := ⟨(a:ℝ), le_refl _, hab⟩
    obtain ⟨x, hx, hxmin⟩ := isCompact_Icc.exists_isMinOn hne hf.continuousOn
    have hle : f x ≤ ⨅ q : {q : ℚ // (a:ℝ) ≤ (q:ℝ) ∧ (q:ℝ) ≤ (b:ℝ)}, f (q:ℝ) :=
      le_ciInf (fun q => hxmin q.2)
    rw [hinf] at hle
    have hfx : 0 < f x := lt_of_le_of_ne (h0 x) (Ne.symm (hfnz x hx))
    linarith
  · -- `0` is attained at `τ`: the infimum is `≥ 0` and, by continuity and density of `ℚ`,
    -- is `< ε` for every `ε > 0`.
    rintro ⟨τ, hτ, hfτ⟩
    have hbdd : BddBelow
        (Set.range (fun q : {q : ℚ // (a:ℝ) ≤ (q:ℝ) ∧ (q:ℝ) ≤ (b:ℝ)} => f (q:ℝ))) :=
      ⟨0, by rintro _ ⟨q, rfl⟩; exact h0 _⟩
    refine le_antisymm ?_ (le_ciInf (fun q => h0 (q:ℝ)))
    apply le_of_forall_pos_lt_add
    intro ε hε
    have hcont : Tendsto f (nhds τ) (nhds 0) := hfτ ▸ hf.continuousAt
    rw [Metric.tendsto_nhds_nhds] at hcont
    obtain ⟨δ, hδ, hδ'⟩ := hcont ε hε
    obtain ⟨q, hqa, hqb, hqdist⟩ := exists_rat_mem_Icc_near hab hτ hδ
    have hqf : f (q:ℝ) < ε := by
      have h2 := hδ' (by rw [Real.dist_eq]; exact hqdist)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (h0 (q:ℝ))] at h2
      exact h2
    have hle : (⨅ q : {q : ℚ // (a:ℝ) ≤ (q:ℝ) ∧ (q:ℝ) ≤ (b:ℝ)}, f (q:ℝ)) ≤ f (q:ℝ) := by
      simpa using ciInf_le hbdd (⟨q, hqa, hqb⟩ : {q : ℚ // (a:ℝ) ≤ (q:ℝ) ∧ (q:ℝ) ≤ (b:ℝ)})
    have : (⨅ q : {q : ℚ // (a:ℝ) ≤ (q:ℝ) ∧ (q:ℝ) ≤ (b:ℝ)}, f (q:ℝ)) < ε :=
      lt_of_le_of_lt hle hqf
    linarith

end Work.EKLRelCross
