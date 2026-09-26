import Mathlib
import Submission.Work.Drive.sweepFamOf

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

open LeanEval.KnotTheory.Quadrisecant in
theorem farSep_window_of_injOn
    {Γ : ℝ → ℝ → Space} (hΓ : Continuous (fun p : ℝ × ℝ => Γ p.1 p.2))
    (hper : ∀ s t : ℝ, Γ s (t + period) = Γ s t)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb1 : b < 1)
    (hinj : ∀ s ∈ Set.Icc a b, Set.InjOn (Γ s) (Set.Ico (0 : ℝ) period))
    {η : ℝ} (hη : 0 < η) (hηper : 2 * η ≤ period) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s ∈ Set.Icc a b, ∀ t₁ ∈ Set.Ico (0:ℝ) period,
      ∀ t₂ ∈ Set.Ico (0:ℝ) period, η ≤ |t₂ - t₁| → |t₂ - t₁| ≤ period - η →
      ρ ≤ ‖Γ s t₁ - Γ s t₂‖ := by
  have hp : 0 < period := period_pos
  have hper0 : ∀ s : ℝ, Γ s period = Γ s 0 := fun s => by simpa using hper s 0
  -- The constraint set: triples `(s, t₁, t₂)` in the compact window whose loop parameters are
  -- `η`-separated and at most `period - η` apart.
  set S : Set (ℝ × ℝ × ℝ) :=
    {q | q.1 ∈ Set.Icc a b ∧ q.2.1 ∈ Set.Icc (0 : ℝ) period ∧
      q.2.2 ∈ Set.Icc (0 : ℝ) period ∧ |q.2.2 - q.2.1| ∈ Set.Icc η (period - η)} with hSdef
  have hSclosed : IsClosed S := by
    rw [hSdef]
    have h1 : IsClosed {q : ℝ × ℝ × ℝ | q.1 ∈ Set.Icc a b} :=
      isClosed_Icc.preimage continuous_fst
    have h2 : IsClosed {q : ℝ × ℝ × ℝ | q.2.1 ∈ Set.Icc (0 : ℝ) period} :=
      isClosed_Icc.preimage (continuous_fst.comp continuous_snd)
    have h3 : IsClosed {q : ℝ × ℝ × ℝ | q.2.2 ∈ Set.Icc (0 : ℝ) period} :=
      isClosed_Icc.preimage (continuous_snd.comp continuous_snd)
    have h4 : IsClosed {q : ℝ × ℝ × ℝ | |q.2.2 - q.2.1| ∈ Set.Icc η (period - η)} :=
      isClosed_Icc.preimage
        (((continuous_snd.comp continuous_snd).sub (continuous_fst.comp continuous_snd)).abs)
    exact h1.inter (h2.inter (h3.inter h4))
  have hScompact : IsCompact S := by
    have hc : IsCompact
        (Set.Icc a b ×ˢ (Set.Icc (0 : ℝ) period ×ˢ Set.Icc (0 : ℝ) period)) :=
      isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    refine hc.of_isClosed_subset hSclosed ?_
    intro q hq
    rw [hSdef] at hq
    exact ⟨hq.1, hq.2.1, hq.2.2.1⟩
  have hSne : S.Nonempty := by
    refine ⟨(a, 0, η), ?_⟩
    rw [hSdef]
    refine ⟨⟨le_rfl, hab.le⟩, ⟨le_rfl, hp.le⟩, ⟨hη.le, by linarith [hηper]⟩, ?_⟩
    rw [sub_zero, abs_of_pos hη]
    exact ⟨le_rfl, by linarith [hηper]⟩
  set f : ℝ × ℝ × ℝ → ℝ := fun q => ‖Γ q.1 q.2.1 - Γ q.1 q.2.2‖ with hfdef
  have hfcont : Continuous f := by
    rw [hfdef]
    have h1 : Continuous (fun q : ℝ × ℝ × ℝ => Γ q.1 q.2.1) :=
      hΓ.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    have h2 : Continuous (fun q : ℝ × ℝ × ℝ => Γ q.1 q.2.2) :=
      hΓ.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
    exact (h1.sub h2).norm
  obtain ⟨q₀, hq₀S, hmin⟩ := hScompact.exists_isMinOn hSne hfcont.continuousOn
  refine ⟨f q₀, ?_, ?_⟩
  · -- positivity of the minimum: the minimum of `‖Γ s t₁ - Γ s t₂‖` over the compact `S` is
    -- attained and strictly positive because `Γ s` is injective on the period and the two
    -- parameters are either genuinely distinct modulo `period` (else `|t₂ - t₁| < η`) or differ
    -- by exactly `period` (else `|t₂ - t₁| > period - η`).
    simp only [hfdef]
    rw [norm_pos_iff]
    intro hsub
    have hs : q₀.1 ∈ Set.Icc a b := hq₀S.1
    have ht₁ : q₀.2.1 ∈ Set.Icc (0 : ℝ) period := hq₀S.2.1
    have ht₂ : q₀.2.2 ∈ Set.Icc (0 : ℝ) period := hq₀S.2.2.1
    have hlow : η ≤ |q₀.2.2 - q₀.2.1| := hq₀S.2.2.2.1
    have hhigh : |q₀.2.2 - q₀.2.1| ≤ period - η := hq₀S.2.2.2.2
    have heq : Γ q₀.1 q₀.2.1 = Γ q₀.1 q₀.2.2 := sub_eq_zero.mp hsub
    -- send `period` back to `0` (periodicity) so that both parameters lie in `Ico 0 period`
    have keymem : ∀ t ∈ Set.Icc (0 : ℝ) period,
        (if t = period then (0 : ℝ) else t) ∈ Set.Ico (0 : ℝ) period := by
      intro t ht
      split_ifs with h
      · exact ⟨le_rfl, hp⟩
      · exact ⟨ht.1, lt_of_le_of_ne ht.2 h⟩
    have keyeq : ∀ t ∈ Set.Icc (0 : ℝ) period,
        Γ q₀.1 (if t = period then (0 : ℝ) else t) = Γ q₀.1 t := by
      intro t ht
      split_ifs with h
      · rw [h]; exact (hper0 q₀.1).symm
      · rfl
    have huv : (if q₀.2.1 = period then (0 : ℝ) else q₀.2.1) =
        (if q₀.2.2 = period then (0 : ℝ) else q₀.2.2) :=
      hinj q₀.1 hs (keymem q₀.2.1 ht₁) (keymem q₀.2.2 ht₂)
        (by rw [keyeq q₀.2.1 ht₁, keyeq q₀.2.2 ht₂]; exact heq)
    have hcase : q₀.2.1 = q₀.2.2 ∨ |q₀.2.2 - q₀.2.1| = period := by
      by_cases h1 : q₀.2.1 = period
      · by_cases h2 : q₀.2.2 = period
        · exact Or.inl (by rw [h1, h2])
        · refine Or.inr ?_
          have hA : (if q₀.2.1 = period then (0 : ℝ) else q₀.2.1) = 0 := by rw [if_pos h1]
          have hB : (if q₀.2.2 = period then (0 : ℝ) else q₀.2.2) = q₀.2.2 := by rw [if_neg h2]
          rw [hA, hB] at huv
          rw [← huv, h1, zero_sub, abs_neg, abs_of_pos hp]
      · by_cases h2 : q₀.2.2 = period
        · refine Or.inr ?_
          have hA : (if q₀.2.1 = period then (0 : ℝ) else q₀.2.1) = q₀.2.1 := by rw [if_neg h1]
          have hB : (if q₀.2.2 = period then (0 : ℝ) else q₀.2.2) = 0 := by rw [if_pos h2]
          rw [hA, hB] at huv
          rw [huv, h2, sub_zero, abs_of_pos hp]
        · refine Or.inl ?_
          have hA : (if q₀.2.1 = period then (0 : ℝ) else q₀.2.1) = q₀.2.1 := by rw [if_neg h1]
          have hB : (if q₀.2.2 = period then (0 : ℝ) else q₀.2.2) = q₀.2.2 := by rw [if_neg h2]
          rw [hA, hB] at huv
          exact huv
    rcases hcase with hcase | hcase
    · rw [hcase, sub_self, abs_zero] at hlow
      linarith
    · rw [hcase] at hhigh
      linarith
  · -- the minimum bounds every admissible pair
    intro s hs t₁ ht₁ t₂ ht₂ hlow hhigh
    have hmem : (s, t₁, t₂) ∈ S := by
      rw [hSdef]
      exact ⟨hs, ⟨ht₁.1, ht₁.2.le⟩, ⟨ht₂.1, ht₂.2.le⟩, ⟨hlow, hhigh⟩⟩
    have hb : f q₀ ≤ f (s, t₁, t₂) := hmin hmem
    simp only [hfdef] at hb
    simpa only [hfdef] using hb

end Work.Drive
