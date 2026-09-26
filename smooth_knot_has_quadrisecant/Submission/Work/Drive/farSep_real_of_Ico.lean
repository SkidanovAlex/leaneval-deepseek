import Mathlib
import Submission.Work.Drive.chordSweepDefs

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **Reduction modulo the period preserves the value of a periodic family.**
For a family `Γ` with `Γ s (t + period) = Γ s t`, replacing `t` by its representative
`toIcoMod hp 0 t ∈ [0, period)` leaves `Γ s t` unchanged. -/
lemma Gamma_eq_toIcoMod {Γ : ℝ → ℝ → Space} (hp : 0 < period)
    (hper : ∀ s t : ℝ, Γ s (t + period) = Γ s t) (s t : ℝ) :
    Γ s t = Γ s (toIcoMod hp 0 t) := by
  have hpe : Function.Periodic (Γ s) period := hper s
  have h1 := (hpe.int_mul (toIcoDiv hp 0 t)) (toIcoMod hp 0 t)
  have h2 : t = toIcoMod hp 0 t + (toIcoDiv hp 0 t : ℝ) * period := by
    have h := self_sub_toIcoDiv_zsmul hp 0 t
    rw [zsmul_eq_mul] at h
    linarith
  exact (congrArg (Γ s) h2).trans h1

/-- **Far separation on `Ico 0 period` extends to all real pairs** (for a `period`-periodic family).
If for every `s ∈ S` the loop `Γ s` separates parameter pairs at scale `η` whenever both parameters
lie in `[0, period)`, then it separates *arbitrary* real pairs at the same scale with the same
constant `ρ`: reducing `t₁, t₂` modulo `period` into `[0,period)` leaves `Γ s tᵢ` unchanged
(periodicity), and the two reduced parameters are `|t₂-t₁|` or `period - |t₂-t₁|` apart, both of
which lie in `[η, period-η]`.  Used to feed the far half of the slices clause
(`Work.Drive.sweepFamOf_farSep_of_close`, stated for real pairs) from
`Work.Drive.farSep_window_of_injOn` (stated on `Ico 0 period`).  No continuity of `Γ`, and no
positivity of `η`, is needed. -/
lemma farSep_real_of_Ico {Γ : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hper : ∀ s t : ℝ, Γ s (t + LeanEval.KnotTheory.Quadrisecant.period) = Γ s t)
    {S : Set ℝ} {η ρ : ℝ}
    (h : ∀ s ∈ S, ∀ t₁ ∈ Set.Ico (0 : ℝ) LeanEval.KnotTheory.Quadrisecant.period,
      ∀ t₂ ∈ Set.Ico (0 : ℝ) LeanEval.KnotTheory.Quadrisecant.period,
      η ≤ |t₂ - t₁| → |t₂ - t₁| ≤ LeanEval.KnotTheory.Quadrisecant.period - η →
        ρ ≤ ‖Γ s t₁ - Γ s t₂‖) :
    ∀ s ∈ S, ∀ t₁ t₂ : ℝ, η ≤ |t₂ - t₁| →
      |t₂ - t₁| ≤ LeanEval.KnotTheory.Quadrisecant.period - η → ρ ≤ ‖Γ s t₁ - Γ s t₂‖ := by
  intro s hs t₁ t₂ hlow hhigh
  have hp : 0 < period := period_pos
  have hpe : Function.Periodic (Γ s) period := hper s
  by_cases hη : η ≤ 0
  · -- Case `η ≤ 0`: the reduced parameters always have cyclic distance `< period ≤ period - η`.
    have hr₁ : toIcoMod hp 0 t₁ ∈ Set.Ico (0 : ℝ) period := toIcoMod_mem_Ico' hp t₁
    have hr₂ : toIcoMod hp 0 t₂ ∈ Set.Ico (0 : ℝ) period := toIcoMod_mem_Ico' hp t₂
    have hbnd : |toIcoMod hp 0 t₂ - toIcoMod hp 0 t₁| ≤ period - η := by
      have hlt : |toIcoMod hp 0 t₂ - toIcoMod hp 0 t₁| < period :=
        abs_lt.mpr ⟨by linarith [hr₁.2, hr₂.1], by linarith [hr₂.2, hr₁.1]⟩
      linarith
    have hlb : η ≤ |toIcoMod hp 0 t₂ - toIcoMod hp 0 t₁| := le_trans hη (abs_nonneg _)
    rw [Gamma_eq_toIcoMod hp hper s t₁, Gamma_eq_toIcoMod hp hper s t₂]
    exact h s hs (toIcoMod hp 0 t₁) hr₁ (toIcoMod hp 0 t₂) hr₂ hlb hbnd
  · -- Case `η > 0`: shift both parameters by the same integer multiple of `period`, so that the
    -- first lands in `[0, period)`; the second then lies in `(-period, 2 * period)`.
    have hd_lt : |t₂ - t₁| < period := by linarith
    have hd₁ : -period < t₂ - t₁ := (abs_lt.mp hd_lt).1
    have hd₂ : t₂ - t₁ < period := (abs_lt.mp hd_lt).2
    set r₁ : ℝ := toIcoMod hp 0 t₁ with hr₁def
    set k₁ : ℤ := toIcoDiv hp 0 t₁ with hk₁def
    have hr₁ : r₁ ∈ Set.Ico (0 : ℝ) period := by
      rw [hr₁def]; exact toIcoMod_mem_Ico' hp t₁
    have ht₁ : t₁ = r₁ + (k₁ : ℝ) * period := by
      have h := self_sub_toIcoDiv_zsmul hp 0 t₁
      rw [zsmul_eq_mul] at h
      rw [← hr₁def, ← hk₁def] at h
      linarith
    set r2p : ℝ := t₂ - (k₁ : ℝ) * period with hr2pdef
    have hΓ₁ : Γ s t₁ = Γ s r₁ := by
      rw [Gamma_eq_toIcoMod hp hper s t₁, hr₁def]
    have hΓ₂ : Γ s t₂ = Γ s r2p := by
      have h2 : r2p + (k₁ : ℝ) * period = t₂ := by rw [hr2pdef]; ring
      have h1 := (hpe.int_mul k₁) r2p
      rw [h2] at h1
      exact h1
    have hr2peq : r2p = r₁ + (t₂ - t₁) := by rw [hr2pdef]; linarith
    have hsub : r2p - r₁ = t₂ - t₁ := by rw [hr2peq]; ring
    have habs : |r2p - r₁| = |t₂ - t₁| := by rw [hsub]
    have hlow' : -period < r2p := by rw [hr2peq]; linarith [hr₁.1, hd₁]
    have hhigh' : r2p < 2 * period := by rw [hr2peq]; linarith [hr₁.2, hd₂]
    by_cases h0 : r2p < 0
    · -- `r2p < 0`: shift the second parameter up by one period.
      set r₂ : ℝ := r2p + period with hr₂def
      have hr₂ : r₂ ∈ Set.Ico (0 : ℝ) period :=
        ⟨by rw [hr₂def]; linarith, by rw [hr₂def]; linarith⟩
      have hΓ₂' : Γ s t₂ = Γ s r₂ := by
        have h2 : r₂ + ((k₁ - 1 : ℤ) : ℝ) * period = t₂ := by
          rw [hr₂def, hr2pdef]; push_cast; ring
        have h1 := (hpe.int_mul (k₁ - 1)) r₂
        rw [h2] at h1
        exact h1
      have hdiff : |r₂ - r₁| = period - |t₂ - t₁| := by
        have hs_neg : t₂ - t₁ < 0 := by linarith [hr₁.1, hr2peq, h0]
        have hd : r₂ - r₁ = (t₂ - t₁) + period := by rw [hr₂def, hr2peq]; ring
        rw [hd, abs_of_pos (by linarith : 0 < (t₂ - t₁) + period), abs_of_neg hs_neg]
        ring
      rw [hΓ₁, hΓ₂']
      refine h s hs r₁ hr₁ r₂ hr₂ ?_ ?_
      · rw [hdiff]; linarith
      · rw [hdiff]; linarith
    · have h0' : 0 ≤ r2p := le_of_not_gt h0
      by_cases h1 : r2p < period
      · -- `r2p ∈ [0, period)`: the reduced pair itself is admissible.
        have hmem : r2p ∈ Set.Ico (0 : ℝ) period := ⟨h0', h1⟩
        rw [hΓ₁, hΓ₂]
        exact h s hs r₁ hr₁ r2p hmem (by rw [habs]; exact hlow) (by rw [habs]; exact hhigh)
      · -- `period ≤ r2p < 2 * period`: shift the second parameter down by one period.
        have h2p : period ≤ r2p := le_of_not_gt h1
        set r₂ : ℝ := r2p - period with hr₂def
        have hr₂ : r₂ ∈ Set.Ico (0 : ℝ) period :=
          ⟨by rw [hr₂def]; linarith, by rw [hr₂def]; linarith⟩
        have hΓ₂' : Γ s t₂ = Γ s r₂ := by
          have h2 : r₂ + ((k₁ + 1 : ℤ) : ℝ) * period = t₂ := by
            rw [hr₂def, hr2pdef]; push_cast; ring
          have h1 := (hpe.int_mul (k₁ + 1)) r₂
          rw [h2] at h1
          exact h1
        have hdiff : |r₂ - r₁| = period - |t₂ - t₁| := by
          have hs_pos : 0 < t₂ - t₁ := by linarith [hr₁.2, hr2peq, h2p]
          have hd : r₂ - r₁ = (t₂ - t₁) - period := by rw [hr₂def, hr2peq]; ring
          rw [hd, abs_of_neg (by linarith : (t₂ - t₁) - period < 0), abs_of_pos hs_pos]
          ring
        rw [hΓ₁, hΓ₂']
        refine h s hs r₁ hr₁ r₂ hr₂ ?_ ?_
        · rw [hdiff]; linarith
        · rw [hdiff]; linarith

end Work.Drive
