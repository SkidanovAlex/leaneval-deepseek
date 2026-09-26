import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.blurLocalGlobal
import Submission.Work.Drive.sweepFamFarSepClean
import Submission.Work.Drive.sweepFam_contDiff_periodic

/-!
# The assembly of the *injectivity* half of the slices clause

The slices clause of the chord sweep,

    `∃ L > 0, ∀ lam δ₁ δ₂ ≤ L, ∀ σ ∈ [a,b],  InjOn (sweepFam r D lam δ₁ δ₂ σ) (Ico 0 period)`,

is the conjunction of two independent halves, both of which are proved (or provided as pins) in
this workspace:

* the **local** half — for parameters within distance `ε` of each other the sweep slice is
  injective — `Work.Drive.sweepFamLocalInj_hgood` (and its `..._nonFold` variant);
* the **far** half — uniformly separated parameters stay at distance at least `ρ` —
  `Work.Drive.sweepFamFarSep'` (`sweepFamFarSepClean.lean`, the clash-free port of
  `Work.Drive.sweepFamFarSep`), which uses only `havoid` (Kuperberg's `O`-avoidance) and the
  injectivity of the *raw* sweep loop.

This module performs the assembly, so that the slices clause is available from its two halves:

* `Work.Drive.injOn_Ico_of_local_and_farSep` — the *generic* glue: a `period`-periodic curve `γ`
  which is injective on every ball of radius `ε` and whose far pairs (at scale `ε`) are separated
  by `ρ` is injective on `[0, period)`.  (The wrapped pairs are pushed back by one period and hit
  the local hypothesis.)
* `Work.Drive.injOn_sweepFam_of_local_and_farSep` — the `sweepFam` instance, taking the local half
  as a hypothesis (so that this module is independent of the still-open
  `sweepFamLocalInj_hgood`) and supplying the far half from the proved
  `Work.Drive.sweepFamFarSep'`.

The generic glue is stated with its own `ε`-ball hypothesis rather than through
`Work.Drive.exists_uniform_local_radius`/`Work.Drive.injOn_Ico_of_radius_and_farSep`
(`blurLocalGlobal`) because the local half is *already* uniform in the parameter box, so no
compactness argument is needed; both routes are recorded so that a caller holding only the
pointwise form can use the `blurLocalGlobal` one.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

variable {E : Type*} [NormedAddCommGroup E]

/-- **The generic glue.**  A `p`-periodic curve injective on every ball of radius `ε` and with its
far pairs (distance `∈ [ε, p - ε]` inside one period) separated by `ρ` is injective on `[0,p)`. -/
theorem injOn_Ico_of_local_and_farSep {γ : ℝ → E} {p ε ρ : ℝ}
    (hp : 0 < p) (hε : 0 < ε) (hρ : 0 < ρ) (hεp : 2 * ε ≤ p)
    (hper : ∀ t : ℝ, γ (t + p) = γ t)
    (hloc : ∀ t₁ t₂ : ℝ, |t₂ - t₁| ≤ ε → γ t₁ = γ t₂ → t₁ = t₂)
    (hfar : ∀ t₁ t₂ : ℝ, t₁ ∈ Set.Ico (0 : ℝ) p → t₂ ∈ Set.Ico (0 : ℝ) p →
      ε ≤ |t₂ - t₁| → |t₂ - t₁| ≤ p - ε → ρ ≤ ‖γ t₁ - γ t₂‖) :
    Set.InjOn γ (Set.Ico (0 : ℝ) p) := by
  have hper' : ∀ t : ℝ, γ t = γ (t - p) := by
    intro t
    simpa using hper (t - p)
  intro t₁ h₁ t₂ h₂ heq
  rw [Set.mem_Ico] at h₁ h₂
  by_cases hle : |t₂ - t₁| ≤ ε
  · exact hloc t₁ t₂ hle heq
  · push_neg at hle
    have habs : -p < t₂ - t₁ ∧ t₂ - t₁ < p :=
      abs_lt.mp (by rw [abs_lt]; exact ⟨by linarith [h₁.1, h₂.2], by linarith [h₁.2, h₂.1]⟩)
    by_cases hcase : |t₂ - t₁| ≤ p - ε
    · have hf := hfar t₁ t₂ (Set.mem_Ico.mpr h₁) (Set.mem_Ico.mpr h₂) hle.le hcase
      simp only [heq, sub_self, norm_zero] at hf
      linarith
    · push_neg at hcase
      rcases le_total t₁ t₂ with h12 | h21
      · have hsub : |t₂ - t₁| = t₂ - t₁ := by rw [abs_of_nonneg (by linarith)]
        rw [hsub] at hcase
        have hnear : |t₁ - (t₂ - p)| ≤ ε := by
          rw [abs_le]; exact ⟨by linarith, by linarith⟩
        have heq' : γ (t₂ - p) = γ t₁ := (hper' t₂).symm.trans heq.symm
        have hEq := hloc (t₂ - p) t₁ hnear heq'
        linarith [h₁.1, h₂.2]
      · have hsub : |t₂ - t₁| = t₁ - t₂ := by rw [abs_of_nonpos (by linarith)]; ring
        rw [hsub] at hcase
        have hnear : |t₂ - (t₁ - p)| ≤ ε := by
          rw [abs_le]; exact ⟨by linarith, by linarith⟩
        have heq' : γ (t₁ - p) = γ t₂ := (hper' t₁).symm.trans heq
        have hEq := hloc (t₁ - p) t₂ hnear heq'
        linarith [h₂.1, h₁.2]

section Sweep

variable {r : ℝ → Space} {d : BandArcData} {D : SweepData d}

/-- **The injectivity half of the slices clause, from its local half.**  The far half is the proved
`Work.Drive.sweepFamFarSep'`; the local half (`Work.Drive.sweepFamLocalInj_hgood`) is taken as a
hypothesis, so that this assembly is independent of it. -/
theorem injOn_sweepFam_of_local_and_farSep {r : ℝ → Space} (hr : IsSmoothKnot r)
    {d : BandArcData} (D : SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hlocal : ∃ L ε : ℝ, 0 < L ∧ 0 < ε ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ L → 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L →
        ∀ σ : ℝ, a ≤ σ → σ ≤ b → ∀ t₁ t₂ : ℝ, |t₂ - t₁| ≤ ε →
          sweepFam r D lam δ₁ δ₂ σ t₁ = sweepFam r D lam δ₁ δ₂ σ t₂ → t₁ = t₂) :
    ∃ L : ℝ, 0 < L ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ L → 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L →
        ∀ σ : ℝ, a ≤ σ → σ ≤ b →
          Set.InjOn (sweepFam r D lam δ₁ δ₂ σ) (Set.Ico (0 : ℝ) period) := by
  obtain ⟨L₁, ε, hL₁, hε, hloc⟩ := hlocal
  have hp : 0 < period := period_pos
  set ε' : ℝ := min ε (period / 3) with hε'def
  have hε'0 : 0 < ε' := lt_min hε (by linarith)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'p : ε' ≤ period / 3 := min_le_right _ _
  obtain ⟨L₂, ρ, hL₂, hρ, hfar⟩ :=
    sweepFamFarSep' (r := r) hr (D := D) havoid ha hab hb ε' hε'0
  refine ⟨min L₁ L₂, lt_min hL₁ hL₂, ?_⟩
  intro lam δ₁ δ₂ h1 h2 h3 h4 h5 h6 σ hσa hσb
  have hlamL₁ : lam ≤ L₁ := le_trans h2 (min_le_left _ _)
  have hδ₁L₁ : δ₁ ≤ L₁ := le_trans h4 (min_le_left _ _)
  have hδ₂L₁ : δ₂ ≤ L₁ := le_trans h6 (min_le_left _ _)
  have hlamL₂ : lam ≤ L₂ := le_trans h2 (min_le_right _ _)
  have hδ₁L₂ : δ₁ ≤ L₂ := le_trans h4 (min_le_right _ _)
  have hδ₂L₂ : δ₂ ≤ L₂ := le_trans h6 (min_le_right _ _)
  have hper : ∀ t : ℝ, sweepFam r D lam δ₁ δ₂ σ (t + period) = sweepFam r D lam δ₁ δ₂ σ t :=
    fun t => (sweepFam_contDiff_periodic hr.continuous D lam δ₁ δ₂
      (ne_of_gt h3) (ne_of_gt h5)).2.1 σ t
  refine injOn_Ico_of_local_and_farSep (γ := fun t => sweepFam r D lam δ₁ δ₂ σ t)
    hp hε'0 hρ ?_ hper ?_ ?_
  · linarith
  · intro t₁ t₂ hnn heq
    exact hloc lam δ₁ δ₂ h1 hlamL₁ h3 hδ₁L₁ h5 hδ₂L₁ σ hσa hσb t₁ t₂
      (le_trans hnn hε'ε) heq
  · intro t₁ t₂ h₁' h₂' hεle hle
    exact hfar lam δ₁ δ₂ h1 hlamL₂ h3 hδ₁L₂ h5 hδ₂L₂ σ hσa hσb t₁ t₂ h₁' h₂' hεle hle

end Sweep

end Work.Drive
