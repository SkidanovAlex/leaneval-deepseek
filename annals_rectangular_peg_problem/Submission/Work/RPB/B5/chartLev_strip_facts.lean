import Mathlib
import Submission.Work.RPB.B5.chartLev_inverse
import Submission.Work.RPB.B5.chart_C12
import Submission.Work.RPB.B5.slabDerivBounds
import Submission.Work.RPB.B5.C12.slabGlobalExtendPeriodic_C12
import Submission.Work.RPB.B5.slabExtendPeriodic
import Submission.Work.RPB.B5.halfChordSmooth
import Submission.Work.RPB.B5.chartLev_strip_deriv_bound

/-!
# B5: the two-sided sign structure of `chartLev` on a uniform strip around `ρ = 0`

The level function of the `ρ`-chart of the chord annulus,
`chartLev W τ t ρ = K₀ (W τ t ρ) + 1`, vanishes at `ρ = 0` and has
`∂_ρ chartLev (τ,t,0) = ‖deriv (CI.c τ) t‖² > 0` (`Work.RPB.B5.chartLev_deriv_zero`).  The
point of this file is to turn that pointwise strict positivity of the `ρ`-derivative into the
*uniform* two-sided sign structure of `chartLev` on a strip `(-δ, δ)`: there are `0 < δ < ρ₀`
and `η > 0` with

* `chartLev W τ t ρ < 0` for `ρ ∈ (-δ, 0)`,
* `0 < chartLev W τ t ρ` for `ρ ∈ (0, δ)`,
* `η ≤ chartLev W τ t (δ/2)` and `chartLev W τ t (-(δ/2)) ≤ -η`,

for **every** `τ ∈ [0,1]` and **every** real `t` (no compactness in `t` at this place: the
derivative bound is proved uniformly, using the `2π`-periodicity `hWper` to reduce to a
fundamental period).

## The two ingredients

* `Work.RPB.B5.chartLev_strip_deriv_bound` (delegated, `chartLev_strip_deriv_bound.lean`): there
  are `κ > 0`, `κ ≤ ρ₀` and `δ > 0` with `δ ≤ ∂_ρ chartLev W τ t ρ` for all `τ ∈ [0,1]`, all
  real `t` and all `ρ ∈ (-κ, κ)`.  (This is `chartLev_deriv_zero` + compactness/periodicity in
  `(τ,t)`; it strengthens the plan's `chartLev_deriv_pos_near_check` by giving a uniform lower
  bound, which is what the `η` below needs.)
* `signStrip_of_derivBound`, below: **pure real analysis**.  If a family `F τ t ρ` vanishes at
  `ρ = 0` and has `∂_ρ F ≥ δ > 0` on the strip `(-2d, 2d)`, then `F` has the two-sided sign
  structure on `(-d, d)` with `η := δ d/2`.  This is the mean value theorem
  (`exists_deriv_eq_slope`), applied four times: on `[0,ρ]` for `ρ > 0`, on `[ρ,0]` for `ρ < 0`,
  and on `[0, d/2]`, `[-d/2, 0]` for the two `η`-statements.  The constant `d` plays the role of
  the final `δ`, with the derivative needed only on the doubled strip `(-2d, 2d)`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- **Mean value theorem sign structure.**  A family `F : ℝ → ℝ → ℝ → ℝ` (variables `(τ,t,ρ)`)
which vanishes on the slice `ρ = 0` over `τ ∈ [0,1]` and whose `ρ`-derivative is bounded below by
`δ > 0` on the strip `|ρ| < 2d` (for `τ ∈ [0,1]` and all real `t`) changes sign exactly once,
transversally, at `ρ = 0`, with the quantitative estimate `F τ t ρ = ∂_ρ F(τ,t,c) ρ` for a
suitable intermediate `c`.

The conclusion is stated in the form needed by `chartLev_strip_facts`: the sign change on
`(-d, d)` and the two-sided bound `η := δ d/2` at `ρ = ±d/2`. -/
lemma signStrip_of_derivBound {F : ℝ → ℝ → ℝ → ℝ} {ρ₀ d δ : ℝ}
    (hd : 0 < d) (hdρ : d ≤ ρ₀) (hδ : 0 < δ)
    (h0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, F τ t 0 = 0)
    (hcont : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ContinuousOn (fun ρ : ℝ => F τ t ρ) (Set.Ioo (-ρ₀) ρ₀))
    (hdiff : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      DifferentiableOn ℝ (fun ρ : ℝ => F τ t ρ) (Set.Ioo (-ρ₀) ρ₀))
    (hbound : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ ρ ∈ Set.Ioo (-(2 * d)) (2 * d),
      δ ≤ deriv (fun ρ : ℝ => F τ t ρ) ρ) :
    ∃ η : ℝ, 0 < η ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      (∀ ρ ∈ Set.Ioo (-d) 0, F τ t ρ < 0) ∧
      (∀ ρ ∈ Set.Ioo (0 : ℝ) d, 0 < F τ t ρ) ∧
      η ≤ F τ t (d / 2) ∧ F τ t (-(d / 2)) ≤ -η := by
  have hρ₀ : 0 < ρ₀ := lt_of_lt_of_le hd hdρ
  refine ⟨δ * (d / 2), by positivity, ?_⟩
  intro τ hτ t
  -- the intervals used below all sit inside the open strip `(-ρ₀, ρ₀)`
  have hsub_pos : ∀ ρ ∈ Set.Ioo (0 : ℝ) d, Set.Icc (0 : ℝ) ρ ⊆ Set.Ioo (-ρ₀) ρ₀ := by
    intro ρ hρ x hx
    rw [Set.mem_Icc] at hx
    rw [Set.mem_Ioo]
    exact ⟨by linarith [hx.1, hρ₀], by linarith [hx.2, hρ.2, hdρ]⟩
  have hsub_neg : ∀ ρ ∈ Set.Ioo (-d) (0 : ℝ), Set.Icc ρ (0 : ℝ) ⊆ Set.Ioo (-ρ₀) ρ₀ := by
    intro ρ hρ x hx
    rw [Set.mem_Icc] at hx
    rw [Set.mem_Ioo]
    exact ⟨by linarith [hx.1, hρ.1, hdρ], by linarith [hx.2, hρ₀]⟩
  -- the single mean value theorem step, with the derivative bound at the intermediate point
  have step : ∀ a b : ℝ, a < b → a ∈ Set.Ioo (-(2 * d)) (2 * d) →
      b ∈ Set.Ioo (-(2 * d)) (2 * d) → Set.Icc a b ⊆ Set.Ioo (-ρ₀) ρ₀ →
      ∃ c ∈ Set.Ioo a b, δ ≤ deriv (fun ρ : ℝ => F τ t ρ) c ∧
        F τ t b - F τ t a = deriv (fun ρ : ℝ => F τ t ρ) c * (b - a) := by
    intro a b hab ha hb hsubab
    have hc' : ContinuousOn (fun ρ : ℝ => F τ t ρ) (Set.Icc a b) := (hcont τ hτ t).mono hsubab
    have hd' : DifferentiableOn ℝ (fun ρ : ℝ => F τ t ρ) (Set.Ioo a b) :=
      (hdiff τ hτ t).mono (fun x hx => hsubab ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
    obtain ⟨c, hc, hceq⟩ := exists_deriv_eq_slope (fun ρ : ℝ => F τ t ρ) hab hc' hd'
    have hcm : c ∈ Set.Ioo (-(2 * d)) (2 * d) := ⟨lt_trans ha.1 hc.1, lt_trans hc.2 hb.2⟩
    refine ⟨c, hc, hbound τ hτ t c hcm, ?_⟩
    rw [hceq, div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_gt hab))]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `F < 0` on `(-d, 0)`
    intro ρ hρ
    obtain ⟨c, hc, hdc, heq⟩ := step ρ 0 hρ.2 ⟨by linarith [hρ.1], by linarith [hρ.2]⟩
      ⟨by linarith [hd], by linarith [hρ.2, hd]⟩ (hsub_neg ρ hρ)
    have hf : F τ t ρ = deriv (fun ρ : ℝ => F τ t ρ) c * ρ := by
      have h2 : F τ t 0 - F τ t ρ = deriv (fun ρ : ℝ => F τ t ρ) c * (0 - ρ) := heq
      rw [h0 τ hτ t] at h2
      linarith
    rw [hf]
    exact mul_neg_of_pos_of_neg (lt_of_lt_of_le hδ hdc) hρ.2
  · -- `F > 0` on `(0, d)`
    intro ρ hρ
    obtain ⟨c, hc, hdc, heq⟩ := step 0 ρ hρ.1 ⟨by linarith [hd], by linarith [hρ.1]⟩
      ⟨by linarith [hρ.1], by linarith [hρ.2, hd]⟩ (hsub_pos ρ hρ)
    have hf : F τ t ρ = deriv (fun ρ : ℝ => F τ t ρ) c * ρ := by
      have h2 : F τ t ρ - F τ t 0 = deriv (fun ρ : ℝ => F τ t ρ) c * (ρ - 0) := heq
      rw [h0 τ hτ t] at h2
      linarith
    rw [hf]
    exact mul_pos (lt_of_lt_of_le hδ hdc) hρ.1
  · -- `η ≤ F (d/2)`
    have hd2 : (0 : ℝ) < d / 2 := by linarith
    have hd2d : d / 2 ∈ Set.Ioo (0 : ℝ) d := ⟨hd2, by linarith⟩
    obtain ⟨c, hc, hdc, heq⟩ := step 0 (d / 2) hd2 ⟨by linarith [hd], by linarith [hd]⟩
      ⟨by linarith [hd2], by linarith [hd]⟩ (hsub_pos (d / 2) hd2d)
    have hf : F τ t (d / 2) = deriv (fun ρ : ℝ => F τ t ρ) c * (d / 2) := by
      have h2 : F τ t (d / 2) - F τ t 0 = deriv (fun ρ : ℝ => F τ t ρ) c * (d / 2 - 0) := heq
      rw [h0 τ hτ t] at h2
      linarith
    rw [hf]
    exact mul_le_mul_of_nonneg_right hdc hd2.le
  · -- `F (-(d/2)) ≤ -η`
    have hd2 : (0 : ℝ) < d / 2 := by linarith
    have hmem : -(d / 2) ∈ Set.Ioo (-d) (0 : ℝ) := ⟨by linarith, by linarith⟩
    obtain ⟨c, hc, hdc, heq⟩ := step (-(d / 2)) 0 (by linarith)
      ⟨by linarith [hd], by linarith [hd]⟩ ⟨by linarith [hd], by linarith [hd]⟩
      (hsub_neg (-(d / 2)) hmem)
    have hf : F τ t (-(d / 2)) = deriv (fun ρ : ℝ => F τ t ρ) c * (-(d / 2)) := by
      have h2 : F τ t 0 - F τ t (-(d / 2))
          = deriv (fun ρ : ℝ => F τ t ρ) c * (0 - -(d / 2)) := heq
      rw [h0 τ hτ t] at h2
      linarith
    rw [hf]
    nlinarith [hdc, hd2]

/-- **The sign structure from the uniform derivative bound.**  Given the uniform lower bound
`δ ≤ ∂_ρ chartLev` on the strip `(-κ, κ)` (all `τ ∈ [0,1]`, all real `t`), the level function has
the two-sided sign structure with `δ' := κ/2` and `η := δ κ/4`. -/
lemma chartLev_strip_facts_of_deriv_bound (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ρ₀ : ℝ) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (hρ₀ : 0 < ρ₀)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hboundenv : ∃ κ : ℝ, 0 < κ ∧ κ ≤ ρ₀ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ ρ ∈ Set.Ioo (-κ) κ,
        δ ≤ deriv (fun ρ : ℝ => Work.RPB.B5.chartLev W τ t ρ) ρ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ρ₀ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
        (∀ ρ ∈ Set.Ioo (-δ) 0, Work.RPB.B5.chartLev W τ t ρ < 0) ∧
        (∀ ρ ∈ Set.Ioo (0 : ℝ) δ, 0 < Work.RPB.B5.chartLev W τ t ρ) ∧
        η ≤ Work.RPB.B5.chartLev W τ t (δ / 2) ∧
        Work.RPB.B5.chartLev W τ t (-(δ / 2)) ≤ -η := by
  obtain ⟨κ, hκpos, hκρ, δ', hδ'pos, hbound⟩ := hboundenv
  -- the half chord extension of `c`, used only through `chartLev_zero`
  obtain ⟨hc, hc_sm, _, _, _, hc_half⟩ := halfChordSmooth CI.c CI.smooth CI.per
  have hd : (0 : ℝ) < κ / 2 := by linarith
  have hdρ : κ / 2 ≤ ρ₀ := by linarith
  have hbound' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ∀ ρ ∈ Set.Ioo (-(2 * (κ / 2))) (2 * (κ / 2)),
        δ' ≤ deriv (fun ρ : ℝ => Work.RPB.B5.chartLev W τ t ρ) ρ := by
    intro τ hτ t ρ hρ
    have h2 : (2 : ℝ) * (κ / 2) = κ := by ring
    rw [h2] at hρ
    exact hbound τ hτ t ρ hρ
  obtain ⟨η, hηpos, hη⟩ :=
    signStrip_of_derivBound (F := fun τ t ρ => Work.RPB.B5.chartLev W τ t ρ) hd hdρ hδ'pos
      (fun τ hτ t => chartLev_zero hρ₀ hc hc_sm hc_half hWchord τ t
        ((chartLev_slice_contDiffOn_C12 hW τ t hτ).of_le (by norm_num)) hτ)
      (fun τ hτ t => (chartLev_slice_contDiffOn_C12 hW τ t hτ).continuousOn)
      (fun τ hτ t => (chartLev_slice_contDiffOn_C12 hW τ t hτ).differentiableOn (by norm_num))
      hbound'
  exact ⟨κ / 2, by linarith, by linarith, η, hηpos, hη⟩

theorem chartLev_strip_facts (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ρ₀ ε : ℝ) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (hρ₀ : 0 < ρ₀)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ))
    (hε : 0 < ε)
    (hρh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-ε) ε,
      Work.RPB.B5.chartLev W τ t (ρh τ t σ) = -σ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ρ₀ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
        (∀ ρ ∈ Set.Ioo (-δ) 0, Work.RPB.B5.chartLev W τ t ρ < 0) ∧
        (∀ ρ ∈ Set.Ioo (0 : ℝ) δ, 0 < Work.RPB.B5.chartLev W τ t ρ) ∧
        η ≤ Work.RPB.B5.chartLev W τ t (δ / 2) ∧
        Work.RPB.B5.chartLev W τ t (-(δ / 2)) ≤ -η := by
  have hchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r :=
    fun τ hτ t r hr => hWchord τ hτ t r ⟨hr.1, hr.2.le⟩
  obtain ⟨κ, hκpos, hκρ, δ', hδ'pos, hbound⟩ :=
    chartLev_strip_deriv_bound CI a ρ₀ W hρ₀ hW hchord hWper
  exact chartLev_strip_facts_of_deriv_bound CI a ρ₀ W hρ₀ hW hchord
    ⟨κ, hκpos, hκρ, δ', hδ'pos, hbound⟩

end Work.RPB.B5
