import Mathlib
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.Interfaces

namespace Work.Drive

/-! # Guidance (H3 lane, from the project lead's `Drive/NOTES_LEAD_hloc_htube_hsurj.md` §3.2(ii)) —
surjective_pUp_of_private

This is the "private-block surjectivity" piece of the corrected `hsurj` counting for the encoded chains
(notes §3.1–§3.2).  `hsurj` as originally posed is FALSE (the level in blocks 1 and 2 is the box
coordinate `x 2`, which no parameter moves), and the fix is: it is enough that blocks 1 and 2 each have
*private* parameter directions (moving that block only) that are onto `ℝ⁴` in the chart.  Then the pair
`((D₀ − D₁) e, (D₀ − D₂) e)` covers `ℝ⁴ × ℝ⁴`, i.e. the stacked 8-vector takes every value.

`Work.Drive.TParity.pUp : Tgt 4 → Tgt 4 → Tgt 8` is the stacking map (defined in
`Submission/Work/Drive/TParity/Basic.lean` as `Work.Drive.pairUp`, with the coordinate lemmas
`pUp_fst8_snd8`, `pUpCLM_apply_fst`, `pUpCLM_apply_snd`; `Tgt m` is `EuclideanSpace ℝ (Fin m)`).

Proof.  Given the two private directions, the whole content is linear algebra:

* from `h₁ (-a)` get `e₁` with `D₀ e₁ = 0`, `D₂ e₁ = 0`, `D₁ e₁ = -a`;
* from `h₂ (-b)` get `e₂` with `D₀ e₂ = 0`, `D₁ e₂ = 0`, `D₂ e₂ = -b`;
* `e := e₁ + e₂` gives `D₀ e - D₁ e = a` and `D₀ e - D₂ e = b`.

Then conclude with `pUp_fst8_snd8`: an arbitrary `w : Tgt 8` is `pUp (fst8 w) (snd8 w)`.

This is used with the derivative identification of `chartDiff3` (`hsurj_sweepChartFam_at`,
`hsurjCentred.lean`) and with `chartAt_fourth_coord_eq_of_snd_eq` (the fourth chart coordinate is the
level) for the `σ` direction.  Keep the statement generic — no `cappingCharted`, no
`projTimesLineCharted`.-/
open scoped Manifold ContDiff in
/-- If `D₁` and `D₂` each have a private direction (killing the other two) hitting all of `ℝ⁴`, then the
stacked pair of differences `((D₀ − D₁) e, (D₀ − D₂) e)` is surjective onto `ℝ⁸`. -/
theorem surjective_pUp_of_private {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D₀ D₁ D₂ : E →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (h₁ : ∀ a, ∃ e, D₀ e = 0 ∧ D₂ e = 0 ∧ D₁ e = a)
    (h₂ : ∀ b, ∃ e, D₀ e = 0 ∧ D₁ e = 0 ∧ D₂ e = b) :
    Function.Surjective (fun e => Work.Drive.TParity.pUp (D₀ e - D₁ e) (D₀ e - D₂ e)) := by
  intro w
  obtain ⟨e₁, h₁₀, h₁₂, h₁₁⟩ := h₁ (-(Work.Drive.TParity.fst8 w))
  obtain ⟨e₂, h₂₀, h₂₁, h₂₂⟩ := h₂ (-(Work.Drive.TParity.snd8 w))
  refine ⟨e₁ + e₂, ?_⟩
  have hD₀ : D₀ (e₁ + e₂) = 0 := by simp [map_add, h₁₀, h₂₀]
  have hD₁ : D₁ (e₁ + e₂) = -(Work.Drive.TParity.fst8 w) := by simp [map_add, h₁₁, h₂₁]
  have hD₂ : D₂ (e₁ + e₂) = -(Work.Drive.TParity.snd8 w) := by simp [map_add, h₁₂, h₂₂]
  show Work.Drive.TParity.pUp (D₀ (e₁ + e₂) - D₁ (e₁ + e₂))
    (D₀ (e₁ + e₂) - D₂ (e₁ + e₂)) = w
  rw [hD₀, hD₁, hD₂, zero_sub, zero_sub, neg_neg, neg_neg,
    Work.Drive.TParity.pUp_fst8_snd8]

end Work.Drive
