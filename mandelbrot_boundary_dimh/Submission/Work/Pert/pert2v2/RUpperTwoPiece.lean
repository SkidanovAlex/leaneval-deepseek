import Mathlib
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.pert2v2.RCloseTwoPiece
import Submission.Work.Interfaces.Parabolic

/-!
# `Work.Pert.pert2v2.RUpperTwoPiece` — `PertData.R_upper` for the two-piece return map

`PertData.R_upper` reads `Tendsto (fun w => R w - w + 1/rotOf f) upperEnd (𝓝 0)`, i.e.

  `∀ ε > 0, ∃ Y, ∀ w, Y < w.im → ‖R w - w + 1/α‖ < ε`.

For the glued two-piece `R` (`pert2v2.twoPieceR_overlap`) this is again **the transport of the high
chart's window estimate**, and no height split of the *statement* is needed:

* every `w` high up is an integer translate `w = z + n` of a high-chart point `z` (the coverage
  `hcov` of `pert2v2.DR_sub_overlap` / `Work.Pert.waist_cover_pinned_v2`), whose height is unchanged
  (the shift is real);
* the same `n` cancels: `R w - w + 1/α = (R z + n) - (z + n) + 1/α = R z - z + 1/α`, using
  `pert2v2.TEquivOn_add_int` and `R = Rhigh` on `Uhigh`;
* and at `z` the window estimate `‖Rhigh z - z + 1/α‖ < ε` holds, supplied by
  `Work.Pert.RBlock5.retOf_sub_id_tendsto_upper_window` together with the identification
  `retP = retOf` on the waist image and `Pert.pert2v2.high_band_R_close_v2`'s machinery.

Unlike `pert2v2.R_close_twoPiece`, this uses `Tendsto … upperEnd` directly (`upperEnd = comap im
atTop`), so no global `1`-periodicity of `w ↦ R w - w` is needed — which matters, since `R` is only
known on `DR`.
-/

namespace Work.Pert.pert2v2

open MandelDim Complex Set Filter
open scoped Topology

noncomputable section

/-- **`R_upper` for the two-piece return map.**  If every point high up is an integer translate of a
point of the high chart (`hdec`, with the translation index taken from the saturation), `R` agrees
with the high piece there (`hRhigh`), and the high piece is a near-translation at the upper end
(`hwin`), then so is `R`. -/
theorem R_upper_twoPiece {R Rhigh : ℂ → ℂ} {DR Uhigh : Set ℂ} {α : ℂ}
    (hequiv : MandelDim.IsTEquivariantOn R DR)
    (hsub : Uhigh ⊆ DR)
    (hRhigh : ∀ w : ℂ, w ∈ Uhigh → R w = Rhigh w)
    (hdec : ∃ Y : ℝ, ∀ w : ℂ, Y ≤ w.im → ∃ n : ℤ, w - (n : ℂ) ∈ Uhigh)
    (hwin : ∀ ε > 0, ∃ Y : ℝ, ∀ w : ℂ, w ∈ Uhigh → Y < w.im →
      ‖Rhigh w - w + 1 / α‖ < ε) :
    Tendsto (fun w : ℂ => R w - w + 1 / α) MandelDim.upperEnd (𝓝 0) := by
  rw [MandelDim.upperEnd, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨Y₁, hY₁⟩ := hdec
  obtain ⟨Y₂, hY₂⟩ := hwin ε hε
  rw [Filter.eventually_comap, Filter.eventually_atTop]
  refine ⟨max Y₁ (Y₂ + 2), fun b hb x hxb => ?_⟩
  have hbx : b ≤ x.im := le_of_eq hxb.symm
  have hx₁ : Y₁ ≤ x.im := le_trans (le_trans (le_max_left Y₁ (Y₂ + 2)) hb) hbx
  have hx₂ : Y₂ < x.im := by
    have h1 : Y₂ + 2 ≤ x.im := le_trans (le_trans (le_max_right Y₁ (Y₂ + 2)) hb) hbx
    linarith
  obtain ⟨n, hn⟩ := hY₁ x hx₁
  -- `z := x - n` is a high-chart point of the same height, and `x = z + n`
  have hzU : x - (n : ℂ) ∈ Uhigh := hn
  have hxzeq : x = (x - (n : ℂ)) + (n : ℂ) := by ring
  have hzDR : x - (n : ℂ) ∈ DR := hsub hzU
  have hR : R x = R (x - (n : ℂ)) + (n : ℂ) := by
    have h := TEquivOn_add_int hequiv n hzDR
    rwa [show x - (n : ℂ) + (n : ℂ) = x from by ring] at h
  have hident : R x - x + 1 / α = Rhigh (x - (n : ℂ)) - (x - (n : ℂ)) + 1 / α := by
    rw [hR, hRhigh _ hzU]
    ring
  rw [hident]
  have hzim : (x - (n : ℂ)).im = x.im := by simp
  simpa using hY₂ _ hzU (by rw [hzim]; exact hx₂)

end

end Work.Pert.pert2v2
