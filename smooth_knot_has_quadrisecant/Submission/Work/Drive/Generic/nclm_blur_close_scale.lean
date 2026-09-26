import Mathlib
import Submission.Work.Drive.Generic.nclmBasic
import Submission.Work.Drive.Generic.nclm_blur_close
import Submission.Work.Drive.AB.pinSetup

/-!
# The blurred chord ends and arc are close to the loops of the window,
# with a bound proportional to the square of the retained width

`Work.Drive.Generic.blurArc' r D δ₂ ε` and the `σ`-blurred chord endpoints
`Work.Drive.chordEndA/B r D δ₂ ε` are the `sweepBump`-averages over the sweep window
`[ε - δ₂, ε + δ₂]` of the loops of the window.  This module proves the *scaled* form of
`Work.Drive.Generic.nclm_blur_close`: for every `c > 0` there is a small window `(0, ε₀]` such
that, for every `ε` in it, the blurred objects are within `c * (sweepW' D ε) ^ 2` of the loop at
any parameter `σ ∈ [ε - δ₂, ε + δ₂]`.

The point is that, unlike in `nclm_blur_close`, the tolerance `τ` is *not* fixed in advance: it is
`c * (sweepW' D ε) ^ 2`, which depends on `ε` (and tends to `0` as `ε → 0`).  The bound `Λ` on
`δ₂` may therefore depend on `ε`, which is exactly what the target statement allows.  The proof is
the proof of `nclm_blur_close` with `ε₀ = 1/4` made explicit (so that the smallness of `τ` can be
chosen after `ε`), together with the positivity of the retained width `sweepW' D ε` for
`ε ∈ (0,1)`.
-/

noncomputable section
namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

/-- **The uniform-`ε₀` form of `nclm_blur_close`.**  For a fixed tolerance `τ > 0` there is
`Λ > 0` such that, for every `ε ∈ (0, 1/4]`, every `δ₂ ≤ Λ` with `δ₂ ≤ ε/2` and every parameter
`σ` of the window `[ε - δ₂, ε + δ₂]`, the blurred chord ends and the blurred arc are within `τ`
of the loop at `σ`.

This is `Work.Drive.Generic.nclm_blur_close` with the existential `ε₀` replaced by the explicit
value `1/4` (the value its proof produces), which is what lets the caller choose `τ` after `ε`. -/
theorem nclm_blur_close_quarter {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData}
    (D : Work.Drive.SweepData d) {τ : ℝ} (hτ : 0 < τ) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ (δ₂ ε σ : ℝ), 0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
      0 < ε → ε ≤ 1 / 4 → ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ‖r (Work.Drive.taR D σ) - Work.Drive.chordEndA r D δ₂ ε‖ ≤ τ ∧
      ‖r (Work.Drive.tbR D σ) - Work.Drive.chordEndB r D δ₂ ε‖ ≤ τ ∧
      ‖(r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ))
          - (Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε)‖ ≤ τ ∧
      (∀ ξ : ℝ, ξ ∈ Set.Icc (0 : ℝ) 1 →
        ‖Work.Drive.sweepArc' r D σ ξ - Work.Drive.Generic.blurArc' r D δ₂ ε ξ‖ ≤ τ) := by
  obtain ⟨M, hM0, hLip⟩ := Work.Drive.exists_knot_lipschitz hr
  have hMne : M ≠ 0 := ne_of_gt hM0
  have hη0 : 0 < τ / (2 * M) := by positivity
  have hηM : M * (τ / (2 * M)) = τ / 2 := by field_simp
  obtain ⟨δ, hδ0, hδta, hδtb⟩ := nclm_exists_uc_lifts (d := d) D hη0
  refine ⟨δ / 4, by linarith, ?_⟩
  intro δ₂ ε σ hδ₂0 hδ₂Λ hδ₂ε hε0 hε4 hσlo hσhi
  have h2δ : 2 * δ₂ ≤ δ := by linarith
  have hτhalf : τ / 2 ≤ τ := by linarith
  have hrcont : Continuous r := hr.smooth.continuous
  -- (i) the `a`-endpoint of the chord
  have hA : ‖r (Work.Drive.taR D σ) - Work.Drive.chordEndA r D δ₂ ε‖ ≤ τ / 2 := by
    rw [show Work.Drive.chordEndA r D δ₂ ε
        = nclmBumpVec (fun v : ℝ => r (Work.Drive.taR D (ε - δ₂ * v))) from rfl]
    rw [norm_sub_rev]
    refine nclm_norm_bumpVec_sub_le
      (F := fun v : ℝ => r (Work.Drive.taR D (ε - δ₂ * v)))
      (c := r (Work.Drive.taR D σ)) ?_ ?_
    · exact hrcont.comp ((Work.Drive.arcWin_taR_continuous D).comp (by fun_prop))
    · intro v hv
      obtain ⟨hmv, hmσ, hd⟩ := nclm_window_mem hδ₂0 hδ₂ε hε0 hε4 hσlo hσhi hv
      calc ‖r (Work.Drive.taR D (ε - δ₂ * v)) - r (Work.Drive.taR D σ)‖
          ≤ M * |Work.Drive.taR D (ε - δ₂ * v) - Work.Drive.taR D σ| := hLip _ _
        _ ≤ M * (τ / (2 * M)) :=
            mul_le_mul_of_nonneg_left (hδta _ hmv _ hmσ (le_trans hd h2δ)) hM0.le
        _ = τ / 2 := hηM
  -- (ii) the `b`-endpoint of the chord
  have hB : ‖r (Work.Drive.tbR D σ) - Work.Drive.chordEndB r D δ₂ ε‖ ≤ τ / 2 := by
    rw [show Work.Drive.chordEndB r D δ₂ ε
        = nclmBumpVec (fun v : ℝ => r (Work.Drive.tbR D (ε - δ₂ * v))) from rfl]
    rw [norm_sub_rev]
    refine nclm_norm_bumpVec_sub_le
      (F := fun v : ℝ => r (Work.Drive.tbR D (ε - δ₂ * v)))
      (c := r (Work.Drive.tbR D σ)) ?_ ?_
    · exact hrcont.comp ((Work.Drive.arcWin_tbR_continuous D).comp (by fun_prop))
    · intro v hv
      obtain ⟨hmv, hmσ, hd⟩ := nclm_window_mem hδ₂0 hδ₂ε hε0 hε4 hσlo hσhi hv
      calc ‖r (Work.Drive.tbR D (ε - δ₂ * v)) - r (Work.Drive.tbR D σ)‖
          ≤ M * |Work.Drive.tbR D (ε - δ₂ * v) - Work.Drive.tbR D σ| := hLip _ _
        _ ≤ M * (τ / (2 * M)) :=
            mul_le_mul_of_nonneg_left (hδtb _ hmv _ hmσ (le_trans hd h2δ)) hM0.le
        _ = τ / 2 := hηM
  -- (iii) the chord vector
  have hC : ‖(r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ))
      - (Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε)‖ ≤ τ := by
    have hsplit : (r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ))
        - (Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε)
        = (r (Work.Drive.tbR D σ) - Work.Drive.chordEndB r D δ₂ ε)
          - (r (Work.Drive.taR D σ) - Work.Drive.chordEndA r D δ₂ ε) := by abel
    rw [hsplit]
    calc ‖(r (Work.Drive.tbR D σ) - Work.Drive.chordEndB r D δ₂ ε)
          - (r (Work.Drive.taR D σ) - Work.Drive.chordEndA r D δ₂ ε)‖
        ≤ ‖r (Work.Drive.tbR D σ) - Work.Drive.chordEndB r D δ₂ ε‖
          + ‖r (Work.Drive.taR D σ) - Work.Drive.chordEndA r D δ₂ ε‖ := norm_sub_le _ _
      _ ≤ τ := by linarith
  -- (iv) the retained arc
  have hD : ∀ ξ : ℝ, ξ ∈ Set.Icc (0 : ℝ) 1 →
      ‖Work.Drive.sweepArc' r D σ ξ - Work.Drive.Generic.blurArc' r D δ₂ ε ξ‖ ≤ τ / 2 := by
    intro ξ hξ
    rw [show Work.Drive.Generic.blurArc' r D δ₂ ε ξ
        = nclmBumpVec (fun v : ℝ => Work.Drive.sweepArc' r D (ε - δ₂ * v) ξ) from rfl]
    rw [norm_sub_rev]
    refine nclm_norm_bumpVec_sub_le
      (F := fun v : ℝ => Work.Drive.sweepArc' r D (ε - δ₂ * v) ξ)
      (c := Work.Drive.sweepArc' r D σ ξ) ?_ ?_
    · have h1 : Continuous (fun v : ℝ => nclmArcPt D (ε - δ₂ * v) ξ) :=
        (nclmArcPt_continuous D ξ).comp (by fun_prop)
      have h2 : (fun v : ℝ => Work.Drive.sweepArc' r D (ε - δ₂ * v) ξ)
          = fun v : ℝ => r (nclmArcPt D (ε - δ₂ * v) ξ) := by
        funext v
        exact nclm_arcPt_eq r D (ε - δ₂ * v) ξ
      rw [h2]
      exact hrcont.comp h1
    · intro v hv
      obtain ⟨hmv, hmσ, hd⟩ := nclm_window_mem hδ₂0 hδ₂ε hε0 hε4 hσlo hσhi hv
      have hcl := nclmArcPt_close D hδta hδtb hmv hmσ (le_trans hd h2δ) hξ
      rw [nclm_arcPt_eq r D (ε - δ₂ * v) ξ, nclm_arcPt_eq r D σ ξ]
      calc ‖r (nclmArcPt D (ε - δ₂ * v) ξ) - r (nclmArcPt D σ ξ)‖
          ≤ M * |nclmArcPt D (ε - δ₂ * v) ξ - nclmArcPt D σ ξ| := hLip _ _
        _ ≤ M * (τ / (2 * M)) := mul_le_mul_of_nonneg_left hcl hM0.le
        _ = τ / 2 := hηM
  exact ⟨le_trans hA hτhalf, le_trans hB hτhalf, hC, fun ξ hξ => le_trans (hD ξ hξ) hτhalf⟩

theorem nclm_blur_close_scale {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData}
    (D : Work.Drive.SweepData d) (c : ℝ) (hc : 0 < c) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ Λ : ℝ, 0 < Λ ∧
      ∀ (δ₂ σ : ℝ), 0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 → ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ‖r (Work.Drive.taR D σ) - Work.Drive.chordEndA r D δ₂ ε‖
          ≤ c * (Work.Drive.sweepW' D ε) ^ 2 ∧
      ‖r (Work.Drive.tbR D σ) - Work.Drive.chordEndB r D δ₂ ε‖
          ≤ c * (Work.Drive.sweepW' D ε) ^ 2 ∧
      ‖(r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ))
          - (Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε)‖
          ≤ c * (Work.Drive.sweepW' D ε) ^ 2 ∧
      (∀ ξ : ℝ, ξ ∈ Set.Icc (0 : ℝ) 1 →
        ‖Work.Drive.sweepArc' r D σ ξ - Work.Drive.Generic.blurArc' r D δ₂ ε ξ‖
          ≤ c * (Work.Drive.sweepW' D ε) ^ 2) := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro ε hε0 hε4
  have hW : 0 < Work.Drive.sweepW' D ε :=
    Work.Drive.wds_sweepW'_pos D hε0 (by linarith)
  have hτ : 0 < c * (Work.Drive.sweepW' D ε) ^ 2 := by positivity
  obtain ⟨Λ, hΛ0, hΛ⟩ := nclm_blur_close_quarter hr D hτ
  exact ⟨Λ, hΛ0, fun δ₂ σ hδ₂0 hδ₂Λ hδ₂ε hσlo hσhi =>
    hΛ δ₂ ε σ hδ₂0 hδ₂Λ hδ₂ε hε0 hε4 hσlo hσhi⟩

end Work.Drive.Generic
