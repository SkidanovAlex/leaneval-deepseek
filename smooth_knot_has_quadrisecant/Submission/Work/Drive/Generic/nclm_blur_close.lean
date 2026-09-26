import Mathlib
import Submission.Work.Drive.Generic.nclmBasic
import Submission.Work.Drive.AB.pinSetup

/-!
# The blurred chord ends and arc are uniformly close to the loops of the window

`Work.Drive.Generic.blurArc' r D δ₂ ε` and the `σ`-blurred chord endpoints
`Work.Drive.chordEndA/B r D δ₂ ε` are the `sweepBump`-averages of the loops of the sweep window
`[ε - δ₂, ε + δ₂]`.  This module proves that they are *uniformly* close to the loop at any
parameter `σ` of that window, as long as `ε` stays in a fixed small window `(0, ε₀]` and `δ₂` is
small (`δ₂ ≤ Λ`).

The proof is elementary, and rests on two facts:

* the two lifts `taR`, `tbR` are uniformly continuous on the unit interval `[0,1]` (where all the
  parameters of the window live, once `ε ≤ 1/4`), so the retained arc of the loop at any parameter
  of the window is close, uniformly in the arc fraction `ξ ∈ [0,1]`, to the retained arc at any
  other parameter of the window;
* a `sweepBump`-average of a vector-valued function which is pointwise within `η` of a constant is
  within `η` of it (the bump has total mass `1` and is non-negative).
-/

noncomputable section
namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

section Helpers

variable {r : ℝ → Space} {d : BandArcData}

/-! ## The vector-valued bump average -/

/-- The `sweepBump`-weighted (Bochner) average of a vector-valued function on `[-1,1]`. -/
noncomputable def nclmBumpVec (F : ℝ → Space) : Space := ∫ v in (-1 : ℝ)..1, sweepBump v • F v

lemma nclmBumpVec_const (c : Space) : nclmBumpVec (fun _ : ℝ => c) = c := by
  rw [nclmBumpVec, intervalIntegral.integral_smul_const, Work.Drive.integral_sweepBump, one_smul]

/-- **The bump average is close to any pointwise-close constant.**  If `F` is within `η` of `c` on
the window `[-1,1]`, then its total-mass-`1` bump average is within `η` of `c`. -/
lemma nclm_norm_bumpVec_sub_le {F : ℝ → Space} {c : Space} {η : ℝ}
    (hF : Continuous F) (h : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ‖F v - c‖ ≤ η) :
    ‖nclmBumpVec F - c‖ ≤ η := by
  have hI1 : IntervalIntegrable (fun v : ℝ => sweepBump v • F v) volume (-1) 1 :=
    (Work.Drive.sweepBump_continuous.smul hF).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun v : ℝ => sweepBump v • c) volume (-1) 1 :=
    (Work.Drive.sweepBump_continuous.smul continuous_const).intervalIntegrable _ _
  have hsub : nclmBumpVec F - nclmBumpVec (fun _ : ℝ => c)
      = ∫ v in (-1 : ℝ)..1, sweepBump v • (F v - c) := by
    simp only [nclmBumpVec]
    rw [← intervalIntegral.integral_sub]
    · exact intervalIntegral.integral_congr (fun v _ => by rw [smul_sub])
    · exact hI1
    · exact hI2
  rw [nclmBumpVec_const] at hsub
  rw [hsub]
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1 : ℝ) ≤ 1)) ?_
  have h1 : (∫ v in (-1 : ℝ)..1, ‖sweepBump v • (F v - c)‖)
      = ∫ v in (-1 : ℝ)..1, sweepBump v * ‖F v - c‖ := by
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    rw [norm_smul, Real.norm_of_nonneg (Work.Drive.sweepBump_nonneg v)]
  rw [h1]
  exact bumpAvg_le ((hF.sub continuous_const).norm.continuousOn) h

/-! ## The retained arc as a function of its two parameters -/

/-- The point of the retained arc at sweep parameter `s` and fraction `ξ`, read as a *parameter*
of the knot. -/
noncomputable def nclmArcPt (D : Work.Drive.SweepData d) (s ξ : ℝ) : ℝ :=
  Work.Drive.taR D s + ξ * Work.Drive.sweepW' D s

lemma nclm_arcPt_eq (r : ℝ → Space) (D : Work.Drive.SweepData d) (s ξ : ℝ) :
    Work.Drive.sweepArc' r D s ξ = r (nclmArcPt D s ξ) := rfl

lemma nclmArcPt_continuous (D : Work.Drive.SweepData d) (ξ : ℝ) :
    Continuous (fun s : ℝ => nclmArcPt D s ξ) := by
  rw [show (fun s : ℝ => nclmArcPt D s ξ)
      = (fun s : ℝ => Work.Drive.taR D s + ξ * Work.Drive.sweepW' D s) from rfl]
  exact (Work.Drive.arcWin_taR_continuous D).add
    ((Work.Drive.arcWin_sweepW'_continuous D).const_mul ξ)

/-! ## Uniform continuity of the two lifts on the unit interval -/

/-- **The uniform-continuity data of the two lifts on `[0,1]`**: there is a radius `δ` such that
both lifts move by at most `η` over parameter distances `≤ δ`. -/
lemma nclm_exists_uc_lifts (D : Work.Drive.SweepData d) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |x - y| ≤ δ →
        |Work.Drive.taR D x - Work.Drive.taR D y| ≤ η) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |x - y| ≤ δ →
        |Work.Drive.tbR D x - Work.Drive.tbR D y| ≤ η) := by
  have huca : UniformContinuousOn (Work.Drive.taR D) (Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      (Work.Drive.arcWin_taR_continuous D).continuousOn
  have hucb : UniformContinuousOn (Work.Drive.tbR D) (Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      (Work.Drive.arcWin_tbR_continuous D).continuousOn
  obtain ⟨δa, hδa0, hδa⟩ := Metric.uniformContinuousOn_iff.mp huca η hη
  obtain ⟨δb, hδb0, hδb⟩ := Metric.uniformContinuousOn_iff.mp hucb η hη
  refine ⟨min δa δb / 2, div_pos (lt_min hδa0 hδb0) (by norm_num), ?_, ?_⟩
  · intro x hx y hy hxy
    refine le_of_lt (hδa x hx y hy ?_)
    rw [Real.dist_eq]
    refine lt_of_le_of_lt hxy ?_
    linarith [min_le_left δa δb]
  · intro x hx y hy hxy
    refine le_of_lt (hδb x hx y hy ?_)
    rw [Real.dist_eq]
    refine lt_of_le_of_lt hxy ?_
    linarith [min_le_right δa δb]

/-- **The retained arcs of two parameters of the window move little**: at every arc fraction
`ξ ∈ [0,1]`, the two arc points are within `η` of each other. -/
lemma nclmArcPt_close (D : Work.Drive.SweepData d) {δ η : ℝ}
    (hta : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |x - y| ≤ δ →
      |Work.Drive.taR D x - Work.Drive.taR D y| ≤ η)
    (htb : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |x - y| ≤ δ →
      |Work.Drive.tbR D x - Work.Drive.tbR D y| ≤ η)
    {x y ξ : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hxy : |x - y| ≤ δ) (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) :
    |nclmArcPt D x ξ - nclmArcPt D y ξ| ≤ η := by
  have hA := hta x hx y hy hxy
  have hB := htb x hx y hy hxy
  have hlin : nclmArcPt D x ξ - nclmArcPt D y ξ
      = (1 - ξ) * (Work.Drive.taR D x - Work.Drive.taR D y)
        + ξ * (Work.Drive.tbR D x - Work.Drive.tbR D y) := by
    rw [nclmArcPt, nclmArcPt, Work.Drive.sweepW', Work.Drive.sweepW']
    ring
  rw [hlin]
  have h1 : (1 - ξ) * |Work.Drive.taR D x - Work.Drive.taR D y| ≤ (1 - ξ) * η :=
    mul_le_mul_of_nonneg_left hA (by linarith [hξ.2])
  have h2 : ξ * |Work.Drive.tbR D x - Work.Drive.tbR D y| ≤ ξ * η :=
    mul_le_mul_of_nonneg_left hB hξ.1
  have h3 : |(1 - ξ) * (Work.Drive.taR D x - Work.Drive.taR D y)
        + ξ * (Work.Drive.tbR D x - Work.Drive.tbR D y)|
      ≤ (1 - ξ) * |Work.Drive.taR D x - Work.Drive.taR D y|
        + ξ * |Work.Drive.tbR D x - Work.Drive.tbR D y| := by
    refine le_trans (abs_add_le _ _) (le_of_eq ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hξ.2] : (0 : ℝ) ≤ 1 - ξ),
      abs_of_nonneg hξ.1]
  nlinarith [h3, h1, h2]

/-! ## The window of the blur -/

/-- **The window of the blur stays in the unit interval.**  For `0 < ε ≤ 1/4`, `δ₂ ≤ ε/2` and
`σ ∈ [ε - δ₂, ε + δ₂]`, both `σ` and `ε - δ₂ v` (`v ∈ [-1,1]`) lie in `[0,1]` and are within
`2 δ₂`. -/
lemma nclm_window_mem {ε σ δ₂ v : ℝ} (hδ₂0 : 0 < δ₂) (hδ₂ε : δ₂ ≤ ε / 2)
    (hε0 : 0 < ε) (hε4 : ε ≤ 1 / 4) (hσlo : ε - δ₂ ≤ σ) (hσhi : σ ≤ ε + δ₂)
    (hv : v ∈ Set.Icc (-1 : ℝ) 1) :
    (ε - δ₂ * v) ∈ Set.Icc (0 : ℝ) 1 ∧ σ ∈ Set.Icc (0 : ℝ) 1 ∧
      |(ε - δ₂ * v) - σ| ≤ 2 * δ₂ := by
  obtain ⟨hv1, hv2⟩ := hv
  have hm1 : δ₂ * v ≤ δ₂ := by
    calc δ₂ * v ≤ δ₂ * 1 := mul_le_mul_of_nonneg_left hv2 hδ₂0.le
      _ = δ₂ := by ring
  have hm2 : -δ₂ ≤ δ₂ * v := by
    calc -δ₂ = δ₂ * (-1) := by ring
      _ ≤ δ₂ * v := mul_le_mul_of_nonneg_left hv1 hδ₂0.le
  have hlow : 0 ≤ ε - δ₂ := by linarith
  have hupp : ε + δ₂ ≤ 1 := by linarith
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ?_⟩
  rw [abs_le]
  constructor <;> linarith

end Helpers

theorem nclm_blur_close {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData}
    (D : Work.Drive.SweepData d) (τ : ℝ) (hτ : 0 < τ) :
    ∃ ε₀ Λ : ℝ, 0 < ε₀ ∧ 0 < Λ ∧ ∀ (δ₂ ε σ : ℝ), 0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
      0 < ε → ε ≤ ε₀ → ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
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
  refine ⟨1 / 4, δ / 4, by norm_num, by linarith, ?_⟩
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

end Work.Drive.Generic
