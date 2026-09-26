import Mathlib
import Submission.Work.Drive.Generic.nclmDefs

/-!
# The window data at the needle's scale

The estimates of the target `Work.Drive.Generic.needleChartLoop_margin` are uniform over the window
`σ ∈ [ε - δ₂, ε + δ₂]` of sweep parameters with `δ₂ ≤ ε/2`.  This module collects the two
elementary inputs of that uniformity:

* `nclm_window_eps` — for `σ` within a small (depending on `ε`) window of `ε`, the width
  `sweepW' D σ` stays within a factor `2` of `sweepW' D ε`, and the two lifts `taR`, `tbR` move by
  at most `sweepW' D ε / 8`;
* `nclm_acc` — a definite lower bound for `⟪e₀, r''⟫` on every retained arc of the window, for a
  fixed unit `e₀` with `⟪e₀, r'' (taR D 0)⟫ > 0`;
* `nclm_tang` — a definite lower bound for `⟪r', v⟫` on every retained arc of the window, `v` being
  the needle's unit chord direction.
-/

namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

variable {r : ℝ → Space} {d : BandArcData}

/-- **The window data at scale `ε`.**  For `ε ∈ (0,1)` there is `Λ > 0` such that for every
`δ₂ ∈ (0, Λ]` with `δ₂ ≤ ε/2` and every `σ ∈ [ε - δ₂, ε + δ₂]` the retained width is comparable to
`sweepW' D ε` and the two lifts have moved by at most `sweepW' D ε / 8`. -/
theorem nclm_window_eps {d : BandArcData} (D : Work.Drive.SweepData d) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ (δ₂ σ : ℝ), 0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
      ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      (Work.Drive.sweepW' D ε / 2 ≤ Work.Drive.sweepW' D σ) ∧
      (Work.Drive.sweepW' D σ ≤ 2 * Work.Drive.sweepW' D ε) ∧
      |Work.Drive.taR D σ - Work.Drive.taR D ε| ≤ Work.Drive.sweepW' D ε / 8 ∧
      |Work.Drive.tbR D σ - Work.Drive.tbR D ε| ≤ Work.Drive.sweepW' D ε / 8 := by
  have hwε : 0 < Work.Drive.sweepW' D ε := by
    have h : 0 < Work.Drive.sweepW D (⟨ε, ⟨hε0.le, hε1.le⟩⟩ : Set.Icc (0:ℝ) 1) :=
      (Work.Drive.sweepW_pos_lt D _ ⟨hε0, hε1⟩).1
    rw [Work.Drive.sweepW', Work.Drive.taR, Work.Drive.tbR,
      wds_clampI_eq hε0.le hε1.le]
    exact h
  have hhalf : 0 < Work.Drive.sweepW' D ε / 8 := by positivity
  have hta : Continuous (Work.Drive.taR D) := arcWin_taR_continuous D
  have htb : Continuous (Work.Drive.tbR D) := arcWin_tbR_continuous D
  have hw : Continuous (Work.Drive.sweepW' D) := arcWin_sweepW'_continuous D
  obtain ⟨θ₁, hθ₁, hθ₁s⟩ := Metric.continuousAt_iff.mp (hta.continuousAt (x := ε))
    (Work.Drive.sweepW' D ε / 8) hhalf
  obtain ⟨θ₂, hθ₂, hθ₂s⟩ := Metric.continuousAt_iff.mp (htb.continuousAt (x := ε))
    (Work.Drive.sweepW' D ε / 8) hhalf
  obtain ⟨θ₃, hθ₃, hθ₃s⟩ := Metric.continuousAt_iff.mp (hw.continuousAt (x := ε))
    (Work.Drive.sweepW' D ε / 2) (by positivity)
  have hΘpos : 0 < min (min θ₁ θ₂) θ₃ := lt_min (lt_min hθ₁ hθ₂) hθ₃
  refine ⟨min (min θ₁ θ₂) θ₃ / 2, by positivity, ?_⟩
  intro δ₂ σ hδ₂0 hδ₂Λ hδ₂ε hσlo hσhi
  have hσθ : |σ - ε| ≤ min (min θ₁ θ₂) θ₃ / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hσΘ : |σ - ε| < min (min θ₁ θ₂) θ₃ := by linarith
  have hd₁ : dist σ ε < θ₁ := by
    rw [Real.dist_eq]
    exact lt_of_lt_of_le (lt_of_lt_of_le hσΘ (min_le_left _ _)) (min_le_left _ _)
  have hd₂ : dist σ ε < θ₂ := by
    rw [Real.dist_eq]
    exact lt_of_lt_of_le (lt_of_lt_of_le hσΘ (min_le_left _ _)) (min_le_right _ _)
  have hd₃ : dist σ ε < θ₃ := by
    rw [Real.dist_eq]
    exact lt_of_lt_of_le hσΘ (min_le_right _ _)
  have hA := hθ₁s hd₁
  have hB := hθ₂s hd₂
  have hW := hθ₃s hd₃
  rw [Real.dist_eq] at hA hB hW
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := abs_lt.mp hW
    linarith [this.1]
  · have := abs_lt.mp hW
    linarith [this.2]
  · exact le_of_lt hA
  · exact le_of_lt hB

/-- **The retained width is positive on the window.**  (Auxiliary, used to read the retained arc as
`[taR σ, tbR σ]`.) -/
lemma nclm_window_wpos {d : BandArcData} (D : Work.Drive.SweepData d) {δ₂ ε σ : ℝ}
    (hδ₂0 : 0 < δ₂) (hδ₂ε : δ₂ ≤ ε / 2) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hσlo : ε - δ₂ ≤ σ) (hσhi : σ ≤ ε + δ₂) : 0 < Work.Drive.sweepW' D σ := by
  have hσ0 : 0 < σ := by linarith
  have hσ1 : σ < 1 := by linarith
  have h : 0 < Work.Drive.sweepW D (⟨σ, ⟨hσ0.le, hσ1.le⟩⟩ : Set.Icc (0:ℝ) 1) :=
    (Work.Drive.sweepW_pos_lt D _ ⟨hσ0, hσ1⟩).1
  rw [Work.Drive.sweepW', Work.Drive.taR, Work.Drive.tbR, wds_clampI_eq hσ0.le hσ1.le]
  exact h

/-- **The acceleration pairing on the window's arcs.**  For a unit `e₀` whose pairing with the
acceleration at the collapsed end is positive, the pairing stays above half its value on every
retained arc of the window. -/
theorem nclm_acc {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) {e₀ : Space}
    (hκ : 0 < inner ℝ e₀ (deriv (deriv r) (Work.Drive.taR D 0))) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (δ₂ ε σ x : ℝ), 0 < δ₂ → δ₂ ≤ ε / 2 → 0 < ε → ε ≤ ε₀ →
      ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ) →
      inner ℝ e₀ (deriv (deriv r) (Work.Drive.taR D 0)) / 2
        ≤ inner ℝ e₀ (deriv (deriv r) x) := by
  set κ := inner ℝ e₀ (deriv (deriv r) (Work.Drive.taR D 0)) with hκdef
  have hacc_cont : Continuous (fun y : ℝ => inner ℝ e₀ (deriv (deriv r) y)) := by
    have h2 : Continuous (deriv (deriv r)) := by
      have h2' : iteratedDeriv 2 r = deriv (deriv r) := by
        rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
      rw [← h2']
      exact hr.smooth.continuous_iteratedDeriv 2 le_top
    exact continuous_const.inner h2
  obtain ⟨δ, hδ, hspec⟩ := Metric.continuousAt_iff.mp
    (hacc_cont.continuousAt (x := Work.Drive.taR D 0)) (κ / 2) (by linarith)
  obtain ⟨ε₁, hε₁0, hε₁1, hwin⟩ := windowDataSmall hr D (δ / 2) (by positivity)
  refine ⟨min ε₁ (1 / 2), lt_min hε₁0 (by norm_num), min_le_right _ _, ?_⟩
  intro δ₂ ε σ x hδ₂0 hδ₂ε hε0 hεε₀ hσlo hσhi hx
  have hε₁ : ε ≤ ε₁ := le_trans hεε₀ (min_le_left _ _)
  have hεhalf : ε ≤ 1 / 2 := le_trans hεε₀ (min_le_right _ _)
  obtain ⟨harc, -, -⟩ := hwin δ₂ ε hδ₂0 hδ₂ε hε0 hε₁
  have hwpos := nclm_window_wpos D hδ₂0 hδ₂ε hε0 hεhalf hσlo hσhi
  have hwtb : Work.Drive.taR D σ + Work.Drive.sweepW' D σ = Work.Drive.tbR D σ := by
    rw [Work.Drive.sweepW']; ring
  set ξ : ℝ := (x - Work.Drive.taR D σ) / Work.Drive.sweepW' D σ with hξ
  have hξ0 : 0 ≤ ξ := by
    rw [hξ]
    exact div_nonneg (by linarith [hx.1]) hwpos.le
  have hξ1 : ξ ≤ 1 := by
    rw [hξ, div_le_one hwpos]
    linarith [hx.2, hwtb]
  have hxeq : x = Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ := by
    rw [hξ]
    field_simp
    ring
  have hdist := harc σ hσlo hσhi ξ hξ0 hξ1
  rw [← hxeq] at hdist
  have hstep := hspec (by rw [Real.dist_eq]; linarith)
  rw [Real.dist_eq] at hstep
  have hstep' : κ / 2 ≤ inner ℝ e₀ (deriv (deriv r) x) := by
    have := abs_lt.mp hstep
    linarith [this.1]
  exact hstep'

/-- **The tangent pairing on the window's arcs.**  With `v` the needle's unit chord direction, the
pairing `⟪r', v⟫` stays above a quarter of the speed at the collapsed end, on every retained arc of
the window. -/
theorem nclm_tang {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (δ₂ ε σ x : ℝ), 0 < δ₂ → δ₂ ≤ ε / 2 → 0 < ε → ε ≤ ε₀ →
      ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ) →
      ‖velocity r (Work.Drive.taR D 0)‖ / 4 ≤
        inner ℝ (velocity r x)
          (‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖⁻¹ •
            (Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε)) := by
  set m := ‖velocity r (Work.Drive.taR D 0)‖ with hmdef
  have hmpos : 0 < m := norm_pos_iff.mpr (hr.regular _)
  set T : Space := m⁻¹ • velocity r (Work.Drive.taR D 0) with hT
  have hTn : ‖T‖ = 1 := by
    rw [hT, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (ne_of_gt hmpos)]
  -- the velocity is nearly constant on the window's arcs
  have hvelcont : Continuous (velocity r) := by
    have h : Continuous (deriv r) := hr.smooth.continuous_deriv (by simp)
    rw [show velocity r = deriv r from rfl]
    exact h
  obtain ⟨θ, hθ, hspec⟩ := Metric.continuousAt_iff.mp
    (hvelcont.continuousAt (x := Work.Drive.taR D 0)) (m / 4) (by linarith)
  -- the chord direction is `δ`-close to the tangent
  obtain ⟨ε₁, hε₁0, hε₁1, hwin⟩ := windowDataSmall hr D (min (θ / 2) (1 / 8)) (by positivity)
  refine ⟨min ε₁ (1 / 2), lt_min hε₁0 (by norm_num), min_le_right _ _, ?_⟩
  intro δ₂ ε σ x hδ₂0 hδ₂ε hε0 hεε₀ hσlo hσhi hx
  have hε₁ : ε ≤ ε₁ := le_trans hεε₀ (min_le_left _ _)
  have hεhalf : ε ≤ 1 / 2 := le_trans hεε₀ (min_le_right _ _)
  obtain ⟨harc, hchordne, hdir⟩ := hwin δ₂ ε hδ₂0 hδ₂ε hε0 hε₁
  have hwpos := nclm_window_wpos D hδ₂0 hδ₂ε hε0 hεhalf hσlo hσhi
  have hwtb : Work.Drive.taR D σ + Work.Drive.sweepW' D σ = Work.Drive.tbR D σ := by
    rw [Work.Drive.sweepW']; ring
  set ξ : ℝ := (x - Work.Drive.taR D σ) / Work.Drive.sweepW' D σ with hξ
  have hξ0 : 0 ≤ ξ := by
    rw [hξ]
    exact div_nonneg (by linarith [hx.1]) hwpos.le
  have hξ1 : ξ ≤ 1 := by
    rw [hξ, div_le_one hwpos]
    linarith [hx.2, hwtb]
  have hxeq : x = Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ := by
    rw [hξ]; field_simp; ring
  have hdist := harc σ hσlo hσhi ξ hξ0 hξ1
  rw [← hxeq] at hdist
  have hθ' : min (θ / 2) (1 / 8) < θ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hstep := hspec (by rw [Real.dist_eq]; linarith)
  rw [dist_eq_norm] at hstep
  -- `⟪velocity r x, T⟫ ≥ 3 m / 4`
  have hnorm_le : ‖velocity r x‖ ≤ 2 * m := by
    have h1 : |‖velocity r x‖ - m| ≤ ‖velocity r x - velocity r (Work.Drive.taR D 0)‖ := by
      have h2 := abs_norm_sub_norm_le (velocity r x) (velocity r (Work.Drive.taR D 0))
      rwa [show ‖velocity r (Work.Drive.taR D 0)‖ = m from hmdef.symm] at h2
    have h3 : |‖velocity r x‖ - m| < m / 4 := lt_of_le_of_lt h1 hstep
    linarith [abs_lt.mp h3 |>.2]
  have hinnerT : 3 * m / 4 ≤ inner ℝ (velocity r x) T := by
    have hinner : inner ℝ (velocity r x) T
        = inner ℝ (velocity r (Work.Drive.taR D 0)) T
          + inner ℝ (velocity r x - velocity r (Work.Drive.taR D 0)) T := by
      have hab : velocity r (Work.Drive.taR D 0)
          + (velocity r x - velocity r (Work.Drive.taR D 0)) = velocity r x := by abel
      conv_lhs => rw [← hab]
      rw [inner_add_left]
    have h1 : inner ℝ (velocity r (Work.Drive.taR D 0)) T = m := by
      rw [hT, inner_smul_right, real_inner_self_eq_norm_sq, hmdef]
      field_simp
    have h2 : |inner ℝ (velocity r x - velocity r (Work.Drive.taR D 0)) T| < m / 4 := by
      refine lt_of_le_of_lt ?_ hstep
      calc |inner ℝ (velocity r x - velocity r (Work.Drive.taR D 0)) T|
          ≤ ‖velocity r x - velocity r (Work.Drive.taR D 0)‖ * ‖T‖ :=
            abs_real_inner_le_norm _ _
        _ = ‖velocity r x - velocity r (Work.Drive.taR D 0)‖ := by rw [hTn, mul_one]
    rw [hinner, h1]
    linarith [abs_lt.mp h2 |>.1]
  -- transfer from `T` to `v`
  set ℓ := ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ with hℓ
  set v : Space := ℓ⁻¹ • (Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε) with hv
  have hvT : ‖v - T‖ ≤ min (θ / 2) (1 / 8) := hdir
  have hb : |inner ℝ (velocity r x) (v - T)| ≤ 2 * m * (min (θ / 2) (1 / 8)) := by
    calc |inner ℝ (velocity r x) (v - T)| ≤ ‖velocity r x‖ * ‖v - T‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ (2 * m) * (min (θ / 2) (1 / 8)) :=
          mul_le_mul hnorm_le hvT (norm_nonneg _) (by positivity)
  have hb' : |inner ℝ (velocity r x) (v - T)| ≤ m / 4 := by
    refine le_trans hb ?_
    have h1 : 2 * m * min (θ / 2) (1 / 8) ≤ 2 * m * (1 / 8) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    linarith
  have hsplit : inner ℝ (velocity r x) v
      = inner ℝ (velocity r x) T + inner ℝ (velocity r x) (v - T) := by
    rw [inner_sub_right]; ring
  have : m / 4 ≤ inner ℝ (velocity r x) v := by
    rw [hsplit]
    linarith [abs_le.mp hb' |>.1, hinnerT]
  exact this

end Work.Drive.Generic
