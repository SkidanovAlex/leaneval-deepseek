import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Qm_slice
import Submission.Work.Pert.waist_low
import Submission.Work.Pert.pert2v2.waist_threshold
import Submission.Work.Pert.pert2v2.window_cover_dev
import Submission.Work.Interfaces.Fatou

namespace Work.Pert.pert2v2

/-!
# `pert2v2.window_cover_axis`

The window-covering lemma in the form in which the PERT assembly can *supply* its deviation
hypothesis: the deviation of `Φ` from the identity is known **only on the imaginary axis**
(that is what `Work.Pert.pinned_dev_log_v2` gives for the pinned coordinate `ΨE`), not on an
arbitrary disc with radius `≥ R₂` as in `Work.Pert.pert2v2.waist_window_cover_margin`.

The bridge is a mean-value estimate along the **horizontal segment** joining `w` to the axis
point `c = (Im w) · i`:

* `‖w - c‖ = |Re w| < 1`, so if `‖Φ' - 1‖ ≤ 1/2` all along that segment, then
  `‖(Φ w - w) - (Φ c - c)‖ ≤ 1/2 · |Re w| < 1/2`, whence
  `‖Φ w - w‖ ≤ ‖Φ c - c‖ + 1/2 ≤ A log (|Im w| + 2) + C + |Im w|/64 + 1/2`;

* and the segment *does* lie in the region where the derivative hypothesis applies, i.e. every
  point `z` of it satisfies `ball z R₂ ⊆ Qm Ξ α`, provided `|Im w|` exceeds a threshold
  depending only on `Ξ` and `R₂` (see the discussion below).

## Why the segment is admissible, and where `Hthr` has to be large

`Qm ξ α` is the complement of the two closed 45°-cones with apices `b₁ = ξ - 1/α` (opening
left) and `b₂ = -ξ` (opening right).  Along the horizontal segment at height `t = |Im w|`:

* the distance to the `b₂`-cone is `(t - ξ - |Re|)/√2 ≥ (t - ξ - 1)/√2`;
* the distance to the `b₁`-cone is at least `Re z + Re (1/α) - ξ ≥ Ξ + 3` (`QAdm` gives
  `Re (1/α) > 2Ξ + 4` and `|Re z| < 1`).

The second bound can be smaller than `R₂`, but only when `Re (1/α)` itself is bounded: from
`|Im (1/α)| < Re (1/α)` (`InF1`), a small `Re (1/α)` forces a small `|Im (1/α)|`, hence a
*positive* lower bound `|t + Im (1/α)| ≥ t - √2R₂ - Ξ - 1`, and then the two bounds add up:
`(Re z - ξ + Re (1/α)) + |Im z + Im (1/α)| ≥ √2 R₂`.  This is exactly the margin hypothesis of
`Work.Pert.Qm_slice.ball_subset_Qm_of_margin_slice`.  Everything is uniform in `α` once
`|Im w| ≥ Ξ + 2√2 R₂ + 3`.
-/

/-- The lower gate `Qm ξ α` is open (local copy; the versions in the sibling files are
`private`). -/
private lemma isOpen_Qm_axis (ξ : ℝ) (α : ℂ) : IsOpen (Work.Pert.Qm ξ α) := by
  have h1 : IsOpen {z : ℂ | -|(z - ((ξ : ℂ) - 1 / α)).im| < (z - ((ξ : ℂ) - 1 / α)).re} :=
    isOpen_lt (continuous_abs.comp
        (Complex.continuous_im.comp (continuous_id.sub continuous_const))).neg
      (Complex.continuous_re.comp (continuous_id.sub continuous_const))
  have h2 : IsOpen {z : ℂ | (z - (-(ξ : ℂ))).re < |(z - (-(ξ : ℂ))).im|} :=
    isOpen_lt (Complex.continuous_re.comp (continuous_id.sub continuous_const))
      (continuous_abs.comp
        (Complex.continuous_im.comp (continuous_id.sub continuous_const)))
  have h3 : Work.Pert.Qm ξ α =
      {z : ℂ | -|(z - ((ξ : ℂ) - 1 / α)).im| < (z - ((ξ : ℂ) - 1 / α)).re} ∩
        {z : ℂ | (z - (-(ξ : ℂ))).re < |(z - (-(ξ : ℂ))).im|} := by
    ext z
    simp [Work.Pert.Qm, MandelDim.Qreg]
  rw [h3]
  exact h1.inter h2

/-- **The deviation at a window point, from the deviation on the axis.**  For

* `α ∈ 𝓕₁` with the gate admissibility `QAdm (Ξ - 1/α) (-Ξ)` (i.e. `Re (1/α) > 2Ξ + 4`),
* `Φ` differentiable on the lower gate, with `‖Φ' - 1‖ ≤ 1/2` on every disc of radius `≥ R₂`
  inside it,
* `‖Φ (± t i) ∓ ± t i‖ ≤ A log (t + 2) + C + t/64` for all `t ≥ Y₀`,

there is a threshold `Hthr = Hthr (Ξ, A, C, R₂, Y₀) > 0`, independent of `α` and `Φ`, such that
for every `w` with `|Re w| < 1` and `|Im w| ≥ Hthr`

  `‖Φ w - w‖ < |Im w| / 32`.

This is precisely the deviation hypothesis consumed by `pert2v2.window_cover_dev` (and by
`pert2v2.waist_window_cover_margin`). -/
theorem axis_dev_lt {Ξ A C R₂ Y₀ : ℝ} (hΞ : 0 < Ξ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hR₂ : 0 < R₂) (hY₀ : 0 < Y₀) :
    ∃ Hthr : ℝ, 0 < Hthr ∧ ∀ (α : ℂ) (Φ : ℂ → ℂ), MandelDim.InF1 α →
      MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) →
      DifferentiableOn ℂ Φ (Work.Pert.Qm Ξ α) →
      (∀ (z : ℂ) (R : ℝ), R₂ ≤ R → Metric.ball z R ⊆ Work.Pert.Qm Ξ α →
        ‖deriv Φ z - 1‖ ≤ 1 / 2) →
      (∀ t : ℝ, Y₀ ≤ t →
        ‖Φ ((t : ℂ) * Complex.I) - (t : ℂ) * Complex.I‖ ≤ A * Real.log (t + 2) + C + t / 64 ∧
        ‖Φ (-((t : ℂ) * Complex.I)) + (t : ℂ) * Complex.I‖ ≤ A * Real.log (t + 2) + C + t / 64) →
      ∀ w : ℂ, |w.re| < 1 → Hthr ≤ |w.im| → ‖Φ w - w‖ < |w.im| / 32 := by
  -- the threshold: the geometric constant `Ξ + 2√2 R₂ + 3`, plus the `waist_threshold` for
  -- `C + 1` (which leaves a whole unit of slack, absorbing the `+ 1/2` coming from the
  -- mean-value estimate)
  obtain ⟨H, hHpos, hthr⟩ := waist_threshold (Ξ := Ξ) (A := A) (C := C + 1) hA (by linarith) hR₂
  refine ⟨max H (max (Y₀ + 1) (Ξ + 2 * Real.sqrt 2 * R₂ + 3)), ?_, ?_⟩
  · have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    refine lt_max_iff.mpr (Or.inr (lt_max_iff.mpr (Or.inr ?_)))
    nlinarith [mul_pos hs hR₂]
  intro α Φ hInF1 hQAdm hdiff hder haxis w hwre hwim
  -- ## the threshold consequences
  have hH : H ≤ |w.im| := le_trans (le_max_left _ _) hwim
  have hYt : Y₀ + 1 ≤ |w.im| :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hwim
  have hCt : Ξ + 2 * Real.sqrt 2 * R₂ + 3 ≤ |w.im| :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hwim
  obtain ⟨hgeom, hR2t, hdev⟩ := hthr |w.im| hH
  have hY0t : Y₀ ≤ |w.im| := by linarith
  have h0t : (0 : ℝ) < |w.im| := by linarith
  -- ## `InF1` and `QAdm` in real coordinates
  have hγ : |(1 / α).im| < (1 / α).re := Work.Pert.abs_im_one_div_lt_re_one_div hInF1
  have hγre : 2 * Ξ + 4 < (1 / α).re := by
    have h := hQAdm ((Ξ : ℂ) - 1 / α) (by simp) (-(Ξ : ℂ)) (by simp)
    have h1 : ((Ξ : ℂ) - 1 / α).re = Ξ - (1 / α).re := by simp
    have h2 : (-(Ξ : ℂ)).re = -Ξ := by simp
    rw [h1, h2] at h
    linarith
  -- ## the axis point `c = (Im w) i` and the horizontal segment joining it to `w`
  set c : ℂ := (w.im : ℂ) * Complex.I with hcdef
  have hcre : c.re = 0 := by simp [hcdef]
  have hcim : c.im = w.im := by simp [hcdef]
  have hseg : ∀ z ∈ segment ℝ c w, |z.re| ≤ |w.re| ∧ z.im = w.im := by
    intro z hz
    rw [segment_eq_image ℝ c w] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    have h1 : ((1 - θ) • c + θ • w).re = θ * w.re := by
      simp only [Complex.add_re, Complex.smul_re, hcre, smul_eq_mul, mul_zero, zero_add]
    have h2 : ((1 - θ) • c + θ • w).im = w.im := by
      simp only [Complex.add_im, Complex.smul_im, hcim, smul_eq_mul]
      ring
    refine ⟨?_, h2⟩
    rw [h1, abs_mul, abs_of_nonneg hθ.1]
    nlinarith [hθ.2, abs_nonneg w.re]
  -- ## the segment lies in the region where the derivative hypothesis applies
  have hball : ∀ z ∈ segment ℝ c w, Metric.ball z R₂ ⊆ Work.Pert.Qm Ξ α := by
    intro z hz
    obtain ⟨hzre, hzim⟩ := hseg z hz
    have hzlt : |z.re| < 1 := lt_of_le_of_lt hzre hwre
    have hzre1 : z.re < 1 := (abs_lt.mp hzlt).2
    have hzre2 : -1 < z.re := (abs_lt.mp hzlt).1
    -- membership in the gate
    have hzQ : z ∈ Work.Pert.Qm Ξ α := by
      rw [Work.Pert.Qm_mem_iff]
      refine ⟨?_, ?_⟩
      · have h2 : 0 < z.re + (1 / α).re - Ξ + |z.im + (1 / α).im| := by
          have h3 := abs_nonneg (z.im + (1 / α).im)
          linarith
        linarith
      · have h2 : 1 ≤ |z.im| - Ξ := by
          rw [hzim]
          linarith
        linarith
    -- the margin hypothesis of `ball_subset_Qm_of_margin_slice`
    have hmarg : R₂ * Real.sqrt 2 ≤
        min (z.re - Work.Pert.sliceLo Ξ α z.im) (Work.Pert.sliceHi Ξ z.im - z.re) := by
      have hsliceLo : z.re - Work.Pert.sliceLo Ξ α z.im
          = z.re - Ξ + (1 / α).re + |w.im + (1 / α).im| := by
        simp only [Work.Pert.sliceLo, hzim]
        ring
      have hsliceHi : Work.Pert.sliceHi Ξ z.im - z.re = |w.im| - Ξ - z.re := by
        simp only [Work.Pert.sliceHi, hzim]
      rw [hsliceLo, hsliceHi]
      refine le_min ?_ ?_
      · -- the `b₁`-cone: `(Re z - ξ + Re (1/α)) + |Im w + Im (1/α)| ≥ √2 R₂`
        by_cases hcase : Real.sqrt 2 * R₂ ≤ z.re - Ξ + (1 / α).re
        · have h3 := abs_nonneg (w.im + (1 / α).im)
          linarith
        · -- otherwise `Re (1/α)` is bounded, and `|Im (1/α)| < Re (1/α)` makes
          -- `|Im w + Im (1/α)|` large
          have hcase' : z.re - Ξ + (1 / α).re < Real.sqrt 2 * R₂ := lt_of_not_ge hcase
          have hγsmall : (1 / α).re < Real.sqrt 2 * R₂ + Ξ + 1 := by linarith
          have hImsmall : |(1 / α).im| < Real.sqrt 2 * R₂ + Ξ + 1 := lt_trans hγ hγsmall
          have hbl : Real.sqrt 2 * R₂ + 1 ≤ |w.im + (1 / α).im| := by
            have h5 : w.im + (1 / α).im + -((1 / α).im) = w.im := by ring
            have h4 : |w.im| - |(1 / α).im| ≤ |w.im + (1 / α).im| := by
              calc |w.im| - |(1 / α).im|
                  = |w.im + (1 / α).im + -((1 / α).im)| - |(1 / α).im| := by rw [h5]
                _ ≤ (|w.im + (1 / α).im| + |(1 / α).im|) - |(1 / α).im| := by
                    linarith [abs_add_le (w.im + (1 / α).im) (-((1 / α).im)),
                      abs_neg ((1 / α).im)]
                _ = |w.im + (1 / α).im| := by ring
            linarith
          linarith
      · -- the `b₂`-cone distance
        have h2 : |w.im| - Ξ - 1 ≥ Real.sqrt 2 * R₂ := by linarith
        linarith
    have h := Work.Pert.ball_subset_Qm_of_margin_slice (ξ := Ξ) (α := α) (x := z.re) (t := z.im)
      (r := R₂) (by simpa [Complex.re_add_im] using hzQ) hmarg
    rwa [Complex.re_add_im] at h
  -- ## the mean value estimate along the segment
  have hmvt : ‖(Φ w - w) - (Φ c - c)‖ ≤ (1 / 2) * ‖w - c‖ := by
    refine Convex.norm_image_sub_le_of_norm_deriv_le (f := fun z : ℂ => Φ z - z)
      (s := segment ℝ c w) (x := c) (y := w) (C := 1 / 2) ?_ ?_ (convex_segment c w)
      (left_mem_segment ℝ c w) (right_mem_segment ℝ c w)
    · intro x hx
      have hxQ : x ∈ Work.Pert.Qm Ξ α := hball x hx (Metric.mem_ball_self hR₂)
      exact ((hdiff x hxQ).differentiableAt (isOpen_Qm_axis Ξ α |>.mem_nhds hxQ)).sub
        differentiableAt_id
    · intro x hx
      have hxQ : x ∈ Work.Pert.Qm Ξ α := hball x hx (Metric.mem_ball_self hR₂)
      have hxder : ‖deriv Φ x - 1‖ ≤ 1 / 2 := hder x R₂ le_rfl (hball x hx)
      have hd : DifferentiableAt ℂ Φ x :=
        (hdiff x hxQ).differentiableAt (isOpen_Qm_axis Ξ α |>.mem_nhds hxQ)
      have hderiv : deriv (fun z : ℂ => Φ z - z) x = deriv Φ x - 1 := by
        have hfun : (fun z : ℂ => Φ z - z) = (Φ - id) := by funext z; simp
        rw [hfun, deriv_sub hd differentiableAt_id, deriv_id]
      rw [hderiv]
      exact hxder
  have hwmc : ‖w - c‖ = |w.re| := by
    have hw : w - c = ((w.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hcdef]
    rw [hw]
    exact RCLike.norm_ofReal w.re
  -- ## the deviation at the axis point
  have haxis' : ‖Φ c - c‖ ≤ A * Real.log (|w.im| + 2) + C + |w.im| / 64 := by
    have h := haxis |w.im| hY0t
    by_cases hT : 0 ≤ w.im
    · have htT : |w.im| = w.im := abs_of_nonneg hT
      have hc' : c = ((|w.im| : ℝ) : ℂ) * Complex.I := by rw [hcdef, htT]
      rw [hc']
      exact h.1
    · have hT' : w.im < 0 := lt_of_not_ge hT
      have htT : |w.im| = -w.im := abs_of_neg hT'
      have hc' : c = -(((|w.im| : ℝ) : ℂ) * Complex.I) := by
        rw [hcdef, htT]
        push_cast
        ring
      have hΦ : Φ c - c
          = Φ (-(((|w.im| : ℝ) : ℂ) * Complex.I)) + ((|w.im| : ℝ) : ℂ) * Complex.I := by
        rw [hc']
        ring
      simpa only [hΦ] using h.2
  -- ## assembly
  have htri : ‖Φ w - w‖ ≤ ‖Φ c - c‖ + ‖(Φ w - w) - (Φ c - c)‖ := by
    have hsplit : Φ w - w = (Φ c - c) + ((Φ w - w) - (Φ c - c)) := by ring
    calc ‖Φ w - w‖ = ‖(Φ c - c) + ((Φ w - w) - (Φ c - c))‖ := congrArg norm hsplit
      _ ≤ _ := norm_add_le _ _
  have hfinal : A * Real.log (|w.im| + 2) + C + |w.im| / 64 + 1 / 2 < |w.im| / 32 := by
    have hlog : Real.log (|w.im| + 2) ≤ Real.log (|w.im| + 3) :=
      Real.log_le_log (by linarith [abs_nonneg w.im]) (by linarith)
    have halog : A * Real.log (|w.im| + 2) ≤ A * Real.log (|w.im| + 3) :=
      mul_le_mul_of_nonneg_left hlog hA
    linarith
  have hstrict : (1 / 2) * ‖w - c‖ < 1 / 2 := by
    rw [hwmc]
    linarith
  linarith

theorem window_cover_axis {Ξ A C R₂ Y₀ : ℝ} (hΞ : 0 < Ξ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hR₂ : 0 < R₂) (hY₀ : 0 < Y₀) :
    ∃ Hthr : ℝ, 0 < Hthr ∧ ∀ (α : ℂ) (Φ : ℂ → ℂ), MandelDim.InF1 α →
      MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) →
      MandelDim.QAdm (some (Ξ : ℂ)) (some (-(Ξ : ℂ) + 1 / α)) →
      DifferentiableOn ℂ Φ (Work.Pert.Qm Ξ α) →
      (∀ (z : ℂ) (R : ℝ), R₂ ≤ R → Metric.ball z R ⊆ Work.Pert.Qm Ξ α →
        ‖deriv Φ z - 1‖ ≤ 1 / 2) →
      (∀ t : ℝ, Y₀ ≤ t →
        ‖Φ ((t : ℂ) * Complex.I) - (t : ℂ) * Complex.I‖ ≤ A * Real.log (t + 2) + C + t / 64 ∧
        ‖Φ (-((t : ℂ) * Complex.I)) + (t : ℂ) * Complex.I‖ ≤ A * Real.log (t + 2) + C + t / 64) →
      ∀ w : ℂ, |w.re| < 1 → Hthr ≤ |w.im| →
        ∃ ς ∈ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α, Φ ς = w ∧ |ς.re| + 2 < |ς.im| - Ξ := by
  -- the covering threshold and the deviation threshold, both independent of `α` and `Φ`
  obtain ⟨H₁, hH₁pos, hH₁⟩ := window_cover_dev (Ξ := Ξ) hR₂
  obtain ⟨H₂, hH₂pos, hH₂⟩ := axis_dev_lt hΞ hA hC hR₂ hY₀
  refine ⟨max H₁ H₂, lt_max_iff.mpr (Or.inl hH₁pos), ?_⟩
  intro α Φ hInF1 hQAdm₁ hQAdm₂ hdiff hder haxis w hwre hwim
  have hw₁ : H₁ ≤ |w.im| := le_trans (le_max_left _ _) hwim
  have hw₂ : H₂ ≤ |w.im| := le_trans (le_max_right _ _) hwim
  -- the deviation at `w` is supplied by the mean-value estimate along the horizontal segment
  exact hH₁ α Φ hInF1 hdiff hder w hwre hw₁
    (hH₂ α Φ hInF1 hQAdm₁ hdiff hder haxis w hwre hw₂)

end Work.Pert.pert2v2
