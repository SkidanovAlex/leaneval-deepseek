import Mathlib
import Submission.Work.Drive.H2.angVelZones

/-!
# The quantitative segment lemmas of the margin pin

Lane H2, the last pin `Work.Drive.ChartLoopMargin`.

The chord and leg zones of the loop are *straight pieces*: the numerator is constant on them
(`Work.Drive.H2.angNum_segment`), so the zone reduces to the sign of an oriented area.  That sign
must be robust against the chart mismatch (the loop is at `σ`, the chart data at the blurred `ε`);
the two lemmas below are the quantitative form of `angNum_segment_pos`, one for each of the two
geometries that occur.  `(v, e)` is the chart frame (both unit, orthogonal).

* `Work.Drive.H2.chordZone_close` — the piece is travelled *backwards along the chord direction*
  (`B - p ≈ -M • v`), the start point lying *below* the centre (`⟪p - c, e⟫ ≤ -Y`, `Y > 0`): the
  **chord zone**.
* `Work.Drive.H2.legZone_close` — the piece is travelled *transversally* (`B - p ≈ s • M • e`,
  `s = ±1`: the two chamfers), the start point having a definite signed chord coordinate
  (`s ⟪p - c, v⟫ ≤ -X`, `X > 0`): the **chamfer zone**.
-/

noncomputable section
namespace Work.Drive.H2

open scoped Real Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The chord zone.** -/
theorem chordZone_close {v e c p B : E} {c₀ M μ Y : ℝ}
    (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (hve : inner ℝ v e = 0)
    (hc₀ : 0 < c₀) (hM : 0 < M) (hY : 0 < Y) (hμ0 : 0 ≤ μ) (hμM : μ ≤ M / 2)
    (hdir : ‖(B - p) + M • v‖ ≤ μ)
    (hpe : inner ℝ (p - c) e ≤ -Y)
    (hsmall : μ * (‖p - c‖ + Y) < Y * (M - μ)) :
    0 < inner ℝ (p - c) e * inner ℝ (c₀ • (B - p)) v
      - inner ℝ (p - c) v * inner ℝ (c₀ • (B - p)) e := by
  set δ : E := (B - p) + M • v with hδ
  have hδnorm : ‖δ‖ ≤ μ := by rw [hδ]; exact hdir
  have hBp : B - p = δ - M • v := by rw [hδ]; abel
  have hTv : inner ℝ (c₀ • (B - p)) v = c₀ * (inner ℝ δ v - M) := by
    rw [hBp, real_inner_smul_left, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      hv, one_pow, mul_one]
  have hTe : inner ℝ (c₀ • (B - p)) e = c₀ * inner ℝ δ e := by
    rw [hBp, real_inner_smul_left, inner_sub_left, real_inner_smul_left, hve, mul_zero, sub_zero]
  rw [hTv, hTe]
  have hδv : |inner ℝ δ v| ≤ μ := by
    have h := abs_real_inner_le_norm δ v
    rw [hv, mul_one] at h
    linarith
  have hδe : |inner ℝ δ e| ≤ μ := by
    have h := abs_real_inner_le_norm δ e
    rw [he, mul_one] at h
    linarith
  have hpv : |inner ℝ (p - c) v| ≤ ‖p - c‖ := by
    have h := abs_real_inner_le_norm (p - c) v
    rwa [hv, mul_one] at h
  obtain ⟨hδv1, hδv2⟩ := abs_le.mp hδv
  obtain ⟨hδe1, hδe2⟩ := abs_le.mp hδe
  obtain ⟨hpv1, hpv2⟩ := abs_le.mp hpv
  have h1 : inner ℝ δ v - M ≤ μ - M := by linarith
  have step1 : Y * (M - μ) ≤ inner ℝ (p - c) e * (inner ℝ δ v - M) := by
    have hneg : inner ℝ δ v - M ≤ 0 := by linarith
    nlinarith [hpe, h1, hY, hM, hμM, hμ0]
  have step2 : -(μ * ‖p - c‖) ≤ -inner ℝ (p - c) v * inner ℝ δ e := by
    nlinarith [hpv1, hpv2, hδe1, hδe2, norm_nonneg (p - c), hμ0]
  have hfinal : 0 < (inner ℝ δ v - M) * inner ℝ (p - c) e - inner ℝ (p - c) v * inner ℝ δ e := by
    have : (inner ℝ δ v - M) * inner ℝ (p - c) e = inner ℝ (p - c) e * (inner ℝ δ v - M) := by
      ring
    nlinarith [step1, step2, hsmall, hY, hM, hμ0, this]
  have hfac : inner ℝ (p - c) e * (c₀ * (inner ℝ δ v - M))
      - inner ℝ (p - c) v * (c₀ * inner ℝ δ e)
      = c₀ * ((inner ℝ δ v - M) * inner ℝ (p - c) e - inner ℝ (p - c) v * inner ℝ δ e) := by
    ring
  rw [hfac]
  exact mul_pos hc₀ hfinal

/-- **The chamfer zone** (both chamfers, uniformly in the sign `s = ±1`). -/
theorem legZone_close {v e c p B : E} {c₀ M μ X : ℝ} {s : ℝ} (hs : s * s = 1)
    (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (hve : inner ℝ v e = 0)
    (hc₀ : 0 < c₀) (hM : 0 < M) (hX : 0 < X) (hμ0 : 0 ≤ μ) (hμM : μ ≤ M / 2)
    (hdir : ‖(B - p) - (s * M) • e‖ ≤ μ)
    (hpv : s * inner ℝ (p - c) v ≤ -X)
    (hsmall : 2 * μ * ‖p - c‖ < X * M) :
    0 < inner ℝ (p - c) e * inner ℝ (c₀ • (B - p)) v
      - inner ℝ (p - c) v * inner ℝ (c₀ • (B - p)) e := by
  set δ : E := (B - p) - (s * M) • e with hδ
  have hδnorm : ‖δ‖ ≤ μ := by rw [hδ]; exact hdir
  have hBp : B - p = δ + (s * M) • e := by rw [hδ]; abel
  have hev : inner ℝ e v = 0 := by rw [real_inner_comm]; exact hve
  have hTv : inner ℝ (c₀ • (B - p)) v = c₀ * inner ℝ δ v := by
    rw [hBp, real_inner_smul_left, inner_add_left, real_inner_smul_left, hev, mul_zero, add_zero]
  have hTe : inner ℝ (c₀ • (B - p)) e = c₀ * (inner ℝ δ e + s * M) := by
    rw [hBp, real_inner_smul_left, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, he]
    ring
  rw [hTv, hTe]
  have hδv : |inner ℝ δ v| ≤ μ := by
    have h := abs_real_inner_le_norm δ v
    rw [hv, mul_one] at h
    linarith
  have hδe : |inner ℝ δ e| ≤ μ := by
    have h := abs_real_inner_le_norm δ e
    rw [he, mul_one] at h
    linarith
  have hpe : |inner ℝ (p - c) e| ≤ ‖p - c‖ := by
    have h := abs_real_inner_le_norm (p - c) e
    rwa [he, mul_one] at h
  obtain ⟨hδv1, hδv2⟩ := abs_le.mp hδv
  obtain ⟨hδe1, hδe2⟩ := abs_le.mp hδe
  obtain ⟨hpe1, hpe2⟩ := abs_le.mp hpe
  -- the leading term
  have hlead : X * M ≤ -s * M * inner ℝ (p - c) v := by
    have := hpv
    nlinarith [hpv, hX, hM]
  -- the two error terms
  have herr1 : -(μ * ‖p - c‖) ≤ inner ℝ (p - c) e * inner ℝ δ v := by
    nlinarith [hpe1, hpe2, hδv1, hδv2, norm_nonneg (p - c), hμ0]
  have herr2 : -(μ * ‖p - c‖) ≤ -inner ℝ (p - c) v * inner ℝ δ e := by
    have hpv' : |inner ℝ (p - c) v| ≤ ‖p - c‖ := by
      have h := abs_real_inner_le_norm (p - c) v
      rwa [hv, mul_one] at h
    obtain ⟨h1, h2⟩ := abs_le.mp hpv'
    nlinarith [h1, h2, hδe1, hδe2, norm_nonneg (p - c), hμ0]
  have hfinal : 0 < inner ℝ (p - c) e * inner ℝ δ v - inner ℝ (p - c) v * (inner ℝ δ e + s * M) := by
    have hsplit : inner ℝ (p - c) e * inner ℝ δ v - inner ℝ (p - c) v * (inner ℝ δ e + s * M)
        = (inner ℝ (p - c) e * inner ℝ δ v - inner ℝ (p - c) v * inner ℝ δ e)
          + (-s * M * inner ℝ (p - c) v) := by ring
    rw [hsplit]
    nlinarith [hlead, herr1, herr2, hsmall]
  have hfac : inner ℝ (p - c) e * (c₀ * inner ℝ δ v)
      - inner ℝ (p - c) v * (c₀ * (inner ℝ δ e + s * M))
      = c₀ * (inner ℝ (p - c) e * inner ℝ δ v
          - inner ℝ (p - c) v * (inner ℝ δ e + s * M)) := by
    ring
  rw [hfac]
  exact mul_pos hc₀ hfinal

end Work.Drive.H2
