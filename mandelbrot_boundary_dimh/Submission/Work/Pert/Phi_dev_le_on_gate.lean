import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.liftF_defect_le_tauC
import Submission.Work.Pert.scale_lattice
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.Fatou
import Submission.Work.Pert.Phi_dev_geom
import Submission.Work.Pert.phi_dev_vert_le

namespace Work.Pert

/-- **Deviation of the pinned perturbed Fatou coordinate from the identity on the upper gate.**

`Φm` is a Fatou coordinate of `F = liftF u σ α` on the gate `Qm Ξ α` and is pinned at `z₀ ≈ -M`
(with `Φm z₀ = -M`).  On the region `-(Ξ+1) ≤ Re z ≤ 2`, `Ξ+3 ≤ Im z` the deviation `Φm z - z`
is bounded by a constant times `1 + log (2+M) + Ξ + log (2 + |Im z|)`.

The proof splits the region at a height `Y` (supplied by `Work.Pert.phi_dev_vert_le`): below it the
region is compact and `Φm - id` is bounded there by continuity; above it the vertical difference
`(Φm z - z) - (Φm (Re z + iY) - (Re z + iY))` is `O (1 + Ξ + log (2 + Im z))` by the Fatou
derivative estimate along the vertical segment. -/
theorem Phi_dev_le_on_gate {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement)
    {Ξ rr M : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z₀ : ℂ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 0 ≤ M)
    (hInF1 : MandelDim.InF1 α) (hα64 : ‖α‖ ≤ 1 / 64)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hNT : ∀ z ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 1 / 32)
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hz₀ : z₀ ∈ Work.Pert.Qm Ξ α) (hz₀re : -(M + 1) ≤ z₀.re) (hz₀re' : z₀.re ≤ -M + 1)
    (hz₀im : |z₀.im| ≤ 1)
    (hpin : Φm z₀ = (((-M : ℝ)) : ℂ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℂ, z ∈ Work.Pert.Qm Ξ α → -(Ξ + 1) ≤ z.re → z.re ≤ 2 →
      Ξ + 3 ≤ z.im →
      ‖Φm z - z‖ ≤ 2 + K * (1 + Real.log (2 + M) + Ξ + Real.log (2 + z.im)) := by
  obtain ⟨Kv, Y, hKv, hY, hvert⟩ :=
    phi_dev_vert_le hF hΞ hrr hInF1 hα64 hQAdm hσ hnorm hu hu2 hτQ hNT hΦm
  obtain ⟨Cb, hbox⟩ := exists_bound_on_targetBox (Ξ := Ξ) (α := α) (Φ := Φm) hΞ Y hQAdm hΦm.1
  -- the reference point of the compact box
  have hCb0 : 0 ≤ Cb := by
    have h := hbox ((0 : ℂ) + ((Ξ + 3 : ℝ) : ℂ) * Complex.I) (by simp; linarith)
      (by simp) (by simp) (by simp; linarith [hY])
    simpa using le_trans (norm_nonneg _) h
  refine ⟨max 1 (2 * (Cb + 2 + Kv)), lt_max_iff.mpr (Or.inl one_pos), ?_⟩
  intro z hz hre1 hre2 him
  set B : ℝ := 1 + Real.log (2 + M) + Ξ + Real.log (2 + z.im) with hBdef
  set X : ℝ := 1 + Ξ + Real.log (2 + z.im) with hXdef
  have hlogM : 0 ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
  have hlogz : 0 ≤ Real.log (2 + z.im) := Real.log_nonneg (by linarith)
  have hB1 : 1 ≤ B := by rw [hBdef]; linarith
  have hBnn : 0 ≤ B := le_trans zero_le_one hB1
  have hBX : X ≤ B := by rw [hBdef, hXdef]; linarith
  have hXnn : 0 ≤ X := by rw [hXdef]; linarith
  have hK1 : 2 * (Cb + 2 + Kv) ≤ max 1 (2 * (Cb + 2 + Kv)) := le_max_right _ _
  have hK2 : (1 : ℝ) ≤ max 1 (2 * (Cb + 2 + Kv)) := le_max_left _ _
  have hCbK : Cb ≤ max 1 (2 * (Cb + 2 + Kv)) := by
    have : Cb ≤ 2 * (Cb + 2 + Kv) := by linarith
    exact le_trans this hK1
  by_cases hle : z.im ≤ Y
  · have h1 : ‖Φm z - z‖ ≤ Cb := hbox z hre1 hre2 him hle
    have h2 : Cb ≤ max 1 (2 * (Cb + 2 + Kv)) * B := by
      calc Cb ≤ max 1 (2 * (Cb + 2 + Kv)) := hCbK
        _ ≤ max 1 (2 * (Cb + 2 + Kv)) * B := le_mul_of_one_le_right (le_trans zero_le_one hK2) hB1
    linarith [h1, h2]
  · have hlt : Y ≤ z.im := le_of_lt (lt_of_not_ge hle)
    have h2 : ‖(Φm z - z)
        - (Φm ((z.re : ℂ) + (Y : ℂ) * Complex.I) - ((z.re : ℂ) + (Y : ℂ) * Complex.I))‖
        ≤ Kv * X := by
      simpa only [hXdef] using hvert z hz hre1 hre2 hlt
    have h3 : ‖Φm ((z.re : ℂ) + (Y : ℂ) * Complex.I) - ((z.re : ℂ) + (Y : ℂ) * Complex.I)‖
        ≤ Cb := by
      refine hbox ((z.re : ℂ) + (Y : ℂ) * Complex.I) ?_ ?_ ?_ ?_
      · simpa using hre1
      · simpa using hre2
      · simpa using hY
      · simp
    have h4 : ‖Φm z - z‖ ≤ Kv * X + Cb := by
      have h6 : Φm z - z
          = ((Φm z - z) - (Φm ((z.re : ℂ) + (Y : ℂ) * Complex.I)
              - ((z.re : ℂ) + (Y : ℂ) * Complex.I)))
            + (Φm ((z.re : ℂ) + (Y : ℂ) * Complex.I)
              - ((z.re : ℂ) + (Y : ℂ) * Complex.I)) := by ring
      rw [h6]
      exact le_trans (norm_add_le _ _) (add_le_add h2 h3)
    have h7 : Kv * X + Cb ≤ max 1 (2 * (Cb + 2 + Kv)) * B := by
      have e1 : Kv * X ≤ (Cb + 2 + Kv) * X :=
        mul_le_mul_of_nonneg_right (by linarith) hXnn
      have e2 : (Cb + 2 + Kv) * X ≤ (Cb + 2 + Kv) * B :=
        mul_le_mul_of_nonneg_left hBX (by linarith)
      have e3 : Cb ≤ Cb * B := le_mul_of_one_le_right hCb0 hB1
      have e4 : Cb * B ≤ (Cb + 2 + Kv) * B :=
        mul_le_mul_of_nonneg_right (by linarith) hBnn
      have e5 : 2 * ((Cb + 2 + Kv) * B) ≤ max 1 (2 * (Cb + 2 + Kv)) * B := by
        have h : (2 * (Cb + 2 + Kv)) * B ≤ max 1 (2 * (Cb + 2 + Kv)) * B :=
          mul_le_mul_of_nonneg_right hK1 hBnn
        calc 2 * ((Cb + 2 + Kv) * B) = (2 * (Cb + 2 + Kv)) * B := by ring
          _ ≤ max 1 (2 * (Cb + 2 + Kv)) * B := h
      have e6 : 0 ≤ (Cb + 2 + Kv) * B := by positivity
      nlinarith [e1, e2, e3, e4, e5]
    linarith [h4, h7]

end Work.Pert
