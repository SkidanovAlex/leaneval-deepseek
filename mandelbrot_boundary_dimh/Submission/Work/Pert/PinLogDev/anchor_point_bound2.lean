import Mathlib
import Submission.Work.Pert.PinLogDev.AnchorWalk
import Submission.Work.Pert.PinLogDev.PinAux2
import Submission.Work.Pert.PinLogDev.anchor_transport
import Submission.Work.Pert.PinLogDev.walk_clear
import Submission.Work.Pert.PinLogDev.drift_le
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.dev_base_v3

/-!
# `Work.Pert.PinLogDev.anchor_point_bound2`

The pinned anchor-point bound: for a parabolic datum `d`, a gate parameter `Ξ ≥ 1 + 64π`, a
clearance `Rde` and a `C₂` satisfying the derivative estimate `hDE`, there are datum-level
constants `K₁, Ms` such that for every admissible perturbation `(f, u, σ, α, Φ)` at depth `M ≥ Ms`
with the *apex normalisation* `Φ (Xc d (-M)) = -M` and `‖α‖ M ≤ 1/2`, the deviation of `Φ` at the
two anchors `± i Yt` of the axis is bounded by `K₁`, uniformly in `M` and in the perturbation.

Assembly (`X₁, Rd, Bn` come from `walk_clear`, `K, Ms₂` from `drift_le`; `Rd := 2Ξ + 4Rde + 100`):

* `walk_clear` produces the truncated anchor walk `W j = Xc d (-(M-j))` down to depth `X₁`, with
  gate membership, `F0f`-steps, the margins `≥ Rd` and the endpoint bounds `‖W n + (M-n)‖ ≤ Bn`,
  `X₁/2 ≤ -Re (W n)`;
* `drift_le` telescopes `Φ (W n) = -M + n + Σ ε j` and bounds `Σ ‖ε j‖` using `hDE` (via the
  clearance from `walk_clear`) and the model comparison at every walk point, giving
  `‖Φ (W n) - W n‖ ≤ K` with `K` independent of `M`;
* `anchor_transport` then carries this bound to `± i Yt` along the L-shaped path
  `W n → {Re W n} ± i Yt → ± i Yt`, whose clearance hypotheses are discharged from the walk's
  margins and `(1/α).re ≥ √2 M` (`PinAux2.sqrt2_mul_le_re_inv`).
-/

namespace Work.Pert.PinLogDev

open Complex Metric Set

noncomputable section

/-! ## helpers -/

lemma ofReal_neg_cast (M : ℝ) : (((-M : ℝ)) : ℂ) = -(M : ℂ) := by simp

lemma abs_re_add_abs_im_le (z : ℂ) : |z.re| + |z.im| ≤ 2 * ‖z‖ := by
  have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have h2 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  linarith

theorem anchor_point_bound2 {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀)
    (Ξ Rde C₂ Yt : ℝ) (hΞ : 1 + 64 * Real.pi ≤ Ξ) (hRde : 0 < Rde) (hC₂ : 0 ≤ C₂)
    (hYt : Ξ + 4 * (Rde + C₂ + 2) + 10 ≤ Yt)
    (hDE : ∀ (Φ' v : ℂ → ℂ) (z' : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z' R) → Set.InjOn Φ' (Metric.ball z' R) →
      DifferentiableOn ℂ v (Metric.ball z' R) → (∀ z ∈ Metric.ball z' R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z' R, z + v z ∈ Metric.ball z' R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z' - 1 / v z'‖ ≤ C₂ / R)
    {rr : ℝ} (hrr : 0 < rr) (hrrD : Metric.closedBall (0 : ℂ) rr ⊆ D₀) :
    ∃ (K₁ Ms : ℝ), 0 ≤ K₁ ∧ 0 < Ms ∧
      ∀ M : ℝ, Ms ≤ M → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / (1000 * (M + 1)) →
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ) (Φ : ℂ → ℂ),
        MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) rr) δ →
        f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) → α = MandelDim.rotOf f →
        DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        (∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr) →
        MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) →
        ‖α‖ * M ≤ 1 / 2 →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α) →
        MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φ (Work.Pert.Qm Ξ α) →
        Work.Pert.Xc d (((-M : ℝ)) : ℂ) ∈ Work.Pert.Qm Ξ α →
        Φ (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) = (((-M : ℝ)) : ℂ) →
        ‖Φ ((Yt : ℂ) * Complex.I) - (Yt : ℂ) * Complex.I‖ ≤ K₁ ∧
        ‖Φ (-((Yt : ℂ) * Complex.I)) + (Yt : ℂ) * Complex.I‖ ≤ K₁ := by
  obtain ⟨Λt, hΛt0, htrans⟩ := anchor_transport Ξ Rde C₂ hΞ hRde hC₂ hDE
  set Rd : ℝ := 2 * Ξ + 4 * Rde + 100 with hRddef
  have hRdpos : 0 < Rd := by rw [hRddef]; linarith [Real.pi_pos]
  have hsq : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff]; constructor <;> norm_num
  have hΞ0 : 0 ≤ Ξ := by linarith [hΞ, Real.pi_pos]
  have hRd2 : Real.sqrt 2 * (2 + 2 * Rde) + 2 ≤ Rd := by
    rw [hRddef]; nlinarith [hsq, hRde, hΞ0]
  obtain ⟨X₁, Ms₁, Bn, hX₁pos, hMs₁pos, hRdX₁, hMsX₁, hξX₁, hBn0, hwalkC⟩ :=
    walk_clear d Ξ hΞ Rd hRdpos
  obtain ⟨K, Ms₂, hK0, hMs₂pos, hdrift⟩ :=
    drift_le d hd Ξ Rde C₂ rr hΞ hRde hC₂ hrr hrrD hDE hX₁pos hBn0 hRd2
  refine ⟨K + Λt * (2 * (Bn + X₁ + 1) + Yt + 1),
    max (max Ms₁ Ms₂) (max (X₁ + 2)
      ((Ξ + Bn + X₁ + 1 + Real.sqrt 2 * Rde) / Real.sqrt 2 + 1)), ?_, ?_, ?_⟩
  · have hYt0 : 0 ≤ Yt := by linarith [hYt, hΞ, Real.pi_pos]
    have h1 : 0 ≤ 2 * (Bn + X₁ + 1) + Yt + 1 := by linarith [hBn0, hX₁pos, hYt0]
    have h2 : 0 ≤ Λt * (2 * (Bn + X₁ + 1) + Yt + 1) := mul_nonneg hΛt0 h1
    linarith only [hK0, h2]
  · exact lt_of_lt_of_le hMs₁pos (le_trans (le_trans (le_max_left Ms₁ Ms₂)
      (le_max_left (max Ms₁ Ms₂) _)) le_rfl)
  · intro M hM δ hδ hδle f Df u σ α Φ hNearOn hf0 hInF1 hα hDu hu hform hnorm hτQ hQAdm
      hαM hNTL hFatou hmempin hpin
    have hM₁ : Ms₁ ≤ M := le_trans (le_trans (le_max_left Ms₁ Ms₂)
      (le_max_left (max Ms₁ Ms₂) _)) hM
    have hM₂ : Ms₂ ≤ M := le_trans (le_trans (le_max_right Ms₁ Ms₂)
      (le_max_left (max Ms₁ Ms₂) _)) hM
    have hMX₁ : X₁ + 2 ≤ M := le_trans (le_trans (le_max_left (X₁ + 2) _)
      (le_max_right (max Ms₁ Ms₂) _)) hM
    have hMb : (Ξ + Bn + X₁ + 1 + Real.sqrt 2 * Rde) / Real.sqrt 2 + 1 ≤ M :=
      le_trans (le_trans (le_max_right (X₁ + 2) _) (le_max_right (max Ms₁ Ms₂) _)) hM
    have hYt0 : 0 ≤ Yt := by linarith [hYt, hΞ, Real.pi_pos]
    have hInF1' : MandelDim.InF1 α := by rw [hα]; exact hInF1
    have hMpos : 0 < M := lt_of_lt_of_le hMs₁pos hM₁
    obtain ⟨n, hn1, hn2, hmemQ0, hstep0, hdef0, hmargA0, hmargB0, halpha0, hbig0,
      hWnB0, hreX0, hWreΞ0⟩ := hwalkC hInF1' hQAdm hM₁ hαM hmempin
    set W : ℕ → ℂ := fun j => Work.Pert.Xc d (-(((M - (j : ℝ)) : ℝ) : ℂ)) with hWdef
    have hmemQ : ∀ j ≤ n, W j ∈ Work.Pert.Qm Ξ α := fun j hj => by
      simpa only [hWdef] using hmemQ0 j hj
    have hstep : ∀ j < n, Work.Pert.F0f f₀ (W j) = W (j + 1) := by
      intro j hj
      have h := hstep0 j hj
      simp only [hWdef] at h ⊢
      rw [h]; congr 1; push_cast; ring
    have hdef : ∀ j < n, ‖Work.Pert.F0f f₀ (W j) - (W j + 1)‖ ≤ 1 / 32 := fun j hj => by
      simpa only [hWdef] using hdef0 j hj
    have hmargA : ∀ j ≤ n, Rd ≤ Work.Pert.margA Ξ α (W j) := fun j hj => by
      simpa only [hWdef] using hmargA0 j hj
    have hmargB : ∀ j ≤ n, Rd ≤ Work.Pert.margB Ξ α (W j) := fun j hj => by
      simpa only [hWdef] using hmargB0 j hj
    have halpha : ∀ j ≤ n, ‖α‖ * ‖W j‖ ≤ 2 / 3 := fun j hj => by
      simpa only [hWdef] using halpha0 j hj
    have hbig : ∀ j ≤ n, 64 ≤ ‖W j‖ := fun j hj => by
      simpa only [hWdef] using hbig0 j hj
    have hWnB : ‖W n + (((M - (n : ℝ)) : ℝ) : ℂ)‖ ≤ Bn := by
      simpa only [hWdef] using hWnB0
    have hreX : X₁ / 2 ≤ -(W n).re := by simpa only [hWdef] using hreX0
    have hWreΞ : (W n).re < -Ξ := by simpa only [hWdef] using hWreΞ0
    have hW0 : W 0 = Work.Pert.Xc d (-(M : ℂ)) := by
      simp only [hWdef]
      congr 1
      push_cast
      ring
    have hpin2 : Φ (Work.Pert.Xc d (-(M : ℂ))) = -(M : ℂ) := by
      rw [← ofReal_neg_cast M]; exact hpin
    have hdriftW : ‖Φ (W n) - W n‖ ≤ K :=
      hdrift M δ f Df u σ α Φ n W hM₂ hδ hδle hNearOn hf0 hInF1' hα hDu hu hform hnorm
        hτQ hQAdm hαM hNTL hFatou hW0 hpin2 hn1 hn2 hWnB hmemQ hstep hdef halpha hbig
        hmargA hmargB
    -- ### the two constants we need repeatedly
    have hMpos' : 0 < M := hMpos
    have hsq2M : Real.sqrt 2 * M ≤ (1 / α).re :=
      sqrt2_mul_le_re_inv hInF1' hMpos' hαM
    have hnormW : ‖W n‖ ≤ Bn + X₁ + 1 := by
      have h2 : ‖(((M - (n : ℝ)) : ℝ) : ℂ)‖ = M - n := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        linarith [hn1, hX₁pos]
      calc ‖W n‖ = ‖(W n + (((M - (n : ℝ)) : ℝ) : ℂ)) - (((M - (n : ℝ)) : ℝ) : ℂ)‖ := by
            rw [add_sub_cancel_right]
        _ ≤ ‖W n + (((M - (n : ℝ)) : ℝ) : ℂ)‖ + ‖(((M - (n : ℝ)) : ℝ) : ℂ)‖ :=
            norm_sub_le _ _
        _ ≤ Bn + (M - n) := by rw [h2]; exact add_le_add hWnB le_rfl
        _ ≤ Bn + X₁ + 1 := by linarith only [hn2]
    have hre_low : -(Bn + X₁ + 1) ≤ (W n).re := by
      have h2 : |(W n).re| ≤ ‖W n‖ := Complex.abs_re_le_norm _
      linarith only [neg_abs_le (W n).re, h2, hnormW]
    -- the `A`-margin is huge at every point of the L-shaped path
    have hAbig : Real.sqrt 2 * Rde ≤ -(Bn + X₁ + 1) - Ξ + Real.sqrt 2 * M := by
      have h3 : (Ξ + Bn + X₁ + 1 + Real.sqrt 2 * Rde) / Real.sqrt 2 ≤ M - 1 := by
        linarith only [hMb]
      have h4 : Ξ + Bn + X₁ + 1 + Real.sqrt 2 * Rde ≤ Real.sqrt 2 * (M - 1) := by
        have h5 : Real.sqrt 2 * ((Ξ + Bn + X₁ + 1 + Real.sqrt 2 * Rde) / Real.sqrt 2)
            = Ξ + Bn + X₁ + 1 + Real.sqrt 2 * Rde := by
          rw [mul_div_cancel₀ _ (by positivity : Real.sqrt 2 ≠ 0)]
        rw [← h5]
        exact mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg 2)
      have hsqrt0 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      rw [mul_sub, mul_one] at h4
      linarith only [h4, hsqrt0]
    -- the `B`-margin at the endpoint
    have hBb : Real.sqrt 2 * Rde ≤ X₁ / 2 - Ξ := by
      have h1 : 2 * Ξ + 2 * Real.sqrt 2 * Rde ≤ Rd := by
        rw [hRddef]; nlinarith [hsq, hRde]
      linarith only [h1, hRdX₁]
    -- ### the transport
    have hvert : ∀ y ∈ Set.Icc (min (W n).im (-Yt)) (max (W n).im Yt),
        Real.sqrt 2 * Rde ≤ Work.Pert.margA Ξ α ((W n).re + (y : ℂ) * Complex.I) ∧
        Real.sqrt 2 * Rde ≤ Work.Pert.margB Ξ α ((W n).re + (y : ℂ) * Complex.I) := by
      intro y hy
      have hre : ((W n).re + (y : ℂ) * Complex.I).re = (W n).re := by
        simp
      have him : ((W n).re + (y : ℂ) * Complex.I).im = y := by
        simp
      constructor
      · rw [Work.Pert.margA, hre, him]
        have h6 : (0:ℝ) ≤ |y + (1 / α).im| := abs_nonneg _
        linarith only [h6, hre_low, hsq2M, hAbig]
      · rw [Work.Pert.margB, hre, him]
        have h6 : (0:ℝ) ≤ |y| := abs_nonneg _
        linarith only [h6, hreX, hBb]
    have hhor : ∀ x ∈ Set.Icc (W n).re 0,
        Real.sqrt 2 * Rde ≤ Work.Pert.margA Ξ α ((x : ℂ) + (Yt : ℂ) * Complex.I) ∧
        Real.sqrt 2 * Rde ≤ Work.Pert.margB Ξ α ((x : ℂ) + (Yt : ℂ) * Complex.I) ∧
        Real.sqrt 2 * Rde ≤ Work.Pert.margA Ξ α ((x : ℂ) + (-Yt : ℂ) * Complex.I) ∧
        Real.sqrt 2 * Rde ≤ Work.Pert.margB Ξ α ((x : ℂ) + (-Yt : ℂ) * Complex.I) := by
      intro x hx
      have hx1 : (W n).re ≤ x := hx.1
      have hre : ((x : ℂ) + (Yt : ℂ) * Complex.I).re = x := by simp
      have him : ((x : ℂ) + (Yt : ℂ) * Complex.I).im = Yt := by simp
      have hre' : ((x : ℂ) + (-Yt : ℂ) * Complex.I).re = x := by simp
      have him' : ((x : ℂ) + (-Yt : ℂ) * Complex.I).im = -Yt := by simp
      have hB1 : Real.sqrt 2 * Rde ≤ Yt - Ξ := by
        have h2 : Real.sqrt 2 * Rde ≤ 4 * (Rde + C₂ + 2) + 10 := by
          nlinarith [hsq, hRde, hC₂]
        linarith only [h2, hYt]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Work.Pert.margA, hre, him]
        have h6 : (0:ℝ) ≤ |Yt + (1 / α).im| := abs_nonneg _
        linarith only [h6, hx1, hre_low, hsq2M, hAbig]
      · rw [Work.Pert.margB, hre, him, abs_of_nonneg hYt0]
        linarith only [hx.2, hB1]
      · rw [Work.Pert.margA, hre', him']
        have h6 : (0:ℝ) ≤ |-Yt + (1 / α).im| := abs_nonneg _
        linarith only [h6, hx1, hre_low, hsq2M, hAbig]
      · rw [Work.Pert.margB, hre', him', abs_neg, abs_of_nonneg hYt0]
        linarith only [hx.2, hB1]
    have htr := htrans (α := α) (F := Work.Pert.liftF u σ α) (Φ := Φ) (W := W n) (Y₀ := Yt)
      (K := K) hK0 hYt hNTL hFatou (hmemQ n le_rfl) hWreΞ hvert hhor hdriftW
    refine ⟨?_, ?_⟩
    · have h1 : |(W n).re| + |(W n).im| + Yt + 1 ≤ 2 * (Bn + X₁ + 1) + Yt + 1 := by
        have h2 := abs_re_add_abs_im_le (W n)
        linarith only [h2, hnormW]
      have h2 : K + Λt * (|(W n).re| + |(W n).im| + Yt + 1)
          ≤ K + Λt * (2 * (Bn + X₁ + 1) + Yt + 1) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left h1 hΛt0)
      linarith only [htr.1, h2]
    · have h1 : |(W n).re| + |(W n).im| + Yt + 1 ≤ 2 * (Bn + X₁ + 1) + Yt + 1 := by
        have h2 := abs_re_add_abs_im_le (W n)
        linarith only [h2, hnormW]
      have h2 : K + Λt * (|(W n).re| + |(W n).im| + Yt + 1)
          ≤ K + Λt * (2 * (Bn + X₁ + 1) + Yt + 1) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left h1 hΛt0)
      linarith only [htr.2, h2]

end

end Work.Pert.PinLogDev
