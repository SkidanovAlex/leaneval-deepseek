import Mathlib
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Parab.Setup
import Submission.Work.Parab.inversion.exists_mul_log_lt

/-!
# `Work.Pert.Ksub2.anchor_scale_close`

The datum's curve `u ↦ τ₀ (φ₀ u)` of a §4.1 datum is asymptotic to the identity *with a
logarithmic error*: along the negative real axis `w = -M` (which lies in the repelling sector
`QLeft ξ₀`, since `arg (-M + ξ₀) = π`),

`τ₀ (φ₀ (-M)) = (-M) + a log M + b + o(1)   (M → ∞)`.

Since `log M = o(M)` this gives `‖τ₀ (φ₀ (-M)) - (-M)‖ ≤ M / 40` for all large `M`, which is the
"anchor scale" comparison used to place the datum's anchor at depth `≈ M`.

The only input is the two-term asymptotic `ParabData.φ_asymp`; no perturbative machinery is
involved.  The sublinearity of the logarithm is taken in the form already available in the
workspace (`Work.Parab.inversion.exists_mul_log_lt_aux`).
-/

namespace Work.Pert.Ksub2

open Complex

/-- `log = o(id)` in the shape needed here: for every pair of complex constants `a`, `b` the
quantity `1 + ‖a log M + b‖` is eventually bounded by `M / 40`. -/
lemma exists_one_add_norm_clog_le (a b : ℂ) :
    ∃ R : ℝ, 0 < R ∧ ∀ M : ℝ, R ≤ M →
      1 + ‖a * Complex.log (M : ℂ) + b‖ ≤ M / 40 := by
  obtain ⟨R₀, _hR₀pos, hR₀⟩ :=
    Work.Parab.inversion.exists_mul_log_lt_aux (a := ‖a‖) (b := 1 + ‖b‖) (c := 1 / 40)
      (by norm_num)
  refine ⟨max (2 * R₀) 1, by positivity, fun M hM => ?_⟩
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) hM
  have hx : R₀ ≤ M / 2 := by
    have h := le_trans (le_max_left _ _) hM
    linarith
  have h := hR₀ (M / 2) hx
  have h2 : (2 : ℝ) * (M / 2) = M := by ring
  rw [h2] at h
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM1
  have hlog : ‖Complex.log (M : ℂ)‖ = Real.log M := by
    rw [← Complex.ofReal_log (le_of_lt hMpos)]
    simp [abs_of_nonneg (Real.log_nonneg hM1)]
  have hb : ‖a * Complex.log (M : ℂ) + b‖ ≤ ‖a‖ * Real.log M + ‖b‖ := by
    calc ‖a * Complex.log (M : ℂ) + b‖ ≤ ‖a * Complex.log (M : ℂ)‖ + ‖b‖ := norm_add_le _ _
      _ = ‖a‖ * ‖Complex.log (M : ℂ)‖ + ‖b‖ := by rw [norm_mul]
      _ = ‖a‖ * Real.log M + ‖b‖ := by rw [hlog]
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  have h80 : M / 80 ≤ M / 40 := by linarith
  linarith [hb, h]

/-- **Anchor scale.**  The datum's Fatou coordinate `φ₀`, pushed through `τ₀`, keeps the far
negative real axis within a factor `1/40` of itself. -/
theorem anchor_scale_close {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ R : ℝ, 0 < R ∧ ∀ M : ℝ, R ≤ M →
      ‖MandelDim.tau0 (d.φ ((-M : ℝ) : ℂ)) - ((-M : ℝ) : ℂ)‖ ≤ M / 40 := by
  obtain ⟨a, b, hasym⟩ := d.φ_asymp
  obtain ⟨R₁, hR₁⟩ := hasym 1 one_pos
  obtain ⟨R₂, _hR₂pos, hR₂⟩ := exists_one_add_norm_clog_le a b
  refine ⟨max (max R₁ R₂) (max d.ξ₀ 1) + 1, by positivity, fun M hM => ?_⟩
  have hR1 : R₁ < M := by
    have : R₁ ≤ max (max R₁ R₂) (max d.ξ₀ 1) := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  have hR2 : R₂ ≤ M := by
    have : R₂ ≤ max (max R₁ R₂) (max d.ξ₀ 1) := le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  have hξ : d.ξ₀ < M := by
    have : d.ξ₀ ≤ max (max R₁ R₂) (max d.ξ₀ 1) := le_trans (le_max_left _ _) (le_max_right _ _)
    linarith
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) ≤ max (max R₁ R₂) (max d.ξ₀ 1) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM1
  set w : ℂ := ((-M : ℝ) : ℂ) with hw
  -- `w` is a deep point of the repelling sector
  have hwQ : w ∈ MandelDim.QLeft d.ξ₀ := by
    change Real.pi / 3 < |Complex.arg (w + (d.ξ₀ : ℂ))|
    have hsum : w + (d.ξ₀ : ℂ) = ((d.ξ₀ - M : ℝ) : ℂ) := by
      rw [hw]; push_cast; ring
    rw [hsum, Complex.arg_ofReal_of_neg (by linarith : d.ξ₀ - M < 0), abs_of_pos Real.pi_pos]
    linarith [Real.pi_pos]
  have hwnorm : ‖w‖ = M := by
    rw [hw, Complex.ofReal_neg, norm_neg]
    simp [abs_of_nonneg (le_of_lt hMpos)]
  have hasymw := hR₁ w hwQ (by rw [hwnorm]; exact hR1)
  have htri : ‖MandelDim.tau0 (d.φ w) - w‖ ≤ 1 + ‖a * Complex.log (-w) + b‖ := by
    have h1 : MandelDim.tau0 (d.φ w) - w
        = (MandelDim.tau0 (d.φ w) - (w + a * Complex.log (-w) + b)) +
          (a * Complex.log (-w) + b) := by
      ring
    rw [h1]
    have := norm_add_le (MandelDim.tau0 (d.φ w) - (w + a * Complex.log (-w) + b))
      (a * Complex.log (-w) + b)
    linarith [le_of_lt hasymw]
  have hneg : -w = ((M : ℝ) : ℂ) := by
    rw [hw, Complex.ofReal_neg]; ring
  rw [hneg] at htri
  exact le_trans htri (hR₂ M hR2)

end Work.Pert.Ksub2
