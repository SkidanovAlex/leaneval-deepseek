import Mathlib
import Submission.Work.Pert.Ksub2.Xcurve_bounds
import Submission.Work.Pert.phi_ne_zero_far
import Submission.Work.Parab.inversion.exists_mul_log_lt
import Submission.Work.Pert.Ksub2.Xc_strip_nhd_bounds

/-!
# `Work.Pert.Ksub2.deriv_phi_strip_lower`

Shishikura (arXiv math/9201282), Appendix A.4, at the *linear* scale: there is a constant `c > 0`
(and a scale `M₀`), depending only on the parabolic datum `d : ParabData f₀ D₀` and on `T`, such
that

`c / M ^ 2 ≤ ‖deriv φ₀ z‖`

for every `M ≥ M₀`, every `u` in the deep strip `Dstrip M T = {-M-1 ≤ Re u ≤ -M, |Im u| ≤ T}` and
every `z ∈ d.Dφ` with `‖z - u‖ ≤ 1/4`.

This is the uniform lower bound on `‖deriv φ₀‖` that the perturbation argument of §4.2 needs on the
neighbourhood of the deep strip (`Ksub2/NOTES.md` §9 item 8, "the explicit lower bound
`cc₀/M² ≤ ‖deriv d.φ z‖`"): the coordinate inverts the Cayley curve `Xc d = τ₀ ∘ φ₀`, whose
derivative is within `1/2` of `1` and whose modulus is `≈ M` on the strip, so

`‖deriv φ₀ z‖ = ‖deriv (Xc d) z‖ / ‖Xc d z‖² ≳ 1/(2 · (3M)²)`.

The two inputs are

* `Work.Pert.Ksub2.Xc_strip_nhd_bounds`: on (the `1/4`-neighbourhood of) the deep strip,
  `‖deriv (Xc d)‖ ≥ 1/2`, `‖Xc d z‖ ≤ 3M` and `φ₀ z ≠ 0`;
* the chain rule `deriv_phi_eq_deriv_Xc` below (with `deriv τ₀ w = 1/w²`), which turns those two
  bounds into a bound for `deriv φ₀`.
-/

namespace Work.Pert.Ksub2

open MandelDim Complex Set Metric

noncomputable section

/-- `deriv τ₀ w = 1 / w ^ 2` for `w ≠ 0` (`τ₀ w = -1/w`). -/
theorem deriv_tau0_one_div (w : ℂ) (hw : w ≠ 0) : deriv MandelDim.tau0 w = 1 / w ^ 2 := by
  have h : MandelDim.tau0 = fun y : ℂ => (-1 : ℂ) * y⁻¹ := by
    funext y; simp [MandelDim.tau0, div_eq_mul_inv]
  rw [h, deriv_const_mul (-1) (differentiableAt_id.inv hw), deriv_inv]
  field_simp

/-- **The chain rule for the Cayley curve.**  `Xc d = τ₀ ∘ φ₀`, and `τ₀` is an involution away
from `0`, so at a point of `Dφ` where `φ₀ ≠ 0` one has `φ₀ = τ₀ ∘ Xc` locally and hence

`deriv φ₀ z = deriv (Xc d) z * (φ₀ z)²`,

because `deriv τ₀ w = 1/w²` and `(1/φ₀ z²) * φ₀ z² = 1`. -/
theorem deriv_phi_eq_deriv_Xc {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {z : ℂ} (hz : z ∈ d.Dφ) (hne : d.φ z ≠ 0) :
    deriv d.φ z = deriv (Work.Pert.Xc d) z * (d.φ z) ^ 2 := by
  have hphi : DifferentiableAt ℂ d.φ z := d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds hz)
  have htau : DifferentiableAt ℂ MandelDim.tau0 (d.φ z) := by
    rw [show MandelDim.tau0 = fun y : ℂ => (-1 : ℂ) * y⁻¹ from rfl]
    exact (differentiableAt_const (-1)).mul (differentiableAt_id.inv hne)
  have hcomp : deriv (fun y : ℂ => MandelDim.tau0 (d.φ y)) z
      = deriv MandelDim.tau0 (d.φ z) * deriv d.φ z := by
    have := deriv_comp (x := z) (h := d.φ) (h₂ := MandelDim.tau0) htau hphi
    simpa [Function.comp_def] using this
  rw [show Work.Pert.Xc d = fun y : ℂ => MandelDim.tau0 (d.φ y) from rfl, hcomp,
    deriv_tau0_one_div (d.φ z) hne]
  field_simp

/-- **The uniform lower bound on `‖deriv φ₀‖` on the deep strip.**  There are `M₀, c > 0`
(depending on `d` and `T`) such that for every `M ≥ M₀`, every `u ∈ Dstrip M T` and every
`z ∈ d.Dφ` at distance `≤ 1/4` from `u`, one has `c / (M * M) ≤ ‖deriv d.φ z‖`. -/
theorem deriv_phi_strip_lower {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) (T : ℝ) :
    ∃ M₀ c : ℝ, 0 < M₀ ∧ 0 < c ∧ ∀ M : ℝ, M₀ ≤ M → ∀ u : ℂ, u ∈ Work.Pert.Dstrip M T →
      ∀ z : ℂ, z ∈ d.Dφ → ‖z - u‖ ≤ 1 / 4 → c / (M * M) ≤ ‖deriv d.φ z‖ := by
  obtain ⟨MXc, _hMXcpos, hXcb⟩ := Work.Pert.Ksub2.Xc_strip_nhd_bounds d T
  refine ⟨max MXc 1, 1 / 64, lt_of_lt_of_le zero_lt_one (le_max_right _ _), by norm_num, ?_⟩
  intro M hM u hu z hzD hzu
  have hMXc : MXc ≤ M := le_trans (le_max_left _ _) hM
  have hM1 : (1 : ℝ) ≤ M := le_trans (le_max_right _ _) hM
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM1
  obtain ⟨hder, hval, hne⟩ := hXcb M hMXc u hu z hzD hzu
  -- the norm of the Cayley curve at `z`, and the resulting lower bound on `‖φ₀ z‖`
  have hXcnorm : ‖Work.Pert.Xc d z‖ = 1 / ‖d.φ z‖ := by
    rw [show Work.Pert.Xc d = fun y : ℂ => MandelDim.tau0 (d.φ y) from rfl]
    show ‖MandelDim.tau0 (d.φ z)‖ = 1 / ‖d.φ z‖
    rw [show MandelDim.tau0 (d.φ z) = (-1 : ℂ) / d.φ z from rfl, norm_div, norm_neg, norm_one]
  have hφnz : ‖d.φ z‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have hφlow : 1 / (3 * M) ≤ ‖d.φ z‖ := by
    have h3M : (0 : ℝ) < 3 * M := by linarith
    have hle : 1 / ‖d.φ z‖ ≤ 3 * M := by rw [← hXcnorm]; exact hval
    rw [div_le_iff₀ h3M]
    have hmul := mul_le_mul_of_nonneg_left hle (norm_nonneg (d.φ z))
    rw [mul_one_div, div_self hφnz] at hmul
    linarith
  -- assemble: `‖φ₀' z‖ = ‖(Xc d)' z‖ · ‖φ₀ z‖²`
  have hsq : (1 / (3 * M)) ^ 2 ≤ ‖d.φ z‖ ^ 2 := pow_le_pow_left₀ (by positivity) hφlow 2
  have hmain : (1 / 2) * (1 / (3 * M)) ^ 2
      ≤ ‖deriv (Work.Pert.Xc d) z‖ * ‖d.φ z‖ ^ 2 :=
    mul_le_mul hder hsq (by positivity) (by positivity)
  rw [deriv_phi_eq_deriv_Xc d hzD hne, norm_mul, norm_pow]
  refine le_trans ?_ hmain
  have hMM : (0 : ℝ) < M * M := mul_pos hMpos hMpos
  rw [div_le_iff₀ hMM]
  have hM0 : M ≠ 0 := ne_of_gt hMpos
  field_simp
  ring_nf
  norm_num

end

end Work.Pert.Ksub2
