import Mathlib
import Submission.Work.Drive.Neutral.StripDiskAux
import Submission.Work.Drive.Neutral.stripTauChart

namespace Work.Drive.Neutral

open Manifold
open scoped Manifold ContDiff Topology

variable {γ : Circle → ℝ × ℝ}

/-- **The divided difference of the plane curve is non-zero on a window of length `≤ π`.**

Strengthening of `Work.Drive.stripSecantW_ne_zero` from `|a - b| < π` to `|a - b| ≤ π`: for `a = b`
the divided difference is the (non-zero) tangent derivative, and for `a ≠ b` it vanishes only if
`curve γ a = curve γ b`, i.e. `a - b ∈ 2π ℤ` with `a ≠ b`, which forces `|a - b| ≥ 2π > π`. -/
lemma stripSecantW_ne_zero_le (hγ : Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {a b : ℝ} (hab : |a - b| ≤ Real.pi) : secantW (curve γ) (a, b) ≠ 0 := by
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (curve γ) :=
    contMDiff_iff_contDiff.mp (hγ.contMDiff.comp (contMDiff_circleExp (m := ∞)))
  intro hzero
  by_cases hab' : a = b
  · subst hab'
    rw [secantW_self] at hzero
    exact curve_deriv_ne_zero γ hγ a hzero
  · have hsub : curve γ a - curve γ b = (a - b) • secantW (curve γ) (a, b) :=
      sub_eq_smul_secantW (hF.of_le (by norm_num)) a b
    rw [hzero, smul_zero, sub_eq_zero] at hsub
    have hinj : Function.Injective γ := hγ.isEmbedding.injective
    have hexp : Circle.exp a = Circle.exp b := hinj hsub
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hexp
    have hmab : a - b = (↑m : ℝ) * (2 * Real.pi) := by linarith [hm]
    have hab2 : |(↑m : ℝ) * (2 * Real.pi)| ≤ Real.pi := by rw [← hmab]; exact hab
    have hab3 : |(↑m : ℝ)| * (2 * Real.pi) ≤ Real.pi := by
      rwa [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at hab2
    have h3 : |(↑m : ℝ)| ≤ 1 / 2 := by nlinarith [Real.pi_pos]
    have h3a : -(1:ℝ) < (↑m : ℝ) := by have := (abs_le.mp h3).1; linarith
    have h3b : (↑m : ℝ) < 1 := by have := (abs_le.mp h3).2; linarith
    have hm0 : m = 0 := by
      have h5 : (-1:ℤ) < m := by rw [← Int.cast_lt (R := ℝ)]; push_cast; exact h3a
      have h6 : m < (1:ℤ) := by rw [← Int.cast_lt (R := ℝ)]; push_cast; exact h3b
      omega
    exact hab' (by rw [hm0] at hm; simpa using hm)

/-- The unit normalisation of a non-zero complex number has modulus one. -/
lemma norm_div_self_norm {z : ℂ} (hz : z ≠ 0) : ‖z / ((‖z‖ : ℝ) : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z)]
  exact div_self (ne_of_gt (norm_pos_iff.mpr hz))

/-- **The divided difference `symmWC` of the symmetric chord family is non-zero for opening
parameters `0 < s ≤ π/2`,** and its unit normalisation has modulus one.

The separation of the two parameters `σ + s` and `σ - s` is `2s ≤ π`, so the (strengthened) secant
non-vanishing lemma applies; the normalisation clause is then formal algebra. -/
theorem symmWC_ne_zero_le (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    (∀ σ s : ℝ, 0 < s → s ≤ Real.pi / 2 → Work.Drive.Neutral.symmWC γ σ s ≠ 0) ∧
      (∀ σ s : ℝ, 0 < s → s ≤ Real.pi / 2 →
        ‖Work.Drive.Neutral.symmWC γ σ s / ((‖Work.Drive.Neutral.symmWC γ σ s‖ : ℝ) : ℂ)‖ = 1) := by
  have hkey : ∀ σ s : ℝ, 0 < s → s ≤ Real.pi / 2 → symmWC γ σ s ≠ 0 := by
    intro σ s hs hsle
    have hdist : |(σ + s) - (σ - s)| ≤ Real.pi := by
      rw [show (σ + s) - (σ - s) = 2 * s from by ring,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * s)]
      linarith
    have hw := stripSecantW_ne_zero_le hγ hdist
    intro h
    exact hw (symmC_eq_zero_iff.mp (by simpa only [symmWC] using h))
  exact ⟨hkey, fun σ s hs hsle => norm_div_self_norm (hkey σ s hs hsle)⟩

end Work.Drive.Neutral
