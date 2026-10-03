import Mathlib
import Submission.Work.A3.Defs

/-!
# Boundedness and continuity of the KMT Fourier transform

For `g : ℤ → ℂ` with `∑_x ‖g x‖ < ∞`, the Fourier transform

  `kmtFhat g t = ∑'_x g x · e(-2πi x t)`

is absolutely convergent *uniformly in `t`* (each summand has modulus `‖g x‖`), hence

* `‖kmtFhat g t‖ ≤ ∑'_x ‖g x‖` for every `t` (`kmtFhat_norm_le`), so `kmtFhat g` is bounded;
* `kmtFhat g` is continuous as the uniform limit of its partial sums
  (`continuous_kmtFhat`), by `continuous_tsum`.

This is the standing prerequisite for the `ℓ²`-theory of the analysis operator
`A_half`: everything that follows in Area A4 manipulates `kmtFhat g` on the frequency torus
and needs it to be a bounded continuous function.
-/

set_option autoImplicit false

namespace Work.KMTAreas.A4

open scoped BigOperators

noncomputable section

/-- The `x`-th summand of the KMT Fourier transform, as a function of the frequency `t`. -/
private def kmtTerm (g : ℤ → ℂ) (x : ℤ) (t : ℝ) : ℂ :=
  g x * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℝ) * t)))

private lemma kmtTerm_apply (g : ℤ → ℂ) (x : ℤ) (t : ℝ) :
    kmtTerm g x t = g x * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℝ) * t))) := rfl

private lemma kmtFhat_eq_tsum (g : ℤ → ℂ) (t : ℝ) :
    Work.A3.kmtFhat g t = ∑' x : ℤ, kmtTerm g x t := rfl

/-- Each summand of the KMT Fourier transform is a continuous function of the frequency. -/
private lemma continuous_kmtTerm (g : ℤ → ℂ) (x : ℤ) : Continuous (kmtTerm g x) := by
  rw [show kmtTerm g x = fun t : ℝ =>
      g x * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℝ) * t))) from rfl]
  continuity

/-- The modulus of the `x`-th summand is `‖g x‖`, independently of the frequency: the character
`e(-2πi x t)` has modulus one. -/
private lemma norm_kmtTerm (g : ℤ → ℂ) (x : ℤ) (t : ℝ) : ‖kmtTerm g x t‖ = ‖g x‖ := by
  rw [kmtTerm_apply, norm_mul, Complex.norm_exp]
  simp

/-- The KMT Fourier transform is dominated, pointwise in the frequency, by the `ℓ¹` norm of `g`. -/
private lemma kmtFhat_norm_le (g : ℤ → ℂ) (hg : Summable fun x : ℤ => ‖g x‖) (t : ℝ) :
    ‖Work.A3.kmtFhat g t‖ ≤ ∑' x : ℤ, ‖g x‖ := by
  rw [kmtFhat_eq_tsum]
  calc ‖∑' x : ℤ, kmtTerm g x t‖
      ≤ ∑' x : ℤ, ‖kmtTerm g x t‖ :=
        norm_tsum_le_tsum_norm (hg.congr fun x => (norm_kmtTerm g x t).symm)
    _ = ∑' x : ℤ, ‖g x‖ := tsum_congr fun x => norm_kmtTerm g x t

/-- The KMT Fourier transform of an `ℓ¹` function is continuous; it is the uniformly convergent
series of the continuous summands `kmtTerm g x`, with the frequency-independent dominating
sequence `x ↦ ‖g x‖`. -/
private lemma continuous_kmtFhat (g : ℤ → ℂ) (hg : Summable fun x : ℤ => ‖g x‖) :
    Continuous fun t : ℝ => Work.A3.kmtFhat g t := by
  have h : Continuous fun t : ℝ => ∑' x : ℤ, kmtTerm g x t :=
    continuous_tsum (fun x => continuous_kmtTerm g x) hg
      (fun x t => le_of_eq (norm_kmtTerm g x t))
  rw [show (fun t : ℝ => Work.A3.kmtFhat g t) = fun t : ℝ => ∑' x : ℤ, kmtTerm g x t from rfl]
  exact h

theorem kmtFhatBounded (g : ℤ → ℂ) (hg : Summable fun x : ℤ => ‖g x‖) :
    (∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖Work.A3.kmtFhat g t‖ ≤ C) ∧
    Continuous (fun t : ℝ => Work.A3.kmtFhat g t) := by
  have hnn : 0 ≤ ∑' x : ℤ, ‖g x‖ := tsum_nonneg fun x => norm_nonneg (g x)
  exact ⟨⟨(∑' x : ℤ, ‖g x‖) + 1, by linarith,
      fun t => le_trans (kmtFhat_norm_le g hg t) (by linarith)⟩,
    continuous_kmtFhat g hg⟩

end

end Work.KMTAreas.A4
