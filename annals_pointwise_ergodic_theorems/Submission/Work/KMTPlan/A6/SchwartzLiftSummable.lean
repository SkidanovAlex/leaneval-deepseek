/-
# Absolute summability and `ℓ²`-membership of the lattice lift `n ↦ ψ (n / R) · e(nβ)`

For a Schwartz function `ψ : ℝ → ℂ`, a scale `R > 0` and a point `β` of the circle
`AddCircle 1`, the lifted sequence

  `n ↦ (ψ : ℝ → ℂ) (n / R) * fourier n β`,   `n : ℤ`,

is absolutely summable, and hence belongs to `ℓ²(ℤ)`.  The two ingredients are

* the pointwise identity `‖fourier n β‖ = 1` (the Fourier character takes values in the unit
  circle), so that `‖ψ (n / R) · fourier n β‖ = ‖ψ (n / R)‖`, and
* the absolute summability of the lattice samples `n ↦ ‖ψ (n / R)‖`, which is the sampling
  lemma `Work.KMTAreas.A4.schwartzSamplingSummable` (Schwartz decay `‖ψ x‖ ≤ C / |x| ^ 2`
  against the shifted `p`-series `∑ n, 1 / |n + a| ^ 2`) at shift `a = 0` and step `c = 1 / R`.

The passage `ℓ¹ ↪ ℓ²` on a discrete index type is Mathlib's `Memℓp.of_exponent_ge`: for the
counting measure the `ℓᵖ` norms are monotone decreasing in `p`, so a summable sequence is
square summable.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.schwartzSamplingSummable

namespace Work.KMTPlan.A6

/-- The `n`-th Fourier character of `AddCircle 1`, evaluated at `β`, has modulus one. -/
lemma norm_fourier_apply_one (β : AddCircle (1 : ℝ)) (n : ℤ) : ‖fourier n β‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

/-- The lattice samples `n ↦ ψ (n / R)` of a Schwartz function have summable norms, for every
scale `R > 0`.  This is `Work.KMTAreas.A4.schwartzSamplingSummable` (the arithmetic progression
`a + c n` of samples, `c ≠ 0`) at `a = 0`, `c = 1 / R`. -/
lemma summable_norm_schwartzLift (ψ : SchwartzMap ℝ ℂ) {R : ℝ} (hR : 0 < R) :
    Summable (fun n : ℤ => ‖(ψ : ℝ → ℂ) ((n : ℝ) / R)‖) := by
  have h := Work.KMTAreas.A4.schwartzSamplingSummable ψ (c := 1 / R) (a := 0)
    (by positivity)
  refine h.congr (fun n => ?_)
  have harg : 0 + (1 / R) * (n : ℝ) = (n : ℝ) / R := by ring
  rw [harg]

theorem SchwartzLiftSummable (ψ : SchwartzMap ℝ ℂ) {R : ℝ} (hR : 0 < R)
    (β : AddCircle (1 : ℝ)) :
    Summable (fun n : ℤ => ‖(ψ : ℝ → ℂ) ((n : ℝ) / R) * fourier n β‖) ∧
    Memℓp (fun n : ℤ => (ψ : ℝ → ℂ) ((n : ℝ) / R) * fourier n β) 2 := by
  -- the norms are those of `ψ (n / R)`, since the Fourier character has modulus one
  have h₁ : Summable (fun n : ℤ => ‖(ψ : ℝ → ℂ) ((n : ℝ) / R) * fourier n β‖) :=
    (summable_norm_schwartzLift ψ hR).congr
      (fun n => by rw [norm_mul, norm_fourier_apply_one β n, mul_one])
  -- a summable sequence on `ℤ` is square summable (`ℓ¹ ⊆ ℓ²` for the counting measure)
  refine ⟨h₁, Memℓp.of_exponent_ge (q := 1) (p := 2) ?_ (by norm_num)⟩
  exact memℓp_gen (p := 1) (by simpa using h₁)

end Work.KMTPlan.A6
