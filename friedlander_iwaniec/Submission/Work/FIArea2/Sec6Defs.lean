/-
# The vocabulary of the §6 Poisson step (6.7) → (6.9)

The derivation of (6.9) from (6.7), with the class decomposition of §6 and the coset Poisson
summation `poisson_coset_2d`, needs three further objects:

* `gQuartic γ t = t₁⁴ − 2γt₁²t₂² + t₂⁴` — the quartic of (7.1);
* `phiOf f z₁ z₂ t = f(|t₁²z₂ − t₂²z₁|²/|Δ|²)` — the lattice phase (6.7) (`f` is understood in the
  frozen `|w|²`-normalisation, so `f(w) = f(|w|²)`);
* `ft2real φ u₁ u₂ = ∫_{ℝ²}φ(t)e(−u·t)dt` — the Fourier transform at *real* frequencies, which the
  scaling `t_j = s_jτ_j` with `s_j² = |Δ|/|z_{3−j}|` produces (the paper's `u_j = h_j|Δz_j|^{−1/2}`).

The two substitution identities connecting them to the paper's (6.8) are
`phiOf_comp_scaling` (pure algebra) and `ft2real_comp_scaling` (the diagonal change of variables),
and `Fint_eq_ft2real` identifies `Work.FIArea2.Fint` (the paper's `F(u₁,u₂)` of (6.8), with the
`e(+·)` sign) with `ft2real` at the negated frequencies.
-/
import Mathlib
import Submission.Work.FIArea2.FintDefs
import Submission.Work.FIArea2.Poisson2dDefs
import Submission.Work.FIPlan.Interface

set_option autoImplicit false

namespace Work.FIArea2

open scoped BigOperators

noncomputable section

/-- **(7.1)**: the quartic `g(t₁,t₂) = t₁⁴ − 2γt₁²t₂² + t₂⁴`. -/
def gQuartic (γ : ℝ) (t : ℝ × ℝ) : ℝ :=
  t.1 ^ 4 - 2 * γ * t.1 ^ 2 * t.2 ^ 2 + t.2 ^ 4

/-- **(6.7)**: the lattice phase `φ(t) = f(|t₁²z₂ − t₂²z₁|²/|Δ|²)`, written through the real and
imaginary parts of `z₁,z₂` (so that no complex coercion is needed). -/
def phiOf (f : ℝ → ℝ) (z1 z2 : GaussianInt) (t : ℝ × ℝ) : ℝ :=
  f (((t.1 ^ 2 * (z2.re : ℝ) - t.2 ^ 2 * (z1.re : ℝ)) ^ 2
      + (t.1 ^ 2 * (z2.im : ℝ) - t.2 ^ 2 * (z1.im : ℝ)) ^ 2)
    / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ^ 2)

/-- The two-dimensional Fourier transform at real frequencies,
`𝓕φ(u₁,u₂) = ∫_{ℝ²}φ(t)e(−u·t)dt`, `e(x) = exp(2πix)`. -/
def ft2real (φ : ℝ × ℝ → ℂ) (u₁ u₂ : ℝ) : ℂ :=
  ∫ t : ℝ × ℝ, φ t *
    Complex.exp (-(2 * Real.pi * Complex.I) * (u₁ * t.1 + u₂ * t.2))

open Work.FIPlan in
/-- The first scaling of §6: `s₁ = √(|Δ|/|z₂|)`. -/
def secScale₁ (z1 z2 : GaussianInt) : ℝ :=
  Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
    / Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)))

open Work.FIPlan in
/-- The second scaling of §6: `s₂ = √(|Δ|/|z₁|)`. -/
def secScale₂ (z1 z2 : GaussianInt) : ℝ :=
  Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
    / Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ)))

open Work.FIPlan in
/-- The cosine `γ = Re(z̄₁z₂)/|z₁z₂|` of (7.1). -/
def gamOf (z1 z2 : GaussianInt) : ℝ :=
  (((star z1 * z2).re : ℤ) : ℝ)
    / Real.sqrt ((((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))))

/-- The paper's `F(u₁,u₂)` of (6.8) is the Fourier transform with the other sign:
`Fint f γ (−u₁) (−u₂) = 𝓕(f ∘ g)(u₁,u₂)`. -/
theorem Fint_eq_ft2real (f : ℝ → ℝ) (γ u₁ u₂ : ℝ) :
    Fint f γ (-u₁) (-u₂) = ft2real (fun t : ℝ × ℝ => ((f (gQuartic γ t) : ℝ) : ℂ)) u₁ u₂ := by
  unfold Fint ft2real gQuartic
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  congr 1
  congr 1
  push_cast
  ring

/-- Splitting the coset phase: `ft2coset φ m γ h = e(h·γ/m)·𝓕φ(h₁/m, h₂/m)`. -/
theorem ft2coset_eq_exp_mul_ft2real (φ : ℝ × ℝ → ℂ) (m : ℕ) (γ h : ℤ × ℤ) :
    ft2coset φ m γ h
      = Complex.exp (2 * Real.pi * Complex.I
          * (((h.1 : ℝ) * (γ.1 : ℝ) + (h.2 : ℝ) * (γ.2 : ℝ)) / (m : ℝ)))
        * ft2real φ ((h.1 : ℝ) / (m : ℝ)) ((h.2 : ℝ) / (m : ℝ)) := by
  unfold ft2coset ft2real
  have hcongr : ∀ t : ℝ × ℝ, φ t * Complex.exp (-(2 * Real.pi * Complex.I)
        * (((h.1 : ℝ) * (t.1 - (γ.1 : ℝ)) + (h.2 : ℝ) * (t.2 - (γ.2 : ℝ))) / (m : ℝ)))
      = Complex.exp (2 * Real.pi * Complex.I
            * (((h.1 : ℝ) * (γ.1 : ℝ) + (h.2 : ℝ) * (γ.2 : ℝ)) / (m : ℝ)))
        * (φ t * Complex.exp (-(2 * Real.pi * Complex.I)
            * (((h.1 : ℝ) / (m : ℝ)) * t.1 + ((h.2 : ℝ) / (m : ℝ)) * t.2))) := by
    intro t
    have key : -(2 * Real.pi * Complex.I)
          * (((h.1 : ℝ) * (t.1 - (γ.1 : ℝ)) + (h.2 : ℝ) * (t.2 - (γ.2 : ℝ))) / (m : ℝ))
        = 2 * Real.pi * Complex.I
            * (((h.1 : ℝ) * (γ.1 : ℝ) + (h.2 : ℝ) * (γ.2 : ℝ)) / (m : ℝ))
          + (-(2 * Real.pi * Complex.I)
            * (((h.1 : ℝ) / (m : ℝ)) * t.1 + ((h.2 : ℝ) / (m : ℝ)) * t.2)) := by
      field_simp
      ring
    rw [key, Complex.exp_add]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => hcongr t),
    MeasureTheory.integral_const_mul]
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  congr 1
  push_cast
  ring

end

end Work.FIArea2
