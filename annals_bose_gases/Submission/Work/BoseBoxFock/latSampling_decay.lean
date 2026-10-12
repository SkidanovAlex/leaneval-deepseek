import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.LatSamplingAux.decayTransScale
import Submission.Work.BoseBoxFock.LatSamplingAux.ftLatticeSummable
import Submission.Work.BoseBoxFock.LatSamplingAux.sampleTransScale
import Submission.Work.BoseBoxFock.poissonEuclid3Summable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- **The shifted Poisson sampling identity under rapid decay (the Schwartz form).**

For `F : ℝ³ → ℂ` continuous and rapidly decreasing at infinity (and with rapidly decreasing
Fourier transform), and any shift `z`,

    `∑'_m FT(F)(k_m)·e^{i⟪k_m,z⟫} = ℓ³ ∑'_d F(z + ℓ·latVec d)` ,   `k_m = (2π/ℓ) • latVec m`,
    `FT(F)(p) = ∫_y e^{-i⟪p,y⟫}F(y)dy` .

The right-hand side is `ℓ³` times the periodisation `P(z) = ∑'_d F(z+ℓd)` of `F` at the scale `ℓ`,
and the left-hand side is its Fourier series evaluated at `z`: the Fourier coefficients of `P` on
the torus of side `ℓ` are `ℓ⁻³∫F(x)e^{-i⟪k_m,x⟫}dx` (one period of `P` is a translate of `F`), so
the identity is the inversion of the absolutely convergent Fourier series of `P`.  Equivalently it
is Poisson summation for the translate `F(· + z)`, whose Fourier transform is
`p ↦ e^{i⟪p,z⟫}FT(F)(p)`.

This is the classical *decay-based* Poisson summation (the corpus's
`Work.BoseFixR.Rb5Lin.poisson_summation_euclid3` / `…_schwartz`), **not**
`Work.BoseFixR.poisson_scaled`, which requires `F` to be *compactly supported* (and so does not
apply to the `f_L` symbol: `fc.f(‖p‖/κ)` is compactly supported *in momentum*, so its inverse
transform is Schwartz but not compactly supported).

**Where it is used.**  It is the `θ`-frame brick of the cubic `Q̃₃` row (FS `lem:2ndQuand`, last
displayed row): the `s`-sum of that row is a `Σ_{s}f_L(s)θExp_s`-sum, i.e. the lattice sampling of
the inverse transform of the low-momentum symbol `fc.f(‖·‖/κ)`, and its periodised kernel is
exactly what the *position-space* word of FS `lem:Q3-splitting1` sees through
`Q_L = lowMult fc κ ℓ`.  Nothing here involves the box, the mode family or a state. -/
theorem latSampling_decay {ℓ : ℝ} (hℓ : 0 < ℓ)
    {F : EuclideanSpace ℝ (Fin 3) → ℂ} (hFc : Continuous F)
    (hFdec : ∀ n : ℕ, ∃ C : ℝ, ∀ y, ‖F y‖ ≤ C * (1 + ‖y‖) ^ (-(n : ℤ)))
    (hFTdec : ∀ n : ℕ, ∃ C : ℝ, ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖∫ y : EuclideanSpace ℝ (Fin 3), Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * F y‖
        ≤ C * (1 + ‖p‖) ^ (-(n : ℤ)))
    (z : EuclideanSpace ℝ (Fin 3)) :
    (∑' m : Fin 3 → ℤ,
        (∫ x : EuclideanSpace ℝ (Fin 3),
            Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) x : ℂ))) * F x)
          * Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) z : ℂ)))
      = (ℓ ^ 3 : ℂ) * ∑' d : Fin 3 → ℤ, F (z + ℓ • Work.BoseBoxFock.latVec d) := by
  have hℓc : ((ℓ : ℂ) ^ 3) ≠ 0 := by
    apply pow_ne_zero
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hℓ)
  -- * `G x = F (z + ℓ • x)`: the translated and rescaled function, to which Poisson summation on
  --   the unit lattice `ℤ³` is applied.
  have hGc : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => F (z + ℓ • x)) := by
    apply hFc.comp
    fun_prop
  have hGdec : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin 3), (1 + ‖x‖) ^ 4 * ‖F (z + ℓ • x)‖ ≤ C :=
    LatSamplingAux.decayTransScale hℓ hFdec z
  -- * absolute convergence of the Fourier series of the periodisation, from the rapid decay of
  --   the Fourier transform.
  have hFTsum := LatSamplingAux.ftLatticeSummable hℓ hFTdec z
  -- * the Fourier samples of `G` at the unit lattice, in terms of `FT(F)` at the dual lattice
  --   `k_m = (2π/ℓ) • latVec m` and the phase `e^{i⟪k_m,z⟫}`.
  have hterm : ∀ m : Fin 3 → ℤ,
      (∫ x : EuclideanSpace ℝ (Fin 3),
          F (z + ℓ • x) * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x (latVec m)))))
        = (ℓ ^ 3 : ℂ)⁻¹ *
          ((∫ y : EuclideanSpace ℝ (Fin 3),
              Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec m) y : ℂ))) * F y)
            * Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec m) z : ℂ))) :=
    fun m => LatSamplingAux.sampleTransScale hℓ F z m
  have hsum : Summable (fun m : Fin 3 → ℤ =>
      ∫ x : EuclideanSpace ℝ (Fin 3),
        F (z + ℓ • x) * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x (latVec m))))) :=
    (hFTsum.mul_left ((ℓ ^ 3 : ℂ)⁻¹)).congr (fun m => (hterm m).symm)
  -- * Poisson summation on `ℤ³` for `G`.
  have hpois := poissonEuclid3Summable (fun x : EuclideanSpace ℝ (Fin 3) => F (z + ℓ • x))
    hGc hGdec hsum
  have hpoisL : (∑' m : Fin 3 → ℤ, F (z + ℓ • latVec m))
      = ∑' m : Fin 3 → ℤ,
          ∫ x : EuclideanSpace ℝ (Fin 3),
            F (z + ℓ • x) * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x (latVec m)))) :=
    hpois
  -- * rewriting the right-hand side of Poisson summation with `hterm` and cancelling `(ℓ³)⁻¹`.
  have hmul : (ℓ ^ 3 : ℂ) * (∑' m : Fin 3 → ℤ, F (z + ℓ • latVec m))
      = ∑' m : Fin 3 → ℤ,
          (∫ y : EuclideanSpace ℝ (Fin 3),
              Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec m) y : ℂ))) * F y)
            * Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec m) z : ℂ)) := by
    rw [hpoisL, tsum_congr hterm, tsum_mul_left, ← mul_assoc, mul_inv_cancel₀ hℓc, one_mul]
  rw [← hmul]

end Work.BoseBoxFock
